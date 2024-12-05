use std::{
    cmp::{max, min},
    collections::{BinaryHeap, HashMap, HashSet},
    vec,
};

use crate::{
    conf_automaton::PCPConf,
    dep::{PCPConfDepGraph, PCPConfNode},
    pcp::{PCPConfig, PCPDir, PCP},
    pcpseq::{ExactSequence, MidExactSequence, MidWildSequence, PCPSequence},
    suffix_tree::SuffixTree,
};
use itertools::Itertools;

#[derive(Clone, Debug)]
enum DependsOn {
    Nexts(Vec<NodeId>),
    Abstract((usize, usize, NodeId)),
}

const INFINITE_MIDCHAR: bool = false;

const MAX_SUBSTR_LEN: u32 = 15;

fn remove_included_seqs(seqs: &mut Vec<PCPSequence>) {
    for i in (0..seqs.len()).rev() {
        if seqs
            .iter()
            .enumerate()
            .any(|(j, s)| i != j && s.contains(&seqs[i]))
        {
            seqs.remove(i);
        }
    }
}
fn nexts(seq: &PCPSequence, pcp: &PCP) -> Vec<PCPSequence> {
    let mut ret = seq
        .apply_pcp_avoid_midwild(pcp, |_| true, INFINITE_MIDCHAR)
        .0;
    remove_included_seqs(&mut ret);
    ret
}

fn nexts_ban_me(seq: &PCPSequence, pcp: &PCP, ban_mes: Vec<PCPSequence>) -> Vec<PCPSequence> {
    let mut ret = seq
        .apply_pcp_avoid_midwild(
            pcp,
            |p| ban_mes.iter().any(|m| p.contains(&m)),
            INFINITE_MIDCHAR,
        )
        .0;
    remove_included_seqs(&mut ret);
    ret
}

fn prevs(seq: &PCPConfig, pcp: &PCP) -> Vec<PCPConfig> {
    seq.co()
        .apply_pcp(&pcp.reverse_pcp())
        .into_iter()
        .map(|c: PCPConfig| c.co())
        .collect_vec()
}

#[test]
fn test_prevs() {
    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1111,1), Tile(1,1001), Tile(0,11)))");
    let tests = vec![
        "1001", "111111", "0011", "10", "1111", "1110", "111", "1", "0", "11", "100", "101",
    ];
    for t in tests {
        for dir in vec![PCPDir::UP, PCPDir::DN] {
            let seq = PCPConfig {
                seq: t.to_string(),
                dir,
            };
            let prevs = prevs(&seq, &pcp);
            if prevs.is_empty() {
                continue;
            }
            let nexts = prevs.iter().flat_map(|c| c.apply_pcp(&pcp)).collect_vec();
            assert!(nexts.contains(&seq), "{:?} {:?} {:?}", seq, prevs, nexts);
        }
    }
}

#[derive(Clone, Debug)]
struct Node {
    id: NodeId,
    bad: bool,
    dirty: bool,
    seq: PCPSequence,
    depends_on: Option<DependsOn>,
    referenced_by: HashSet<NodeId>,
}

impl Node {
    fn new(id: NodeId, seq: PCPSequence) -> Self {
        Self {
            id,
            bad: false,
            dirty: false,
            seq,
            depends_on: None,
            referenced_by: HashSet::new(),
        }
    }
    fn get_dependent_nodes(&self) -> Vec<NodeId> {
        match self.depends_on {
            Some(DependsOn::Nexts(ref nexts)) => nexts.clone(),
            Some(DependsOn::Abstract((_, _, id))) => vec![id],
            None => vec![],
        }
    }
}

use crate::suffix_tree::ukkonens_suffix_tree::UkkonensSuffixTree;
struct BadConfigStore {
    bad_up: Box<dyn SuffixTree>,
    bad_dn: Box<dyn SuffixTree>,
}
impl BadConfigStore {
    fn new() -> BadConfigStore {
        Self {
            // bad_up: Box::new(SuffixTreeTest{
            //     a: NaiveSuffixTree::new(),
            //     b: UkkonensSuffixTree::new(),
            // }),
            // bad_dn: Box::new(SuffixTreeTest {
            //     a: NaiveSuffixTree::new(),
            //     b: UkkonensSuffixTree::new(),
            // }),
            bad_up: Box::new(UkkonensSuffixTree::new()),
            bad_dn: Box::new(UkkonensSuffixTree::new()),
            // bad_up: Box::new(NaiveSuffixTree::new()),
            // bad_dn: Box::new(NaiveSuffixTree::new()),
        }
    }

    fn add_config(&mut self, conf: &PCPConfig) {
        match conf.dir {
            PCPDir::UP => {
                self.bad_up.insert(conf.seq.as_str());
            }
            PCPDir::DN => {
                self.bad_dn.insert(conf.seq.as_str());
            }
        }
    }

    fn contains_subset_of(&self, seq: &PCPSequence) -> bool {
        match seq {
            PCPSequence::Exact(ExactSequence { seq, dir }) => match dir {
                PCPDir::UP => self.bad_up.contains(seq),
                PCPDir::DN => self.bad_dn.contains(seq),
            },
            PCPSequence::MidExact(MidExactSequence { mid, dir }) => match dir {
                PCPDir::UP => self.bad_up.is_substr(&mid.as_str()),
                PCPDir::DN => self.bad_dn.is_substr(&mid.as_str()),
            },
            PCPSequence::MidWild { .. } => false,
        }
    }
}

fn get_str_from_seq(seq: &PCPSequence) -> String {
    match seq {
        PCPSequence::Exact(ExactSequence { seq, dir }) => seq.clone(),
        PCPSequence::MidExact(MidExactSequence { mid, dir }) => mid.clone(),
        PCPSequence::MidWild { .. } => todo!(),
    }
}

struct Graph {
    pcp: PCP,

    bad: BadConfigStore,
    bad_nodes_configs: BadConfigStore,

    nodes: Vec<Node>,

    reachable_frontier: BinaryHeap<(i32, NodeId)>, // (priority, id)
    reachable_dirties: HashSet<NodeId>,
    reachable: HashSet<NodeId>,

    mid_to_node: HashMap<PCPDir, HashMap<String, NodeId>>,
    exact_to_node: HashMap<PCPDir, HashMap<String, NodeId>>,

    starts: HashSet<NodeId>,
}

fn substrings(s: &str, min_len: usize, max_len: usize) -> Vec<String> {
    let mut ret = HashSet::<String>::new();

    for len in min_len..=max_len {
        for i in 0..=s.len() - len {
            ret.insert(s[i..i + len].to_string());
        }
    }

    ret.into_iter().collect_vec()
}

impl<'a> Graph {
    fn new(pcp: PCP) -> Self {
        let mut g = Self {
            pcp: pcp.clone(),
            bad: BadConfigStore::new(),
            bad_nodes_configs: BadConfigStore::new(),
            nodes: vec![],
            reachable_frontier: BinaryHeap::new(),
            reachable_dirties: HashSet::new(),
            reachable: HashSet::new(),
            mid_to_node: HashMap::new(),
            exact_to_node: HashMap::new(),
            starts: HashSet::new(),
        };
        g.mid_to_node.insert(PCPDir::UP, HashMap::new());
        g.mid_to_node.insert(PCPDir::DN, HashMap::new());
        g.exact_to_node.insert(PCPDir::UP, HashMap::new());
        g.exact_to_node.insert(PCPDir::DN, HashMap::new());

        let confs = pcp.co().enumerate_configurations(300000);
        println!("max_len: {:?}", confs.iter().map(|c| c.seq.len()).max());
        for conf in confs.into_iter().filter(|c| c.seq.len() <= 200) {
            g.add_bad(&conf.reverse());
        }

        for conf in pcp.get_init_config().iter_mut() {
            g.seq_to_node(&conf.to_seq());
        }
        g.starts = g.nodes.iter().map(|n| n.id).collect();

        g.recompute_start_component();
        println!(
            "finished init: {:?} {:?}",
            g.bad.bad_dn.size(),
            g.bad.bad_up.size()
        );
        g
    }

    fn is_starts_bad(&self) -> bool {
        self.starts.iter().any(|id| self.nodes[*id].bad)
    }

    fn get_bad_path(&self, id: NodeId) -> Vec<String> {
        assert!(self.nodes[id].bad);

        let mut ret = vec![];
        let mut cur = id;
        while self.nodes[cur].bad && self.nodes[cur].depends_on.is_some() {
            ret.push(format!("{:?}", self.nodes[cur].seq));
            let next = self.nodes[cur]
                .get_dependent_nodes()
                .into_iter()
                .filter(|n| self.nodes[*n].bad)
                .next();
            cur = next.unwrap();
        }
        ret.push(format!("{:?}", self.nodes[cur].seq));
        ret
    }

    fn is_reachable(&self, id: NodeId) -> bool {
        self.reachable.contains(&id)
    }

    fn add_nodes_to_start_component(&mut self, root_id: NodeId) {
        if self.reachable.contains(&root_id) {
            return;
        }
        self.reachable.insert(root_id);

        let (is_dirty, is_frontier) = {
            let node = self.get_node(root_id).unwrap();
            (node.dirty, node.depends_on.is_none())
        };

        if is_dirty {
            self.reachable_dirties.insert(root_id);
        }
        if is_frontier {
            self.reachable_frontier.push((
                -(self.nodes[root_id].seq.num_chars() as i32)
                    + (if let PCPSequence::MidExact(_) = &self.nodes[root_id].seq {
                        100000 as i32
                    } else {
                        0
                    }),
                root_id,
            ));
        }

        for dep in self.get_node(root_id).unwrap().get_dependent_nodes() {
            self.add_nodes_to_start_component(dep);
        }
    }

    fn find_closed_me_components(&mut self) -> Vec<MidExactSequence> {
        self.recompute_start_component();
        let dirties = self.reachable_dirties.clone();
        let frontiers = self.reachable_frontier.clone();
        let mut badstates: HashSet<NodeId> = HashSet::new();
        let mut queue: Vec<NodeId> = dirties
            .into_iter()
            .chain(frontiers.into_iter().map(|(_, id)| id))
            .collect();

        while let Some(id) = queue.pop() {
            badstates.insert(id);
            for dep in self.nodes[id].referenced_by.clone().into_iter() {
                if !badstates.contains(&dep) {
                    queue.push(dep);
                }
            }
        }
        let nodes = self.reachable.difference(&badstates).cloned().collect_vec();
        let mut mes: Vec<PCPSequence> = nodes
            .iter()
            .flat_map(|id| match &self.nodes[*id].seq {
                PCPSequence::MidExact(MidExactSequence { mid, dir }) => {
                    Some(self.nodes[*id].seq.clone())
                }
                _ => None,
            })
            .collect();

        remove_included_seqs(&mut mes);
        mes.into_iter()
            .map(|m| match m {
                PCPSequence::MidExact(m) => m,
                _ => panic!(),
            })
            .collect()
    }

    fn recompute_start_component(&mut self) {
        self.reachable.clear();
        self.reachable_frontier.clear();
        self.reachable_dirties.clear();
        let starts = self.starts.clone();
        for s in starts {
            self.add_nodes_to_start_component(s);
        }
    }

    fn one_step_concretize(&mut self, node_id: NodeId) {
        let node = self.get_node(node_id).unwrap();

        // ないほうがパフォーマンス高いかも
        // if let Some(abs_node) = self.find_abstraction_node_for(&node.seq) {
        //     let abs_str = get_str_from_seq(&abs_node.seq);
        //     let pos = get_str_from_seq(&node.seq).find(&abs_str).unwrap();
        //     assert!(!abs_node.bad);
        //     self.set_node_dependency(
        //         node_id,
        //         DependsOn::Abstract((pos, pos + abs_str.len(), abs_node.id)),
        //     );
        //     //println!("found another absnode {:?}");
        //     return;
        // }

        match node.depends_on {
            Some(DependsOn::Nexts(ref nexts)) => {
                println!("warn: concretizing a node that already concrete");
            }
            Some(DependsOn::Abstract((l, r, id))) => {
                let new_span = if r == node.seq.num_chars() as usize {
                    (0, r - l + 1)
                } else {
                    (l + 1, r + 1)
                };

                let is_exact_seq = if let PCPSequence::Exact(_) = self.nodes[id].seq {
                    true
                } else {
                    false
                };

                if new_span.1 - new_span.0
                    > min(
                        node.seq.num_chars() - (if is_exact_seq { 0 } else { 1 }),
                        MAX_SUBSTR_LEN,
                    ) as usize
                {
                    let new_depends_on = DependsOn::Nexts(
                        nexts(&node.seq, &self.pcp)
                            .into_iter()
                            .map(|seq| self.seq_to_node(&seq).id)
                            .collect(),
                    );
                    self.set_node_dependency(node_id, new_depends_on);
                } else {
                    let new_str: String = get_str_from_seq(&node.seq)
                        .chars()
                        .skip(new_span.0)
                        .take(new_span.1 - new_span.0)
                        .collect();
                    let new_depends_on = DependsOn::Abstract((
                        new_span.0,
                        new_span.1,
                        self.seq_to_node(&PCPSequence::MidExact(MidExactSequence {
                            mid: new_str,
                            dir: node.seq.dir(),
                        }))
                        .id,
                    ));
                    self.set_node_dependency(node_id, new_depends_on);
                }
            }
            None => println!("warn: concretizing a node that doesnt have depends_on"),
        }
    }
    fn set_node_is_dirty(&mut self, id: NodeId) {
        self.nodes[id].dirty = true;
        if self.is_reachable(id) {
            self.reachable_dirties.insert(id);
        }
    }
    fn process_dirty(&mut self, id: NodeId) {
        self.reachable_dirties.remove(&id);
        self.nodes.get_mut(id).unwrap().dirty = false;
        let node = self.get_node(id).unwrap();
        //println!("{:?} -> {:?}", id, node.depends_on);

        match &node.depends_on {
            Some(DependsOn::Nexts(_)) => {
                self.notify_node_is_bad(node.id);
            }
            Some(DependsOn::Abstract((_, _, _))) => {
                self.one_step_concretize(id);
            }
            None => todo!(),
        }
    }
    fn seq_to_node(&'a mut self, seq: &PCPSequence) -> &'a Node {
        match seq {
            PCPSequence::Exact(ExactSequence { seq, dir }) => {
                if let Some(id) = self.exact_to_node.get(dir).unwrap().get(seq) {
                    return self.get_node(*id).unwrap();
                }
            }
            PCPSequence::MidExact(MidExactSequence { mid, dir }) => {
                if let Some(id) = self.mid_to_node.get(dir).unwrap().get(mid) {
                    return self.get_node(*id).unwrap();
                }
            }
            PCPSequence::MidWild { .. } => {
                todo!()
            }
        }
        let id = self.nodes.len();
        let node = Node::new(id, seq.clone());
        self.add_node(node);
        self.get_node(id).unwrap()
    }
    fn add_bad(&mut self, conf: &PCPConfig) {
        self.bad.add_config(conf);
    }
    fn is_contains_bad(&self, seq: &PCPSequence) -> bool {
        self.bad.contains_subset_of(seq)
            || (if let PCPSequence::MidExact(MidExactSequence { mid, dir }) = seq {
                self.bad_nodes_configs.contains_subset_of(seq)
            } else {
                false
            })
    }
    fn add_node(&mut self, node: Node) {
        if self.get_node(node.id).is_some() {
            return;
        }
        self.nodes.push(node.clone());
        match &node.seq {
            PCPSequence::Exact(ExactSequence { seq, dir }) => {
                self.exact_to_node
                    .get_mut(dir)
                    .unwrap()
                    .insert(seq.clone(), node.id);
            }
            PCPSequence::MidExact(MidExactSequence { mid, dir }) => {
                self.mid_to_node
                    .get_mut(dir)
                    .unwrap()
                    .insert(mid.clone(), node.id);
            }
            PCPSequence::MidWild { .. } => {
                todo!()
            }
        }

        if node.depends_on.is_none() {
            self.reachable_frontier
                .push((-(node.seq.num_chars() as i32), node.id));
        }
        if self.is_contains_bad(&node.seq) {
            self.notify_node_is_bad(node.id);
        }
    }
    fn pop_dirty_node(&mut self) -> Option<NodeId> {
        if self.reachable_dirties.len() == 0 {
            return None;
        }
        let id = self.reachable_dirties.iter().next().unwrap().clone();
        self.reachable_dirties.remove(&id);
        Some(id)
    }
    // fn find_abstraction_node_for(&'a self, seq: &PCPSequence) -> Option<&'a Node> {
    //     return None;
    //     let seqstr = get_str_from_seq(seq);
    //     if let PCPSequence::Exact(_) = seq {
    //         let all_relax = self
    //             .mid_to_node
    //             .get(&seq.dir())
    //             .unwrap()
    //             .get(&seqstr)
    //             .map(|id| self.get_node(*id).unwrap());
    //         if all_relax.is_some() && !all_relax.unwrap().bad {
    //             return all_relax;
    //         }
    //     }

    //     if let Some(key) = substrings(
    //         &seqstr,
    //         1,
    //         max(1, min(MAX_SUBSTR_LEN as usize, seqstr.len())) - 1,
    //     )
    //     .into_iter()
    //     .sorted_by_key(|s| (s.len() as i32))
    //     .find(|s| {
    //         self.mid_to_node.get(&seq.dir()).unwrap().contains_key(s)
    //             && !self.nodes[*self.mid_to_node.get(&seq.dir()).unwrap().get(s).unwrap()].bad
    //     }) {
    //         let id = self.mid_to_node.get(&seq.dir()).unwrap().get(&key).unwrap();
    //         //println!("found abstraction for {:?} -> {:?}", seq, self.nodes[*id].seq);
    //         return self.get_node(*id);
    //     }
    //     None
    // }
    fn pop_frontier_node(&'a mut self) -> Option<&'a Node> {
        loop {
            let cur = self.reachable_frontier.pop();
            if cur.is_none() {
                return None;
            }
            let (_, id) = cur.unwrap();
            if self.nodes[id].depends_on.is_none() {
                return self.get_node(id);
            }
        }
    }
    fn get_node(&'a self, id: NodeId) -> Option<&'a Node> {
        self.nodes.get(id)
    }
    fn set_node_dependency(&mut self, id: NodeId, depends_on: DependsOn) {
        for dep in self.nodes[id].get_dependent_nodes() {
            self.nodes[dep].referenced_by.remove(&id);
        }
        let mut is_ditry = false;

        self.nodes[id].depends_on = Some(depends_on);

        for dep in self.nodes[id].get_dependent_nodes() {
            self.nodes[dep].referenced_by.insert(id);
            is_ditry |= self.nodes[dep].bad;
            self.add_nodes_to_start_component(dep);
        }

        if is_ditry {
            self.set_node_is_dirty(id);
        }
    }
    fn unroll_node_dependency(&mut self, id: NodeId) {
        if self.nodes[id].depends_on.is_some() {
            return;
        }
        let non_abstractable = match &self.nodes[id].seq {
            PCPSequence::MidExact(MidExactSequence { mid, dir }) => mid.len() == 1,
            _ => false,
        };
        let dep = if non_abstractable {
            DependsOn::Nexts(
                nexts(&self.nodes[id].seq, &self.pcp)
                    .into_iter()
                    .map(|seq| self.seq_to_node(&seq).id)
                    .collect(),
            )
        } else {
            let abs_seq: PCPSequence = PCPSequence::MidExact(MidExactSequence {
                mid: get_str_from_seq(&self.nodes[id].seq)
                    .chars()
                    .take(1)
                    .collect(),
                dir: self.nodes[id].seq.dir(),
            });
            DependsOn::Abstract((0, 1, self.seq_to_node(&abs_seq).id))
        };
        self.set_node_dependency(id, dep);
    }

    fn notify_node_is_bad(&mut self, id: NodeId) {
        if self.nodes[id].bad {
            return;
        }
        self.nodes[id].bad = true;
        self.bad_nodes_configs.add_config(&PCPConfig {
            seq: get_str_from_seq(&self.nodes[id].seq),
            dir: self.nodes[id].seq.dir(),
        });
        if self.is_reachable(id) {
            for ref_by in self.nodes[id].referenced_by.clone().into_iter() {
                self.set_node_is_dirty(ref_by);
            }
        }
    }

    fn get_invariant(&mut self) -> Vec<Node> {
        self.recompute_start_component();
        self.reachable.iter().for_each(|id| {
            println!(
                "{:?} -> {:?}",
                self.nodes[*id].seq, self.nodes[*id].depends_on
            );
        });
        assert!(self
            .reachable
            .iter()
            .all(|&id| !self.nodes[id].bad && self.nodes[id].depends_on.is_some()));

        self.reachable
            .iter()
            .map(|id| self.nodes[*id].clone())
            .collect()
    }

    fn get_most_abstracted(&self, node: &Node) -> Option<NodeId> {
        let mut cur = node.id;
        while let Some(DependsOn::Abstract((_, _, id))) = &self.nodes[cur].depends_on {
            cur = *id;
        }
        Some(cur)
    }

    fn get_invariant_automata(&mut self) -> PCPConfDepGraph {
        self.recompute_start_component();
        let mut seqs = vec![];
        for &id in self.reachable.iter() {
            if let DependsOn::Abstract(_) = &self.nodes[id].depends_on.as_ref().unwrap() {
                continue;
            }
            seqs.push(self.nodes[id].seq.clone());
        }
        let inv_node_idxs = self
            .reachable
            .iter()
            .flat_map(|&id| self.get_most_abstracted(&self.nodes[id]))
            .unique()
            .collect_vec();

        let mes = inv_node_idxs
            .iter()
            .filter_map(|id| {
                if let PCPSequence::MidExact(m) = &self.nodes[*id].seq {
                    Some(PCPSequence::MidExact(m.clone()))
                } else {
                    None
                }
            })
            .collect_vec();
        println!("seqs: {:?}", seqs.len());
        for &id in inv_node_idxs.iter() {
            self.nodes[id]
                .seq
                .apply_pcp_avoid_midwild(
                    &self.pcp,
                    |c| mes.iter().any(|m| !m.contains(&c)),
                    
                    INFINITE_MIDCHAR,
                )
                .1
                .into_iter()
                .for_each(|seq| {
                    seqs.push(seq);
                });
        }

        println!("seqs: {:?}", seqs.len());

        for i in (0..seqs.len()).rev() {
            if seqs.iter().enumerate().any(|(idx, s)| {
                let a = idx != i && s.dir() == seqs[i].dir() && s.contains(&seqs[i]);
                a
            }) {
                seqs.remove(i);
            }
        }

        println!("seqs: {:?}", seqs.len());

        let mut shrinked_seqs = self
            .pcp
            .get_init_config()
            .iter()
            .map(|c| {
                seqs.iter()
                    .find(|s| s.dir() == c.dir && s.contains(&c.to_seq()))
                    .unwrap()
                    .clone()
            })
            .collect_vec();

        let mut dep_graph: PCPConfDepGraph = PCPConfDepGraph::new();
        dep_graph.starts = (0..shrinked_seqs.len()).collect();
        let mut i = 0;
        while i < shrinked_seqs.len() {
            let c = shrinked_seqs[i].clone();
            let mut c_node = PCPConfNode {
                conf: PCPConf {
                    conf: c.to_nfa(),
                    dir: c.dir(),
                    exact: None,
                },
                deps: vec![],
            };
            for tile in self.pcp.tiles.iter() {
                let mut cur_deps: Vec<usize> = vec![];
                for n in c
                    .apply_tile(
                        &tile,
                        &|_| true,
                        
                        INFINITE_MIDCHAR,
                    )
                    .into_iter()
                {
                    let nfa = n.to_nfa();
                    if nfa.is_empty() {
                        continue;
                    }
                    if let Some((idx, _)) = shrinked_seqs
                        .iter()
                        .find_position(|s| s.dir() == n.dir() && s.contains(&n))
                    {
                        cur_deps.push(idx);
                    } else if let Some((idx, nc)) = seqs
                        .iter()
                        .find_position(|s| s.dir() == n.dir() && s.contains(&n))
                    {
                        cur_deps.push(shrinked_seqs.len());
                        shrinked_seqs.push(nc.clone());
                        seqs.remove(idx);
                    } else if let Some(((aidx, _), (bidx, _))) =
                        shrinked_seqs.iter().enumerate().tuple_combinations().find(
                            |((_, a), (_, b))| {
                                a.dir() == n.dir()
                                    && b.dir() == n.dir()
                                    && a.to_nfa().union(&b.to_nfa(), true).includes(&nfa)
                            },
                        )
                    {
                        cur_deps.push(aidx);
                        cur_deps.push(bidx);
                    } else if let Some(((i1, _), (i2, nc2))) = shrinked_seqs
                        .iter()
                        .enumerate()
                        .cartesian_product(seqs.iter().enumerate())
                        .find(|((_, a), (_, b))| {
                            a.dir() == n.dir()
                                && b.dir() == n.dir()
                                && a.to_nfa().union(&b.to_nfa(), true).includes(&nfa)
                        })
                    {
                        cur_deps.push(i1);
                        cur_deps.push(shrinked_seqs.len());
                        shrinked_seqs.push(nc2.clone());
                        seqs.remove(i2);
                    } else if let Some(((i1, nc1), (i2, nc2))) = seqs
                        .iter()
                        .enumerate()
                        .tuple_combinations()
                        .find(|((_, a), (_, b))| {
                            a.dir() == n.dir()
                                && b.dir() == n.dir()
                                && a.to_nfa().union(&b.to_nfa(), true).includes(&nfa)
                        })
                        .clone()
                    {
                        cur_deps.push(shrinked_seqs.len());
                        shrinked_seqs.push(nc1.clone());
                        cur_deps.push(shrinked_seqs.len());
                        shrinked_seqs.push(nc2.clone());
                        seqs.remove(i1);
                        seqs.remove(i2);
                    } else {
                        assert!(false)
                    }
                }
                c_node.deps.push(cur_deps);
            }
            dep_graph.nodes.insert(dep_graph.nodes.len(), c_node);
            i += 1;
        }

        // let mut all_unioned = dep_graph.iter().next().unwrap().conf.conf.determinize().create_trash_state(&(vec![Some('0'), Some('1')].into_iter().collect()));
        // for c in dep_graph.iter().skip(1) {
        //     all_unioned = all_unioned.negate().intersection(&c.conf.conf.determinize().create_trash_state(&(vec![Some('0'), Some('1')].into_iter().collect())).negate()).negate();
        //     all_unioned.reduce_size();
        //     println!("{:?}", all_unioned.transition.len());
        //     assert!(all_unioned.is_deterministic());
        // }

        for s in shrinked_seqs.iter() {
            println!("{:?}", s);
        }

        println!("{:?}", dep_graph.nodes.len());
        //dep_graph.compress_dep_graph();
        //dep_graph.show_dot_graph("dep_graph".to_string());
        println!("compressed: {:?}", dep_graph.nodes.len());
        dep_graph
    }

    fn get_graph_dot(&self) -> String {
        let mut ret = "digraph G {\n".to_string();
        for id in self.reachable.iter() {
            let node = &self.nodes[*id];
            ret += &format!(
                "{} [label=\"{:?},{}\", shape=\"{}\", style=\"filled\", fillcolor=\"{}\"]\n",
                node.id,
                node.seq.dir(),
                match &node.seq {
                    PCPSequence::Exact(ExactSequence { seq, dir }) => seq.to_string(),
                    PCPSequence::MidExact(MidExactSequence { mid, dir }) => format!(".*{mid}.*"),
                    PCPSequence::MidWild { .. } => todo!(),
                },
                match &node.seq {
                    PCPSequence::Exact(_) => "box",
                    PCPSequence::MidExact(_) => "ellipse",
                    PCPSequence::MidWild { .. } => "diamond",
                },
                if node.bad {
                    "red"
                } else if node.dirty {
                    "gray"
                } else if node.depends_on.is_none() {
                    "yellow"
                } else {
                    "white"
                }
            );
            let is_abstract_dep = if let Some(DependsOn::Abstract((_, _, id))) = &node.depends_on {
                true
            } else {
                false
            };
            for dep in node.get_dependent_nodes() {
                ret += &format!(
                    "{} -> {} [style=\"{}\"]\n",
                    node.id,
                    dep,
                    if is_abstract_dep { "dotted" } else { "solid" }
                );
            }
        }
        for start in self.starts.iter() {
            ret += &format!("start -> {} [style=\"solid\"]\n", start);
            ret += &format!("start [label=\"\", shape=\"point\"]\n");
        }
        ret += "}\n";
        ret
    }

    fn print_graph_dot(&self, name: &str) {
        let dot = self.get_graph_dot();
        std::fs::write("graph.dot", dot).unwrap();
        let output = std::process::Command::new("dot")
            .arg("-Tpng")
            .arg("graph.dot")
            .arg("-o")
            .arg(name.to_string() + ".png")
            .output()
            .unwrap();
        println!("{:?}", output);
    }

    fn add_safe_oracle(&mut self, seq: &PCPSequence) {
        let cur = self.seq_to_node(seq).id;
        self.nodes[cur].depends_on = Some(DependsOn::Nexts(vec![]));
        self.nodes[cur].dirty = false;
        self.recompute_start_component();
    }

    fn step(&mut self) -> bool {
        if let Some(dirty_node) = self.pop_dirty_node() {
            self.process_dirty(dirty_node);
            return false;
        }

        self.recompute_start_component();
        if let Some(id) = { self.pop_frontier_node().map(|n| n.id) } {
            self.unroll_node_dependency(id);
        }
        //self.print_graph_dot();
        //println!("{:?}", self.reachable_frontier.iter().map(|a| self.nodes[a.1].seq.clone()).collect_vec());

        println!(
            "reachable: {:?} me: {:?} frontier: {:?} dirties: {:?}",
            self.reachable.len(),
            self.reachable
                .iter()
                .filter(|r| match self.nodes[**r].seq {
                    PCPSequence::MidExact(_) => true,
                    _ => false,
                })
                .count(),
            //self.reachable
            // .iter()
            // .filter_map(|r| match &self.nodes[*r].seq {
            //     PCPSequence::MidExact(r) => return Some(r.clone()),
            //     _ => None,
            // }).collect_vec(),
            self.reachable_frontier.len(),
            self.reachable_dirties.len()
        );
        return (self.reachable_dirties.is_empty() && self.reachable_frontier.is_empty())
            || self.is_starts_bad();
    }
}

impl PCPConfig {
    pub fn to_seq(&self) -> PCPSequence {
        PCPSequence::Exact(ExactSequence {
            seq: self.seq.clone(),
            dir: self.dir,
        })
    }
}

type NodeId = usize;

pub fn infix_prefix_suffix_method(pcp: PCP) -> (bool, PCPConfDepGraph) {
    let mut g: Graph = Graph::new(pcp.clone());
    // g.add_safe_oracle(&&PCPSequence::Exact(ExactSequence {
    //     seq: "11011".to_string(),
    //     dir: PCPDir::DN,
    // }));
    g.add_safe_oracle(&&&PCPSequence::MidExact(MidExactSequence {
        mid: "1".to_string(),
        dir: PCPDir::DN,
    }));
    g.add_safe_oracle(&&&PCPSequence::MidExact(MidExactSequence {
        mid: "0".to_string(),
        dir: PCPDir::DN,
    }));
    println!(
        "{:?}",
        g.starts
            .iter()
            .map(|s| g.nodes[*s].seq.clone())
            .collect_vec()
    );

    let mut frame = 0;
    let mut mes: HashSet<MidExactSequence> = HashSet::new();
    let base_dir = "frames";
    while !g.step() {
        // g.recompute_start_component();
        // g.print_graph_dot(&format!("{}/{:04}", base_dir, frame));
        frame += 1;


        // if frame % 1000 == 0 {
        //     mes.extend(g.find_closed_me_components().into_iter());
        //     println!("{:?}", mes);
        // }

    }
    g.recompute_start_component();
    g.print_graph_dot("aaaa");
    if g.is_starts_bad() {
        println!("bad");
        for s in g.starts.iter() {
            if g.nodes[*s].bad {
                println!("{:?}", g.get_bad_path(*s));
            }
        }
        return (false, PCPConfDepGraph::new());
    } else {
        println!("closed");
        println!(
            "{:?}",
            g.get_invariant()
                .iter()
                .map(|n| {
                    match &n.seq {
                        PCPSequence::Exact(ExactSequence { seq, dir }) => {
                            format!("{:?} {}", dir, seq)
                        }
                        PCPSequence::MidExact(MidExactSequence { mid, dir }) => {
                            format!("{:?} .*{}.*", dir, mid)
                        }
                        PCPSequence::MidWild(MidWildSequence { dir, front, back }) => {
                            format!("{:?} {}.*{}", dir, front, back)
                        }
                    }
                })
                .collect_vec()
        );
        let inv_aut = g.get_invariant_automata();
        return (true, inv_aut);
    }
}

pub fn infix_prefix_suffix_method_find_closed_me(pcp: PCP, max_loop_count: usize) -> Vec<MidExactSequence> {
    let mut g: Graph = Graph::new(pcp.clone());
    g.add_safe_oracle(&&PCPSequence::Exact(ExactSequence {
        seq: "0".to_string(),
        dir: PCPDir::DN,
    }));
    println!(
        "{:?}",
        g.starts
            .iter()
            .map(|s| g.nodes[*s].seq.clone())
            .collect_vec()
    );

    let mut mes: HashSet<MidExactSequence> = HashSet::new();
    let mut loopcount = 0;
    while !g.step() {
        loopcount += 1;

        if loopcount % 100 == 0 {
            mes.extend(g.find_closed_me_components().into_iter());
        }

        if loopcount == max_loop_count {
            break;
        }
    }

    mes.extend(g.find_closed_me_components().into_iter());
    mes.into_iter().collect()
}
