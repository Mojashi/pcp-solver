use rand::seq::SliceRandom;
use std::io::Write;
use std::{
    collections::{BinaryHeap, HashMap, HashSet},
    io,
};

use crate::{
    automaton::{State, NFA},
    conf_automaton::PCPConf,
    dep::{PCPConfDepGraph, PCPConfNode},
    pcp::{PCPConfig, PCPDir, PCP},
    suffix_tree::{NaiveSuffixTree, SuffixTree},
    union_find::UnionFind,
};
use itertools::Itertools;
use rand::random;

#[derive(Clone, Debug)]
enum DependsOn {
    Nexts(Vec<NodeId>),
    OthersAbstract(Vec<NodeId>),
    Abstract((Option<Vec<HashSet<State>>>, NodeId)),
}

impl DependsOn {
    fn get_dependent_nodes(&self) -> Vec<NodeId> {
        match self {
            DependsOn::Nexts(nexts) => nexts.clone(),
            DependsOn::OthersAbstract(nexts) => nexts.clone(),
            DependsOn::Abstract((_, id)) => vec![*id],
        }
    }
}

fn nexts(seq: &PCPConf, pcp: &PCP) -> Vec<PCPConf> {
    let mut m = seq
        .apply_pcp(pcp)
        .into_iter()
        .filter(|c| !c.conf.is_empty())
        .collect_vec();
    return m;
    //m.push(seq.clone());
    let uppers = m.iter().filter(|c| c.dir == PCPDir::UP).collect_vec();
    let lowers = m.iter().filter(|c| c.dir == PCPDir::DN).collect_vec();
    let mut upper_union = NFA::new();
    let mut lower_union = NFA::new();
    for c in uppers {
        upper_union.union_mut(&c.conf, true);
    }
    for c in lowers {
        lower_union.union_mut(&c.conf, true);
    }
    upper_union = upper_union.reduce_size();
    lower_union = lower_union.reduce_size();
    return vec![
        PCPConf {
            dir: PCPDir::UP,
            conf: upper_union,
            exact: None,
        },
        PCPConf {
            dir: PCPDir::DN,
            conf: lower_union,
            exact: None,
        },
    ]
    .into_iter()
    .filter(|c| !c.conf.is_empty())
    .collect_vec();
}

fn prevs(seq: &PCPConfig, pcp: &PCP) -> Vec<PCPConfig> {
    seq.co()
        .apply_pcp(&pcp.reverse_pcp())
        .into_iter()
        .map(|c| c.co())
        .collect_vec()
}

#[test]
fn prev_test() {
    let pcp = PCP::parse_repr("1110_0__10_1__1_1011");
    let seq = PCPConfig {
        seq: "01010111010".to_string(),
        dir: PCPDir::UP,
    };
    let prevs = prevs(&seq, &pcp);
    println!("{:?}", prevs);
    assert_eq!(prevs.len(), 1);
    assert_eq!(prevs[0].seq, "1010101110");
}

#[derive(Clone, Debug)]
struct Node {
    id: NodeId,
    bad: Option<PCPConfig>,
    dirty: bool,
    seq: PCPConf,
    depends_on: Option<DependsOn>,
    referenced_by: HashSet<NodeId>,
    abstracted: bool,
}

impl Node {
    fn new(id: NodeId, seq: PCPConf) -> Self {
        Self {
            id,
            bad: None,
            dirty: false,
            seq: PCPConf {
                dir: seq.dir,
                conf: seq.conf.reduce_size(),
                exact: seq.exact,
            },
            depends_on: None,
            abstracted: false,
            referenced_by: HashSet::new(),
        }
    }

    fn get_dependent_nodes(&self) -> Vec<NodeId> {
        match &self.depends_on {
            Some(dep) => dep.get_dependent_nodes(),
            None => vec![],
        }
    }
}

struct BadConfigStore {
    bad_up: NaiveSuffixTree,
    bad_dn: NaiveSuffixTree,
}
impl BadConfigStore {
    fn new() -> BadConfigStore {
        Self {
            bad_up: NaiveSuffixTree::new(),
            bad_dn: NaiveSuffixTree::new(),
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

    fn contains_subset_of(&self, seq: &PCPConf) -> Option<PCPConfig> {
        match seq.dir {
            PCPDir::UP => self
                .bad_up
                .strs
                .iter()
                .find(|s| seq.conf.accept(&s.chars().collect_vec()))
                .map(|s| PCPConfig {
                    seq: s.clone(),
                    dir: PCPDir::UP,
                }),
            PCPDir::DN => self
                .bad_dn
                .strs
                .iter()
                .find(|s| seq.conf.accept(&s.chars().collect_vec()))
                .map(|s| PCPConfig {
                    seq: s.clone(),
                    dir: PCPDir::DN,
                }),
        }
    }
}

pub struct Graph {
    pcp: PCP,
    bad: BadConfigStore,

    pub nodes: Vec<Node>,

    reachable_frontier: BinaryHeap<(i32, NodeId)>, // (priority, id)
    reachable_dirties: HashSet<NodeId>,
    pub reachable: HashSet<NodeId>,

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

        let confs = pcp.co().enumerate_configurations(10000);
        println!("max_len: {:?}", confs.iter().map(|c| c.seq.len()).max());
        g.add_bad(&PCPConfig {
            seq: "".to_string(),
            dir: PCPDir::DN,
        });
        g.add_bad(&PCPConfig {
            seq: "".to_string(),
            dir: PCPDir::UP,
        });
        for conf in confs.into_iter().filter(|c| c.seq.len() <= 700) {
            g.add_bad(&conf.reverse());
        }

        for conf in pcp.get_init_config().iter() {
            g.seq_to_node(PCPConf::from_exact(conf));
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
        self.starts.iter().any(|id| self.nodes[*id].bad.is_some())
    }

    fn is_contained_in_union(&self, id: usize) -> Option<Vec<NodeId>> {
        return None;
        if let Some(DependsOn::Nexts(_)) = self.nodes[id].depends_on {
        } else {
            return None;
        }
        let seq = &self.nodes[id].seq;
        let mut ret = NFA::new();
        let ids = self
            .reachable
            .iter()
            .filter(|&&oid| {
                oid != id
                    && !(self.nodes[oid].seq.includes(seq) && seq.includes(&self.nodes[oid].seq))
                    && self.nodes[oid].seq.dir == seq.dir
            })
            .cloned()
            .collect_vec();
        for u in ids.iter().map(|id| &self.nodes[*id].seq.conf) {
            ret.union_mut(u, true);
        }
        if ret.includes(&seq.conf) {
            return Some(ids.clone());
        } else {
            return None;
        }
    }

    fn union_closed_check(&self) -> bool {
        let mut union_upper = NFA::new();
        let mut union_lower = NFA::new();
        for id in self.reachable.iter() {
            let seq = &self.nodes[*id].seq;
            if seq.dir == PCPDir::UP {
                union_upper.union_mut(&seq.conf, true);
            } else {
                union_lower.union_mut(&seq.conf, true);
            }
        }
        let (proceeded_up, proceeded_dn): (Vec<_>, Vec<_>) = nexts(
            &PCPConf {
                dir: PCPDir::UP,
                conf: union_upper.clone(),
                exact: None,
            },
            &self.pcp,
        )
        .into_iter()
        .chain(
            nexts(
                &PCPConf {
                    dir: PCPDir::DN,
                    conf: union_lower.clone(),
                    exact: None,
                },
                &self.pcp,
            )
            .into_iter(),
        )
        .partition(|c| c.dir == PCPDir::UP);
        let mut proceed_union_upper = NFA::new();
        let mut proceed_union_lower = NFA::new();
        for c in proceeded_up {
            proceed_union_upper.union_mut(&c.conf, true);
        }
        for c in proceeded_dn {
            proceed_union_lower.union_mut(&c.conf, true);
        }
        return union_upper.includes(&proceed_union_upper)
            && union_lower.includes(&proceed_union_lower);
    }

    fn find_abstraction_node_for(&self, node: &Node) -> Option<NodeId> {
        let mut searched = HashSet::new();
        let mut que = Vec::new();
        node.referenced_by.iter().for_each(|n| {
            que.push(*n);
            searched.insert(*n);
        });
        searched.insert(node.id);
        while !que.is_empty() {
            let cur = que.pop().unwrap();
            if !self.reachable.contains(&cur) {
                continue;
            }
            let cur_node: &Node = self.get_node(cur).unwrap();
            if cur_node.seq.dir == node.seq.dir
                && !cur_node.bad.is_some()
                && !cur_node.dirty
                && cur_node.seq.conf.includes(&node.seq.conf)
            {
                return Some(cur);
            }
            for n in cur_node.referenced_by.iter() {
                if !searched.contains(n) {
                    searched.insert(*n);
                    que.push(*n);
                }
            }
        }

        for other_id in self.reachable.iter().filter(|id| !searched.contains(id)) {
            let other = self.get_node(*other_id).unwrap();
            if other.seq.exact.is_none()
                && node.seq.dir == other.seq.dir
                && !other.bad.is_some()
                && node.id != other.id
                && other.seq.conf.includes(&node.seq.conf)
                && !node.seq.conf.includes(&other.seq.conf)
            {
                return Some(other.id);
            }
        }
        None
    }

    // まあ有用っぽいけど遅い
    fn find_concretize_node_for(&self, node: &Node) -> Vec<NodeId> {
        return vec![];
        self.reachable_dirties
            .iter()
            .filter(|other_id| {
                let other = self.get_node(**other_id).unwrap();
                return node.seq.dir == other.seq.dir
                    && !other.bad.is_some()
                    && node.id != other.id
                    && node.seq.conf.includes(&other.seq.conf)
                    && !other.seq.conf.includes(&node.seq.conf);
            })
            .cloned()
            .collect_vec()
    }

    fn seq_to_node(&'a mut self, seq: PCPConf) -> &'a Node {
        // let id = self.nodes.len();
        // let node = Node::new(id, seq);
        // self.add_node(node);
        // return self.get_node(id).unwrap();
        //seq.conf.show_dot("seq");
        let id = if let Some(e) = self
            .nodes
            .iter()
            .find(|n| n.seq.dir == seq.dir && n.seq.conf.is_equal(&seq.conf))
        {
            e.id
        } else {
            let id = self.nodes.len();
            let node = Node::new(id, seq);
            self.add_node(node);
            id
        };
        self.get_node(id).unwrap()
    }

    fn get_bad_path(&self, id: NodeId) -> Vec<String> {
        assert!(self.nodes[id].bad.is_some());

        let mut ret = vec![];
        let mut cur = id;
        while self.nodes[cur].bad.is_some() && self.nodes[cur].depends_on.is_some() {
            ret.push(format!("{:?}", self.nodes[cur].seq));
            let next = self.nodes[cur]
                .get_dependent_nodes()
                .into_iter()
                .filter(|n| self.nodes[*n].bad.is_some())
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

        if let Some(b) = &self.nodes[root_id].bad {
            self.notify_node_is_bad(root_id, b.clone());
            return;
        }

        let (is_dirty, is_frontier) = {
            let node = self.get_node(root_id).unwrap();
            (node.dirty, node.depends_on.is_none())
        };

        if is_dirty {
            self.reachable_dirties.insert(root_id);
        }
        if is_frontier {
            self.reachable_frontier.push((
                -(self.nodes[root_id].seq.conf.states.len() as i32
                    + if self.nodes[root_id].seq.exact.is_some() {
                        1000
                    } else {
                        0
                    }),
                root_id,
            ));
        }

        let mut is_dirty = false;
        for dep in self.get_node(root_id).unwrap().get_dependent_nodes() {
            self.add_nodes_to_start_component(dep);
            is_dirty |= self.nodes[dep].dirty;
        }
        if is_dirty {
            self.set_node_is_dirty(root_id);
        }
    }

    fn find_closed_components(&mut self) -> Vec<NodeId> {
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
        return self.reachable.difference(&badstates).cloned().collect_vec();
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
        let new_dep = if let Some(abs) = self.find_abstraction_node_for(&self.nodes[node_id]) {
            DependsOn::Abstract((None, abs))
        } else {
            match &self.nodes[node_id].depends_on {
                None => {
                    if !self.nodes[node_id].abstracted {
                        self.create_abstraction(&self.nodes[node_id].seq.clone())
                    } else {
                        DependsOn::Nexts(
                            nexts(&self.nodes[node_id].seq, &self.pcp)
                                .into_iter()
                                .map(|seq| self.seq_to_node(seq).id)
                                .collect(),
                        )
                    }
                }
                Some(DependsOn::Nexts(ref nexts)) => {
                    println!("warn: concretizing a node that already concrete");
                    self.nodes[node_id].depends_on.clone().unwrap()
                }
                Some(DependsOn::OthersAbstract(ref nexts)) => {
                    self.create_abstraction(&self.nodes[node_id].seq.clone())
                }
                Some(DependsOn::Abstract((None, id))) => {
                    self.create_abstraction(&self.nodes[node_id].seq.clone())
                }
                Some(DependsOn::Abstract((Some(ds), id))) => {
                    let mut ds: Vec<HashSet<String>> = ds.clone();
                    loop {
                        if ds.len() == 0 {
                            println!("re-abstraction");
                            break self.create_abstraction(&self.nodes[node_id].seq.clone());
                        }

                        let random_idx = random::<usize>() % ds.len();
                        let mut removed_set = ds.remove(random_idx);
                        removed_set.remove(&removed_set.iter().next().unwrap().clone());
                        ds.push(removed_set);
                        ds.retain(|s| s.len() > 1);

                        let mut nfa = self.nodes[node_id].seq.conf.clone();

                        if let Some(_) = self.is_contains_bad(&PCPConf {
                            dir: self.nodes[node_id].seq.dir,
                            conf: nfa.clone(),
                            exact: None,
                        }) {
                            nfa = self.nodes[node_id].seq.conf.clone();
                        }

                        let new_nfa =
                            nfa.merge_states(ds.iter().map(|s| s.iter().collect()).collect_vec());
                        if !self.nodes[node_id].seq.conf.is_equal(&new_nfa) {
                            break DependsOn::Abstract((
                                Some(ds),
                                self.seq_to_node(PCPConf {
                                    dir: self.nodes[node_id].seq.dir,
                                    conf: new_nfa,
                                    exact: None,
                                })
                                .id,
                            ));
                        }
                    }
                }
            }
        };
        self.set_node_dependency(node_id, new_dep);
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
        if self.nodes[id].bad.is_some() {
            return;
        }
        //println!("{:?} -> {:?}", id, node.depends_on);

        match self.nodes[id].depends_on.clone() {
            Some(DependsOn::Nexts(nextconfs)) => {
                if self.nodes[id].bad.is_some() {
                    return;
                }
                let prevconfs = nextconfs
                    .iter()
                    .flat_map(|n| self.nodes[*n].bad.clone())
                    .flat_map(|c| prevs(&c, &self.pcp))
                    .collect_vec();
                for prevconf in prevconfs {
                    if self.nodes[id].seq.accept(&prevconf) {
                        self.notify_node_is_bad(id, prevconf.clone());
                        break;
                    }
                }
            }
            Some(DependsOn::OthersAbstract(nextconfs)) => {
                self.one_step_concretize(id);
            }
            Some(DependsOn::Abstract((_, _))) => {
                self.one_step_concretize(id);
            }
            None => todo!(),
        }
    }
    fn add_bad(&mut self, conf: &PCPConfig) {
        self.bad.add_config(conf);
        let bad_nodes = self
            .nodes
            .iter()
            .filter(|n| n.bad.is_some())
            .map(|n| n.id)
            .collect_vec();
        bad_nodes.iter().for_each(|&id| {
            if self.nodes[id].seq.accept(&conf) {
                self.notify_node_is_bad(id, conf.clone());
            }
        });
    }
    fn is_contains_bad(&self, seq: &PCPConf) -> Option<PCPConfig> {
        self.bad.contains_subset_of(seq)
    }
    fn add_node(&mut self, node: Node) {
        if self.get_node(node.id).is_some() {
            return;
        }
        self.nodes.push(node.clone());

        if node.depends_on.is_none() {
            self.add_nodes_to_start_component(node.id);
        }
        if let Some(badconfig) = self.is_contains_bad(&node.seq) {
            println!("reached bad {:?}", node.id);
            self.notify_node_is_bad(node.id, badconfig);
        } else {
            if let Some(ids) = self.is_contained_in_union(node.id) {
                println!("contained in union {:?} by {:?}", node.id, ids.clone());

                self.set_node_dependency(node.id, DependsOn::OthersAbstract(ids));
            } else {
                let concs = self.find_concretize_node_for(&node);
                println!("concs {:?}", concs.len());
                for conc in concs {
                    // if let Some(DependsOn::Abstract((_, id))) = &self.nodes[conc].depends_on {
                    //     if self.nodes[*id].seq.conf.states.len() <= node.seq.conf.states.len() {
                    //         println!("skip {:?} {:?}", node.id, id);
                    //         continue;
                    //     }
                    // }
                    self.set_node_dependency(conc, DependsOn::Abstract((None, node.id)));
                }
            }
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

        self.nodes[id].depends_on = Some(depends_on.clone());

        for dep in self.nodes[id].get_dependent_nodes() {
            self.nodes[dep].referenced_by.insert(id);
            is_ditry |= self.nodes[dep].bad.is_some();
            self.add_nodes_to_start_component(dep);
        }

        if is_ditry {
            self.set_node_is_dirty(id);
        }
    }

    fn create_abstraction_merge_as_can(&mut self, seq: &PCPConf) -> DependsOn {
        let mut nfa = seq.conf.clone();

        if self
            .is_contains_bad(&PCPConf {
                dir: seq.dir,
                conf: nfa.clone(),
                exact: None,
            })
            .is_some()
        {
            println!("bad abstraction");
        }

        let mut state_shuffled = nfa.states.iter().cloned().collect_vec();
        state_shuffled.shuffle(&mut rand::thread_rng());
        let combs = state_shuffled.iter().tuple_combinations().collect_vec();
        println!("p {:?}", combs.len());

        let mut ds = UnionFind::<State>::new();

        let mut bad_merges: Vec<(State, State)> = vec![];
        for (s, t) in combs.iter() {
            if !ds.connected(s, t) {
                if bad_merges
                    .iter()
                    .any(|(a, b)| ds.connected(&s, a) && ds.connected(&t, b))
                {
                    continue;
                }
                let s_contents = ds.find_contents(s);
                let t_contents = ds.find_contents(t);
                let s = nfa
                    .states
                    .iter()
                    .find(|a| s_contents.contains(*a))
                    .cloned()
                    .unwrap();
                let t = nfa
                    .states
                    .iter()
                    .find(|a| t_contents.contains(*a))
                    .cloned()
                    .unwrap();

                let try_nfa = nfa.merge_states(vec![[&s, &t].into_iter().collect()]);
                let represent_state = if try_nfa.states.contains(&s) { &s } else { &t };
                assert!(try_nfa.states.contains(represent_state));
                let bad = self
                    .is_contains_bad(&PCPConf {
                        dir: seq.dir,
                        conf: try_nfa.clone(),
                        exact: None,
                    })
                    .is_some();
                if !bad {
                    nfa = try_nfa;
                    ds.merge(&s, &t);
                } else {
                    bad_merges.push((s, t));
                }
            }
        }

        if nfa.is_equal(&seq.conf) {
            return DependsOn::Nexts(
                nexts(seq, &self.pcp)
                    .into_iter()
                    .map(|seq| self.seq_to_node(seq).id)
                    .collect(),
            );
        }

        let mut hm = ds.to_hashmaps();
        hm.retain(|s| s.len() > 1);
        println!("merged: {} -> {}", seq.conf.states.len(), nfa.states.len());

        let ret_node_id = self
            .seq_to_node(PCPConf {
                dir: seq.dir,
                conf: nfa,
                exact: None,
            })
            .id;
        self.nodes[ret_node_id].abstracted = true;
        return DependsOn::Abstract((Some(hm), ret_node_id));
    }

    fn create_abstraction_labelling_residuals(&mut self, seq: &PCPConf) -> DependsOn {
        let mut nfa = seq.conf.clone();

        if self
            .is_contains_bad(&PCPConf {
                dir: seq.dir,
                conf: nfa.clone(),
                exact: None,
            })
            .is_some()
        {
            println!("bad abstraction");
            return DependsOn::Nexts(
                nexts(seq, &self.pcp)
                    .into_iter()
                    .map(|seq| self.seq_to_node(seq).id)
                    .collect(),
            );
        }

        let badstrings: Vec<String> = match seq.dir {
            PCPDir::UP => self.bad.bad_up.strs.clone(),
            PCPDir::DN => self.bad.bad_dn.strs.clone(),
        }
        .iter()
        .map(|s| s.clone())
        .collect_vec();
        let rev_badstrings: Vec<String> = badstrings
            .iter()
            .map(|s| s.chars().rev().collect::<String>())
            .collect_vec();

        print!("states: {}", seq.conf.states.len());
        io::stdout().flush().unwrap();

        loop {
            let bef_states = nfa.states.len();
            // let ress = nfa.backward_acceptables_for_each_states_ss(
            //     nfa.start.clone(),
            //     badstrings
            //         .iter()
            //         .map(|s| s.as_str())
            //         .collect_vec(),
            // );

            let ress = nfa.residuals_for_each_states(
                nfa.start.clone(),
                badstrings.iter().map(|s| s.as_str()).collect_vec(),
            );
            nfa = nfa.quotient_aut(ress);
            print!(" -> {}", nfa.states.len());

            let reversed = nfa.reversed();
            let ress = reversed.residuals_for_each_states(
                reversed.start.clone(),
                rev_badstrings.iter().map(|s| s.as_str()).collect_vec(),
            );
            nfa = nfa.quotient_aut(ress);
            print!(" -> {}", nfa.states.len());

            if bef_states <= nfa.states.len() {
                break;
            }
        }
        println!("");
        //nfa.show_dot("nfaa");

        // assert!(self
        //     .is_contains_bad(&PCPConf {
        //         dir: seq.dir,
        //         conf: nfa.clone(),
        //         exact: None,
        //     })
        //     .is_none());

        if nfa.is_equal(&seq.conf) {
            return DependsOn::Nexts(
                nexts(seq, &self.pcp)
                    .into_iter()
                    .map(|seq| self.seq_to_node(seq).id)
                    .collect(),
            );
        }

        let ret_node = self
            .seq_to_node(PCPConf {
                dir: seq.dir,
                conf: nfa,
                exact: None,
            })
            .id;
        self.nodes[ret_node].abstracted = true;
        return DependsOn::Abstract((Some(vec![]), ret_node));
    }

    fn create_abstraction(&mut self, seq: &PCPConf) -> DependsOn {
        return self.create_abstraction_merge_as_can(seq);
        //return self.create_abstraction_labelling_residuals(seq);
    }

    fn notify_node_is_bad(&mut self, id: NodeId, badconfig: PCPConfig) {
        if self.nodes[id].bad.is_some() {
            return;
        }
        self.add_bad(&badconfig);
        self.nodes[id].bad = Some(badconfig.clone());
        if self.is_reachable(id) {
            for ref_by in self.nodes[id].referenced_by.clone().into_iter() {
                self.set_node_is_dirty(ref_by);
            }
            assert!(self.nodes[id].seq.accept(&badconfig));

            let prevconfs = prevs(&badconfig, &self.pcp);
            for ref_by in self.nodes[id].referenced_by.clone().into_iter() {
                if self.nodes[ref_by].bad.is_some() {
                    continue;
                }
                match self.nodes[ref_by].depends_on.as_ref().unwrap() {
                    DependsOn::Nexts(_) => {
                        for prevconf in prevconfs.iter() {
                            if self.nodes[ref_by].seq.accept(&prevconf) {
                                self.notify_node_is_bad(ref_by, prevconf.clone());
                            }
                        }
                    }
                    DependsOn::OthersAbstract(_) => {
                        if self.nodes[ref_by].seq.accept(&badconfig) {
                            self.notify_node_is_bad(ref_by, badconfig.clone());
                        }
                    }
                    DependsOn::Abstract(_) => {
                        if self.nodes[ref_by].seq.accept(&badconfig) {
                            self.notify_node_is_bad(ref_by, badconfig.clone());
                        }
                    }
                }
            }
        }
    }

    fn get_invariant(&mut self) -> Vec<Node> {
        self.recompute_start_component();
        assert!(self
            .reachable
            .iter()
            .all(|&id| !self.nodes[id].bad.is_some() && self.nodes[id].depends_on.is_some()));

        self.reachable
            .iter()
            .map(|id| self.nodes[*id].clone())
            .collect()
    }

    fn find_most_abstract(&self, node: &Node) -> NodeId {
        let mut current = node;
        loop {
            match &current.depends_on {
                Some(DependsOn::Abstract((_, id))) => {
                    current = &self.nodes[*id];
                }
                Some(DependsOn::OthersAbstract(ids)) => break,
                _ => {
                    break;
                }
            }
        }
        current.id
    }

    fn get_invariant_auts(&mut self) -> PCPConfDepGraph {
        assert!(self.union_closed_check());
        let inv = self.get_invariant();
        let mut dep = PCPConfDepGraph::new();
        let most_abstracted_nodeids = inv
            .iter()
            .map(|n| self.find_most_abstract(n))
            .unique()
            .collect_vec();

        for node_idx in most_abstracted_nodeids.iter() {
            let node = &self.nodes[*node_idx];
            assert!(!node.dirty && !node.bad.is_some() && node.depends_on.is_some());
            match node.depends_on {
                Some(DependsOn::Nexts(_)) => {}
                _ => assert!(false),
            }

            let candidates: Vec<NodeId> = node
                .get_dependent_nodes()
                .iter()
                .map(|n| self.find_most_abstract(&self.nodes[*n]))
                .collect_vec();
            let candidate_union_auts_upper = candidates
                .iter()
                .filter(|cand| self.nodes[**cand].seq.dir == PCPDir::UP)
                .fold(NFA::new(), |acc, cand| {
                    acc.union(&self.nodes[*cand].seq.conf, true)
                });
            let candidate_union_auts_lower = candidates
                .iter()
                .filter(|cand| self.nodes[**cand].seq.dir == PCPDir::DN)
                .fold(NFA::new(), |acc, cand| {
                    acc.union(&self.nodes[*cand].seq.conf, true)
                });

            let mut deps: Vec<Vec<usize>> = vec![];
            for tile in self.pcp.tiles.iter() {
                deps.push(
                    node.seq
                        .apply(tile)
                        .iter()
                        .filter(|c| !c.conf.is_empty())
                        .map(|c| {
                            if c.dir == PCPDir::UP {
                                assert!(
                                    candidate_union_auts_upper.includes(&c.conf),
                                    "{}",
                                    node_idx
                                );
                            } else {
                                assert!(
                                    candidate_union_auts_lower.includes(&c.conf),
                                    "{}",
                                    node_idx
                                );
                            }

                            let cov = candidates
                                .iter()
                                .find(|cand| {
                                    self.nodes[**cand].seq.dir == c.dir
                                        && self.nodes[**cand].seq.conf.includes(&c.conf)
                                })
                                .unwrap();
                            *cov
                        })
                        .collect_vec(),
                );
            }
            dep.nodes.insert(
                node.id,
                PCPConfNode {
                    conf: node.seq.clone(),
                    deps: deps,
                },
            );
        }
        dep
    }

    fn get_graph_dot(&self) -> String {
        let mut ret = "digraph G {\n".to_string();
        for id in self.reachable.iter() {
            let node = &self.nodes[*id];
            ret += &format!(
                "{} [label=\"{}:{:?},{} ex:{}\", shape=\"{}\", style=\"filled\", fillcolor=\"{}\"]\n",
                node.id,
                node.id,
                node.seq.dir,
                match &node.seq.exact {
                    Some(e) => e.to_string(),
                    None => node.seq.conf.states.len().to_string(),
                },
                node.seq.conf.get_element().map(|e| e.iter().collect::<String>()).unwrap(),
                match node.seq.exact {
                    Some(_) => "box",
                    None => "ellipse",
                },
                if node.bad.is_some() {
                    "red"
                } else if node.dirty {
                    "gray"
                } else if node.depends_on.is_none() {
                    "yellow"
                } else {
                    "white"
                }
            );
            let is_abstract_dep = match &node.depends_on {
                Some(DependsOn::Abstract(_)) => true,
                Some(DependsOn::OthersAbstract(_)) => true,
                _ => false,
            };
            for dep in node.get_dependent_nodes() {
                ret += &format!(
                    "{} -> {} [style=\"{}\",label=\"{}\"]\n",
                    node.id,
                    dep,
                    if is_abstract_dep { "dotted" } else { "solid" },
                    if let Some(DependsOn::Abstract((a, _))) = &node.depends_on {
                        format!("{:?}", a).replace('\"', "")
                    } else {
                        "".to_string()
                    }
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

    fn print_graph_dot(&self) {
        let dot = self.get_graph_dot();
        std::fs::write("graph.dot", dot).unwrap();
        let output = std::process::Command::new("dot")
            .arg("-Tpng")
            .arg("graph.dot")
            .arg("-o")
            .arg("graph.png")
            .output()
            .unwrap();
        println!("{:?}", output);
    }

    fn step(&mut self) -> bool {
        println!("step");
        if let Some(dirty_node) = self.pop_dirty_node() {
            self.process_dirty(dirty_node);
            return false;
        }
        self.recompute_start_component();
        //self.print_graph_dot();

        // let closed = self.find_closed_components();
        // let closed = closed
        //     .iter()
        //     .filter(|c| self.nodes[**c].seq.dir == PCPDir::UP)
        //     .cloned()
        //     .collect_vec();
        // if closed.len() > 0 {
        //     println!("closed: {:?}", closed.len());
        //     for &c in closed.iter() {
        //         //self.nodes[c].seq.conf.show_dot(format!("closed_{}.dot", c).as_str());
        //         let example = self.nodes[c].seq.conf.get_element().unwrap();
        //         println!("example: {:?}", example);
        //     }
        // }

        if let Some(id) = { self.pop_frontier_node().map(|n| n.id) } {
            if let Some(bad) = &self.nodes[id].bad {
                println!("front bad: {:?}", bad);
                self.notify_node_is_bad(id, bad.clone());
            } else {
                println!("o");
                self.one_step_concretize(id);
                println!("o2");
            }
        }
        println!(
            "reachable: {:?} frontier: {:?} dirties: {:?}",
            self.reachable.len(),
            self.reachable_frontier.len(),
            self.reachable_dirties.len()
        );
        return (self.reachable_dirties.is_empty() && self.reachable_frontier.is_empty())
            || self.is_starts_bad();
    }
}

type NodeId = usize;

pub fn regular_language_method(pcp: PCP) -> (bool, PCPConfDepGraph) {
    let mut g: Graph = Graph::new(pcp.clone());
    // println!(
    //     "{:?}",
    //     g.starts
    //         .iter()
    //         .map(|s| g.nodes[*s].seq.clone())
    //         .collect_vec()
    // );

    while !g.step() {}
    g.recompute_start_component();
    g.print_graph_dot();

    if g.is_starts_bad() {
        println!("bad");
        for s in g.starts.iter() {
            if g.nodes[*s].bad.is_some() {
                println!("{:?}", g.get_bad_path(*s));
            }
        }
        return (false, PCPConfDepGraph::new());
    } else {
        println!("closed");
        return (true, g.get_invariant_auts());
    }
}
