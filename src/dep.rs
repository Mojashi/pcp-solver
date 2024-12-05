use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    io::Write,
};

use itertools::Itertools;

use crate::{automaton::NFA, conf_automaton::PCPConf, pcp::{PCPDir, PCP}};

#[derive(Clone)]
pub struct PCPConfNode {
    pub conf: PCPConf,
    pub deps: Vec<Vec<usize>>,
}

pub struct PCPConfDepGraph {
    pub nodes: BTreeMap<usize, PCPConfNode>,
    pub starts: Vec<usize>,
}
impl PCPConfDepGraph {
    pub fn new() -> PCPConfDepGraph {
        PCPConfDepGraph {
            nodes: BTreeMap::new(),
            starts: Vec::new(),
        }
    }

    pub fn shrink_to_one_node(&self, instance: &PCP) -> PCPConfDepGraph {
        let mut unioned_up = NFA::new();
        let mut unioned_dn = NFA::new();
        for n in self.nodes.iter() {
            if n.1.conf.dir == PCPDir::UP {
                unioned_up.union_mut(&n.1.conf.conf, true);
                //unioned_up = unioned_up.reduce_size();
            } else {
                unioned_dn.union_mut(&n.1.conf.conf, true);
                //unioned_dn = unioned_dn.reduce_size();
            }
            println!("unioned_up: {:?}", unioned_up.transition.len());
            println!("unioned_dn: {:?}", unioned_dn.transition.len());
        }
        let unioned_up = PCPConf {
            dir: PCPDir::UP,
            conf: unioned_up,
            exact: None,
        };
        let unioned_dn = PCPConf {
            dir: PCPDir::DN,
            conf: unioned_dn,
            exact: None,
        };
        let nodes = vec![unioned_up,unioned_dn];
        let deps = nodes.iter().map(|node| instance.tiles.iter().map(|t| 
            node.apply(t).iter().flat_map(|c| 
                if c.conf.is_empty() { vec![].into_iter() }
                else if c.dir == PCPDir::UP { vec![0].into_iter() }
                else { vec![1].into_iter() }
            ).collect_vec()
        ).collect_vec()
    ).collect_vec();

        PCPConfDepGraph {
            nodes: (0..2).map(|i| (i, PCPConfNode { conf: nodes[i].clone(), deps: deps[i].clone() })).collect(),
            starts: vec![0, 1],
        }
    }

    pub fn compress_dep_graph(&mut self) {
        // compress straight line
        let keys = self.nodes.keys().cloned().collect::<Vec<_>>();
        for idx in keys.iter() {
            let onestep = self.nodes[idx]
                .deps
                .iter()
                .flat_map(|v| v.iter())
                .filter(|i| **i != *idx)
                .cloned()
                .collect::<BTreeSet<_>>();
            let twostep = onestep
                .iter()
                .flat_map(|v| self.nodes[v].deps.iter().flat_map(|v| v.iter()))
                .filter(|i| **i != *idx && !onestep.contains(i))
                .cloned()
                .collect::<BTreeSet<_>>();

            if twostep.len() <= 1 {
                let dest = twostep.iter().next().unwrap();
                if self.nodes[dest].conf.dir == self.nodes[idx].conf.dir {
                    self.nodes.get_mut(idx).unwrap().conf.conf = self.nodes[idx]
                        .conf
                        .conf
                        .union(&self.nodes[dest].conf.conf, true);
                    let newdep = vec![*dest, *idx].into_iter().collect_vec();
                    for i in 0..self.nodes[idx].deps.len() {
                        self.nodes.get_mut(idx).unwrap().deps[i] = newdep.clone();
                    }
                }
            }
        }
        self.remove_unreachable();
    }

    pub fn remove_unreachable(&mut self) {
        let mut reachable = BTreeSet::new();
        for start in self.starts.iter() {
            reachable.insert(*start);
        }
        let mut stack = self.starts.clone();
        while let Some(idx) = stack.pop() {
            for dest in self.nodes[&idx].deps.iter().flat_map(|v| v.iter()) {
                if reachable.insert(*dest) {
                    stack.push(*dest);
                }
            }
        }

        let removed_keys = self
            .nodes
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            .difference(&reachable)
            .cloned()
            .collect_vec();
        for k in removed_keys {
            self.nodes.remove(&k);
        }
    }

    pub fn show_dot_graph(&self, path: String) {
        let mut f = std::fs::File::create(path.clone() + ".dot").unwrap();
        f.write_all(b"digraph G {\n").unwrap();
        for (idx, n) in self.nodes.iter() {
            for dep in n.deps.iter().flat_map(|v| v.iter()) {
                f.write_all(format!("{} -> {};\n", idx, dep).as_bytes())
                    .unwrap();
            }
        }
        f.write_all(b"}\n").unwrap();

        let _ = std::process::Command::new("dot")
            .arg("-Tpng")
            .arg(path.clone() + ".dot")
            .arg("-o")
            .arg(path + ".png")
            .output()
            .unwrap();
    }

    // fn construct_from_pcpconfs(pcp: PCP, confs: Vec<PCPConf>) -> PCPConfDepGraph {
    //     let mut dep_graph: PCPConfDepGraph = PCPConfDepGraph::new();
    //     let mut shrinked_seqs: Vec<PCPConf> = pcp.get_init_config().into_iter().map(|c| 
    //         confs.iter().find(|cc| cc.dir == c.dir && cc.conf.accept(&c.seq.chars().collect_vec())).unwrap().clone()
    //     ).collect_vec();
    //     dep_graph.starts = (0..shrinked_seqs.len()).collect_vec();

    //     let mut i = 0;
    //     while i < shrinked_seqs.len() {
    //         let c = shrinked_seqs[i].clone();
    //         let mut c_node = PCPConfNode {
    //             conf: c.clone(),
    //             deps: vec![],
    //         };
    //         for tile in pcp.tiles.iter() {
    //             let mut cur_deps: Vec<usize> = vec![];
    //             for n in c.apply(&tile).into_iter() {
    //                 if n.conf.is_empty() {
    //                     continue;
    //                 }
    //                 if let Some((idx, _)) = shrinked_seqs
    //                     .iter()
    //                     .find_position(|s| s.dir == n.dir && s.conf.includes(&n.conf))
    //                 {
    //                     cur_deps.push(idx);
    //                 } else if let Some((idx, nc)) = confs
    //                     .iter()
    //                     .find_position(|s| s.dir == n.dir && s.conf.includes(&n.conf))
    //                 {
    //                     cur_deps.push(shrinked_seqs.len());
    //                     shrinked_seqs.push(nc.clone());
    //                     confs.remove(idx);
    //                 } else if let Some(((aidx, _), (bidx, _))) =
    //                     shrinked_seqs.iter().enumerate().tuple_combinations().find(
    //                         |((_, a), (_, b))| {
    //                             a.dir == n.dir
    //                                 && b.dir == n.dir
    //                                 && a.conf.union(&b.conf, true).includes(&n.conf)
    //                         },
    //                     )
    //                 {
    //                     cur_deps.push(aidx);
    //                     cur_deps.push(bidx);
    //                 } else if let Some(((i1, _), (i2, nc2))) = shrinked_seqs
    //                     .iter()
    //                     .enumerate()
    //                     .cartesian_product(seqs.iter().enumerate())
    //                     .find(|((_, a), (_, b))| {
    //                         a.dir() == n.dir()
    //                             && b.dir() == n.dir()
    //                             && a.to_nfa().union(&b.to_nfa(), true).includes(&nfa)
    //                     })
    //                 {
    //                     cur_deps.push(i1);
    //                     cur_deps.push(shrinked_seqs.len());
    //                     shrinked_seqs.push(nc2.clone());
    //                     seqs.remove(i2);
    //                 } else if let Some(((i1, nc1), (i2, nc2))) = seqs
    //                     .iter()
    //                     .enumerate()
    //                     .tuple_combinations()
    //                     .find(|((_, a), (_, b))| {
    //                         a.dir() == n.dir()
    //                             && b.dir() == n.dir()
    //                             && a.to_nfa().union(&b.to_nfa(), true).includes(&nfa)
    //                     })
    //                     .clone()
    //                 {
    //                     cur_deps.push(shrinked_seqs.len());
    //                     shrinked_seqs.push(nc1.clone());
    //                     cur_deps.push(shrinked_seqs.len());
    //                     shrinked_seqs.push(nc2.clone());
    //                     seqs.remove(i1);
    //                     seqs.remove(i2);
    //                 } else {
    //                     assert!(false)
    //                 }
    //             }
    //             c_node.deps.push(cur_deps);
    //         }
    //         dep_graph.nodes.insert(dep_graph.nodes.len(), c_node);
    //         i += 1;
    //     }

    //     dep_graph
    // }
}
