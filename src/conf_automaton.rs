use itertools::Itertools;

use crate::{
    automaton::{self, Transducer, Transition, NFA},
    pcp::{PCPConfig, PCPDir, Tile, PCP},
};

pub struct ConfAutomaton {
    pub upper: automaton::NFA<char>,
    pub lower: automaton::NFA<char>,
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct PCPConf {
    pub dir: PCPDir,
    pub conf: automaton::NFA<char>,
    pub exact: Option<String>,
}

#[derive(Debug, Clone)]
pub enum ExactOrAut {
    Exact(PCPConfig),
    Aut(PCPConf),
}

impl ExactOrAut {
    pub fn swap_dir(&self) -> ExactOrAut {
        match self {
            ExactOrAut::Exact(conf) => ExactOrAut::Exact(conf.swap_dir()),
            ExactOrAut::Aut(conf) => ExactOrAut::Aut(conf.swap_dir()),
        }
    }
    pub fn dir(&self) -> PCPDir {
        match self {
            ExactOrAut::Exact(conf) => conf.dir,
            ExactOrAut::Aut(conf) => conf.dir,
        }
    }
    pub fn accept(&self, seq: &String) -> bool {
        match self {
            ExactOrAut::Exact(conf) => conf.seq == *seq,
            ExactOrAut::Aut(conf) => conf.conf.accept(&seq.chars().collect_vec()),
        }
    }
    // pub fn apply_pcp(&self, pcp: &PCP) -> Vec<ExactOrAut> {
    //     match self {
    //         ExactOrAut::Exact(conf) => conf
    //             .apply_pcp(pcp)
    //             .into_iter()
    //             .map(|c| ExactOrAut::Exact(c))
    //             .collect_vec(),
    //         ExactOrAut::Aut(conf) => conf.apply_pcp(pcp),
    //     }
    // }
    pub fn size(&self) -> usize {
        match self {
            ExactOrAut::Exact(conf) => conf.seq.len(),
            ExactOrAut::Aut(conf) => conf.conf.states.len(),
        }
    }
    pub fn is_equal(&self, other: &ExactOrAut) -> bool {
        self.dir() == other.dir() && self.includes(other) && other.includes(self)
    }
    pub fn includes(&self, other: &ExactOrAut) -> bool {
        self.dir() == other.dir()
            && match (self, other) {
                (ExactOrAut::Aut(conf1), ExactOrAut::Aut(conf2)) => {
                    conf1.conf.includes(&conf2.conf)
                }
                (ExactOrAut::Exact(conf1), ExactOrAut::Aut(conf2)) => {
                    conf2.conf.is_equal(&NFA::from_constant(&conf1.seq))
                }
                (_, ExactOrAut::Exact(conf2)) => self.accept(&conf2.seq),
            }
    }

    pub fn toAut(&self) -> PCPConf {
        match self {
            ExactOrAut::Exact(conf) => PCPConf::from_exact(conf),
            ExactOrAut::Aut(conf) => conf.clone(),
        }
    }
}

#[test]
fn test_apply_tile() {
    let pcp = PCP::parse_pcp_string("Tile(100,1), Tile(0,100), Tile(1,00)");
    let conf2 = PCPConfig {
        dir: PCPDir::UP,
        seq: "00".to_string(),
    };
    let conf = PCPConf::from_exact(&conf2);

    let nex1 = conf.apply_pcp(&pcp);
    let nex2 = conf2.apply_pcp(&pcp);

    nex2.iter().for_each(|s| {
        assert!(
            nex1.iter()
                .any(|s2| s2.dir == s.dir && s2.conf.accept(&s.seq.chars().collect_vec())),
            "{:?}",
            s
        );
    })
}

impl PCPConf {
    pub fn from_exact(conf: &PCPConfig) -> Self {
        PCPConf {
            dir: conf.dir,
            conf: NFA::from_constant(&conf.seq),
            exact: Some(conf.seq.clone()),
        }
    }
    pub fn swap_dir(&self) -> PCPConf {
        PCPConf {
            dir: self.dir.opposite(),
            conf: self.conf.clone(),
            exact: self.exact.clone(),
        }
    }
    pub fn apply_pcp(&self, pcp: &PCP) -> Vec<PCPConf> {
        if let Some(e) = &self.exact {
            PCPConfig {
                dir: self.dir,
                seq: e.clone(),
            }
            .apply_pcp(pcp).into_iter().map(|c| PCPConf::from_exact(&c)).collect_vec()
        } else {
            pcp.tiles
                .iter()
                .flat_map(|tile| self.apply(tile))
                .collect_vec()
        }
    }
    pub fn apply(&self, tile: &Tile) -> Vec<PCPConf> {
        if self.dir == PCPDir::DN {
            return self
                .swap_dir()
                .apply(&tile.swap_tile())
                .into_iter()
                .map(|c| c.swap_dir())
                .collect_vec();
        }

        let mut ret = vec![PCPConf {
            dir: self.dir,
            conf: self
                .conf
                .append_vec(&tile.up.chars().map(|s| Some(s)).collect_vec())
                .left_quotient(&tile.dn.chars().map(|s| Some(s)).collect_vec())
                .reduce_size(),
            exact: None,
        }];

        for len in 0..tile.dn.len() {
            let (consumed, remaining) = &tile.dn.split_at(len);
            if self.conf.accept(&consumed.chars().collect_vec()) && remaining.starts_with(&tile.up)
            {
                ret.push(PCPConf::from_exact(&PCPConfig {
                    dir: PCPDir::DN,
                    seq: remaining[tile.up.len()..].to_string(),
                }))
            }
        }
        ret.into_iter().collect_vec()
    }

    pub fn accept(&self, conf: &PCPConfig) -> bool {
        conf.dir == self.dir && self.conf.accept(&conf.seq.chars().collect_vec())
    }

    pub fn includes(&self, other: &PCPConf) -> bool {
        self.dir == other.dir && self.conf.includes(&other.conf)
    }
    pub fn accept_empty(&self) -> bool {
        self.conf.accept(&vec![])
    }
}

pub struct PCPAutomaton {
    // these domains are the same
    pub upper: automaton::Transducer<char, char>,
    pub lower: automaton::Transducer<char, char>,
}
    
#[test]
fn test_reduced_aut_() {
    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1001,1), Tile(10,0), Tile(0,100)))");//.reverse_pcp();
    let mut reduced_aut: PCPAutomaton = pcp.to_automaton();

    // reduced_aut.upper.show_dot("reduced/upper");
    // reduced_aut.lower.show_dot("reduced/lower");

    for i in 0..10 {
        let new_reduced_aut = reduced_aut.construct_reduced_automaton();
        println!(
            "{:?}",
            new_reduced_aut
                .upper
                .get_input_nfa()
                .is_equal(&reduced_aut.upper.get_output_nfa())
        );
        println!(
            "{:?}",
            new_reduced_aut
                .lower
                .get_input_nfa()
                .is_equal(&reduced_aut.lower.get_output_nfa())
        );

        //println!("{:?}", new_reduced_aut.upper.get_input_nfa().reduce_size().is_equal(&reduced_aut.upper.get_output_nfa().reduce_size()));
        //new_reduced_aut.upper.get_input_nfa().reduce_size().show_dot("new_reduced_aut_upper_input");
        //reduced_aut.upper.get_output_nfa().reduce_size().show_dot("reduced_aut_upper_output");

        reduced_aut = new_reduced_aut;

        println!("reduced upper: {}", reduced_aut.upper.states.len());
        println!("reduced lower: {}", reduced_aut.lower.states.len());
        // reduced_aut
        //     .upper
        //     .show_dot(("reduced/upper".to_string() + i.to_string().as_str()).borrow());
        // reduced_aut
        //     .lower
        //     .show_dot(("reduced/lower".to_string() + i.to_string().as_str()).borrow());
        // if i % 2 == 0 {
        //     assert!(reduced_aut.upper.get_input_nfa().accept(co_ans.borrow()));
        //     assert!(reduced_aut.lower.get_input_nfa().accept(co_ans.borrow()));
        // } else {
        //     assert!(reduced_aut.upper.get_input_nfa().accept(ans.borrow()));
        //     assert!(reduced_aut.lower.get_input_nfa().accept(ans.borrow()));
        // }
        assert!(reduced_aut.upper.get_input_nfa().accept(&vec![]));
        assert!(reduced_aut.lower.get_input_nfa().accept(&vec![]));
    }
}

#[test]
fn test_reduced_aut2() {
    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1101,1), Tile(1,101), Tile(0,011)))");
    let mut reduced_aut = pcp.to_automaton();
    for i in 0..6 {
        reduced_aut = reduced_aut.construct_reduced_automaton();
        assert!(reduced_aut.upper.get_input_nfa().accept(&vec![]));
        assert!(reduced_aut.lower.get_input_nfa().accept(&vec![]));

        println!(
            "reduced upper: {}",
            reduced_aut
                .upper
                .transition
                .values()
                .flatten()
                .collect_vec()
                .len()
        );
        println!(
            "reduced lower: {}",
            reduced_aut
                .lower
                .transition
                .values()
                .flatten()
                .collect_vec()
                .len()
        );
    }
    reduced_aut.upper.show_dot("reduced/upper");
    reduced_aut.lower.show_dot("reduced/lower");
    println!("ans: {:?}", reduced_aut.upper.get_input_nfa().get_element());
    println!("ans: {:?}", reduced_aut.lower.get_input_nfa().get_element());
}

impl PCPAutomaton {
    pub fn construct_reduced_automaton(&self) -> PCPAutomaton {
        let upper_inverse = self.upper.inverse();
        let upper_inverse_input = upper_inverse.get_input_nfa(); //.reduce_size();

        // upper_inverse.get_input_nfa().show_dot("upper_inverse_i");
        // upper_inverse.show_dot("upper_inverse");
        // panic!("stop");

        let lower_inverse = self.lower.inverse();
        let lower_inverse_input = lower_inverse.get_input_nfa(); //.reduce_size();
        let upper_inverse_reduced = upper_inverse
            .intersection_input(&lower_inverse_input)
            .reduce_size();
        let lower_inverse_reduced = lower_inverse
            .intersection_input(&upper_inverse_input)
            .reduce_size();

        return PCPAutomaton {
            upper: upper_inverse_reduced,
            lower: lower_inverse_reduced,
        };
    }
}

impl PCP {
    pub fn to_automaton(&self) -> PCPAutomaton {
        let upper = self.to_automaton_upper();
        let lower = self.swap_pcp().to_automaton_upper();
        return PCPAutomaton { upper, lower };
    }

    fn to_automaton_upper(&self) -> automaton::Transducer<char, char> {
        let mut aut = Transducer::new();

        let start = aut.start.clone();
        aut.accept.insert(start.clone());
        for (idx, tile) in self.tiles.iter().enumerate() {
            assert!(idx.to_string().len() == 1);
            let idx_char = idx.to_string().chars().next().unwrap();

            let mut last_state = start.clone();
            for (i, t) in tile.up.chars().enumerate() {
                let next_state = if i < tile.up.len() - 1 {
                    automaton::new_state()
                } else {
                    start.clone()
                };
                let label = if i == 0 {
                    (Some(idx_char), Some(t))
                } else {
                    (None, Some(t))
                };
                aut.add_transition(Transition {
                    from: last_state.clone(),
                    to: next_state.clone(),
                    label: label,
                });
                last_state = next_state;
            }
        }
        aut
    }
}

// impl Tile {
//     pub fn multi_next_transducer_for_lower(&self) -> automaton::Transducer<char, char> {
//         self.swap_tile().multi_next_transducer_for_upper_conf()
//     }
//     pub fn multi_next_transducer_for_upper_conf(&self) -> automaton::Transducer<char, char> {
//         for rem_len in 0..self.dn.len() {
//             let (upper_remainder, look_ahead_consume) = self.up.split_at(rem_len);

//         }
//     }

//     fn look_ahead_transducer(&self, )
// }
