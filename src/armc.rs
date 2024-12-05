// Abstract Regular Model Checking
use crate::{
    automaton::{BaseAutomaton, NFA},
    conf_automaton::PCPConf,
    pcp::{PCPDir, PCP},
};
use itertools::Itertools;

pub fn nexts(seq: &PCPConf, pcp: &PCP) -> Vec<PCPConf> {
    let mut m = seq
        .apply_pcp(pcp)
        .into_iter()
        .filter(|c| !c.conf.is_empty())
        .collect_vec();

    m.push(seq.clone());
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

fn tie_into_two(confs: Vec<PCPConf>) -> (PCPConf, PCPConf) {
    let mut upper_union = NFA::new();
    let mut lower_union = NFA::new();
    for c in confs {
        if c.dir == PCPDir::UP {
            upper_union.union_mut(&c.conf, true);
        } else {
            lower_union.union_mut(&c.conf, true);
        }
    }
    (
        PCPConf {
            dir: PCPDir::UP,
            conf: upper_union.reduce_size(),
            exact: None,
        },
        PCPConf {
            dir: PCPDir::DN,
            conf: lower_union.reduce_size(),
            exact: None,
        },
    )
}

impl BaseAutomaton<Option<char>> {
    fn quotient_backward_eq(&self, l: usize) -> BaseAutomaton<Option<char>> {
        self.quotient_aut(self.backward_length_bounded_lang(l))
    }
    fn quotient_forward_eq(&self, l: usize) -> BaseAutomaton<Option<char>> {
        self.quotient_aut(self.forward_length_bounded_lang(l))
    }
}

pub fn armc(pcp: PCP) {
    for bounded_length in 2.. {
        let (mut upper_conf, mut lower_conf) = tie_into_two(
            pcp.get_init_config()
                .iter()
                .map(|s| PCPConf::from_exact(&s))
                .collect_vec(),
        );

        println!("bounded_length: {}", bounded_length);
        for i in 1.. {
            println!("i: {}", i);
            let (upper_conf_nex, lower_conf_nex) = tie_into_two(
                nexts(&upper_conf, &pcp)
                    .into_iter()
                    .chain(nexts(&lower_conf, &pcp))
                    .collect_vec(),
            );

            if upper_conf_nex.accept_empty() || lower_conf_nex.accept_empty() {
                println!("accept empty. give up {}", bounded_length);
                break;
            }
            let upper_closed = upper_conf.conf.includes(&upper_conf_nex.conf);
            let lower_closed = lower_conf.conf.includes(&lower_conf_nex.conf);
            println!("{} {} {}", bounded_length, upper_closed, lower_closed);
            if upper_closed && lower_closed {
                return;
            }

            upper_conf = PCPConf {
                dir: PCPDir::UP,
                conf: upper_conf_nex
                    .conf
                    .quotient_backward_eq(bounded_length)
                    .quotient_forward_eq(bounded_length),
                exact: None,
            };
            println!(
                "shrinked upper {} -> {} ({})",
                upper_conf_nex.conf.states.len(),
                upper_conf.conf.states.len(),
                upper_conf_nex
                    .conf.reduce_size().states.len()
            );
            lower_conf = PCPConf {
                dir: PCPDir::DN,
                conf: lower_conf_nex
                    .conf
                    //.quotient_backward_eq(bounded_length)
                    .quotient_forward_eq(bounded_length),
                exact: None,
            };
            println!(
                "shrinked lower {} -> {}",
                lower_conf_nex.conf.states.len(),
                lower_conf.conf.states.len()
            );

            // upper_conf_nex.conf.show_dot("upper_conf_nex");
            // lower_conf_nex.conf.show_dot("lower_conf_nex");
            // upper_conf.conf.show_dot("upper_conf2");
            // lower_conf.conf.show_dot("lower_conf2");
        }
        // assert!(false);
    }
}
