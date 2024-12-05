use std::{borrow::Borrow, collections::HashSet};

use crate::{
    automaton::{AppRegex, Transition, NFA},
    pcp::{PCPDir, Tile, PCP},
};
use itertools::Itertools;
use regex::Regex;

fn enumerate01strings(len: usize) -> Vec<String> {
    if len == 0 {
        return vec!["".to_string()];
    }
    let mut ret = vec![];
    for s in enumerate01strings(len - 1) {
        ret.push(s.clone() + "0");
        ret.push(s + "1");
    }
    ret
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct MidWildSequence {
    pub front: String,
    pub back: String,
    pub dir: PCPDir,
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct MidExactSequence {
    pub mid: String,
    pub dir: PCPDir,
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub struct ExactSequence {
    pub seq: String,
    pub dir: PCPDir,
}

pub fn parse_pcp_seq(s: &str, dir: PCPDir) -> PCPSequence {
    if s.starts_with(".*") && s.ends_with(".*") && s.len() > 2 {
        return PCPSequence::MidExact(MidExactSequence {
            mid: s[2..s.len() - 2].to_string(),
            dir,
        });
    } else if s.contains(".*") {
        let mut parts = s.split(".*");
        let front = parts.next().unwrap();
        let back = parts.next().unwrap();
        return PCPSequence::MidWild(MidWildSequence {
            front: front.to_string(),
            back: back.to_string(),
            dir,
        });
    } else {
        return PCPSequence::Exact(ExactSequence {
            seq: s.to_string(),
            dir,
        });
    }
}

impl ExactSequence {
    fn contains_empty(&self) -> bool {
        self.seq.len() == 0
    }
    fn contains(&self, s: &PCPSequence) -> bool {
        match s {
            PCPSequence::Exact(e) => {
                self.dir == s.dir() && self.seq == e.seq || self.contains_empty() && e.seq == ""
            }
            PCPSequence::MidWild(_) => false,
            PCPSequence::MidExact(_) => false,
        }
    }
}

impl MidExactSequence {
    fn sample(&self) -> Vec<String> {
        let front = (0..5)
            .into_iter()
            .flat_map(|midlen| enumerate01strings(midlen));
        let back = (0..5)
            .into_iter()
            .flat_map(|midlen| enumerate01strings(midlen));
        front
            .cartesian_product(back)
            .map(|(f, b)| vec![f, self.mid.clone(), b].concat())
            .collect_vec()
    }

    fn contains_empty(&self) -> bool {
        self.mid.len() == 0
    }
    fn contains(&self, s: &PCPSequence) -> bool {
        match s {
            PCPSequence::Exact(e) => {
                self.dir == s.dir() && e.seq.contains(&self.mid)
                    || self.contains_empty() && e.seq == ""
            }
            PCPSequence::MidExact(e) => self.dir == s.dir() && e.mid.contains(&self.mid),
            PCPSequence::MidWild(e) => {
                self.dir == s.dir() && (e.front.contains(&self.mid) || e.back.contains(&self.mid))
            }
        }
    }
}

#[test]
fn step_test() {
    let b = PCPSequence::MidWild(MidWildSequence {
        front: "".to_string(),
        back: "1".to_string(),
        dir: PCPDir::DN,
    });

    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1110,01), Tile(101,1), Tile(1,1011)))");
    let nexts = b.apply_pcp(&pcp, |s| true, false);

    println!("{:?}", nexts);
}

#[test]
fn contain_test() {
    let a = PCPSequence::MidExact(MidExactSequence {
        mid: "0110".to_owned(),
        dir: PCPDir::DN,
    });
    let b = PCPSequence::MidWild(MidWildSequence {
        front: "".to_owned(),
        back: "11101101".to_owned(),
        dir: PCPDir::DN,
    });
    assert!(a.contains(&b));
}

#[test]
fn exact_seq_test() {
    let s = PCPSequence::Exact(ExactSequence {
        seq: "110".to_string(),
        dir: PCPDir::DN,
    });
    let tile = Tile {
        up: "1101".to_string(),
        dn: "110".to_string(),
    };
    let nexts = s.apply_tile(&tile, &|s| true, false);

    assert_eq!(nexts.len(), 1);
    assert_eq!(
        nexts[0],
        PCPSequence::Exact(ExactSequence {
            seq: "10".to_string(),
            dir: PCPDir::DN,
        })
    );
}

impl MidWildSequence {
    fn sample(&self) -> Vec<String> {
        (0..5)
            .into_iter()
            .flat_map(|midlen| {
                enumerate01strings(midlen)
                    .into_iter()
                    .map(|mid| vec![self.front.clone(), mid, self.back.clone()].concat())
            })
            .collect_vec()
    }

    fn contains_empty(&self) -> bool {
        self.front.len() == 0 && self.back.len() == 0
    }
    fn contains(&self, s: &PCPSequence) -> bool {
        match s {
            PCPSequence::Exact(e) => {
                self.dir == s.dir()
                    && e.seq.len() >= self.front.len() + self.back.len()
                    && e.seq.starts_with(&self.front)
                    && e.seq.ends_with(&self.back)
                    || self.contains_empty() && e.seq == ""
            }
            PCPSequence::MidWild(e) => {
                self.dir == s.dir()
                    && e.front.starts_with(&self.front)
                    && e.back.ends_with(&self.back)
            }
            PCPSequence::MidExact(_) => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, PartialOrd, Ord, Hash)]
pub enum PCPSequence {
    MidWild(MidWildSequence),
    Exact(ExactSequence),
    MidExact(MidExactSequence),
}

impl PCPSequence {
    pub fn num_chars(&self) -> u32 {
        match self {
            PCPSequence::Exact(e) => e.seq.len() as u32,
            PCPSequence::MidWild(e) => e.front.len() as u32 + e.back.len() as u32,
            PCPSequence::MidExact(e) => e.mid.len() as u32,
        }
    }

    pub fn sample(&self) -> Vec<String> {
        match self {
            PCPSequence::Exact(e) => vec![e.seq.clone()],
            PCPSequence::MidWild(e) => e.sample(),
            PCPSequence::MidExact(e) => e.sample(),
        }
    }

    pub fn contains_empty(&self) -> bool {
        match self {
            PCPSequence::Exact(e) => e.contains_empty(),
            PCPSequence::MidWild(e) => e.contains_empty(),
            PCPSequence::MidExact(e) => e.contains_empty(),
        }
    }
    pub fn contains(&self, s: &PCPSequence) -> bool {
        let ret = match self {
            PCPSequence::Exact(e) => e.contains(s),
            PCPSequence::MidWild(e) => e.contains(s),
            PCPSequence::MidExact(e) => e.contains(s),
        };

        // match s {
        //     PCPSequence::Exact(_) => {}
        //     _ =>
        //     if ret  {
        //         s.sample().iter().for_each(|ss| {
        //             if !self.contains(&PCPSequence::Exact(ExactSequence { seq: ss.clone(), dir: self.dir() })) {
        //                 panic!("invalid self: {:?} s: {:?}  ss: {:?}", self, s, ss);
        //             }
        //         })
        //     }
        // }

        ret
    }

    pub fn apply_pcp_avoid_midwild(
        &self,
        pcp: &PCP,
        is_ok: impl Fn(&PCPSequence) -> bool,

        infinite_midchar: bool,
    ) -> (Vec<PCPSequence>, Vec<PCPSequence>) {
        let (mut wilds, non_wilds): (Vec<PCPSequence>, Vec<PCPSequence>) = self
            .apply_pcp(pcp, |_| true, infinite_midchar)
            .into_iter()
            .map(|s| match s {
                PCPSequence::MidWild(w) => {
                    if w.front.len() == 0 && w.back.len() == 0 {
                        PCPSequence::MidExact(MidExactSequence {
                            mid: "".to_string(),
                            dir: w.dir,
                        })
                    } else {
                        PCPSequence::MidWild(w)
                    }
                }
                _ => s,
            })
            .partition(|s| match s {
                PCPSequence::MidWild(_) => true,
                _ => false,
            });

        let mut ret: HashSet<PCPSequence> = non_wilds.into_iter().collect();
        let mut visited_wilds: HashSet<PCPSequence> = HashSet::new();

        while wilds.len() > 0 {
            visited_wilds.extend(wilds.clone());
            let (nwilds, nnon_wilds): (Vec<PCPSequence>, Vec<PCPSequence>) = wilds
                .into_iter()
                .flat_map(|s| s.apply_pcp(pcp, |s| true, infinite_midchar))
                .into_iter()
                .map(|s| match s {
                    PCPSequence::MidWild(w) => {
                        if w.front.len() == 0 && w.back.len() == 0 {
                            PCPSequence::MidExact(MidExactSequence {
                                mid: "".to_string(),
                                dir: w.dir,
                            })
                        } else {
                            PCPSequence::MidWild(w)
                        }
                    }
                    _ => s,
                })
                .partition(|s| match s {
                    PCPSequence::MidWild(_) => true,
                    _ => false,
                });
            wilds = nwilds
                .into_iter()
                .filter(|s| !visited_wilds.contains(s))
                .collect_vec();
            ret.extend(nnon_wilds);
        }

        return (
            ret.into_iter().collect_vec(),
            visited_wilds.into_iter().collect_vec(),
        );
    }

    pub fn apply_pcp(
        &self,
        pcp: &PCP,
        is_ok: impl Fn(&PCPSequence) -> bool,

        infinite_midchar: bool,
    ) -> Vec<PCPSequence> {
        let ret = pcp
            .tiles
            .iter()
            .flat_map(|tile| self.apply_tile(tile, &is_ok, infinite_midchar))
            .sorted()
            .dedup()
            .collect_vec();

        // ret.into_iter()
        //     .flat_map(|f| match f {
        //         PCPSequence::Exact(e) => vec![PCPSequence::Exact(e)],
        //         PCPSequence::MidWild(e) => {
        //             if e.front.len() > 0 {
        //                 PCPSequence::MidWild(e.clone()).apply_pcp(pcp)
        //             }
        //             else {
        //                 vec![PCPSequence::MidExact(MidExactSequence { mid: e.back.clone(), dir: e.dir})]
        //             }
        //         }
        //         PCPSequence::MidExact(e) => vec![PCPSequence::MidExact(e)],
        //     })
        //     .collect_vec()
        ret
    }

    pub fn apply_tile(
        &self,
        tile: &Tile,
        is_ok: &impl Fn(&PCPSequence) -> bool,

        infinite_midchar: bool,
    ) -> Vec<PCPSequence> {
        let ret = match self {
            PCPSequence::MidWild(seq) => seq.apply_tile(tile, is_ok, infinite_midchar),
            PCPSequence::Exact(seq) => seq
                .apply_tile(tile)
                .into_iter()
                .map(|f| PCPSequence::Exact(f))
                .collect_vec(),
            PCPSequence::MidExact(seq) => seq.apply_tile(tile, is_ok, infinite_midchar),
        };

        // match self {
        //     PCPSequence::Exact(_) => {}
        //     _ => {
        //         let valid = self
        //             .sample()
        //             .into_iter()
        //             .flat_map(|s| {
        //                 PCPSequence::Exact(ExactSequence {
        //                     seq: s.clone(),
        //                     dir: self.dir(),
        //                 })
        //                 .apply_tile(tile)
        //                 .into_iter()
        //                 .map(|n| (s.clone(), n)).collect_vec()
        //             })
        //             .find(|(o, s)| ret.iter().all(|f| !f.contains(&s)));
        //         match valid {
        //             None => {}
        //             Some(cex) => {
        //                 panic!(
        //                     "invalid tile {:?} for {:?}. ret: {:?} cex: {:?}",
        //                     tile, self, ret, cex
        //                 );
        //             }
        //         }
        //     }
        // }

        ret
    }

    pub fn dir(&self) -> PCPDir {
        match self {
            PCPSequence::MidWild(seq) => seq.dir,
            PCPSequence::Exact(seq) => seq.dir,
            PCPSequence::MidExact(seq) => seq.dir,
        }
    }

    pub fn swap_dir(&self) -> PCPSequence {
        match self {
            PCPSequence::MidWild(seq) => PCPSequence::MidWild(MidWildSequence {
                front: seq.front.clone(),
                back: seq.back.clone(),
                dir: seq.dir.opposite(),
            }),
            PCPSequence::Exact(seq) => PCPSequence::Exact(ExactSequence {
                seq: seq.seq.clone(),
                dir: seq.dir.opposite(),
            }),
            PCPSequence::MidExact(seq) => PCPSequence::MidExact(MidExactSequence {
                mid: seq.mid.clone(),
                dir: seq.dir.opposite(),
            }),
        }
    }

    pub fn to_nfa(&self) -> NFA<char> {
        match self {
            PCPSequence::Exact(e) => e.to_nfa(),
            PCPSequence::MidExact(e) => e.to_nfa(),
            PCPSequence::MidWild(e) => e.to_nfa(),
        }
    }
    pub fn set_to_nfa_all_dir_eq(seqs: Vec<PCPSequence>) -> NFA<char> {
        let mut exacts = ExactSequence::set_to_nfa_all_dir_eq(
            seqs.iter()
                .filter_map(|s| match s {
                    PCPSequence::Exact(e) => Some(e.clone()),
                    _ => None,
                })
                .collect_vec(),
        );
        let mids = MidExactSequence::set_to_nfa_all_dir_eq(
            seqs.iter()
                .filter_map(|s| match s {
                    PCPSequence::MidExact(e) => Some(e.clone()),
                    _ => None,
                })
                .collect_vec(),
        );
        let midwilds = MidWildSequence::set_to_nfa_all_dir_eq(
            seqs.iter()
                .filter_map(|s| match s {
                    PCPSequence::MidWild(e) => Some(e.clone()),
                    _ => None,
                })
                .collect_vec(),
        );

        exacts.union_mut(&mids, true);
        exacts.union_mut(&midwilds, true);
        exacts
    }
    pub fn set_to_nfa(seqs: &Vec<PCPSequence>) -> (NFA<char>, NFA<char>) {
        let (upper, lower) = seqs.iter().cloned().partition(|s| s.dir() == PCPDir::UP);
        (
            PCPSequence::set_to_nfa_all_dir_eq(upper),
            PCPSequence::set_to_nfa_all_dir_eq(lower),
        )
    }
}

impl ExactSequence {
    pub fn to_nfa(&self) -> NFA<char> {
        NFA::from_constant(self.seq.as_str())
    }

    pub fn set_to_nfa_all_dir_eq(seqs: Vec<ExactSequence>) -> NFA<char> {
        NFA::from_constants(&seqs.iter().map(|s| s.seq.as_str()).collect_vec())
    }

    pub fn apply_pcp(&self, pcp: &PCP) -> Vec<ExactSequence> {
        pcp.tiles
            .iter()
            .flat_map(|tile| self.apply_tile(tile))
            .collect_vec()
    }

    pub fn swap_dir(&self) -> ExactSequence {
        ExactSequence {
            seq: self.seq.clone(),
            dir: self.dir.opposite(),
        }
    }
    fn apply_tile(&self, tile: &Tile) -> Vec<ExactSequence> {
        if self.dir == PCPDir::DN {
            return ExactSequence {
                seq: self.seq.clone(),
                dir: self.dir.opposite(),
            }
            .apply_tile(&tile.swap_tile())
            .into_iter()
            .map(|s| s.swap_dir())
            .collect_vec();
        }

        let upper = self.seq.clone() + &tile.up;
        if upper.starts_with(&tile.dn) {
            return vec![ExactSequence {
                seq: upper[tile.dn.len()..].to_string(),
                dir: self.dir,
            }];
        }

        if tile.dn.starts_with(&upper) {
            return vec![ExactSequence {
                seq: tile.dn[upper.len()..].to_string(),
                dir: self.dir.opposite(),
            }];
        }

        return vec![];
    }
}

#[test]
fn midwild_apply_test() {
    let s = PCPSequence::MidWild(MidWildSequence {
        front: "11".to_string(),
        back: "011011".to_string(),
        dir: PCPDir::UP,
    });
}

impl MidWildSequence {
    pub fn to_nfa(&self) -> NFA<char> {
        let pref_nfa = NFA::from_constant(self.front.as_str());
        let suff_nfa = NFA::from_constant(self.back.as_str());
        pref_nfa
            .concat(&NFA::get_arbitary_nfa(&vec!['0', '1']))
            .concat(&suff_nfa)
    }
    fn set_to_nfa_all_dir_eq(seqs: Vec<MidWildSequence>) -> NFA<char> {
        let mut queue = seqs.into_iter().map(|s| s.to_nfa()).collect_vec();
        while queue.len() > 1 {
            let mut a = queue.pop().unwrap();
            let b = queue.pop().unwrap();
            a.union_mut(&b, true);
            queue.push(a);
        }
        if queue.len() == 0 {
            return NFA::new();
        }
        queue.pop().unwrap().reduce_size()
    }
    fn apply_tile(
        &self,
        tile: &Tile,
        is_ok: &impl Fn(&PCPSequence) -> bool,

        infinite_midchar: bool,
    ) -> Vec<PCPSequence> {
        if self.dir == PCPDir::DN {
            return MidWildSequence {
                front: self.front.clone(),
                back: self.back.clone(),
                dir: self.dir.opposite(),
            }
            .apply_tile(&tile.swap_tile(), is_ok, infinite_midchar)
            .into_iter()
            .map(|s| s.swap_dir())
            .collect_vec();
        }
        if self.front.len() == 0 {
            // * -> *
            if self.back.len() == 0 {
                return vec![PCPSequence::MidExact(MidExactSequence {
                    mid: "".to_string(),
                    dir: PCPDir::UP,
                })];
            } else {
                let mut ret: Vec<PCPSequence> = vec![];
                for start_len in 0..tile.dn.len() {
                    let rest_dn = tile.dn[start_len..].to_string();
                    if rest_dn.starts_with(&self.back) {
                        let c = PCPSequence::Exact(ExactSequence {
                            seq: tile.dn[..start_len + self.back.len()].to_string(),
                            dir: self.dir,
                        });
                        if is_ok(&c) {
                            ret.extend(c.apply_tile(tile, is_ok, infinite_midchar))
                        }
                    }
                    if self.back.starts_with(&rest_dn) {
                        let c = PCPSequence::Exact(ExactSequence {
                            seq: tile.dn[..start_len].to_string() + &self.back,
                            dir: self.dir,
                        });
                        if is_ok(&c) {
                            ret.extend(c.apply_tile(tile, is_ok, infinite_midchar))
                        }
                    }
                }
                ret.push(PCPSequence::MidExact(MidExactSequence {
                    mid: self.back.clone() + &tile.up,
                    dir: self.dir,
                }));
                return ret;
            }
        }
        if self.front.starts_with(&tile.dn) {
            return vec![PCPSequence::MidWild(MidWildSequence {
                front: self.front[tile.dn.len()..].to_string(),
                back: self.back.clone() + &tile.up,
                dir: self.dir,
            })];
        }

        let mut ret: Vec<PCPSequence> = vec![];
        if self.front.len() > 0 && tile.dn.starts_with(&self.front) {
            let c = PCPSequence::MidWild(MidWildSequence {
                front: tile.dn.clone(),
                back: self.back.clone(),
                dir: self.dir,
            });
            if is_ok(&c) {
                ret.extend(c.apply_tile(tile, is_ok, infinite_midchar));
            }

            if !infinite_midchar {
                for mid_chars in 0..tile.dn.len() - self.front.len() {
                    let suf = tile.dn[self.front.len() + mid_chars..].to_string();
                    if self.back.starts_with(&suf) || suf.starts_with(&self.back) {
                        let mid =
                            tile.dn[self.front.len()..self.front.len() + mid_chars].to_string();
                        let c = PCPSequence::Exact(ExactSequence {
                            seq: self.front.clone() + &mid + &self.back,
                            dir: self.dir,
                        });
                        if is_ok(&c) {
                            ret.extend(c.apply_tile(tile, is_ok, infinite_midchar));
                        }
                    }
                }
            }
        }
        ret.dedup();
        ret
    }
}

impl MidExactSequence {
    pub fn to_nfa(&self) -> NFA<char> {
        let mut base = NFA::from_constant(self.mid.as_str());
        base.add_transition(Transition {
            from: base.start.clone(),
            to: base.start.clone(),
            label: Some('0'),
        });
        base.add_transition(Transition {
            from: base.start.clone(),
            to: base.start.clone(),
            label: Some('1'),
        });
        let accepts = base.accept.clone();
        for a in accepts.iter() {
            base.add_transition(Transition {
                from: a.clone(),
                to: a.clone(),
                label: Some('0'),
            });
            base.add_transition(Transition {
                from: a.clone(),
                to: a.clone(),
                label: Some('1'),
            });
        }
        base
    }

    pub fn set_to_nfa_all_dir_eq(seqs: Vec<MidExactSequence>) -> NFA<char> {
        let mut base = NFA::from_constants(&seqs.iter().map(|s| s.mid.as_str()).collect_vec());
        base.add_transition(Transition {
            from: base.start.clone(),
            to: base.start.clone(),
            label: Some('0'),
        });
        base.add_transition(Transition {
            from: base.start.clone(),
            to: base.start.clone(),
            label: Some('1'),
        });
        let accepts = base.accept.clone();
        for a in accepts.iter() {
            base.add_transition(Transition {
                from: a.clone(),
                to: a.clone(),
                label: Some('0'),
            });
            base.add_transition(Transition {
                from: a.clone(),
                to: a.clone(),
                label: Some('1'),
            });
        }
        base
    }

    fn apply_tile(
        &self,
        tile: &Tile,
        is_ok: &impl Fn(&PCPSequence) -> bool,

        infinite_midchar: bool,
    ) -> Vec<PCPSequence> {
        if self.dir == PCPDir::DN {
            return MidExactSequence {
                mid: self.mid.clone(),
                dir: self.dir.opposite(),
            }
            .apply_tile(&tile.swap_tile(), is_ok, infinite_midchar)
            .into_iter()
            .map(|s| s.swap_dir())
            .collect_vec();
        }

        // 完全に .*self.mid.* の最初の .* に飲まれて、 .*self.mid.*tail は .*self.mid.* に含まれるので無視していい
        let mut ret: Vec<PCPSequence> = vec![PCPSequence::MidExact(self.clone())];

        if self.mid.len() == 0 {
            return ret;
        }
        for start_len in 0..tile.dn.len() {
            let rest_dn = tile.dn[start_len..].to_string();
            if rest_dn.starts_with(&self.mid) {
                let c = PCPSequence::MidWild(MidWildSequence {
                    front: tile.dn[..start_len + self.mid.len()].to_string(),
                    back: "".to_string(),
                    dir: self.dir,
                });
                if is_ok(&c) {
                    ret.extend(c.apply_tile(tile, is_ok, infinite_midchar))
                }
            }
            if self.mid.starts_with(&rest_dn) {
                let c = PCPSequence::MidWild(MidWildSequence {
                    front: tile.dn[..start_len].to_string() + &self.mid,
                    back: "".to_string(),
                    dir: self.dir,
                });
                if is_ok(&c) {
                    ret.extend(c.apply_tile(tile, is_ok, infinite_midchar))
                }
            }
        }

        ret.dedup();
        ret
    }
}
