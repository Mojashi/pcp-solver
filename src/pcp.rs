use std::{
    collections::{HashSet, VecDeque},
    io::BufRead,
    rc::Rc,
};

use itertools::Itertools;
use regex::Regex;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tile {
    pub up: String,
    pub dn: String,
}

impl Tile {
    pub fn swap_tile(&self) -> Tile {
        Tile {
            up: self.dn.clone(),
            dn: self.up.clone(),
        }
    }

    pub fn reverse_tile(&self) -> Tile {
        Tile {
            up: self.up.chars().rev().collect(),
            dn: self.dn.chars().rev().collect(),
        }
    }

    pub fn by_dir(&self, dir: PCPDir) -> &str {
        match dir {
            PCPDir::UP => &self.up,
            PCPDir::DN => &self.dn,
        }
    }
}


fn common_prefix(a: &str, b: &str) -> String {
    a.chars()
        .zip(b.chars())
        .take_while(|(a, b)| a == b)
        .map(|(a, _)| a)
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PCP {
    pub tiles: Vec<Tile>,
}



impl PCP {
    pub fn repr(&self) -> String {
        self.tiles
            .iter()
            .map(|t| format!("{}_{}", t.up, t.dn))
            .join("__")
    }
    pub fn parse_repr(r: &str) -> PCP {
        let mut tiles = vec![];
        for tile in r.split("__") {
            let mut parts = tile.split("_");
            let up = parts.next().unwrap();
            let dn = parts.next().unwrap();
            tiles.push(Tile {
                up: up.to_string(),
                dn: dn.to_string(),
            });
        }
        PCP { tiles }
    }
    // parse string like PCP(Vector(Tile(1110,1), Tile(1,0), Tile(0,1110)))
    pub fn parse_pcp_string(s: &str) -> PCP {
        let r = Regex::new(r"Tile\((\d*),(\d*)\)").unwrap();

        let tiles = r
            .captures_iter(s)
            .map(|cap| Tile {
                up: cap[1].to_string(),
                dn: cap[2].to_string(),
            })
            .collect();

        PCP { tiles: tiles }
    }

    pub fn co(&self) -> PCP {
        self.swap_pcp().reverse_pcp()
    }

    pub fn swap_pcp(&self) -> PCP {
        PCP {
            tiles: self.tiles.iter().map(|tile| tile.swap_tile()).collect(),
        }
    }

    pub fn reverse_pcp(&self) -> PCP {
        PCP {
            tiles: self
                .tiles
                .iter()
                .map(|tile| Tile {
                    up: tile.up.chars().rev().collect(),
                    dn: tile.dn.chars().rev().collect(),
                })
                .collect(),
        }
    }
    pub fn calc_constant_append(&self) -> (String, String) {
        // get common prefix for up and dn
        let up = self.tiles.iter().map(|t| t.up.clone()).collect_vec();
        let dn = self.tiles.iter().map(|t| t.dn.clone()).collect_vec();

        let up_prefix = up
            .iter()
            .fold(up[0].clone(), |acc, x| common_prefix(&acc, x));
            
        let dn_prefix = dn
            .iter()
            .fold(dn[0].clone(), |acc, x| common_prefix(&acc, x));

        println!("up_prefix: {}, dn_prefix: {}", up_prefix, dn_prefix);
        (up_prefix, dn_prefix)
    }
}

fn gen_random_pcp(num_tile: usize, tile_size: usize) -> PCP {
    let mut tiles = vec![];
    for _ in 0..num_tile {
        let mut up = String::new();
        let mut dn = String::new();
        for _ in 0..(rand::random::<usize>() % tile_size + 1) {
            up += (&rand::random::<u8>() % 2).to_string().as_str();
        }
        for _ in 0..(rand::random::<usize>() % tile_size + 1) {
            dn += (&rand::random::<u8>() % 2).to_string().as_str();
        }
        tiles.push(Tile { up, dn });
    }
    PCP { tiles }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum PCPDir {
    UP,
    DN,
}

impl PCPDir {
    pub fn opposite(&self) -> PCPDir {
        match self {
            PCPDir::UP => PCPDir::DN,
            PCPDir::DN => PCPDir::UP,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Ord, PartialOrd)]
pub struct PCPConfig {
    pub seq: String,
    pub dir: PCPDir,
}

impl PCPConfig {
    pub fn apply_pcp(&self, pcp: &PCP) -> Vec<PCPConfig> {
        pcp.tiles
            .iter()
            .flat_map(|tile| self.apply_tile(tile))
            .collect_vec()
    }

    pub fn co(&self) -> PCPConfig {
        self.swap_dir().reverse()
    }

    pub fn swap_dir(&self) -> PCPConfig {
        PCPConfig {
            seq: self.seq.clone(),
            dir: self.dir.opposite(),
        }
    }
    pub fn reverse(&self) -> PCPConfig {
        PCPConfig {
            seq: self.seq.chars().rev().collect(),
            dir: self.dir,
        }
    }
    pub fn apply_tile(&self, tile: &Tile) -> Option<PCPConfig> {
        if self.dir == PCPDir::DN {
            return self
                .swap_dir()
                .apply_tile(&tile.swap_tile())
                .map(|s| s.swap_dir());
        }

        let upper = self.seq.clone() + &tile.up;
        if upper.starts_with(&tile.dn) {
            return Some(PCPConfig {
                seq: upper[tile.dn.len()..].to_string(),
                dir: PCPDir::UP,
            });
        }

        if tile.dn.starts_with(&upper) {
            return Some(PCPConfig {
                seq: tile.dn[upper.len()..].to_string(),
                dir: PCPDir::DN,
            });
        }

        return None;
    }

    pub fn inv_apply_tile(&self, tile: &Tile) -> Option<PCPConfig> {
        self.reverse()
            .apply_tile(&tile.reverse_tile().swap_tile())
            .map(|c| c.reverse())
    }
    pub fn inv_apply_pcp(&self, pcp: &PCP) -> Vec<PCPConfig> {
        pcp.tiles
            .iter()
            .flat_map(|tile| self.inv_apply_tile(tile))
            .collect_vec()
    }
}

impl PCP {
    pub fn enumerate_configurations(&self, size: u32) -> Vec<PCPConfig> {
        let mut q: VecDeque<Rc<PCPConfig>> = VecDeque::new();
        let emp_conf = Rc::new(PCPConfig {
            seq: "".to_string(),
            dir: PCPDir::UP,
        });
        let mut visited: HashSet<Rc<PCPConfig>> = HashSet::new();
        visited.insert(emp_conf.clone());
        q.push_back(emp_conf);

        while visited.len() < size as usize {
            if q.len() == 0 {
                break;
            }
            let seq = q.pop_front().unwrap();
            let next = seq.apply_pcp(self);
            let new_next = next
                .into_iter()
                .filter(|n| !visited.contains(n))
                .map(|n| Rc::new(n))
                .collect_vec();
            //println!("{:?} -> {:?}", seq, new_next);

            for n in new_next.into_iter() {
                visited.insert(n.clone());
                q.push_back(n);
            }
        }

        println!("visited: {:?}", visited.len());
        visited
            .into_iter()
            .map(|n| n.as_ref().clone())
            .collect_vec()
    }

    pub fn enumerate_frontier(&self, depth: usize) -> HashSet<PCPConfig> {
        let emp_conf = PCPConfig {
            seq: "".to_string(),
            dir: PCPDir::UP,
        };
        let mut visited: HashSet<PCPConfig> = HashSet::new();
        let mut frontier: HashSet<PCPConfig> = HashSet::new();
        frontier.insert(emp_conf.clone());
        visited.insert(emp_conf.clone());

        for _ in 0..depth {
            let mut new_frontier = HashSet::new();
            for seq in frontier.iter() {
                for (tile_idx, tile) in self.tiles.iter().enumerate() {
                    let next = seq.apply_tile(&tile);
                    for n in next.into_iter() {
                        if visited.contains(&n) {
                            continue;
                        }
                        visited.insert(n.clone());
                        new_frontier.insert(n);
                    }
                }
            }
            frontier = new_frontier;
        }

        frontier
    }

    pub fn enumerate_frontier_with_history(
        &self,
        depth: usize,
    ) -> HashSet<(Vec<usize>, PCPConfig)> {
        let emp_conf = PCPConfig {
            seq: "".to_string(),
            dir: PCPDir::UP,
        };
        let mut visited: HashSet<PCPConfig> = HashSet::new();
        let mut frontier: HashSet<(Vec<usize>, PCPConfig)> = HashSet::new();
        frontier.insert((vec![], emp_conf.clone()));
        visited.insert(emp_conf.clone());

        for _ in 0..depth {
            let mut new_frontier = HashSet::new();
            for (history, seq) in frontier.iter() {
                for (tile_idx, tile) in self.tiles.iter().enumerate() {
                    let next = seq.apply_tile(&tile);
                    for n in next.into_iter() {
                        if visited.contains(&n) {
                            continue;
                        }
                        visited.insert(n.clone());
                        let new_history = history.iter().cloned().chain(vec![tile_idx]).collect();
                        new_frontier.insert((new_history, n));
                    }
                }
            }
            frontier = new_frontier;
        }

        frontier
    }
    pub fn get_init_config(&self) -> Vec<PCPConfig> {
        PCPConfig {
            seq: "".to_string(),
            dir: PCPDir::UP,
        }
        .apply_pcp(self)
    }
}

impl PartialOrd for PCP {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PCP {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.repr().cmp(&other.repr())
    }
}

pub fn parse_instance_list(fname: &str) -> Vec<PCP> {
    let mut ret = vec![];
    let f = std::fs::File::open(fname).unwrap();
    let mut content = std::io::BufReader::new(f)
        .lines()
        .collect_vec()
        .iter()
        .map(|s| s.as_ref().unwrap().to_string())
        .collect_vec();
    let seperator = Regex::new(r"\s+").expect("Invalid regex");

    while content.is_empty() == false {
        let startline = content
            .iter()
            .enumerate()
            .find(|(_, s)| s.starts_with("Instance"))
            .unwrap()
            .0;
        let ups = seperator.split(&content[startline + 2]).collect_vec();
        let dns = seperator.split(&content[startline + 3]).collect_vec();

        ret.push(PCP {
            tiles: ups
                .iter()
                .zip(dns.iter())
                .map(|(u, d)| Tile {
                    up: u.to_string(),
                    dn: d.to_string(),
                })
                .filter(|t| -> bool { t.up.len() > 0 && t.dn.len() > 0 })
                .collect_vec(),
        });
        content = content[startline + 5..].to_vec();
    }

    ret
}

fn enumerate_all(pcp: &PCP, max_depth: usize) -> HashSet<PCPConfig> {
    let mut seen = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back((
        PCPConfig {
            seq: "".to_string(),
            dir: PCPDir::UP,
        },
        0,
    ));
    seen.insert(PCPConfig {
        seq: "".to_string(),
        dir: PCPDir::UP,
    });
    seen.insert(PCPConfig {
        seq: "".to_string(),
        dir: PCPDir::DN,
    });
    while let Some((cur, depth)) = queue.pop_front() {
        if depth >= max_depth {
            continue;
        }
        for next in cur.apply_pcp(pcp) {
            if seen.contains(&next) {
                continue;
            }
            seen.insert(next.clone());
            queue.push_back((next, depth + 1));
        }
    }
    seen
}
pub fn enumerate_from_backwards(pcp: &PCP, max_depth: usize) -> HashSet<PCPConfig> {
    enumerate_all(&pcp.co(), max_depth)
        .into_iter()
        .map(|c| c.reverse())
        .collect()
}

pub fn unsolved_instances() -> Vec<PCP> {
    vec![
        PCP::parse_pcp_string("Tile(1111,1) Tile(1,1101) Tile(0,11)"),
        PCP::parse_pcp_string("Tile(1110,01) Tile(101,1) Tile(1,1011)"),
        PCP::parse_pcp_string("Tile(1110,1) Tile(1,0) Tile(0,1110)"),
        PCP::parse_pcp_string("Tile(1110,0) Tile(10,1) Tile(1,1011)"),
        PCP::parse_pcp_string("Tile(1101,1) Tile(11,011) Tile(0,111)"),
        PCP::parse_pcp_string("Tile(1101,1) Tile(1,101) Tile(0,011)"),
        PCP::parse_pcp_string("Tile(1101,1) Tile(1,10) Tile(0,1011)"),
        PCP::parse_pcp_string("Tile(1001,1) Tile(10,0) Tile(0,100)"),
    ]
}

pub fn unsolved_instances2() -> Vec<PCP> {
    vec![
        PCP::parse_pcp_string("PCP(Vector(Tile(1111,110), Tile(1110,1), Tile(1,1111)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1111,101), Tile(1110,1), Tile(1,1111)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1111,10), Tile(011,1), Tile(1,1111)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1110,01), Tile(101,1), Tile(1,1011)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1110,1), Tile(1,0), Tile(0,1110)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1001,1), Tile(10,0), Tile(0,100)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1111,110), Tile(1011,1), Tile(1,1111)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1101,1), Tile(1,101), Tile(0,011)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1111,110), Tile(1101,1), Tile(1,1111)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1101,1), Tile(1,10), Tile(0,1011)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1111,100), Tile(0011,1), Tile(1,1111)))"),
        PCP::parse_pcp_string("PCP(Vector(Tile(1110,0), Tile(10,1), Tile(1,1011))"),
    ]
}

#[test]
fn test_7() {
    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1101,1), Tile(1,101), Tile(0,011)))");
    // shortest
    let sol = [
        0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 2, 1, 0, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 0, 1, 0,
        0, 1, 0, 2, 1, 0, 0, 1, 0, 1, 0, 0, 0, 2, 1, 0, 0, 1, 2, 0, 2, 1, 0, 0, 1, 0, 0, 0, 2, 1,
        0, 1, 2, 0, 2, 1, 1, 1, 2, 0, 2, 1, 0, 0, 1, 0, 1, 0, 1, 2, 1, 1, 1, 2, 1, 1, 2, 0, 2, 1,
        0, 0, 1, 0, 0, 1, 0, 2, 1, 1, 1, 2, 0, 2, 1, 0, 0, 0, 2, 1, 0, 0, 1, 2, 1, 1, 2, 1, 0, 1,
        0, 1, 2, 1, 0, 1, 1, 0, 2, 1, 0, 0, 1, 0, 2, 1, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0, 1, 2, 1, 0,
        0, 2, 1, 1, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1,
    ];

    let upper = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].up.clone())
        .collect_vec()
        .join("");
    let lower = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].dn.clone())
        .collect_vec()
        .join("");

    assert_eq!(upper, lower);
}

#[test]
fn test_4() {
    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1110,1), Tile(1,0), Tile(0,1110)))");
    // shortest
    let sol = [
        0, 0, 0, 1, 2, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 2, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 2, 1, 2, 1,
        1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 2, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2, 2, 1, 1, 1, 0,
        0, 0, 1, 1, 1, 2, 1, 2, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 2, 2, 0, 1, 0, 0, 0, 2, 2, 2, 0,
        0, 0, 1, 2, 2, 0, 1, 1, 1, 2, 0, 2, 2, 2, 1, 1, 1, 2, 2, 2, 0, 1, 1, 2, 2, 2, 1, 1, 1, 2,
        1, 1, 2, 0, 0, 1, 1, 1, 2, 0, 0, 1, 2, 2, 2, 2, 2, 0, 1, 1, 1, 1, 1, 2, 0, 0, 2, 2, 2, 1,
        1, 1, 2,
    ];

    let upper = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].up.clone())
        .collect_vec()
        .join("");
    let lower = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].dn.clone())
        .collect_vec()
        .join("");

    assert_eq!(upper, lower);
}

#[test]
fn test_5() {
    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1001,1), Tile(10,0), Tile(0,100)))");
    let sol = [
        0, 1, 1, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0, 1, 2, 0, 2, 2, 0, 1, 2, 0, 2, 0, 2, 0, 1, 1, 2, 2,
        0, 2, 2, 0, 1, 2, 0, 1, 2, 0, 0, 1, 2, 1, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2, 1, 1,
        2, 2, 0, 1, 1, 2, 2, 0, 1, 2, 2, 0, 1, 2, 1, 2, 0, 0, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 2, 2,
        0, 2, 0, 2, 2, 2, 0, 1, 2, 2, 2, 1, 2, 0, 1, 2, 2, 1, 2, 0, 2, 1, 1, 2, 2, 0, 2, 1, 2, 2,
        0, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 0, 1, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 2, 2,
        1, 2, 2, 1, 2, 0, 1, 2, 2, 1, 2, 1, 2, 2, 0, 2, 1, 2, 2, 1, 2, 0, 1, 2, 1, 2, 2, 0, 2, 2,
        1, 2, 0, 1, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 2, 0, 2, 2, 2, 0, 1, 2, 2, 1, 2, 0, 2, 1, 2, 2,
        0, 1, 2, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 2, 0, 2, 0, 0, 1, 2,
        0, 2, 2, 0, 2, 2, 2, 2, 0, 1, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 0, 2, 2, 0, 1, 2,
        2, 1, 2, 0, 0, 1, 2, 0, 1, 2, 0, 1, 1, 2, 2, 0, 2, 1, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0,
        1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 2, 0, 1, 1, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2,
        1, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2, 2, 1, 2, 2, 1, 2, 0, 1, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 1,
        2, 1, 2, 2, 0, 2, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 2, 2, 0, 2, 1, 2, 2, 0,
        2, 1, 2, 2, 0, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 2, 0, 2, 2, 2, 0, 2, 2, 2,
        0, 2, 1, 2, 2, 1, 2, 2, 1, 2, 0, 1, 2, 1, 2, 1, 2, 2, 0, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2,
        1, 2,
    ];

    let upper = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].up.clone())
        .collect_vec()
        .join("");
    let lower = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].dn.clone())
        .collect_vec()
        .join("");

    assert_eq!(upper, lower);
}

#[test]
fn test_12() {
    let pcp = PCP::parse_pcp_string("PCP(Vector(Tile(1001,1), Tile(10,0), Tile(0,100)))");
    let sol = [
        0, 1, 1, 0, 0, 1, 0, 1, 2, 0, 2, 0, 0, 1, 2, 0, 2, 2, 0, 1, 2, 0, 2, 0, 2, 0, 1, 1, 2, 2,
        0, 2, 2, 0, 1, 2, 0, 1, 2, 0, 0, 1, 2, 1, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 2, 0, 2, 2, 1, 1,
        2, 2, 0, 1, 1, 2, 2, 0, 1, 2, 2, 0, 1, 2, 1, 2, 0, 0, 1, 2, 1, 2, 0, 2, 1, 2, 0, 2, 2, 2,
        0, 2, 0, 2, 2, 2, 0, 1, 2, 2, 2, 1, 2, 0, 1, 2, 2, 1, 2, 0, 2, 1, 1, 2, 2, 0, 2, 1, 2, 2,
        0, 1, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 0, 1, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 2, 2, 2,
        1, 2, 2, 1, 2, 0, 1, 2, 2, 1, 2, 1, 2, 2, 0, 2, 1, 2, 2, 1, 2, 0, 1, 2, 1, 2, 2, 0, 2, 2,
        1, 2, 0, 1, 1, 2, 2, 0, 0, 1, 2, 1, 2, 0, 2, 0, 2, 2, 2, 0, 1, 2, 2, 1, 2, 0, 2, 1, 2, 2,
        0, 1, 2, 1, 0, 1, 1, 0, 2, 0, 1, 2, 0, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 2, 0, 2, 0, 0, 1, 2,
        0, 2, 2, 0, 2, 2, 2, 2, 0, 1, 2, 0, 2, 0, 2, 2, 2, 0, 1, 1, 2, 1, 1, 2, 0, 2, 2, 0, 1, 2,
        2, 1, 2, 0, 0, 1, 2, 0, 1, 2, 0, 1, 1, 2, 2, 0, 2, 1, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 0, 0,
        1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 2, 0, 1, 1, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2,
        1, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2, 2, 1, 2, 2, 1, 2, 0, 1, 2, 2, 0, 2, 0, 2, 2, 2, 0, 2, 1,
        2, 1, 2, 2, 0, 2, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 2, 2, 1, 2, 0, 1, 2, 2, 0, 2, 1, 2, 2, 0,
        2, 1, 2, 2, 0, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 1, 2, 0, 1, 2, 2, 0, 2, 2, 2, 0, 2, 2, 2,
        0, 2, 1, 2, 2, 1, 2, 2, 1, 2, 0, 1, 2, 1, 2, 1, 2, 2, 0, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2,
        1, 2,
    ];

    let upper = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].up.clone())
        .collect_vec()
        .join("");
    let lower = sol
        .iter()
        .map(|x| pcp.tiles[*x as usize].dn.clone())
        .collect_vec()
        .join("");

    assert_eq!(upper, lower);
}
