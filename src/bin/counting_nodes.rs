use itertools::{Either, Itertools};
use pcp_solver::{
    pcp::{unsolved_instances, unsolved_instances2}, pcpseq::{MidExactSequence, PCPSequence}, infix_prefix_suffix_method::infix_prefix_suffix_method_find_closed_me
};
use std::{
    cmp::{max, min}, collections::{HashMap, HashSet, VecDeque}, sync::{Arc, Mutex}, thread, usize
};

use pcp_solver::pcp::{PCPConfig, PCPDir, PCP};


fn count_nodes_dfs(pcp: &PCP, config: PCPConfig, depth: usize) -> u64 {
    if depth == 0 {
        return 1;
    }
    let mut count = 0;
    for next in config.apply_pcp(pcp) {
        count += count_nodes_dfs(&pcp, next, depth - 1);
    }
    count
}



fn main() {
    let pcp = unsolved_instances2().get(6).unwrap().clone().reverse_pcp();
    println!("{:?}", pcp);
    let args = std::env::args().collect::<Vec<String>>();
    let depth = args.get(1).unwrap().parse::<usize>().unwrap();
    let ans = count_nodes_dfs(&pcp, PCPConfig { seq: "".to_string(), dir: PCPDir::UP }, depth);
    println!("{}", ans);
}
