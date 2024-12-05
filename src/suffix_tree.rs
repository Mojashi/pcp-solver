use std::collections::HashSet;

use itertools::Itertools;

pub trait SuffixTree {
    fn insert(&mut self, s: &str);
    fn is_substr(&self, s: &str) -> bool;
    fn contains(&self, s: &str) -> bool;
    fn size(&self) -> usize;
}

type NodeId = usize;
struct Node {
    children: Vec<(char, NodeId)>,
}

pub struct NaiveSuffixTree {
    nodes: Vec<Node>,
    pub strs: HashSet<String>,
}
impl NaiveSuffixTree {
    pub fn new() -> Self {
        NaiveSuffixTree {
            nodes: vec![Node { children: vec![] }],
            strs: HashSet::new(),
        }
    }
    fn _insert(&mut self, s: &str) {
        let mut rest = s;
        let mut node_id: NodeId = 0;
        while !rest.is_empty() {
            let mut found = false;
            for (c, child_id) in &self.nodes[node_id].children {
                if rest.starts_with(*c) {
                    rest = &rest[c.len_utf8()..];
                    node_id = *child_id;
                    found = true;
                    break;
                }
            }
            if !found {
                let new_node_id = self.nodes.len();
                self.nodes.push(Node { children: vec![] });
                self.nodes[node_id]
                    .children
                    .push((rest.chars().next().unwrap(), new_node_id));
                rest = &rest[rest.chars().next().unwrap().len_utf8()..];
                node_id = new_node_id;
            }
        }
    }
}
impl SuffixTree for NaiveSuffixTree {
    fn size(&self) -> usize {
        self.strs.len()
    }
    fn insert(&mut self, s: &str) {
        self.strs.insert(s.to_string());
        for i in 0..s.len() {
            self._insert(&s[i..]);
        }
    }
    fn is_substr(&self, s: &str) -> bool {
        let mut rest = s;
        let mut node_id: NodeId = 0;
        while !rest.is_empty() {
            let mut found = false;
            assert!(self.nodes[node_id].children.iter().map(|c| c.0).all_unique());
            for (c, child_id) in &self.nodes[node_id].children {
                if rest.starts_with(*c) {
                    rest = &rest[1..];
                    node_id = *child_id;
                    found = true;
                    break;
                }
            }
            if !found {
                return false;
            }
        }
        true
    }

    fn contains(&self, s: &str) -> bool {
        self.strs.contains(s)
    }
}

pub mod ukkonens_suffix_tree {
    use std::{cmp::min, collections::HashSet};

    use itertools::Itertools;

    use crate::suffix_tree::SuffixTree;

    type NodeId = usize;
    const GLOBAL_END: isize = std::isize::MAX;
    const ALPHABET_SIZE: usize = 256;
    struct Node {
        next: [NodeId; ALPHABET_SIZE],
        suffix_link: NodeId,
        start: isize,
        end: isize,
    }
    impl Node {
        fn edge_length(&self) -> isize {
            self.end - self.start
        }
    }

    pub struct UkkonensSuffixTree {
        cur_str: Vec<char>,
        nodes: Vec<Node>,
        root: NodeId,

        need_sl: usize,
        remainder: usize,
        active_node: usize,
        active_e: usize,
        active_len: usize,

        str_store: HashSet<String>,
    }

    impl UkkonensSuffixTree {
        pub fn new() -> Self {
            Self {
                cur_str: vec![],
                nodes: vec![Node {
                    next: [0; ALPHABET_SIZE],
                    suffix_link: 0,
                    start: -1,
                    end: -1,
                }],
                root: 0,
                need_sl: 0,
                remainder: 0,
                active_node: 0,
                active_e: 0,
                active_len: 0,
                str_store: HashSet::new(),
            }
        }

        fn new_node(&mut self, start: isize, end: isize) -> NodeId {
            let mut nd = Node {
                next: [0; ALPHABET_SIZE],
                suffix_link: 0,
                start: start,
                end: end,
            };
            self.nodes.push(nd);
            self.nodes.len() - 1
        }

        fn active_edge(&self) -> char {
            return self.cur_str[self.active_e];
        }
        fn add_sl(&mut self, node: NodeId) {
            if self.need_sl > 0 {
                self.nodes[self.need_sl].suffix_link = node;
            }
            self.need_sl = node;
        }

        fn edge_length(&self, node: NodeId) -> usize {
            (min(self.nodes[node].end, self.cur_str.len() as isize) - self.nodes[node].start)
                as usize
        }

        fn walk_down(&mut self, node: NodeId) -> bool {
            if self.active_len as isize >= self.nodes[node].edge_length() {
                self.active_e += self.nodes[node].edge_length() as usize;
                self.active_len -= self.nodes[node].edge_length() as usize;
                self.active_node = node;
                return true;
            }
            return false;
        }

        /*
            st_extend(char c) {
            text[++pos] = c;
            needSL = 0;
            remainder++;
            while(remainder > 0) {
                if (active_len == 0) active_e = pos;
                if (tree[active_node].next[active_edge()] == 0) {
                    int leaf = new_node(pos);
                    tree[active_node].next[active_edge()] = leaf;
                    add_SL(active_node); //rule 2
                } else {
                    int nxt = tree[active_node].next[active_edge()];
                    if (walk_down(nxt)) continue; //observation 2
                    if (text[tree[nxt].start + active_len] == c) { //observation 1
                        active_len++;
                        add_SL(active_node); //observation 3
                        break;
                    }
                    int split = new_node(tree[nxt].start, tree[nxt].start + active_len);
                    tree[active_node].next[active_edge()] = split;
                    int leaf = new_node(pos);
                    tree[split].next[c] = leaf;
                    tree[nxt].start += active_len;
                    tree[split].next[text[tree[nxt].start]] = nxt;
                    add_SL(split); //rule 2
                }
                remainder--;
                if (active_node == root && active_len > 0) { //rule 1
                    active_len--;
                    active_e = pos - remainder + 1;
                } else
                    active_node = tree[active_node].slink > 0 ? tree[active_node].slink : root; //rule 3
            }
        }
        */
        fn st_extend(&mut self, c: char) {
            self.cur_str.push(c);
            self.need_sl = 0;
            self.remainder += 1;
            while self.remainder > 0 {
                if self.active_len == 0 {
                    self.active_e = self.cur_str.len() - 1;
                }
                let active_edge = self.active_edge() as usize;
                if self.nodes[self.active_node].next[active_edge] == 0 {
                    let leaf = self.new_node(self.cur_str.len() as isize - 1, GLOBAL_END as isize);
                    self.nodes[self.active_node].next[active_edge] = leaf;
                    self.add_sl(self.active_node); //rule 2
                } else {
                    let nxt = self.nodes[self.active_node].next[active_edge];
                    if self.walk_down(nxt) {
                        continue; //observation 2
                    }
                    if self.cur_str[self.nodes[nxt].start as usize + self.active_len] == c {
                        //observation 1
                        self.active_len += 1;
                        self.add_sl(self.active_node); //observation 3
                        break;
                    }
                    let split = self.new_node(
                        self.nodes[nxt].start,
                        self.nodes[nxt].start + self.active_len as isize,
                    );
                    self.nodes[self.active_node].next[active_edge] = split;
                    let leaf = self.new_node(self.cur_str.len() as isize - 1, GLOBAL_END as isize);
                    self.nodes[split].next[c as usize] = leaf;
                    self.nodes[nxt].start += self.active_len as isize;
                    let s = self.nodes[nxt].start as usize;
                    self.nodes[split].next[self.cur_str[s] as usize] = nxt;
                    self.add_sl(split); //rule 2
                }
                self.remainder -= 1;
                if self.active_node == self.root && self.active_len > 0 {
                    //rule 1
                    self.active_len -= 1;
                    self.active_e =
                        (self.cur_str.len() as isize - 1 - self.remainder as isize + 1) as usize;
                } else {
                    self.active_node = if self.nodes[self.active_node].suffix_link > 0 {
                        self.nodes[self.active_node].suffix_link
                    } else {
                        self.root
                    }; //rule 3
                }
            }
        }
    }
    impl super::SuffixTree for UkkonensSuffixTree {
        fn size(&self) -> usize {
            self.nodes.len()
        }
        fn insert(&mut self, s: &str) {
            for c in s.chars() {
                self.st_extend(c);
            }
            self.st_extend('\0');
            self.str_store.insert(s.to_string());
            self.active_node = 0;
            self.active_len = 0;
            self.remainder = 0;
        }
        fn is_substr(&self, s: &str) -> bool {
            let mut rest = s;
            let mut node_id: NodeId = 0;
            while !rest.is_empty() {
                let next_char = rest.chars().next().unwrap();
                let next = self.nodes[node_id].next[next_char as usize];
                if next == 0 {
                    return false;
                }
                let next_node = &self.nodes[next];
                let min_len = std::cmp::min(self.edge_length(next), rest.len());
                if (0..min_len).all(|i| {
                    rest.chars().nth(i).unwrap()
                        == self.cur_str[(next_node.start as usize + i) as usize]
                }) {
                    rest = &rest[min_len..];
                    node_id = next;
                } else {
                    return false;
                }
            }
            true
        }
        fn contains(&self, s: &str) -> bool {
            self.str_store.contains(s)
        }
    }

    #[test]
    fn test_suff2() {
        let mut t = UkkonensSuffixTree::new();
        t.insert("sdsssdsdsds");
        let all_substrings = (0.."sdsssdsdsds".len())
            .map(|i| "sdsssdsdsds".get(i..).unwrap())
            .collect::<Vec<&str>>();
        for s in all_substrings {
            assert!(t.is_substr(s));
        }
        assert!(!t.is_substr("sdsssdsdsdss"));
        assert!(!t.is_substr("ssss"));
        assert!(!t.is_substr("sdssds"));
        assert!(!t.is_substr("dd"));
    }

    #[test]
    fn test_suff() {
        let mut t = UkkonensSuffixTree::new();
        t.st_extend('a');
        t.st_extend('b');
        t.st_extend('c');
        t.st_extend('a');
        t.st_extend('b');

        assert!(t.is_substr("abcab"));
        assert!(t.is_substr("abc"));
        assert!(t.is_substr("ab"));
        assert!(t.is_substr("a"));
        assert!(t.is_substr("b"));
        assert!(t.is_substr("c"));
        assert!(t.is_substr("abca"));
        assert!(t.is_substr("bca"));
        assert!(t.is_substr("ca"));
        assert!(!t.is_substr("d"));
        assert!(!t.is_substr("abcb"));
    }
}

pub struct SuffixTreeTest<A, B>
where
    A: SuffixTree,
    B: SuffixTree,
{
    pub a: A,
    pub b: B,
}

impl<A, B> SuffixTree for SuffixTreeTest<A, B>
where
    A: SuffixTree,
    B: SuffixTree,
{
    fn size(&self) -> usize {
        self.a.size()
    }
    fn insert(&mut self, s: &str) {
        self.a.insert(s);
        self.b.insert(s);
    }
    fn is_substr(&self, s: &str) -> bool {
        if self.a.is_substr(s) != self.b.is_substr(s) {
            panic!("{} {} {}", self.a.is_substr(s), self.b.is_substr(s), s);
        }
        self.a.is_substr(s)
    }
    fn contains(&self, s: &str) -> bool {
        assert_eq!(self.a.contains(s), self.b.contains(s));
        self.a.contains(s)
    }
}
