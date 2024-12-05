use std::{collections::{HashMap, HashSet}, hash::Hash};

#[derive(Debug, Clone)]
pub struct UnionFind<Node>
where
    Node: Eq + std::hash::Hash + Clone,
{
    nodes: HashMap<Node, usize>,
    parent_or_size: HashMap<usize, isize>,
}

impl<Node> UnionFind<Node>
where
    Node: Eq + std::hash::Hash + Clone,
{
    pub fn new() -> Self {
        UnionFind {
            nodes: HashMap::new(),
            parent_or_size: HashMap::new(),
        }
    }

    fn to_num(&mut self, a: &Node) -> usize {
        let len = self.nodes.len();
        let ret = self.nodes.get(a);
        match ret {
            Some(x) => *x,
            None => {
                self.nodes.insert(a.clone(), len);
                self.parent_or_size.insert(len, -1);
                len
            }
        }
    }

    pub fn merge_nodes(&mut self, a: Node, b: Node) {
        let a = self.to_num(&a);
        let b = self.to_num(&b);
        self._merge(a, b);
    }

    fn _merge(&mut self, a: usize, b: usize) {
        let mut root_a = self._root(a);
        let mut root_b = self._root(b);

        if -self.parent_or_size[&root_a] < -self.parent_or_size[&root_b] {
            std::mem::swap(&mut root_a, &mut root_b);
        }
        self.parent_or_size.insert(
            root_a,
            self.parent_or_size[&root_a] + self.parent_or_size[&root_b],
        );
        self.parent_or_size.insert(root_b, root_a as isize);
    }

    pub fn merge(&mut self, a: &Node, b: &Node) {
        let a = self.to_num(a);
        let b = self.to_num(b);
        self._merge(a, b);
    }

    pub fn connected(&mut self, a: &Node, b: &Node) -> bool {
        let a = self.to_num(a);
        let b = self.to_num(b);
        self._root(a) == self._root(b)
    }

    fn _root(&mut self, a: usize) -> usize {
        let mut ret = a;
        while self.parent_or_size[&ret] >= 0 {
            let nex = self.parent_or_size[&ret] as usize;
            //self.parent_or_size.insert(ret, self.parent_or_size[&nex]);
            ret = nex;
        }
        ret
    }

    pub fn find_contents(&mut self, a: &Node) -> HashSet<Node> {
        let a = self.to_num(a);
        let root = self._root(a);
        let mut ret = HashSet::new();
        for (k, v) in self.nodes.clone().iter() {
            if self._root(*v) == root {
                ret.insert(k.clone());
            }
        }
        ret
    }

    pub fn to_hashmaps(&mut self) -> Vec<HashSet<Node>> {
        let mut ret = HashMap::new();
        for (k, v) in self.nodes.clone().iter() {
            let root = self._root(*v);
            let entry = ret.entry(root).or_insert(HashSet::new());
            entry.insert(k.clone());
        }
        ret.into_iter().map(|(_, v)| v).collect()
    }
}
