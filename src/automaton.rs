use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque},
    hash::Hash,
    iter::once,
    str::Chars,
    vec,
};

use itertools::Itertools;
use regex_syntax::hir::Hir;

#[derive(Debug, Clone)]
pub enum AppRegex {
    Star(Box<AppRegex>),
    Or(Box<AppRegex>, Box<AppRegex>),
    Concat(Box<AppRegex>, Box<AppRegex>),
    Ch(char),
    Eps,
    Nothing,
}

#[test]
fn test_parse2() {
    let regex1 = AppRegex::parse("(01+)*");
    println!("{:?}", regex1);
    let nfa1 = NFA::from_regex(&regex1);
    assert!(!nfa1.accept(&"1".chars().collect_vec()));
}

#[test]
fn test_inclusion() {
    let regex1 = AppRegex::parse("(01+)*");
    let regex2 = AppRegex::parse("1*(01+)*");
    println!("{:?}", regex1);
    println!("{:?}", regex2);
    let nfa1 = NFA::from_regex(&regex1);
    let nfa2 = NFA::from_regex(&regex2);
    assert!(nfa2.find_difference(&nfa1).is_some());
    assert!(nfa1.find_difference(&nfa2).is_none());
    assert!(!nfa1.includes(&nfa2));
    assert!(nfa2.includes(&nfa1));
}

#[test]
fn test_parse() {
    let regex = "1111(0|1)*0";
    let regex = AppRegex::parse(regex);
    assert!(!NFA::from_regex(&regex).accept(&"011110111".chars().collect_vec()));
    println!("{:?}", regex);
    let regex = AppRegex::parse("a(bddd|cf)*d");
    println!("{:?}", regex);

    let regex = AppRegex::parse("a(b|c)*d");
    println!("{:?}", regex);

    let regex = AppRegex::parse("ab*d");
    println!("{:?}", regex);

    let regex = AppRegex::parse("(11|01)*");
    println!("{:?}", regex);

    let regex = AppRegex::parse("10");
    println!("{:?}", regex);
    assert!(NFA::from_regex(&regex).accept(&"10".chars().collect_vec()));

    let regex = AppRegex::parse("100+");
    println!("{:?}", regex);
    assert!(!NFA::from_regex(&regex).accept(&"10".chars().collect_vec()));

    let regex = AppRegex::parse("10+");
    println!("{:?}", regex);
    assert!(NFA::from_regex(&regex).accept(&"10".chars().collect_vec()));

    let regex = AppRegex::parse("10?");
    println!("{:?}", regex);
    assert!(NFA::from_regex(&regex).accept(&"1".chars().collect_vec()));
    assert!(NFA::from_regex(&regex).accept(&"10".chars().collect_vec()));
    assert!(!NFA::from_regex(&regex).accept(&"100".chars().collect_vec()));
    assert!(!NFA::from_regex(&regex).accept(&"".chars().collect_vec()));

    let regex = AppRegex::parse("a(b|)");
    assert!(NFA::from_regex(&regex).accept(&"a".chars().collect_vec()));
    assert!(NFA::from_regex(&regex).accept(&"ab".chars().collect_vec()));

    let regex = AppRegex::parse("111*(011111*|11111*)(011111*|11111*)(011111*|11111*)*");
    println!("{:?}", regex);
    assert!(NFA::from_regex(&regex).accept(&"111111011110111101111".chars().collect_vec()));
}

impl AppRegex {
    pub fn parse(s: &str) -> AppRegex {
        fn convert_tree(tree: &Hir) -> AppRegex {
            match tree.kind() {
                regex_syntax::hir::HirKind::Empty => AppRegex::Eps,
                regex_syntax::hir::HirKind::Literal(l) => {
                    l.0.iter()
                        .map(|c| AppRegex::Ch(char::from_u32(*c as u32).unwrap()))
                        .collect_vec()
                        .into_iter()
                        .reduce(|acc, x| AppRegex::Concat(Box::new(acc), Box::new(x)))
                        .unwrap_or(AppRegex::Eps)
                }
                regex_syntax::hir::HirKind::Concat(c) => c
                    .iter()
                    .map(|x| convert_tree(x))
                    .collect_vec()
                    .into_iter()
                    .reduce(|acc, x| AppRegex::Concat(Box::new(acc), Box::new(x)))
                    .unwrap_or(AppRegex::Eps),
                regex_syntax::hir::HirKind::Alternation(a) => a
                    .iter()
                    .map(|x| convert_tree(x))
                    .collect_vec()
                    .into_iter()
                    .reduce(|acc, x| AppRegex::Or(Box::new(x), Box::new(acc)))
                    .unwrap_or(AppRegex::Nothing),
                regex_syntax::hir::HirKind::Repetition(r) => {
                    let sub = Box::new(convert_tree(&r.sub));
                    let minregex = (0..r.min)
                        .map(|_| sub.clone())
                        .collect_vec()
                        .into_iter()
                        .reduce(|acc, x| Box::new(AppRegex::Concat(acc, x)))
                        .unwrap_or(Box::new(AppRegex::Eps));
                    if r.max.is_some() {
                        let optional_r = Box::new(AppRegex::Or(sub, Box::new(AppRegex::Eps)));
                        let mid = (r.min..r.max.unwrap())
                            .map(|_| optional_r.clone())
                            .collect_vec()
                            .into_iter()
                            .reduce(|acc, x| Box::new(AppRegex::Concat(acc, x)))
                            .unwrap_or(Box::new(AppRegex::Eps));
                        return AppRegex::Concat(minregex, mid);
                    }
                    AppRegex::Concat(minregex, Box::new(AppRegex::Star(sub)))
                }
                regex_syntax::hir::HirKind::Capture(c) => convert_tree(&c.sub),
                regex_syntax::hir::HirKind::Class(regex_syntax::hir::Class::Bytes(c)) => c
                    .ranges()
                    .iter()
                    .flat_map(|r| (r.start()..=r.end()).map(|c| AppRegex::Ch(c as char)))
                    .collect_vec()
                    .into_iter()
                    .reduce(|acc, x| AppRegex::Or(Box::new(acc), Box::new(x)))
                    .unwrap_or(AppRegex::Nothing),
                regex_syntax::hir::HirKind::Class(regex_syntax::hir::Class::Unicode(c)) => c
                    .ranges()
                    .iter()
                    .flat_map(|r| (r.start()..=r.end()).map(|c| AppRegex::Ch(c as char)))
                    .collect_vec()
                    .into_iter()
                    .reduce(|acc, x| AppRegex::Or(Box::new(acc), Box::new(x)))
                    .unwrap_or(AppRegex::Nothing),
                _ => panic!("Unsupported regex {:?}", tree),
            }
        }
        convert_tree(&regex_syntax::parse(s).unwrap())
    }
}
pub type State = String;
fn product_state(a: &State, b: &State) -> State {
    format!("({},{})", a, b)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Transition<A>
where
    A: Eq + std::hash::Hash + Clone + Ord + Ord,
{
    pub from: State,
    pub to: State,
    pub label: A,
}

fn extract_states<A>(transitions: &Vec<Transition<A>>) -> BTreeSet<State>
where
    A: Eq + std::hash::Hash + Clone + Ord + Ord,
{
    transitions
        .iter()
        .flat_map(|t| vec![t.from.clone(), t.to.clone()])
        .collect()
}

static mut STATE_COUNTER: u64 = 0;
pub fn new_state() -> State {
    unsafe {
        STATE_COUNTER += 1;
        format!("q{}", STATE_COUNTER)
    }
}
fn group_transitions_by_from<A>(
    transitions: Vec<Transition<A>>,
) -> HashMap<State, Vec<Transition<A>>>
where
    A: Eq + std::hash::Hash + Clone + Ord,
{
    transitions
        .into_iter()
        .into_group_map_by(|t| t.from.clone())
        .into_iter()
        .map(|(k, v)| (k, v.into_iter().unique().collect()))
        .collect()
}

pub trait HasEps {
    fn eps() -> Self;
}

#[test]
fn test_input_nfa() {
    let mut t = Transducer::new();
    t.add_transition(Transition {
        from: "q1".to_string(),
        to: "q1".to_string(),
        label: (Some('1'), Some('0')),
    });

    let nfa = t.get_input_nfa();
    nfa.show_dot("test_input_nfa");
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct BaseAutomaton<A>
where
    A: Eq + std::hash::Hash + Clone + HasEps + std::fmt::Debug + Ord,
{
    pub transition: BTreeMap<State, Vec<Transition<A>>>,
    pub accept: BTreeSet<State>,
    pub start: State,
    pub states: BTreeSet<State>,
}

fn escape_state_for_dot(s: &State) -> String {
    format!("\"{}\"", s.replace("\"", "\\\""))
}

#[test]
fn test_reachable() {
    let mut nfa = NFA::new();
    nfa.add_transition(Transition {
        from: nfa.start.clone(),
        to: "a2".to_string(),
        label: Some('a'),
    });
    nfa.add_transition(Transition {
        from: "a2".to_string(),
        to: "a3".to_string(),
        label: Some('b'),
    });
    nfa.add_transition(Transition {
        from: "a3".to_string(),
        to: nfa.start.clone(),
        label: Some('c'),
    });
    nfa.add_transition(Transition {
        from: nfa.start.clone(),
        to: nfa.start.clone(),
        label: Some('d'),
    });
    nfa.accept = vec![nfa.start.clone()].into_iter().collect();
    assert!(
        nfa.reachable_states()
            == vec![nfa.start.clone(), "a2".to_string(), "a3".to_string()]
                .into_iter()
                .collect()
    );

    let rev = nfa.reversed();
    let rev_reachable = rev.reachable_states();
    println!("{:?}", rev.transition);

    rev.show_dot("test_reachable2");
    nfa.show_dot("test_reachable");
    println!("{:?}", rev_reachable);
    assert!(vec![nfa.start.clone(), "a2".to_string(), "a3".to_string()]
        .into_iter()
        .all(|s| rev_reachable.contains(&s)));
}

#[test]
fn testtt() {
    let mut h1 = BTreeSet::<String>::new();
    let mut h2 = BTreeSet::<String>::new();
    h1.insert("a".to_string());
    h1.insert("b".to_string());
    h2.insert("a".to_string());
    h2.insert("b".to_string());

    assert!(h1 == h2);

    #[derive(Debug, Eq, PartialEq, Clone)]
    struct StatePair(BTreeSet<State>, BTreeSet<State>);
    impl Ord for StatePair {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            (other.0.len() + other.1.len()).cmp(&(self.0.len() + self.1.len()))
        }
    }
    impl PartialOrd for StatePair {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }

    let mut h = StatePair(BTreeSet::new(), BTreeSet::new());
    h.0.insert("a".to_string());
    h.0.insert("b".to_string());
    h.1.insert("a".to_string());
    h.1.insert("b".to_string());
    let mut h2 = StatePair(BTreeSet::new(), BTreeSet::new());
    h2.0.insert("b".to_string());
    h2.0.insert("a".to_string());
    h2.0.insert("a".to_string());
    h2.1.insert("b".to_string());
    h2.1.insert("a".to_string());

    assert!(h == h2);
    assert!(h.0.is_subset(&h.1));
}

#[test]
fn test_equal() {
    let nfa_1 = NFA::from_regex(&AppRegex::parse("a(b|c)*d"));
    let nfa_2 = NFA::from_regex(&AppRegex::parse("a(b|c)*d"));
    assert!(nfa_1.is_equal(&nfa_2));

    let nfa_1 = NFA::from_regex(&AppRegex::parse("a(b|c)*d"));
    let nfa_2 = NFA::from_regex(&AppRegex::parse("ab(b|c)*d"));
    assert!(!nfa_1.is_equal(&nfa_2));

    let nfa_1 = NFA::from_regex(&AppRegex::parse("ab(b*)d"));
    let nfa_2 = NFA::from_regex(&AppRegex::parse("a(b*)bd"));
    assert!(nfa_1.is_equal(&nfa_2));

    let nfa_1 = NFA::from_regex(&AppRegex::parse("ab(b*)bbbbbd"));
    let nfa_2 = NFA::from_regex(&AppRegex::parse("abbbbbb*bd"));
    assert!(nfa_1.is_equal(&nfa_2));

    let nfa_1 = NFA::from_regex(&AppRegex::parse(""));
    let nfa_2 = NFA::from_regex(&AppRegex::parse(""));
    assert!(nfa_1.is_equal(&nfa_2));

    let nfa_1 = NFA::from_regex(&AppRegex::parse("ab"));
    let nfa_2 = NFA::from_regex(&AppRegex::parse("a"));
    assert!(!nfa_1.is_equal(&nfa_2));
}

impl<A> BaseAutomaton<A>
where
    A: Eq + std::hash::Hash + Clone + HasEps + std::fmt::Debug + Ord,
{
    pub fn new() -> BaseAutomaton<A> {
        let start = new_state();
        BaseAutomaton {
            transition: BTreeMap::new(),
            accept: BTreeSet::new(),
            start: start.clone(),
            states: vec![start.clone()].into_iter().collect(),
        }
    }

    pub fn init(
        transitions: Vec<Transition<A>>,
        accept: BTreeSet<State>,
        start: State,
    ) -> BaseAutomaton<A> {
        let transitions = transitions
            .into_iter()
            .unique()
            .filter(|t| !(t.label == A::eps() && t.from == t.to))
            .collect_vec();
        let transition_map: BTreeMap<State, Vec<Transition<A>>> =
            group_transitions_by_from(transitions.clone())
                .into_iter()
                .collect();
        let mut states = extract_states(&transitions);
        states.insert(start.clone());
        let accept = accept
            .clone()
            .into_iter()
            .filter(|s| states.contains(s))
            .collect();
        BaseAutomaton {
            transition: transition_map,
            accept,
            start,
            states,
        }
    }

    pub fn add_transition(&mut self, transition: Transition<A>) {
        self.states.insert(transition.from.clone());
        self.states.insert(transition.to.clone());
        self.transition
            .entry(transition.from.clone())
            .or_insert(vec![])
            .push(transition);
    }

    pub fn incoming_transition_map(&self) -> HashMap<State, Vec<Transition<A>>> {
        let mut incoming: HashMap<State, Vec<Transition<A>>> = HashMap::new();
        for (from, transitions) in &self.transition {
            for transition in transitions {
                incoming
                    .entry(transition.to.clone())
                    .or_insert(vec![])
                    .push(transition.clone());
            }
        }
        incoming
    }

    pub fn to_dot(&self) -> String {
        let mut dot = String::new();
        dot.push_str("digraph {\n");
        for (from, transitions) in &self.transition {
            for transition in transitions {
                let label = format!("{:?}", transition.label);
                dot.push_str(&format!(
                    "{} -> {} [label={}]\n",
                    escape_state_for_dot(from),
                    escape_state_for_dot(&transition.to),
                    escape_state_for_dot(&label)
                ));
            }
        }
        for state in &self.accept {
            dot.push_str(&format!(
                "{} [shape=doublecircle]\n",
                escape_state_for_dot(state)
            ));
        }

        let super_start = new_state();
        dot.push_str(&format!("{} [shape=point]\n", super_start));
        dot.push_str(&format!(
            "{} -> {}\n",
            super_start,
            escape_state_for_dot(&self.start)
        ));

        dot.push_str("}\n");
        dot
    }
    pub fn show_dot(&self, base_name: &str) {
        let dot = self.to_dot();
        let dot_name = format!("{}.dot", base_name);
        let path = std::path::Path::new(&dot_name);
        std::fs::write(path, dot).unwrap();
        let output = std::process::Command::new("dot")
            .arg("-Tpng")
            .arg(dot_name)
            .arg("-o")
            .arg(format!("{}.png", base_name))
            .output()
            .unwrap();
    }
    pub fn union(
        &self,
        other: &BaseAutomaton<A>,
        rename_if_collision_state_name: bool,
    ) -> BaseAutomaton<A> {
        let overlap_name = self.states.intersection(&other.states).count() > 0;
        let mut other: Cow<BaseAutomaton<A>> = Cow::Borrowed(other);
        if rename_if_collision_state_name && overlap_name {
            other = Cow::Owned(other.rename_states());
        } else if overlap_name {
            panic!("Overlap state names");
        };

        let mut new_transitions: Vec<Transition<A>> = self
            .transition
            .iter()
            .chain(other.transition.iter())
            .flat_map(|(_, transitions)| transitions.clone().into_iter())
            .collect_vec();
        let new_start = new_state();
        new_transitions.push(Transition {
            from: new_start.clone(),
            to: self.start.clone(),
            label: A::eps(),
        });
        new_transitions.push(Transition {
            from: new_start.clone(),
            to: other.start.clone(),
            label: A::eps(),
        });

        BaseAutomaton::init(
            new_transitions,
            self.accept
                .clone()
                .into_iter()
                .chain(other.accept.clone().into_iter())
                .collect::<BTreeSet<_>>(),
            new_start,
        )
    }

    pub fn union_mut(&mut self, other: &BaseAutomaton<A>, rename_if_collision_state_name: bool) {
        let overlap_name = self.states.intersection(&other.states).count() > 0;
        let mut other: Cow<BaseAutomaton<A>> = Cow::Borrowed(other);
        if rename_if_collision_state_name && overlap_name {
            other = Cow::Owned(other.rename_states());
        } else if overlap_name {
            panic!("Overlap state names");
        };

        for (_, transitions) in &other.transition {
            for transition in transitions {
                self.add_transition(transition.clone());
            }
        }
        self.accept = self
            .accept
            .clone()
            .into_iter()
            .chain(other.accept.clone().into_iter())
            .collect::<BTreeSet<_>>();
        let new_start = new_state();
        self.add_transition(Transition {
            from: new_start.clone(),
            to: self.start.clone(),
            label: A::eps(),
        });
        self.add_transition(Transition {
            from: new_start.clone(),
            to: other.start.clone(),
            label: A::eps(),
        });
        self.start = new_start;
    }

    pub fn rename_states(&self) -> BaseAutomaton<A> {
        let new_states = self
            .states
            .iter()
            .map(|s| (s.clone(), new_state()))
            .collect::<HashMap<_, _>>();
        let new_transitions = self
            .transition
            .values()
            .flatten()
            .map(|t| Transition {
                from: new_states.get(&t.from).unwrap().clone(),
                to: new_states.get(&t.to).unwrap().clone(),
                label: t.label.clone(),
            })
            .collect_vec();
        BaseAutomaton::init(
            new_transitions,
            self.accept
                .iter()
                .map(|a| new_states.get(a).unwrap().clone())
                .collect(),
            new_states.get(&self.start).unwrap().clone(),
        )
    }

    pub fn concat(&self, other: &BaseAutomaton<A>) -> BaseAutomaton<A> {
        let mut new_transitions: Vec<Transition<A>> = self
            .transition
            .iter()
            .chain(other.transition.iter())
            .flat_map(|(_, transitions)| transitions.clone().into_iter())
            .collect_vec();
        let new_start = self.start.clone();
        for state in self.accept.iter() {
            new_transitions.push(Transition {
                from: state.clone(),
                to: other.start.clone(),
                label: A::eps(),
            });
        }
        BaseAutomaton::init(new_transitions, other.accept.clone(), new_start)
    }

    pub fn product_by<B, C>(
        &self,
        other: &BaseAutomaton<B>,
        map_pair: impl Fn(&A, &B) -> Option<C>,
    ) -> BaseAutomaton<C>
    where
        B: Eq + std::hash::Hash + Clone + std::fmt::Debug + HasEps + Ord,
        C: Eq + std::hash::Hash + Clone + std::fmt::Debug + HasEps + Ord,
    {
        let mut product_transitions: Vec<Transition<C>> = vec![];

        let mut queue: VecDeque<(State, State)> = VecDeque::new();
        let mut inserted: BTreeSet<(State, State)> = BTreeSet::new();
        inserted.insert((self.start.clone(), other.start.clone()));
        queue.push_back((self.start.clone(), other.start.clone()));

        while !queue.is_empty() {
            let (cur_a, cur_b) = queue.pop_front().unwrap();

            let emp_transitions_a: Vec<Transition<A>> = vec![Transition {
                from: cur_a.clone(),
                to: cur_a.clone(),
                label: A::eps(),
            }];
            let emp_transitions_b: Vec<Transition<B>> = vec![Transition {
                from: cur_b.clone(),
                to: cur_b.clone(),
                label: B::eps(),
            }];
            let a_emp = vec![];
            let b_emp = vec![];

            let transitions_a = self
                .transition
                .get(&cur_a)
                .unwrap_or(&a_emp)
                .into_iter()
                .chain(emp_transitions_a.iter());
            let transitions_b = other
                .transition
                .get(&cur_b)
                .unwrap_or(&b_emp)
                .into_iter()
                .chain(emp_transitions_b.iter());

            transitions_a
                .cartesian_product(transitions_b)
                .filter_map(|(a, b)| map_pair(&a.label, &b.label).map(|label| (a, b, label)))
                .for_each(|(a, b, new_label)| {
                    let new_state = product_state(&a.to, &b.to);
                    product_transitions.push(Transition {
                        from: product_state(&cur_a, &cur_b),
                        to: new_state.clone(),
                        label: new_label,
                    });
                    if !inserted.contains(&(a.to.clone(), b.to.clone())) {
                        inserted.insert((a.to.clone(), b.to.clone()));
                        queue.push_back((a.to.clone(), b.to.clone()));
                    }
                });
        }

        product_transitions.retain(|t| t.label != C::eps() || t.from != t.to);

        BaseAutomaton::init(
            product_transitions,
            inserted
                .iter()
                .filter(|(a, b)| self.accept.contains(a) && other.accept.contains(b))
                .map(|(a, b)| product_state(a, b))
                .collect(),
            product_state(&self.start, &other.start),
        )
    }

    pub fn reversed(&self) -> BaseAutomaton<A> {
        let mut new_transitions: Vec<Transition<A>> = self
            .transition
            .values()
            .flatten()
            .map(|t| Transition {
                to: t.from.clone(),
                from: t.to.clone(),
                label: t.label.clone(),
            })
            .collect();

        let new_start = if self.accept.len() != 1 {
            let new_start = new_state();
            for state in self.accept.iter() {
                new_transitions.push(Transition {
                    from: new_start.clone(),
                    to: state.clone(),
                    label: A::eps(),
                });
            };
            new_start
        } else {
            self.accept.iter().next().unwrap().clone()
        };

        BaseAutomaton::init(
            new_transitions,
            vec![self.start.clone()].into_iter().collect(),
            new_start,
        )
    }

    pub fn reachable_states(&self) -> BTreeSet<State> {
        let mut reachable: BTreeSet<State> = BTreeSet::new();
        let mut queue: VecDeque<State> = VecDeque::new();
        queue.push_back(self.start.clone());
        reachable.insert(self.start.clone());
        while let Some(cur) = queue.pop_front() {
            if let Some(transitions) = self.transition.get(&cur) {
                for transition in transitions {
                    if !reachable.contains(&transition.to) {
                        reachable.insert(transition.to.clone());
                        queue.push_back(transition.to.clone());
                    }
                }
            }
        }
        reachable
    }

    pub fn distances_from_start(&self) -> HashMap<State, usize> {
        let mut distances: HashMap<State, usize> = HashMap::new();
        let mut pq: BinaryHeap<(isize, State)> = BinaryHeap::new();
        pq.push((0, self.start.clone()));
        while let Some((dist, cur)) = pq.pop() {
            let dist = -dist;
            if !distances.contains_key(&cur) {
                distances.insert(cur.clone(), dist as usize);
                if let Some(transitions) = self.transition.get(&cur) {
                    for transition in transitions {
                        pq.push((-(dist as isize + 1), transition.to.clone()));
                    }
                }
            }
        }
        distances
    }

    pub fn reduce_size_unreachable(&self) -> BaseAutomaton<A> {
        let forward_reachable: BTreeSet<State> = self.reachable_states();
        let backward_reachable: BTreeSet<State> = self.reversed().reachable_states();
        let reachable: BTreeSet<State> = forward_reachable
            .intersection(&backward_reachable)
            .cloned()
            .collect();
        let new_transitions = self
            .transition
            .iter()
            .flat_map(|(_, transitions)| transitions.clone().into_iter())
            .filter(|t| reachable.contains(&t.from) && reachable.contains(&t.to))
            .collect();
        BaseAutomaton::init(new_transitions, self.accept.clone(), self.start.clone())
    }

    // A -(none)-> B -(none)-> C => A -(none)-> C
    pub fn remove_none_none_transitions(&self) -> BaseAutomaton<A> {
        println!("{:?}", self.transition.len());
        let mut removed_something: bool = false;

        let mut transition_from_map = self.transition.clone();
        let mut transition_to_map: HashMap<String, Vec<Transition<A>>> = self
            .transition
            .values()
            .flatten()
            .map(|t| (*t).clone())
            .into_group_map_by(|t| t.to.clone());
        let emp_vec: Vec<Transition<A>> = vec![];
        for state in self.states.iter() {
            if *state == self.start || self.accept.contains(state) {
                continue;
            }
            let out_transitions = transition_from_map.get(state).unwrap_or(&emp_vec).clone();
            if out_transitions.iter().all(|t| t.label == A::eps()) {
                let in_transitions = transition_to_map.get(state).unwrap_or(&emp_vec).clone();
                if in_transitions.iter().all(|t| t.label == A::eps()) {
                    removed_something = true;
                    for (i, o) in in_transitions
                        .iter()
                        .cartesian_product(out_transitions.iter())
                    {
                        let t = Transition {
                            from: i.from.clone(),
                            to: o.to.clone(),
                            label: A::eps(),
                        };
                        transition_from_map
                            .entry(i.from.clone())
                            .or_insert(vec![])
                            .push(t.clone());
                        transition_to_map
                            .entry(o.to.clone())
                            .or_insert(vec![])
                            .push(t);
                    }
                    transition_from_map.remove(state);
                    transition_to_map.remove(state);
                    for ot in out_transitions {
                        transition_to_map
                            .entry(ot.to.clone())
                            .or_insert(vec![])
                            .retain(|t| t.from != *state);
                    }
                    for it in in_transitions {
                        transition_from_map
                            .entry(it.from.clone())
                            .or_insert(vec![])
                            .retain(|t| t.to != *state);
                    }
                }
            }
        }
        let ret = BaseAutomaton::init(
            transition_from_map
                .values()
                .flatten()
                .map(|t| (*t).clone())
                .collect(),
            self.accept.clone(),
            self.start.clone(),
        )
        .reduce_size_unreachable();
        println!("done");
        if removed_something {
            ret.remove_none_none_transitions()
        } else {
            ret
        }
    }

    pub fn reachable_states_with<'a>(
        &'a self,
        froms: &Vec<&'a State>,
        s: &Vec<A>,
    ) -> BTreeSet<State> {
        let mut reachable: BTreeSet<(usize, &'a State)> = BTreeSet::new();
        let mut queue: VecDeque<(usize, &'a State)> = VecDeque::new();

        let s = s.into_iter().filter(|s| **s != A::eps()).collect_vec();

        queue.extend(froms.iter().map(|f| (s.len(), *f)));
        reachable.extend(froms.iter().map(|f| (s.len(), *f)));

        let mut ret = BTreeSet::new();

        while let Some((cur_s, cur_state)) = queue.pop_front() {
            if cur_s == 0 {
                ret.insert(cur_state.clone());
            }

            if let Some(transitions) = self.transition.get(cur_state) {
                for transition in transitions {
                    if transition.label == A::eps() {
                        let new_state = (cur_s, &transition.to);
                        if !reachable.contains(&new_state) {
                            reachable.insert(new_state.clone());
                            queue.push_back(new_state);
                        }
                    } else if cur_s > 0 && *s[s.len() - cur_s] == transition.label {
                        let new_state = (cur_s - 1, &transition.to);
                        if !reachable.contains(&new_state) {
                            reachable.insert(new_state.clone());
                            queue.push_back(new_state);
                        }
                    }
                }
            }
        }

        ret
    }

    pub fn labels(&self) -> BTreeSet<A> {
        self.transition
            .values()
            .flatten()
            .map(|t| t.label.clone())
            .collect()
    }

    pub fn append_vec(&self, s: &Vec<A>) -> BaseAutomaton<A> {
        let s = &s.into_iter().filter(|s| **s != A::eps()).collect_vec();
        if s.len() == 0 {
            return self.clone();
        }

        let new_states = s.iter().map(|_| new_state()).collect_vec();

        let mut new_transitions: Vec<Transition<A>> =
            self.transition.values().flatten().cloned().collect_vec();

        for a in self.accept.iter() {
            new_transitions.push(Transition {
                from: a.clone(),
                to: new_states[0].clone(),
                label: s[0].clone(),
            });
        }

        let mut cur = new_states[0].clone();

        for (i, a) in s.iter().enumerate().skip(1) {
            let next: String = new_states[i].clone();
            new_transitions.push(Transition {
                from: cur.clone(),
                to: next.clone(),
                label: (*a).clone(),
            });
            cur = next;
        }

        BaseAutomaton::init(
            new_transitions,
            [cur].into_iter().collect(),
            self.start.clone(),
        )
    }

    pub fn left_quotient(&self, s: &Vec<A>) -> BaseAutomaton<A> {
        let s = &s
            .into_iter()
            .filter(|s| **s != A::eps())
            .cloned()
            .collect_vec();
        let new_start = new_state();
        let reachables = self.reachable_states_with(&vec![&self.start], s);
        let start_transitions = reachables
            .into_iter()
            .map(|to| Transition {
                from: new_start.clone(),
                to: to.clone(),
                label: A::eps(),
            })
            .collect_vec();

        BaseAutomaton::init(
            [
                start_transitions,
                self.transition.values().flatten().cloned().collect_vec(),
            ]
            .concat(),
            self.accept.clone(),
            new_start,
        )
    }

    fn transition_with_a(&self) -> HashMap<&State, HashMap<A, BTreeSet<State>>> {
        let mut labels = self.labels();
        labels.insert(A::eps());
        self.states
            .iter()
            .map(|from| {
                let nexts = labels
                    .iter()
                    .map(|l| {
                        let tos = self.reachable_states_with(&vec![&from], &vec![l.clone()]);
                        (l.clone(), tos)
                    })
                    .collect();
                (from, nexts)
            })
            .collect()
    }

    pub fn minimize_bisimulation(&self) -> BaseAutomaton<A> {
        #[derive(Debug, Eq, PartialEq, Hash, Clone)]
        struct Behaviour<A>
        where
            A: Eq + std::hash::Hash + Clone + Ord,
        {
            nexts: Vec<(A, usize)>,
            accept_self: bool,
        }
        //println!("srtarting;");

        // This line is slow when the number of alphabet is large
        let transition_a_map: HashMap<&State, HashMap<A, BTreeSet<State>>> =
            self.transition_with_a();

        let emp_set = BTreeSet::<State>::new();
        let emp_vec = vec![];
        let acceptable_states = self
            .states
            .iter()
            .filter(|s| {
                transition_a_map
                    .get(s)
                    .unwrap()
                    .get(&A::eps())
                    .unwrap_or(&emp_set)
                    .intersection(&self.accept)
                    .collect_vec()
                    .len()
                    > 0
            })
            .collect::<BTreeSet<_>>();

        let transitino_to_map: HashMap<String, Vec<Transition<A>>> = transition_a_map
            .iter()
            .flat_map(|(from, tos)| {
                tos.iter()
                    .filter(|a| *a.0 != A::eps())
                    .flat_map(move |(l, to)| {
                        to.iter().map(move |to| Transition {
                            from: (*from).clone(),
                            to: to.clone(),
                            label: l.clone(),
                        })
                    })
            })
            .into_group_map_by(|t| t.to.clone());
        let mut num_blocks = 1;
        let mut block_map: BTreeMap<State, usize> =
            self.states.iter().map(|s| (s.clone(), 0)).collect();
        let mut block_id_to_states: HashMap<usize, BTreeSet<State>> =
            vec![(0, self.states.clone())].into_iter().collect();
        let mut dirty_states: BTreeSet<State> = self.states.iter().cloned().collect();

        while dirty_states.len() > 0 {
            let dirty_state = dirty_states.iter().next().unwrap().clone();
            let cur_block = block_map.get(&dirty_state).unwrap().clone();
            let block_states: BTreeSet<String> =
                block_id_to_states.get(&cur_block).unwrap().clone();
            block_states.iter().for_each(|s| {
                dirty_states.remove(s);
            });

            let behaviour_map: HashMap<Behaviour<A>, Vec<(&State, Behaviour<A>)>> = block_states
                .iter()
                .map(|s| {
                    (
                        s,
                        Behaviour {
                            nexts: transition_a_map
                                .get(s)
                                .unwrap()
                                .iter()
                                .filter(|(l, _)| *l != &A::eps())
                                .flat_map(|(l, tos)| {
                                    tos.iter()
                                        .map(|to| (l.clone(), block_map.get(to).unwrap().clone()))
                                })
                                .unique()
                                .sorted()
                                .collect_vec(),
                            accept_self: acceptable_states.contains(s),
                        },
                    )
                })
                .into_group_map_by(|(_, b)| (*b).clone());

            let largest_block = behaviour_map
                .iter()
                .max_by_key(|(_, states)| states.len())
                .unwrap()
                .0;
            let mut changed_states: BTreeSet<&State> = BTreeSet::new();
            for (s, b) in behaviour_map.iter() {
                if s == largest_block {
                    continue;
                }
                for (s, _) in b {
                    block_id_to_states
                        .get_mut(&cur_block)
                        .unwrap()
                        .remove(s.as_str());
                    block_map.insert((*s).clone(), num_blocks);
                    block_id_to_states
                        .entry(num_blocks)
                        .or_insert(BTreeSet::new())
                        .insert((*s).clone());
                    changed_states.insert(s);
                }
                num_blocks += 1;
            }

            for d in changed_states.into_iter() {
                transitino_to_map
                    .get(d)
                    .unwrap_or(&emp_vec)
                    .iter()
                    .for_each(|t| {
                        dirty_states.insert(t.from.clone());
                    });
            }
        }

        let block_to_new_state: HashMap<usize, State> =
            block_map.iter().map(|(_, b)| (*b, new_state())).collect();

        let new_transitions: Vec<Transition<A>> = self
            .transition
            .values()
            .flatten()
            .map(|t| Transition {
                from: block_to_new_state
                    .get(block_map.get(&t.from).unwrap())
                    .unwrap()
                    .clone(),
                to: block_to_new_state
                    .get(block_map.get(&t.to).unwrap())
                    .unwrap()
                    .clone(),
                label: t.label.clone(),
            })
            .unique()
            .collect();

        let new_start = block_to_new_state
            .get(block_map.get(&self.start).unwrap())
            .unwrap()
            .clone();
        let new_accept: BTreeSet<State> = self
            .accept
            .iter()
            .map(|s| {
                block_to_new_state
                    .get(block_map.get(s).unwrap())
                    .unwrap()
                    .clone()
            })
            .collect();

        BaseAutomaton::init(new_transitions, new_accept, new_start)
    }

    pub fn includes(&self, other: &BaseAutomaton<A>) -> bool {
        let other = &other.rename_states();
        let unioned = self.union(other, false);

        unioned.is_equal_state(
            &vec![self.start.clone()].into_iter().collect(),
            &vec![self.start.clone(), other.start.clone()]
                .into_iter()
                .collect(),
        )
    }

    // antichain algorithm
    pub fn find_difference(&self, other: &BaseAutomaton<A>) -> Option<Vec<A>> {
        type PairState = (State, BTreeSet<State>);

        let transitions_a = self.transition_with_a();
        let transitions_b = other.transition_with_a();
        let alphabets = self
            .labels()
            .union(&other.labels())
            .cloned()
            .filter(|c| c != &A::eps())
            .collect_vec();

        let mut reached: BTreeMap<State, Vec<BTreeSet<State>>> = BTreeMap::new();
        let mut queue: VecDeque<(Vec<A>, PairState)> = VecDeque::new();

        let a_starts = transitions_a
            .get(&self.start)
            .unwrap()
            .get(&A::eps())
            .unwrap();
        let b_starts = transitions_b
            .get(&other.start)
            .unwrap()
            .get(&A::eps())
            .unwrap();

        for a_start in a_starts {
            queue.push_back((vec![], (a_start.clone(), b_starts.clone())));
            reached.insert(a_start.clone(), vec![b_starts.clone()]);
        }

        while let Some((s, (cur_a, cur_bs))) = queue.pop_front() {
            if self.accept.contains(&cur_a) && !cur_bs.iter().any(|b| other.accept.contains(b)) {
                return Some(s);
            }
            for ch in alphabets.iter() {
                let next_s = s.clone().into_iter().chain(vec![ch.clone()]).collect_vec();
                let next_bs: BTreeSet<State> = cur_bs
                    .iter()
                    .flat_map(|cur_b| {
                        transitions_b
                            .get(cur_b)
                            .unwrap_or(&HashMap::new())
                            .get(ch)
                            .unwrap_or(&BTreeSet::new())
                            .clone()
                    })
                    .collect();
                for next_a in transitions_a
                    .get(&cur_a)
                    .unwrap_or(&HashMap::new())
                    .get(ch)
                    .unwrap_or(&BTreeSet::new())
                {
                    if reached
                        .get(next_a)
                        .unwrap_or(&vec![])
                        .iter()
                        .all(|frontier_bs| !frontier_bs.is_subset(&next_bs))
                    {
                        reached
                            .entry(next_a.clone())
                            .or_insert(vec![])
                            .push(next_bs.clone());
                        queue.push_back((next_s.clone(), (next_a.clone(), next_bs.clone())));
                    }
                }
            }
        }
        None
    }

    pub fn is_equal(&self, other: &BaseAutomaton<A>) -> bool {
        let other = &other.rename_states();
        let unioned = self.union(other, false);
        unioned.is_equal_state(
            &vec![self.start.clone()].into_iter().collect(),
            &vec![other.start.clone()].into_iter().collect(),
        )
    }

    // Checking NFA equivalence with bisimulations up to congruence
    pub fn is_equal_state(
        &self,
        self_state: &BTreeSet<State>,
        other_state: &BTreeSet<State>,
    ) -> bool {
        fn normalform(ss: &BTreeSet<State>, relatinos: &Vec<&StatePair>) -> BTreeSet<State> {
            let mut ret = ss.clone();
            let mut used: Vec<bool> = vec![false; relatinos.len()];
            loop {
                let before_size = ret.len();
                for (i, r) in relatinos.iter().enumerate() {
                    if used[i] {
                        continue;
                    }
                    if r.0.is_subset(&ret) || r.1.is_subset(&ret) {
                        ret.extend(r.1.clone());
                        ret.extend(r.0.clone());
                        used[i] = true;
                    }
                }
                if before_size == ret.len() {
                    break;
                }
            }
            ret
        }
        fn eps_closure<A>(
            s: BTreeSet<State>,
            transition_a_map: &HashMap<&State, HashMap<A, BTreeSet<State>>>,
        ) -> BTreeSet<State>
        where
            A: Eq + std::hash::Hash + Clone + Ord + HasEps,
        {
            s.into_iter()
                .flat_map(|s| {
                    transition_a_map
                        .get(&s)
                        .unwrap()
                        .get(&A::eps())
                        .unwrap()
                        .clone()
                })
                .collect()
        }
        #[derive(Debug, Eq, PartialEq, Clone)]
        struct StatePair(BTreeSet<State>, BTreeSet<State>);
        impl Ord for StatePair {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                (other.0.len() + other.1.len()).cmp(&(self.0.len() + self.1.len()))
            }
        }
        impl PartialOrd for StatePair {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        let mut labels = self.labels();
        labels.remove(&A::eps());
        let transition_a_map = self.transition_with_a();
        let mut todos: BinaryHeap<StatePair> = BinaryHeap::new();
        let mut relations: Vec<StatePair> = vec![];
        let emp_map: HashMap<A, BTreeSet<State>> = HashMap::new();
        let emp_set: BTreeSet<State> = BTreeSet::new();

        todos.push(StatePair(self_state.clone(), other_state.clone()));
        while let Some(StatePair(l, r)) = todos.pop() {
            let l = eps_closure(l, &transition_a_map);
            let r = eps_closure(r, &transition_a_map);
            let c = relations.iter().chain(todos.iter()).collect_vec();

            if normalform(&l, &c) == normalform(&r, &c) {
                continue;
            }

            let accept_l = l.intersection(&self.accept).count() > 0;
            let accept_r = r.intersection(&self.accept).count() > 0;
            if accept_l != accept_r {
                return false;
            }

            for ch in labels.iter() {
                let next_l: BTreeSet<State> = l
                    .iter()
                    .flat_map(|s| {
                        transition_a_map
                            .get(s)
                            .unwrap_or(&emp_map)
                            .get(&ch)
                            .unwrap_or(&emp_set)
                            .clone()
                    })
                    .collect();
                let next_r: BTreeSet<State> = r
                    .iter()
                    .flat_map(|s| {
                        transition_a_map
                            .get(s)
                            .unwrap_or(&emp_map)
                            .get(&ch)
                            .unwrap_or(&emp_set)
                            .clone()
                    })
                    .collect();
                todos.push(StatePair(next_l, next_r));
            }
            relations.push(StatePair(l, r));
        }
        true
    }

    pub fn reduce_size(&self) -> BaseAutomaton<A> {
        let mut a = self.reduce_size_unreachable();

        //assert!(a.is_equal(&self));
        a = a.minimize_bisimulation();
        let b = a.reversed().minimize_bisimulation().reversed();
        //assert!(a.is_equal(&b));
        //assert!(self.is_equal(&b));
        b
    }

    pub fn map_labels<B>(&self, map: impl Fn(&A) -> B) -> BaseAutomaton<B>
    where
        B: Eq + std::hash::Hash + Clone + std::fmt::Debug + HasEps + Ord,
    {
        let new_transitions: Vec<Transition<B>> = self
            .transition
            .values()
            .flatten()
            .map(|t| Transition {
                from: t.from.clone(),
                to: t.to.clone(),
                label: map(&t.label),
            })
            .collect();
        BaseAutomaton::init(new_transitions, self.accept.clone(), self.start.clone())
    }

    // the first state is the representative state
    pub fn merge_states(&self, merge: Vec<BTreeSet<&State>>) -> BaseAutomaton<A> {
        if merge.len() == 0 {
            return self.clone();
        }

        let state_maps: HashMap<&State, State> = merge
            .iter()
            .map(|s| {
                let new_state = (*s.iter().next().unwrap()).clone();
                s.iter()
                    .map(|s| (*s, new_state.clone()))
                    .collect::<HashMap<_, _>>()
            })
            .flatten()
            .collect();

        let map_state = |s: &State| state_maps.get(s).unwrap_or(s).clone();

        let new_transitions: Vec<Transition<A>> = self
            .transition
            .values()
            .flatten()
            .map(|t| Transition {
                from: map_state(&t.from).clone(),
                to: map_state(&t.to).clone(),
                label: t.label.clone(),
            })
            .collect();

        BaseAutomaton::init(
            new_transitions,
            self.accept.iter().map(|s| map_state(s).clone()).collect(),
            map_state(&self.start).clone(),
        )
    }

    pub fn intersection(&self, other: &BaseAutomaton<A>) -> BaseAutomaton<A> {
        self.product_by(other, |a, b| if a == b { Some(a.clone()) } else { None })
    }
    pub fn difference(&self, other: &BaseAutomaton<A>) -> BaseAutomaton<A> {
        self.intersection(&other.negate())
    }

    pub fn negate(&self) -> BaseAutomaton<A> {
        if !self.is_deterministic() {
            self.determinize().negate()
        } else {
            let new_accept: BTreeSet<State> = self
                .states
                .iter()
                .filter(|s| !self.accept.contains(*s))
                .cloned()
                .collect();
            BaseAutomaton::init(
                self.transition.values().flatten().cloned().collect(),
                new_accept,
                self.start.clone(),
            )
        }
    }

    pub fn is_deterministic(&self) -> bool {
        let contains_eps = self
            .transition
            .values()
            .flatten()
            .any(|t| t.label == A::eps());
        let contains_multiple = self
            .transition
            .iter()
            .any(|(_, ts)| !ts.iter().map(|t| t.label.clone()).all_unique());

        !contains_eps && !contains_multiple
    }

    pub fn is_total(&self, alphabet: &BTreeSet<A>) -> bool {
        let used_labels = self.labels();
        if !used_labels.difference(&alphabet).collect_vec().is_empty() {
            return false;
        }
        return self.states.iter().all(|s| {
            alphabet.iter().all(|a| {
                self.transition
                    .get(s)
                    .unwrap_or(&vec![])
                    .iter()
                    .any(|t| t.label == *a)
            })
        });
    }

    pub fn create_trash_state(&self, alphabet: &BTreeSet<A>) -> BaseAutomaton<A> {
        if self.is_total(alphabet) {
            return self.clone();
        }
        let new_state = new_state();
        let mut new_transitions: Vec<Transition<A>> = vec![];
        let emp_vec: Vec<Transition<A>> = vec![];
        for state in self.states.iter() {
            for ch in alphabet.iter() {
                let t = self
                    .transition
                    .get(state)
                    .unwrap_or(&emp_vec)
                    .iter()
                    .find(|t| t.label == *ch);
                match t {
                    Some(t) => new_transitions.push(t.clone()),
                    None => new_transitions.push(Transition {
                        from: state.clone(),
                        to: new_state.clone(),
                        label: ch.clone(),
                    }),
                };
            }
        }
        for ch in alphabet.iter() {
            new_transitions.push(Transition {
                from: new_state.clone(),
                to: new_state.clone(),
                label: ch.clone(),
            });
        }
        return BaseAutomaton::init(new_transitions, self.accept.clone(), self.start.clone());
    }

    pub fn determinize(&self) -> BaseAutomaton<A> {
        if self.is_deterministic() {
            return self.clone();
        }
        let trans_with_a: HashMap<&String, HashMap<A, BTreeSet<String>>> = self.transition_with_a();
        let mut states_map: HashMap<BTreeSet<State>, State> = HashMap::new();
        let mut queue: VecDeque<BTreeSet<State>> = VecDeque::new();
        let mut transition_map: HashMap<State, HashMap<A, State>> = HashMap::new();
        let mut new_accept: BTreeSet<State> = BTreeSet::new();

        let start_set: BTreeSet<String> = trans_with_a
            .get(&self.start)
            .unwrap_or(&HashMap::new())
            .get(&A::eps())
            .unwrap_or(&BTreeSet::new())
            .clone()
            .into_iter()
            .collect();
        let new_start = new_state();
        states_map.insert(start_set.clone(), new_start.clone());
        queue.push_back(start_set.clone());

        while let Some(cur) = queue.pop_front() {
            let cur_name = states_map.get(&cur).unwrap().clone();

            let mut next_map: HashMap<A, BTreeSet<State>> = cur
                .iter()
                .flat_map(|s| trans_with_a.get(s).unwrap().clone())
                .fold(HashMap::new(), |mut acc, (a, tos)| {
                    acc.entry(a.clone()).or_insert(BTreeSet::new()).extend(tos);
                    acc
                });
            next_map.remove(&A::eps());

            if cur.iter().any(|s| self.accept.contains(s)) {
                new_accept.insert(cur_name.clone());
            }

            for (a, tos) in next_map.iter_mut() {
                if tos.len() == 0 {
                    continue;
                }
                let tos_state = new_state();
                if !states_map.contains_key(&tos) {
                    queue.push_back(tos.clone());
                    states_map.insert(tos.clone(), tos_state);
                };
                if !transition_map.contains_key(&cur_name) {
                    transition_map.insert(cur_name.clone(), HashMap::new());
                }
                transition_map
                    .get_mut(&cur_name)
                    .unwrap()
                    .insert(a.clone(), states_map.get(tos).unwrap().clone());
            }
        }

        let ret = BaseAutomaton::init(
            transition_map
                .into_iter()
                .flat_map(|(from, tos)| {
                    tos.iter()
                        .map(|(a, to)| Transition {
                            from: from.clone(),
                            to: to.clone(),
                            label: a.clone(),
                        })
                        .collect_vec()
                })
                .collect(),
            new_accept,
            new_start,
        );

        assert!(ret.is_deterministic());
        ret
    }
}

pub type DFA<A> = BaseAutomaton<A>;

impl<A, B> HasEps for (Option<A>, Option<B>)
where
    A: Eq + std::hash::Hash + Clone + Ord,
    B: Eq + std::hash::Hash + Clone + Ord,
{
    fn eps() -> (Option<A>, Option<B>) {
        (None, None)
    }
}

pub type Transducer<A, B> = BaseAutomaton<(Option<A>, Option<B>)>;

impl<A, B> Transducer<A, B>
where
    A: Eq + std::hash::Hash + Clone + std::fmt::Debug + Ord,
    B: Eq + std::hash::Hash + Clone + std::fmt::Debug + Ord,
{
    pub fn inverse(&self) -> Transducer<B, A> {
        let new_transitions: Vec<Transition<(Option<B>, Option<A>)>> = self
            .transition
            .iter()
            .flat_map(|(_, transitions)| {
                transitions
                    .iter()
                    .map(|t| Transition {
                        to: t.to.clone(),
                        from: t.from.clone(),
                        label: (t.label.1.clone(), t.label.0.clone()),
                    })
                    .collect::<Vec<_>>()
            })
            .collect_vec();
        Transducer::init(new_transitions, self.accept.clone(), self.start.clone())
    }

    pub fn get_output_nfa(&self) -> NFA<B> {
        self.map_labels(|(_, b)| b.clone())
    }

    pub fn get_input_nfa(&self) -> NFA<A> {
        self.map_labels(|(a, _)| a.clone())
    }

    pub fn intersection_input(&self, nfa: &NFA<A>) -> Transducer<A, B> {
        self.product_by::<Option<A>, (Option<A>, Option<B>)>(nfa, |a, b| {
            if a.0 == *b {
                Some(a.clone())
            } else {
                None
            }
        })
    }
    pub fn compose<C: Eq + std::hash::Hash + Clone + std::fmt::Debug + HasEps + Ord>(
        &self,
        other: &Transducer<B, C>,
    ) -> Transducer<A, C> {
        self.product_by(other, |a, b| {
            if a.1 == b.0 {
                Some((a.0.clone(), b.1.clone()))
            } else {
                None
            }
        })
    }

    pub fn parallel<C: Eq + std::hash::Hash + Clone + std::fmt::Debug + HasEps + Ord>(
        &self,
        other: &Transducer<A, C>,
    ) -> Transducer<A, (Option<B>, Option<C>)> {
        self.product_by(other, |a, b| {
            if a.0 == b.0 {
                if a.1 == None && b.1 == None {
                    Some((a.0.clone(), None))
                } else {
                    Some((a.0.clone(), Some((a.1.clone(), b.1.clone()))))
                }
            } else {
                None
            }
        })
    }
}

impl<A> HasEps for Option<A>
where
    A: Eq + std::hash::Hash + Clone + Ord,
{
    fn eps() -> Option<A> {
        None
    }
}

pub type NFA<A> = BaseAutomaton<Option<A>>;

#[test]
fn test_from_regex() {
    let regex = AppRegex::parse("a(b|c)*d");
    println!("{:?}", regex);
    let nfa = NFA::from_regex(&regex);
    nfa.show_dot("test_from_regex");
    println!("{:?}", nfa);
    assert!(nfa.accept(&vec!['a', 'd']));
    assert!(nfa.accept(&vec!['a', 'b', 'd']));
    assert!(nfa.accept(&vec!['a', 'c', 'd']));
    assert!(nfa.accept(&vec!['a', 'b', 'b', 'd']));
    assert!(nfa.accept(&vec!['a', 'c', 'c', 'd']));
    assert!(nfa.accept(&vec!['a', 'b', 'b', 'b', 'd']));
    assert!(nfa.accept(&vec!['a', 'c', 'c', 'c', 'd']));
    assert!(nfa.accept(&vec!['a', 'b', 'c', 'd']));
    assert!(nfa.accept(&vec!['a', 'c', 'b', 'd']));
    assert!(nfa.accept(&vec!['a', 'b', 'b', 'c', 'd']));
    assert!(nfa.accept(&vec!['a', 'c', 'c', 'b', 'd']));
    assert!(!nfa.accept(&vec!['a', 'b', 'b', 'd', 'b', 'd']));
}
#[test]
fn test_from_regex2() {
    let r = NFA::from_regex(&AppRegex::parse("111(111)*")).reduce_size();
    r.show_dot("test_from_regex2");

    assert!(!r.accept(&vec![]));
    assert!(r.accept(&vec!['1', '1', '1']));
    assert!(r.accept(&vec!['1', '1', '1', '1', '1', '1']));
    assert!(r.accept(&vec!['1', '1', '1', '1', '1', '1', '1', '1', '1']));
}
#[test]
fn test_from_constant() {
    let nfa = NFA::from_constant("abc");
    println!("{:?}", nfa);
    assert!(nfa.accept(&vec!['a', 'b', 'c']));
    assert!(!nfa.accept(&vec!['a', 'b', 'c', 'd']));
    assert!(!nfa.accept(&vec!['a', 'b']));
    assert!(!nfa.accept(&vec!['a', 'b', 'c', 'd']));
}

#[test]
fn test_left_quotient() {
    let nfa = NFA::from_constant("abcded");
    let left_quotient = nfa.left_quotient(&vec![Some('a')]);
    println!("{:?}", left_quotient);
    assert!(left_quotient.accept(&vec!['b', 'c', 'd', 'e', 'd']));
    let left_quotient2 = left_quotient.left_quotient(&vec![]);
    assert!(left_quotient.is_equal(&left_quotient2));

    let left_quotient3 = left_quotient2.left_quotient(&vec![Some('b'), Some('c')]);
    assert!(left_quotient3.accept(&vec!['d', 'e', 'd']));
    assert!(!left_quotient3.accept(&vec!['b', 'c', 'd', 'e', 'd']));
}
#[test]
fn test_left_quotient2() {
    let nfa = NFA::from_constant("00");
    let nfa = nfa.append_vec(&vec![Some('1')]);
    assert!(nfa.accept(&vec!['0', '0', '1']));
    let nfa = nfa.left_quotient(&vec![Some('0')]);
    assert!(nfa.accept(&vec!['0', '1']));
    let nfa = nfa.left_quotient(&vec![Some('0')]);
    assert!(nfa.accept(&vec!['1']));
}

impl NFA<char> {
    pub fn from_constant(s: &str) -> NFA<char> {
        let start = new_state();
        let mut cur = start.clone();
        let mut transitions: Vec<Transition<Option<char>>> = vec![];
        for c in s.chars() {
            let next = new_state();
            transitions.push(Transition {
                from: cur.clone(),
                to: next.clone(),
                label: Some(c),
            });
            cur = next;
        }
        NFA::init(transitions, vec![cur.clone()].into_iter().collect(), start)
    }
    pub fn from_constants(ss: &Vec<&str>) -> NFA<char> {
        let start = new_state();
        let mut transitions: Vec<Transition<Option<char>>> = vec![];
        let mut accepting = BTreeSet::new();
        let mut state_map: HashMap<String, State> = HashMap::new();
        state_map.insert("".to_string(), start.clone());

        for s in ss.iter() {
            let mut cur = "".to_string();
            for c in s.chars() {
                let next = cur.clone() + &c.to_string();
                if !state_map.contains_key(&next) {
                    state_map.insert(next.clone(), new_state());
                }
                transitions.push(Transition {
                    from: state_map.get(&cur).unwrap().clone(),
                    to: state_map.get(&next).unwrap().clone(),
                    label: Some(c),
                });
                cur = next;
            }
            accepting.insert(state_map.get(&cur).unwrap().clone());
        }
        NFA::init(transitions, accepting, start).reduce_size()
    }
    pub fn get_arbitary_nfa(chars: &Vec<char>) -> NFA<char> {
        let start = new_state();

        NFA::init(
            chars
                .iter()
                .map(|c| Transition {
                    from: start.clone(),
                    to: start.clone(),
                    label: Some(c.clone()),
                })
                .collect(),
            vec![start.clone()].into_iter().collect(),
            start,
        )
    }
    pub fn from_regex(regex: &AppRegex) -> NFA<char> {
        match regex {
            AppRegex::Star(regex) => {
                let mut nfa: NFA<char> = NFA::from_regex(regex);
                let new_accept = new_state();
                nfa.accept.clone().iter().for_each(|state| {
                    nfa.add_transition(Transition {
                        from: state.clone(),
                        to: new_accept.clone(),
                        label: None,
                    });
                });
                nfa.add_transition(Transition {
                    from: nfa.start.clone(),
                    to: new_accept.clone(),
                    label: None,
                });
                nfa.add_transition(Transition {
                    from: new_accept.clone(),
                    to: nfa.start.clone(),
                    label: None,
                });
                nfa.accept = vec![new_accept].into_iter().collect();
                nfa
            }
            AppRegex::Or(left, right) => {
                let left_nfa = NFA::from_regex(left);
                let right_nfa = NFA::from_regex(right);
                left_nfa.union(&right_nfa, true)
            }
            AppRegex::Concat(left, right) => {
                let left_nfa = NFA::from_regex(left);
                let right_nfa = NFA::from_regex(right);
                left_nfa.concat(&right_nfa)
            }
            AppRegex::Ch(c) => {
                let start = new_state();
                let accept: BTreeSet<State> = vec![new_state()].into_iter().collect();
                NFA::init(
                    vec![Transition {
                        from: start.clone(),
                        to: accept.iter().next().unwrap().clone(),
                        label: Some(c.clone()),
                    }],
                    accept,
                    start,
                )
            }
            AppRegex::Eps => {
                let start = new_state();
                NFA::init(vec![], vec![start.clone()].into_iter().collect(), start)
            }
            AppRegex::Nothing => {
                let start = new_state();
                NFA::init(vec![], BTreeSet::new(), start)
            }
        }
    }
}

impl<A> NFA<A>
where
    A: Eq + std::hash::Hash + Clone + std::fmt::Debug + Ord,
{
    pub fn new_total(alphabet: &BTreeSet<A>) -> NFA<A> {
        let start = new_state();
        BaseAutomaton::init(
            alphabet
                .iter()
                .map(|a| Transition {
                    from: start.clone(),
                    to: start.clone(),
                    label: Some(a.clone()),
                })
                .collect_vec(),
            vec![start.clone()].into_iter().collect(),
            start,
        )
    }

    fn accept_from_state<'a>(
        &'a self,
        s: Vec<&A>,
        state: &'a State,
        visited: &mut BTreeSet<(usize, &'a State)>,
    ) -> bool {
        if visited.contains(&(s.len(), state)) {
            return false;
        }
        if s.len() == 0 && self.accept.contains(state) {
            return true;
        }
        visited.insert((s.len(), state));

        if let Some(transition) = self.transition.get(state) {
            for transition in transition {
                if let Some(label) = &transition.label {
                    if s.len() > 0 && s[0] == label {
                        if self.accept_from_state(s[1..].to_vec(), &transition.to, visited) {
                            return true;
                        }
                    }
                } else {
                    if self.accept_from_state(s.clone(), &transition.to, visited) {
                        return true;
                    }
                }
            }
        }
        false
    }
    pub fn accept(&self, s: &Vec<A>) -> bool {
        let mut visited: BTreeSet<(usize, &State)> = BTreeSet::new();
        self.accept_from_state(s.iter().collect(), &self.start, &mut visited)
    }
    pub fn accept_from(&self, s: &Vec<A>, state: &State) -> bool {
        let mut visited: BTreeSet<(usize, &State)> = BTreeSet::new();
        self.accept_from_state(s.iter().collect(), state, &mut visited)
    }

    pub fn get_element(&self) -> Option<Vec<A>> {
        let mut visited: BTreeSet<&State> = BTreeSet::new();

        fn dfs<'a, A>(
            nfa: &'a NFA<A>,
            cur: &'a State,
            visited: &mut BTreeSet<&'a State>,
        ) -> Option<Vec<A>>
        where
            A: Eq + std::hash::Hash + Clone + std::fmt::Debug + Ord,
        {
            if visited.contains(cur) {
                return None;
            }
            visited.insert(cur);
            if nfa.accept.contains(cur) {
                return Some(vec![]);
            }
            if let Some(transition) = nfa.transition.get(cur) {
                for transition in transition {
                    if let Some(s) = dfs(nfa, &transition.to, visited) {
                        if let Some(label) = &transition.label {
                            return Some(
                                vec![label.clone()]
                                    .into_iter()
                                    .chain(s.into_iter())
                                    .collect(),
                            );
                        }
                        return Some(s);
                    }
                }
            }
            None
        }

        dfs(self, &self.start, &mut visited)
    }

    pub fn is_empty(&self) -> bool {
        self.get_element().is_none()
    }

    pub fn remove_eps(&self) -> NFA<A> {
        let mut trans_with_a: HashMap<&String, HashMap<Option<A>, BTreeSet<String>>> =
            self.transition_with_a();
        let mut new_transitions: Vec<Transition<Option<A>>> = vec![];

        for s in self.transition.keys() {
            trans_with_a.get_mut(s).unwrap().remove(&None);
            trans_with_a[s].iter().for_each(|(a, tos)| {
                assert!(a.is_some());
                new_transitions.extend(tos.iter().map(|to| Transition {
                    from: s.clone(),
                    to: to.clone(),
                    label: a.clone(),
                }));
            });
        }

        let ret = NFA::init(new_transitions, self.accept.clone(), self.start.clone());
        assert!(ret.is_eps_free());
        ret
    }

    pub fn is_eps_free(&self) -> bool {
        self.transition
            .values()
            .flatten()
            .all(|t| t.label.is_some())
    }
}

impl BaseAutomaton<Option<char>> {
    
    pub fn _backward_acceptables_for_each_states_s<'a>(
        &self,
        from_state: State,
        s: &'a str,
        pos: usize,
        ret: &mut HashMap<State, BTreeSet<&'a str>>,
        visited: &mut BTreeSet<(State, usize)>,
    ) {
        visited.insert((from_state.clone(), pos));
        ret.entry(from_state.clone())
            .or_insert(BTreeSet::new())
            .insert(&s[..pos]);

        for t in self.transition.get(&from_state).unwrap_or(&vec![]) {
            if let Some(ch) = t.label {
                if s.len() > pos && s.as_bytes()[pos] == ch as u8 {
                    if !visited.contains(&(t.to.clone(), pos + 1)) {
                        self._backward_acceptables_for_each_states_s(
                            t.to.clone(),
                            s,
                            pos + 1,
                            ret,
                            visited,
                        );
                    }
                }
            } else {
                if !visited.contains(&(t.to.clone(), pos)) {
                    self._backward_acceptables_for_each_states_s(
                        t.to.clone(),
                        s,
                        pos,
                        ret,
                        visited,
                    );
                }
            }
        }
    }
    pub fn backward_acceptables_for_each_states_ss<'a>(
        &self,
        from_state: State,
        strings: Vec<&'a str>,
    ) -> HashMap<State, BTreeSet<&'a str>> {
        let mut ret: HashMap<State, BTreeSet<&'a str>> = HashMap::new();
        for s in strings {
            let mut visited: BTreeSet<(State, usize)> = BTreeSet::new();
            self._backward_acceptables_for_each_states_s(from_state.clone(), s, 0, &mut ret, &mut visited);
        }
        ret
    }
    pub fn residuals_for_each_states<'a>(
        &self,
        from_state: State,
        strings: Vec<&'a str>,
    ) -> HashMap<State, BTreeSet<&'a str>> {
        let mut ret: HashMap<State, BTreeSet<&'a str>> = HashMap::new();
        let mut q = vec![];
        for s in strings.into_iter() {
            q.push((from_state.clone(), s));
        }
        while let Some((state, s)) = q.pop() {
            if ret.get(&state).unwrap_or(&BTreeSet::new()).contains(&s) {
                continue;
            }
            ret.entry(state.clone())
                .or_insert(BTreeSet::new())
                .insert(s);

            for adj in self.transition.get(&state).unwrap_or(&vec![]) {
                if let Some(ch) = adj.label {
                    if s.len() > 0 && ch == s.chars().next().unwrap() {
                        q.push((adj.to.clone(), &s[1..]));
                    }
                }
                if adj.label.is_none() {
                    q.push((adj.to.clone(), s));
                }
            }
        }
        ret
    }
    pub fn backward_length_bounded_lang(&self, l: usize) -> HashMap<State, BTreeSet<String>> {
        let mut ret: HashMap<State, BTreeSet<String>> = HashMap::new();
        let mut q: Vec<(State, String)> = vec![];
        q.push((self.start.clone(), "".to_string()));
        ret.entry(self.start.clone())
            .or_insert(BTreeSet::new())
            .insert("".to_string());

        while let Some((cur_state, s)) = q.pop() {
            for adj in self.transition.get(&cur_state).unwrap_or(&vec![]) {
                let next: (String, String) = if let Some(ch) = adj.label {
                    (adj.to.clone(), s.clone() + &ch.to_string())
                } else {
                    (adj.to.clone(), s.clone())
                };
                if next.1.len() <= l {
                    if ret
                        .get(&next.0)
                        .unwrap_or(&BTreeSet::new())
                        .contains(&next.1)
                    {
                        continue;
                    }
                    ret.entry(next.0.clone())
                        .or_insert(BTreeSet::new())
                        .insert(next.1.clone());
                    q.push(next);
                }
            }
        }
        ret
    }
    pub fn forward_length_bounded_lang(&self, l: usize) -> HashMap<State, BTreeSet<String>> {
        self.reversed()
            .backward_length_bounded_lang(l)
            .into_iter()
            .map(|(s, ss)| {
                (
                    s,
                    ss.into_iter()
                        .map(|s| s.chars().rev().collect::<String>())
                        .collect::<BTreeSet<String>>(),
                )
            })
            .collect()
    }
    pub fn quotient_aut<V: Eq + Hash>(
        &self,
        identifiers: HashMap<State, V>,
    ) -> BaseAutomaton<Option<char>> {
        let mut new_states: HashMap<Option<&V>, State> = HashMap::new();
        for (_, ids) in identifiers.iter() {
            new_states.insert(Some(&ids), new_state());
        }
        new_states.insert(None, new_state());

        let new_transitions: Vec<Transition<Option<char>>> = self
            .transition
            .iter()
            .flat_map(|(from, ts)| {
                ts.iter()
                    .map(|t| Transition {
                        from: new_states.get(&identifiers.get(from)).unwrap().clone(),
                        to: new_states.get(&identifiers.get(&t.to)).unwrap().clone(),
                        label: t.label.clone(),
                    })
                    .collect_vec()
            })
            .collect_vec();

        let new_start = new_states
            .get(&identifiers.get(&self.start))
            .unwrap()
            .clone();
        let new_accept: BTreeSet<State> = self
            .accept
            .iter()
            .map(|s| new_states.get(&identifiers.get(s)).unwrap().clone())
            .collect();
        BaseAutomaton::init(new_transitions, new_accept, new_start)
    }
}

#[test]
fn test_diff() {
    let nfa1 = NFA::from_constant("abc");
    let nfa2 = NFA::from_constant("ddd").union(&NFA::from_constant("abc"), true);

    assert!(nfa1.find_difference(&nfa2).is_none());
    assert!(nfa2.find_difference(&nfa1) == Some("ddd".chars().map(|c| Some(c)).collect_vec()));
}
