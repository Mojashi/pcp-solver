use std::collections::{HashMap, HashSet};
use std::io::Write;
use handlebars::Handlebars;
use crate::{
    automaton::{BaseAutomaton, State, NFA},
    pcp::PCP,
};
use crate::proof::prover_config::ProverConfig;

fn enumerate_reachable_intersection(
    a1: &BaseAutomaton<Option<char>>,
    a2: &BaseAutomaton<Option<char>>,
) -> Vec<(State, State)> {
    let mut queue: Vec<(String, String)> = vec![((a1.start.clone(), a2.start.clone()))];
    let mut visited: HashSet<(String, String)> = HashSet::new();
    let mut ret = vec![];

    let labels: Vec<Option<char>> = a1.labels().union(&a2.labels()).cloned().collect();

    while !queue.is_empty() {
        let (s1, s2) = queue.pop().unwrap();
        if visited.contains(&(s1.clone(), s2.clone())) {
            continue;
        }
        visited.insert((s1.clone(), s2.clone()));

        let t1 = a1.transition.get(&State::from(&s1)).unwrap();
        let t2 = a2.transition.get(&State::from(&s2)).unwrap();

        for l in labels.iter() {
            let next1 = t1.iter().find(|t| t.label == *l).map(|t| t.to.clone());
            let next2 = t2.iter().find(|t| t.label == *l).map(|t| t.to.clone());

            if next1.is_some() && next2.is_some() {
                let next1 = next1.unwrap();
                let next2 = next2.unwrap();
                queue.push((next1.to_string(), next2.to_string()));
                ret.push((next1, next2));
            }
        }
    }

    return visited
        .iter()
        .map(|(s1, s2)| (State::from(s1), State::from(s2)))
        .collect();
}
struct Prover {
    base_directory: String,
    aut_map: HashMap<String, BaseAutomaton<Option<char>>>,
    config: ProverConfig,
    handlebars: Handlebars<'static>,
}

impl Prover {
    fn new(base_directory: String, config: ProverConfig) -> Self {
        // create dir
        std::fs::create_dir_all(&base_directory).unwrap();
        let contains_template_file = "proof/templates/contains.thy";
        let mut handlebars = Handlebars::new();
        handlebars.register_template_file("contains", contains_template_file).unwrap();
        
        Prover {
            base_directory,
            aut_map: HashMap::new(),
            config,
            handlebars,
        }
    }



    fn show_contains(&self, a_name: &str, b_name: &str) {
        let aut_a = self.aut_map.get(a_name).unwrap();
        let aut_b = self.aut_map.get(b_name).unwrap();

        assert!(aut_a.includes(aut_b));

        let theory_name = format!("{}_contains_{}", a_name, b_name);
        let file: String = theory_name.clone() + ".thy";
        let fp = std::fs::File::create(file).unwrap();
        let mut writer = std::io::BufWriter::new(fp);
        
        let mut data = HashMap::new();
        data.insert("theory_name", theory_name);
        data.insert("aut_a", a_name.to_string());
        data.insert("aut_b", b_name.to_string());
        let result = self.handlebars.render("contains", &data).unwrap();

        writeln!(writer, "{}", result).unwrap();
    }
    fn prove_closed(&self, i: &Vec<NFA<char>>, pcp: &PCP) {
        todo!()
    }
}


#[cfg(test)]
mod tests {
    use crate::automaton::Transition;

    use super::*;

    #[test]
    fn test_prover() {
        let mut a = BaseAutomaton::new();
        a.add_transition(Transition {
            from: State::from("q0"),
            to: State::from("q1"),
            label: Some('0'),
        });
        a.add_transition(Transition {
            from: State::from("q1"),
            to: State::from("q0"),
            label: Some('1'),
        });
        a.add_transition(Transition {
            from: State::from("q1"),
            to: State::from("q0"),
            label: Some('0'),
        });
        a.add_transition(Transition {
            from: State::from("q0"),
            to: State::from("q0"),
            label: Some('1'),
        });
        a.start = State::from("q0");
        a.states = vec![State::from("q0"), State::from("q1")]
            .into_iter()
            .collect();
        a.accept = vec![State::from("q1")].into_iter().collect();

        let mut b = BaseAutomaton::new();
        b.add_transition(Transition {
            from: State::from("q0"),
            to: State::from("q1"),
            label: Some('0'),
        });
        b.add_transition(Transition {
            from: State::from("q1"),
            to: State::from("q0"),
            label: Some('1'),
        });
        b.add_transition(Transition {
            from: State::from("q1"),
            to: State::from("q0"),
            label: Some('0'),
        });
        b.add_transition(Transition {
            from: State::from("q0"),
            to: State::from("q0"),
            label: Some('1'),
        });
        b.start = State::from("q0");
        b.states = vec![State::from("q0"), State::from("q1")]
            .into_iter()
            .collect();
        b.accept = vec![State::from("q1")].into_iter().collect();

        println!("{:?}", enumerate_reachable_intersection(&a, &b));

        let mut p = Prover::new("proof".to_string(), ProverConfig::default());
    }
}
