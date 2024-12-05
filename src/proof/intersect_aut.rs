use std::{
    collections::BTreeMap,
    rc::Rc,
};

use itertools::Itertools;

use crate::automaton::{BaseAutomaton, Transition, NFA};

use super::{aut_def::IAutomataDef, isabelle_files::IsabelleThyMeta, organizer::Organizer};

pub struct NaiveIntersect {
    pub aut1: Rc<dyn IAutomataDef>,
    pub aut2: Rc<dyn IAutomataDef>,

    pub state_map: BTreeMap<String, String>,
    pub aut: NFA<char>,
}

impl NaiveIntersect {
    pub fn new(
        organizer: &mut dyn Organizer,
        aut1: Rc<dyn IAutomataDef>,
        aut2: Rc<dyn IAutomataDef>,
    ) -> NaiveIntersect {
        let mut new_transitions = Vec::new();
        let mut state_map: BTreeMap<String, String> = BTreeMap::new();
        let config = &organizer.get_config();

        for s1 in aut1.get_app_aut().states.iter() {
            for s2 in aut2.get_app_aut().states.iter() {
                state_map.insert(
                    format!("({},{})", s1, s2),
                    format!(
                        "({}, {})",
                        aut1.get_state_map().get(s1).unwrap(),
                        aut2.get_state_map().get(s2).unwrap()
                    ),
                );
                for c in config.get_alphabet().iter() {
                    let t1 = aut1.get_app_aut().get_next_state(s1.clone(), *c);
                    let t2 = aut2.get_app_aut().get_next_state(s2.clone(), *c);

                    new_transitions.push(Transition {
                        from: format!("({},{})", s1, s2),
                        to: format!("({},{})", t1, t2),
                        label: Some(*c),
                    });
                }
            }
        }

        let aut = BaseAutomaton::init(
                new_transitions,
                aut1.get_app_aut()
                    .accept
                    .iter()
                    .cartesian_product(aut2.get_app_aut().accept.iter())
                    .map(|(a, b)| format!("({}, {})", a, b))
                    .collect(),
                format!("({},{})", aut1.get_app_aut().start, aut2.get_app_aut().start),
            );

        NaiveIntersect {
            aut1,
            aut2,
            state_map,
            aut,
        
        }
    }
}

impl IAutomataDef for NaiveIntersect {
    fn get_id(&self) -> String {
        format!("intersect_{}_{}", self.aut1.get_id(), self.aut2.get_id())
    }
    
    fn get_needed_theories(&self) -> Vec<IsabelleThyMeta> {
        self.aut1.get_needed_theories().into_iter().chain(self.aut2.get_needed_theories().into_iter()).collect_vec()
    }
    
    fn get_automaton(&self) -> String {
        format!("(intersect {} {})", self.aut1.get_automaton(), self.aut2.get_automaton())
    }
    
    fn get_state_type(&self) -> String {
        format!("({}\\<times>{})", self.aut1.get_state_type(), self.aut2.get_state_type())
    }

    fn get_app_aut(&self) -> &NFA<char> {
        &self.aut
    }

    fn get_aut_unfolding_method(&self) -> String {
        format!("(simp only: intersect_def, {}, {})", self.aut1.get_aut_unfolding_method(), self.aut2.get_aut_unfolding_method())
    }

    fn get_univ_unfolding_method(&self) -> String {
        format!("({}, {})", self.aut1.get_univ_unfolding_method(), self.aut2.get_univ_unfolding_method())
    }
    fn get_transition_proceed_method(&self) -> String {
        format!("({}, {})", self.aut1.get_transition_proceed_method(), self.aut2.get_transition_proceed_method())
    }

    fn get_state_split_lemma(&self) -> String {
        todo!()
    }

    fn get_state_map(&self) -> &BTreeMap<crate::automaton::State, String> {
        &self.state_map
    }
}

// pub struct IntersectAutsOps {
//     pub theory_name: String,

//     pub aut1: Rc<dyn IAutomataDef>,
//     pub aut2: Rc<dyn IAutomataDef>,

//     pub dest: Rc<dyn IAutomataDef>,
// }

// fn gen_intersect_transition_fun(
//     config: &ProverConfig,
//     aut1: Rc<dyn IAutomataDef>,
//     aut2: Rc<dyn IAutomataDef>,
//     fun_name: String,
// ) -> String {
//     let mut rows: Vec<String> = Vec::new();
//     aut1.get_app_aut().transition.values().flatten().for_each(|t1| {
//         aut2.get_app_aut()
//             .transition
//             .values()
//             .flatten()
//             .filter(|t2| t2.label == t1.label)
//             .for_each(|t2| {
//                 rows.push(format!(
//                     "((({}), ({})), ({})) => ({}, {})",
//                     aut1.get_state_map().get(&t1.from).unwrap(),
//                     aut2.get_state_map().get(&t2.from).unwrap(),
//                     config.alphabet_map.get(&t1.label.unwrap()).unwrap(),
//                     aut1.get_state_map().get(&t1.to).unwrap(),
//                     aut2.get_state_map().get(&t2.to).unwrap(),
//                 ))
//             })
//     });

//     let new_state_type = format!(
//         "({}\\<times>{})",
//         aut1.get_state_type(), aut2.get_state_type()
//     );
//     format!(
//         "abbreviation {}::\"{} \\<Rightarrow> alphabet \\<Rightarrow> {}\" where \n
//         \"{} s c \\<equiv> case (s, c) of\n
//         {}\"",
//         fun_name,
//         new_state_type,
//         new_state_type,
//         fun_name,
//         rows.join("|\n").as_str(),
//     )
// }

// impl IntersectAutsOps {
//     pub fn new(
//         organizer: &mut dyn Organizer,
//         aut1: Rc<dyn IAutomataDef>,
//         aut2: Rc<dyn IAutomataDef>,
//     ) -> IntersectAutsOps {
//         let config = &organizer.get_config();
//         let theory_name = format!("intersect_{}_{}", aut1.get_id(), aut2.get_id());
//         let mut theory = organizer.get_theory(&theory_name).clone();
//         let dest_aut_name = theory_name.clone();

//         let naive_intersect = NaiveIntersect::new(organizer, aut1.clone(), aut2.clone());

//         // let state_split_content = intersect_def.state_map.values()
//         //     .map(|v| format!("\"s = {}\"", v))
//         //     .join(" |\n");

//         // let handlebars = get_handlebars();
//         // let transition_fun_name = format!("transition");
//         // let res = handlebars.render("intersect", &json!({
//         //     "theory_name": theory_name.clone(),
//         //     "transition_fun_def": gen_intersect_transition_fun(&organizer.get_config(), &aut1, &aut2, transition_fun_name.clone()),
//         //     "transition_fun_name": transition_fun_name,
//         //     "aut1_path": get_relative_path(&config.gen_directory, &aut1.theory_path),
//         //     "aut1_name": aut1.automaton_name.clone(),
//         //     "aut2_path": get_relative_path(&config.gen_directory, &aut2.theory_path),
//         //     "aut2_name": aut2.automaton_name.clone(),
//         //     "dest_aut_path": get_relative_path(&config.gen_directory, &intersect_def.theory_path),
//         //     "dest_aut_name": intersect_def.theory_name.clone(),
//         //     "state_split_lemma_name": intersect_def.state_split_lemma.clone(),
//         //     "state_split_content": state_split_content,
//         //     "all_states": intersect_def.state_map.values().join(", "),
//         // })).unwrap();

//         // std::fs::create_dir_all(&config.gen_directory).unwrap();
//         // std::fs::write(&filepath, res).unwrap();

//         // IntersectAutsOps {
//         //     theory_name: theory_name.clone(),
//         //     theory_path,
//         //     aut1,
//         //     aut2,
//         //     dest: intersect_def,
//         // }
//     }
// }

// #[cfg(test)]
// mod tests {
//     use crate::{
//         automaton::{AppRegex, NFA},
//         proof::organizer_impl::OrganizerImpl,
//     };

//     use super::*;
//     #[test]
//     fn test_prover() {
//         let mut organizer = OrganizerImpl::default();

//         let a = NFA::from_regex(&AppRegex::parse("1000"));
//         let a_def = organizer.define_aut(a);

//         let ch = '1';

//         organizer.append_ch(a_def, ch);
//     }
// }
