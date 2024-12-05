use std::rc::Rc;

use itertools::Itertools;

use crate::automaton::BaseAutomaton;

use super::{
    isabelle_files::IsabelleThyMeta, nfa_def::IAutomataDef, organizer::Organizer
};

// fn simulate_pref_quotient(
//     aut: &BaseAutomaton<Option<char>>,
//     s: &str,
// ) -> BaseAutomaton<Option<char>> {
//     let mut cur = aut.start.clone();
//     for c in s.chars() {
//         let next = (&aut).get_next_state(cur, c);
//         cur = next;
//     }
//     let mut ret = aut.clone();
//     ret.start = cur;
//     return ret;
// }

pub struct PrefQuotientAutomatDef {
    pub src: Rc<dyn IAutomataDef>,
    pub aut: BaseAutomaton<Option<char>>,
    pub aut_expr: String,
    pub s: String,
}

impl PrefQuotientAutomatDef {
    pub fn new(organizer: &dyn Organizer, aut: Rc<dyn IAutomataDef>, s: &str) -> PrefQuotientAutomatDef {
        // let q_aut = simulate_pref_quotient(&aut.get_app_aut(), s);

        PrefQuotientAutomatDef {
            src: aut.clone(),
            aut: aut.get_app_aut().left_quotient(&s.chars().into_iter().map(|c| Some(c)).collect_vec()),
            aut_expr: format!(
                "(pref_quotient {} {})",
                aut.get_automaton(),
                organizer.get_config().map_string_to_list(s)
            ),
            s: s.to_string(),
        }
    }
}

impl IAutomataDef for PrefQuotientAutomatDef {
    fn get_id(&self) -> String {
        format!("{}_pref_quotient_{}", self.src.get_id(), self.s)
    }

    fn get_needed_theories(&self) -> Vec<IsabelleThyMeta> {
        self.src.get_needed_theories()
    }

    fn get_automaton(&self) -> String {
        self.aut_expr.clone()
    }

    fn get_state_type(&self) -> String {
        self.src.get_state_type()
    }

    fn get_app_aut(&self) -> &crate::automaton::NFA<char> {
        &self.aut
    }

    fn get_aut_unfolding_method(&self) -> String {
        format!(
            "({}, {})",
            self.src.get_aut_unfolding_method(),
            self.src.get_transition_proceed_method()
        )
    }

    fn get_transition_proceed_method(&self) -> String {
        self.src.get_transition_proceed_method()
    }

    fn get_state_map(&self) -> &std::collections::BTreeMap<crate::automaton::State, String> {
        self.src.get_state_map()
    }
}
