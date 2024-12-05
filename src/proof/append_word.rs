use std::rc::Rc;

use itertools::Itertools;

use crate::automaton::NFA;

use super::{isabelle_files::IsabelleThyMeta, nfa_def::IAutomataDef, Organizer};

pub struct AppendWordAutomataDef {
    pub src: Rc<dyn IAutomataDef>,
    pub w: String,
    pub aut: NFA<char>,
    pub aut_expr: String,
}

impl AppendWordAutomataDef {
    pub fn new(organizer: &dyn Organizer, src: Rc<dyn IAutomataDef>, w: String) -> AppendWordAutomataDef {
        
        AppendWordAutomataDef {
            aut: src.get_app_aut().append_vec(&w.chars().into_iter().map(|c| Some(c)).collect_vec()),
            aut_expr: format!(
                "(append_word {} {})",
                src.get_automaton(),
                organizer.get_config().map_string_to_list(&w),
            ),
            src,
            w,
        }
    }
}

impl IAutomataDef for AppendWordAutomataDef {
    fn get_id(&self) -> String {
        format!("append_{}_{}", self.src.get_id(), self.w)
    }

    fn get_needed_theories(&self) -> Vec<IsabelleThyMeta> {
        self.src.get_needed_theories()
    }

    fn get_automaton(&self) -> String {
        self.aut_expr.clone()
    }

    fn get_state_type(&self) -> String {
        format!("(AppendWordState {})", self.src.get_state_type())
    }

    fn get_app_aut(&self) -> &crate::automaton::NFA<char> {
        &self.aut
    }

    fn get_aut_unfolding_method(&self) -> String {
        self.src.get_aut_unfolding_method()
    }

    fn get_transition_proceed_method(&self) -> String {
        self.src.get_transition_proceed_method()
    }

    fn get_state_map(&self) -> &std::collections::BTreeMap<crate::automaton::State, String> {
        todo!()
    }
}
