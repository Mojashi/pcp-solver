use super::{isabelle_files::IsabelleThyMeta, nfa_def::IAutomataDef, organizer::Organizer};
use crate::automaton::BaseAutomaton;
use std::rc::Rc;

pub struct UnionAutsAutomataDef {
    pub aut1: Rc<dyn IAutomataDef>,
    pub aut2: Rc<dyn IAutomataDef>,
    pub aut_expr: String,

    pub aut: BaseAutomaton<Option<char>>,
}

impl UnionAutsAutomataDef {
    pub fn new(
        _: &dyn Organizer,
        aut1: Rc<dyn IAutomataDef>,
        aut2: Rc<dyn IAutomataDef>,
    ) -> UnionAutsAutomataDef {
        UnionAutsAutomataDef {
            aut_expr: format!("(union {} {})", aut1.get_automaton(), aut2.get_automaton(),),
            aut: aut1.get_app_aut().union(&aut2.get_app_aut(), true).clone(),
            aut1,
            aut2,
        }
    }
}

impl IAutomataDef for UnionAutsAutomataDef {
    fn get_id(&self) -> String {
        format!("{}_union_{}", self.aut1.get_id(), self.aut2.get_id())
    }

    fn get_needed_theories(&self) -> Vec<IsabelleThyMeta> {
        self.aut1
            .get_needed_theories()
            .into_iter()
            .chain(self.aut2.get_needed_theories())
            .collect()
    }

    fn get_automaton(&self) -> String {
        self.aut_expr.clone()
    }

    fn get_state_type(&self) -> String {
        format!(
            "(({}, {}) UnionState)",
            self.aut1.get_state_type(),
            self.aut2.get_state_type()
        )
    }

    fn get_app_aut(&self) -> &crate::automaton::NFA<char> {
        &self.aut
    }

    fn get_aut_unfolding_method(&self) -> String {
        format!(
            "({}?, {}?)",
            self.aut1.get_aut_unfolding_method(),
            self.aut2.get_aut_unfolding_method(),
        )
    }

    fn get_transition_proceed_method(&self) -> String {
        format!(
            "({}?, {}?)",
            self.aut1.get_transition_proceed_method(),
            self.aut2.get_transition_proceed_method(),
        )
    }

    fn get_state_map(&self) -> &std::collections::BTreeMap<crate::automaton::State, String> {
        todo!()
    }
}
