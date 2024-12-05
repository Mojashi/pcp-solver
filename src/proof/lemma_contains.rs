use super::{isabelle_files::IsabelleThySameSession, nfa_def::IAutomataDef, organizer::Organizer};
use crate::proof::isabelle_files::IsabelleThyMeta;
use std::rc::Rc;

pub struct ContainsLemma {
    pub meta: IsabelleThySameSession,

    pub aut1: Rc<dyn IAutomataDef>,
    pub aut2: Rc<dyn IAutomataDef>,

    pub lemma_name: String,
}

impl ContainsLemma {
    pub fn new(
        organizer: &mut dyn Organizer,
        aut1: Rc<dyn IAutomataDef>,
        aut2: Rc<dyn IAutomataDef>,
    ) -> ContainsLemma {
        let theory_name = format!("{}_contains_{}", aut1.get_id(), aut2.get_id());
        let mut theory = organizer.get_theory(&theory_name).clone();

        assert!(aut1.get_app_aut().includes(&aut2.get_app_aut()));

        theory.add_imports(aut1.get_needed_theories_from(organizer, &theory.dir_path));
        theory.add_imports(aut2.get_needed_theories_from(organizer, &theory.dir_path));

        theory.add_import(&IsabelleThyMeta::new_another_sess_thy("PCPLib", "NFA"));
        theory.add_import(&IsabelleThyMeta::new_another_sess_thy(
            "PCPLib",
            "NFAPCPUtil",
        ));

        let a_state = aut1.get_state_type();
        let b_state = aut2.get_state_type();
        theory.break_line();

        let a_proceed = aut1.get_transition_proceed_method();
        let b_proceed = aut2.get_transition_proceed_method();

        theory.add_content(
            "declare step_rel.simps [simp del]\n\
            declare exists_diff_rel.simps [simp del]\n\
            declare inv_cond.simps [simp del]",
        );

        theory.break_line();

        let a_aut = aut1.get_automaton();
        let b_aut = aut2.get_automaton();
        let a_aut_unfold = aut1.get_aut_unfolding_method();
        let b_aut_unfold = aut2.get_aut_unfolding_method();
        theory.add_content(&format!(
            "lemma no_counterexample:
  shows \"inv_cond 
    {b_aut} {a_aut}
    ((init_explore_state {b_aut} {a_aut}), [])
    ==> False\"
    apply({b_aut_unfold}?, {a_aut_unfold}?)
  by(drule_tac accept_from_iff_antichain, simp?)+"
        ));
        theory.break_line();
        theory.add_content(&format!(
            "lemma {theory_name}:
            \"lang {b_aut} \\<subseteq> lang {a_aut}\"\n\
            using inv_cond_init_False_then_contain[OF no_counterexample] by blast"
        ));
        theory.break_line();
        //theory.add_content(&format!("hide_fact no_counterexample"));

        organizer.set_theory(&theory_name, theory.clone());
        ContainsLemma {
            meta: theory.get_meta().clone(),
            aut1,
            aut2,
            lemma_name: format!("{}.{}", theory_name, theory_name),
        }
    }
}
