use itertools::Itertools;

use super::{
    isabelle_files::{IsabelleThyMeta, IsabelleThySameSession},
    organizer::{Organizer, PCPConfDefDepGraph},
    pcp_instance_def::PCPInstanceDef,
};
use std::rc::Rc;

pub struct InvariantLemma {
    pub meta: IsabelleThySameSession,
    pub theorem: String,
}

impl InvariantLemma {
    pub fn new(
        organizer: &mut dyn Organizer,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> InvariantLemma {
        let theory_name = "invariant".to_string();
        let mut theory = organizer.get_theory(theory_name.as_str()).clone();
        theory.add_import(&IsabelleThyMeta::new_another_sess_thy("PCPLib", "PCPTrans"));
        let closed_lemma = organizer.closed_lemma(instance.clone(), depgraph);
        let accept_init_lemma = organizer.accept_init_lemma(instance.clone(), depgraph);
        theory.add_import(&IsabelleThyMeta::SameSession(closed_lemma.meta.clone()));
        theory.add_import(&IsabelleThyMeta::SameSession(accept_init_lemma.meta.clone()));

        let inv = closed_lemma.inv.clone();
        let aut_unfold_methods = depgraph
            .nodes
            .iter()
            .map(|(idx, n)| format!(
                "((rule not_accept_empty_simp, ({}, simp)?))",
                    n.conf.aut.get_aut_unfolding_method()))
            .collect_vec()
            .join(",\n");
        theory.add_content(&format!(
            "lemma non_empty_up:\n\
            \"(PCPTrans.UP []) \\<notin> {inv}\"\n\
            apply (simp only:{inv}_def) apply(intro notin_union)?
            apply ({aut_unfold_methods})\n\
            done"
        ));
        theory.add_content(&format!(
            "lemma non_empty_dn:\n\
            \"(PCPTrans.DN []) \\<notin> {inv}\"\n\
            apply (simp only:{inv}_def) apply(intro notin_union)?
            apply ({aut_unfold_methods})\n\
            done"
        ));

        theory.add_content(&format!(
            "lemma this_is_invariant: \"is_invariant {instance} {inv}\"\n\
            apply(rule is_invariant_imp[OF _ {closed} non_empty_up non_empty_dn])\n\
            using {accept_init} unfolding {inv}_def by blast",
            instance = instance.instance,
            closed = closed_lemma.lemma,
            accept_init = accept_init_lemma.lemma,
        ));

        theory.add_content(&format!(
            "theorem pcp_no_solution:\n\
            \"\\<not> have_solution {instance}\"\n\
            using this_is_invariant no_solution_if_exists_invariant by auto",
            instance = instance.instance
        ));

        organizer.set_theory(theory_name.as_str(), theory.clone());

        InvariantLemma {
            meta: theory.get_meta(),
            theorem: format!("{}.pcp_no_solution", theory_name),
        }
    }
}
