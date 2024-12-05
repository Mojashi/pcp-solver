use super::{
    isabelle_files::{IsabelleThyMeta, IsabelleThySameSession},
    organizer::{Organizer, PCPConfDefDepGraph},
    pcp_instance_def::PCPInstanceDef,
};
use crate::proof::lemma_step_contained::StepCoveringLemma;
use itertools::Itertools;
use std::rc::Rc;

pub struct ClosedLemma {
    pub meta: IsabelleThySameSession,
    pub lemma: String,
    pub inv: String,
}

impl ClosedLemma {
    pub fn new(
        organizer: &mut dyn Organizer,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> ClosedLemma {
        let theory_name = "closed".to_string();
        let mut theory = organizer.get_theory(&theory_name).clone();

        let step_contained_lemmas = depgraph
            .nodes
            .iter()
            .map(|node| {
                StepCoveringLemma::new(
                    organizer,
                    node.1.conf.clone(),
                    instance.clone(),
                    node.1
                        .deps
                        .iter()
                        .map(|is| {
                            is.iter()
                                .map(|i| depgraph.nodes[i].conf.clone())
                                .collect_vec()
                        })
                        .collect_vec(),
                )
            })
            .collect_vec();
        theory.add_imports(
            step_contained_lemmas
                .iter()
                .map(|l| IsabelleThyMeta::SameSession(l.meta.clone()))
                .collect_vec(),
        );

        let inv = "inv";
        theory.add_content(&format!(
            "definition {inv}::\"PCPTrans.config set\" where\n\
             \"{inv} == {}\"",
            depgraph
                .nodes
                .iter()
                .map(|n| format!("(lang_autconf {})", n.1.conf.autconf_expr))
                .join(" \\<union> \n")
        ));

        // let union_fact = step_contained_lemmas.iter().fold("basic_monos(1)[of \"{}\"]".to_string(),
        // |acc, l| format!("Un_mono[OF {}\n {}]", acc, l.lemma));

        let use_step_cov_fact = step_contained_lemmas
            .iter()
            .map(|l| {
                if l.coverings.len() == 0 {
                    format!("apply(rule u_subset_empty[OF {}])", l.lemma)
                } else {
                    format!("apply(rule u_subset[OF {}], blast)", l.lemma)
                }
            })
            .collect_vec()
            .join("\n");

        theory.add_content(&format!(
            "theorem closed: \"pcp_step_configs pcp_instance {inv} \\<subseteq> {inv}\"\n\
             unfolding inv_def pcp_step_configs_simp\n\
             apply(intro Un_least)?\n\
             {use_step_cov_fact}\n\
             done", 
        ));
        organizer.set_theory(&theory_name, theory.clone());
        ClosedLemma {
            meta: theory.get_meta().clone(),
            lemma: format!("{}.{}", theory_name, "closed"),
            inv: format!("{}.{}", theory_name, inv),
        }
    }
}
