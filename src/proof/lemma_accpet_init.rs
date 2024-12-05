use super::{
    isabelle_files::{IsabelleThyMeta, IsabelleThySameSession},
    organizer::{Organizer, PCPConfDefDepGraph},
    pcp_instance_def::PCPInstanceDef,
};
use std::rc::Rc;

pub struct AcceptInitLemma {
    pub meta: IsabelleThySameSession,
    pub lemma: String,
}

impl AcceptInitLemma {
    pub fn new(
        organizer: &mut dyn Organizer,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> AcceptInitLemma {
        let theory_name = format!("accept_init");
        let mut theory = organizer.get_theory(theory_name.as_str()).clone();
        theory.add_import(&IsabelleThyMeta::SameSession(instance.meta.clone()));

        let initial_confs = instance.pcp.get_init_config();
        let mut accept_lemmas = vec![];
        let mut coverings = vec![];

        for conf in initial_confs.iter() {
            let aut = depgraph
                .nodes
                .iter()
                .find(|(_, n)| {
                    n.conf.dir == conf.dir
                        && n.conf
                            .aut
                            .get_app_aut()
                            .accept(&conf.seq.chars().collect::<Vec<_>>())
                })
                .unwrap()
                .clone()
                .1;
            let accept_lemma = organizer.accept_lemma(aut.conf.clone(), conf);
            theory.add_import(&&IsabelleThyMeta::SameSession(accept_lemma.meta.clone()));
            accept_lemmas.push(accept_lemma);
            coverings.push(aut);
        }

        theory.add_content(&format!(
            "lemma accept_init:\n\
            \"(pcp_init_set {instance_name}) \\<subseteq> {unions}\"\n\
            apply (simp only: {init_eq_lemma})\n\
            using {accept_lemmas} by simp",
            instance_name = instance.instance,
            unions = coverings
                .iter()
                .map(|a| format!("(lang_autconf {})", a.conf.autconf_expr.clone()))
                .collect::<Vec<_>>()
                .join(" \\<union> "),
            init_eq_lemma = instance.init_eq_lemma,
            accept_lemmas = accept_lemmas
                .iter()
                .map(|a| a.lemma.clone())
                .collect::<Vec<_>>()
                .join(" "),
        ));

        organizer.set_theory(theory_name.as_str(), theory.clone());
        AcceptInitLemma {
            meta: theory.get_meta(),
            lemma: format!("{}.{}", theory_name, "accept_init"),
        }
    }
}
