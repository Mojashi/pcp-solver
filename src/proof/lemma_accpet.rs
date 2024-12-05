use crate::pcp::PCPConfig;
use super::{autconf_def::AutConfDef, isabelle_files::IsabelleThySameSession, Organizer};

pub struct AcceptLemma {
    pub meta: IsabelleThySameSession,
    pub lemma: String,
}

impl AcceptLemma {
    pub fn new(organizer: &mut dyn Organizer, autconf: &AutConfDef, conf: &PCPConfig) -> AcceptLemma {
        let config = organizer.get_config();
        let theory_name = format!("accept_{}_{}_{}", autconf.aut.get_id(), config.map_dir(conf.dir), conf.seq.replace(",", "_"));
        let mut theory = organizer.get_theory(theory_name.as_str()).clone();

        theory.add_imports(autconf.get_needed_theories());

        theory.add_content(&format!(
            "lemma contain_lem:\"PCPTrans.{dir} {seq} \\<in> lang_autconf {conf}\"\n\
            unfolding lang_autconf_elem_iff_accept by ({unfold_conf}, simp add:bind_insert_iff)",
            dir = config.map_dir(conf.dir),
            seq = config.map_string_to_list(&conf.seq),
            conf = autconf.autconf_expr,
            unfold_conf = autconf.aut.get_aut_unfolding_method(),
        ));

        organizer.set_theory(theory_name.as_str(), theory.clone());

        AcceptLemma {
            meta: theory.get_meta().clone(),
            lemma: format!("{}.{}", theory_name, "contain_lem"),
        }
    }
}
