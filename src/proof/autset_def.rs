use super::autconf_def::AutConfDef;
use super::organizer::Organizer;
use itertools::Itertools;
use std::rc::Rc;

pub struct AutSetDef {
    pub theory_name: String,

    pub aut_set: Vec<Rc<AutConfDef>>,

    pub autset_name: String,
}

impl AutSetDef {
    pub fn new(
        organizer: &mut dyn Organizer,
        aut_set: Vec<Rc<AutConfDef>>,
        theory_name: String,
    ) -> AutSetDef {
        // let mut theory = organizer.get_theory(&theory_name).clone();
        // let theory_dir = theory.dir_path.clone();
        // theory.add_imports(aut_set.iter().flat_map(|a| {
        //     a.get_needed_theories_from(organizer, &theory_dir)
        //         .into_iter()
        // }));
        // theory.add_content(&format!(
        //     "definition {autset_name} :: \"PCPTrans.config set\" where\
        //     \"{autset_name} \\<equiv> {member_langs}\"",
        //     autset_name = theory_name,
        //     member_langs = aut_set
        //         .iter()
        //         .map(|a| format!("(lang_autconf {})", a.autconf_expr))
        //         .join(" \\<union> ")
        // ));
        // organizer.set_theory(&theory_name, theory);

        // AutSetDef {
        //     theory_name: theory_name.clone(),
        //     aut_set: aut_set,
        //     autset_name: theory_name,
        // }
        todo!()
    }
}
