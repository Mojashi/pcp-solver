use super::isabelle_files::IsabelleThyMeta;
use super::nfa_def::IAutomataDef;
use super::organizer::Organizer;
use crate::pcp::PCPDir;
use std::iter::once;
use std::rc::Rc;

pub struct AutConfDef {
    pub aut: Rc<dyn IAutomataDef>,
    pub dir: PCPDir,

    pub autconf_expr: String,
}

impl AutConfDef {
    pub fn new(
        organizer: &mut dyn Organizer,
        aut: Rc<dyn IAutomataDef>,
        dir: PCPDir,
    ) -> AutConfDef {
        let dir_str = organizer.get_config().map_dir(dir);
        AutConfDef {
            aut: aut.clone(),
            dir,
            autconf_expr: format!("(autconfig.{dir_str} {})", aut.get_automaton()),
        }
    }

    pub fn get_needed_theories(&self) -> Vec<IsabelleThyMeta> {
        self.aut.get_needed_theories().into_iter().chain(once(IsabelleThyMeta::new_another_sess_thy("PCPLib", "PCPNFA"))).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        automaton::{AppRegex, NFA},
        proof::{organizer::Organizer, organizer_impl::OrganizerImpl},
    };

    #[test]
    fn test_prover() {
        let a = NFA::from_regex(&AppRegex::parse("10"));

        let mut organizer = OrganizerImpl::default();
        let config = organizer.get_config();
        let aut = organizer.define_aut(a);
        organizer.define_autconf(aut, PCPDir::DN);

        // organizer.save_all()
    }
}
