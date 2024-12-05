use std::{collections::HashMap, fs, io, path::Path, rc::Rc};

use crate::{
    automaton::BaseAutomaton,
    pcp::{PCPConfig, PCPDir, PCP},
};

use super::{
    append_word::AppendWordAutomataDef,
    autconf_def::AutConfDef,
    autset_def::AutSetDef,
    isabelle_files::IsabelleThyFile,
    lemma_accpet::AcceptLemma,
    lemma_accpet_init::AcceptInitLemma,
    lemma_closed::ClosedLemma,
    lemma_contains::ContainsLemma,
    lemma_invariant::InvariantLemma,
    nfa_def::{ConcreteNFADef, IAutomataDef},
    organizer::{Organizer, PCPConfDefDepGraph},
    pcp_instance_def::PCPInstanceDef,
    pref_quotient::PrefQuotientAutomatDef,
    prover_config::ProverConfig,
    step_autconf_tile::StepAutConfTileOps,
    union_aut::UnionAutsAutomataDef,
};

pub struct OrganizerImpl {
    config: ProverConfig,
    autconf_cache: HashMap<(String, PCPDir), Rc<AutConfDef>>,
    accept_cache: HashMap<(String, PCPDir, PCPConfig), Rc<AcceptLemma>>,
    theory_map: HashMap<String, IsabelleThyFile>,
    contains_cache: HashMap<(String, String), Rc<ContainsLemma>>,
}

impl OrganizerImpl {
    pub fn new(config: ProverConfig) -> OrganizerImpl {
        OrganizerImpl {
            config,
            autconf_cache: HashMap::new(),
            accept_cache: HashMap::new(),
            theory_map: HashMap::new(),
            contains_cache: HashMap::new(),
        }
    }

    pub fn default() -> OrganizerImpl {
        OrganizerImpl::new(ProverConfig::default())
    }
}

fn copy_dir_all(src: impl AsRef<Path>, dst: impl AsRef<Path>) -> io::Result<()> {
    fs::create_dir_all(&dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let ty = entry.file_type()?;
        if ty.is_dir() {
            copy_dir_all(entry.path(), dst.as_ref().join(entry.file_name()))?;
        } else {
            fs::copy(entry.path(), dst.as_ref().join(entry.file_name()))?;
        }
    }
    Ok(())
}

impl Organizer for OrganizerImpl {
    fn get_config(&self) -> ProverConfig {
        self.config.clone()
    }

    fn save_all(&self, session_name: &str, dir: &str, lib_path: &str) {
        let _ = std::fs::remove_dir_all(dir);

        let gen_dir = format!("{}/proof", dir);
        copy_dir_all(lib_path, &format!("{}/lib", dir)).unwrap();
        std::fs::create_dir_all(gen_dir.clone()).unwrap();

        for (_, t) in self.theory_map.iter() {
            t.save(&gen_dir);
        }

        let rootfile = format!(
            "session \"{}\" = \"PCPLib\" + \n\
                sessions\n\
                    \"HOL-Eisbach\"\n\
                theories
                    invariant",
                    session_name
        );
        let root_file = gen_dir.clone() + "/ROOT";
        fs::write(&root_file, rootfile).unwrap();
    }

    fn get_theory<'a>(&'a mut self, name: &str) -> &'a IsabelleThyFile {
        if self.theory_map.get(name).is_none() {
            self.theory_map.insert(
                name.to_string(),
                IsabelleThyFile::new(name, "."),
            );
        }
        self.theory_map.get(name).unwrap()
    }
    fn set_theory(&mut self, name: &str, theory: IsabelleThyFile) {
        self.theory_map.insert(name.to_string(), theory);
    }

    fn define_aut(&mut self, aut: BaseAutomaton<Option<char>>) -> Rc<dyn IAutomataDef> {
        ConcreteNFADef::new(self, aut.clone())
    }

    fn define_autconf(
        &mut self,
        aut: Rc<dyn IAutomataDef>,
        dir: crate::pcp::PCPDir,
    ) -> Rc<AutConfDef> {
        let key = (aut.get_automaton(), dir);
        if !self.autconf_cache.contains_key(&key) {
            let a = Rc::new(AutConfDef::new(self, aut.clone(), dir));
            self.autconf_cache.insert(key.clone(), a);
        }
        self.autconf_cache.get(&key).unwrap().clone()
    }

    fn define_autconfset(
        &mut self,
        autset: Vec<Rc<AutConfDef>>,
        theory_name: String,
    ) -> Rc<AutSetDef> {
        Rc::new(super::autset_def::AutSetDef::new(self, autset, theory_name))
    }

    fn define_pcp_instance(&mut self, config: PCP) -> Rc<PCPInstanceDef> {
        Rc::new(PCPInstanceDef::new(self, config))
    }

    fn append_word(&mut self, aut: Rc<dyn IAutomataDef>, w: String) -> Rc<dyn IAutomataDef> {
        Rc::new(AppendWordAutomataDef::new(self, aut, w))
    }

    fn pref_quotient(&mut self, aut: Rc<dyn IAutomataDef>, pref: String) -> Rc<dyn IAutomataDef> {
        Rc::new(PrefQuotientAutomatDef::new(self, aut, &pref))
    }

    fn step_autconf_tile(
        &mut self,
        autconf: Rc<AutConfDef>,
        instance: Rc<PCPInstanceDef>,
        idx: usize,
    ) -> Rc<StepAutConfTileOps> {
        Rc::new(StepAutConfTileOps::new(self, autconf, instance, idx))
    }

    fn contains_lemma(
        &mut self,
        aut: Rc<dyn IAutomataDef>,
        aut2: Rc<dyn IAutomataDef>,
    ) -> Rc<ContainsLemma> {
        let id1 = aut.get_id();
        let id2 = aut2.get_id();
        if self.contains_cache.contains_key(&(id1.clone(), id2.clone())) {
            return self.contains_cache.get(&(id1, id2)).unwrap().clone();
        }
        let ret = Rc::new(ContainsLemma::new(self, aut, aut2));
        self.contains_cache.insert((id1, id2), ret.clone());
        ret
    }

    fn accept_lemma(&mut self, aut: Rc<AutConfDef>, conf: &PCPConfig) -> Rc<AcceptLemma> {
        if self.accept_cache.contains_key(&(aut.aut.get_id(), aut.dir, conf.clone())) {
            return self.accept_cache.get(&(aut.aut.get_id(), aut.dir, conf.clone())).unwrap().clone();
        }
        let ret = Rc::new(AcceptLemma::new(self, aut.as_ref(), conf));
        self.accept_cache.insert((aut.aut.get_id(), aut.dir, conf.clone()), ret.clone());
        ret
    }

    fn accept_init_lemma(
        &mut self,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> Rc<AcceptInitLemma> {
        Rc::new(AcceptInitLemma::new(self, instance, depgraph))
    }

    fn closed_lemma(
        &mut self,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> Rc<ClosedLemma> {
        Rc::new(ClosedLemma::new(self, instance, depgraph))
    }

    fn invariant_lemma(
        &mut self,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> Rc<super::lemma_invariant::InvariantLemma> {
        Rc::new(InvariantLemma::new(self, instance, depgraph))
    }

    fn union_def(
        &mut self,
        aut1: Rc<dyn IAutomataDef>,
        aut2: Rc<dyn IAutomataDef>,
    ) -> Rc<dyn IAutomataDef> {
        Rc::new(UnionAutsAutomataDef::new(self, aut1, aut2))
    }
}
