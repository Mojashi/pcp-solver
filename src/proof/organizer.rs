use super::{
    autconf_def::AutConfDef, autset_def::AutSetDef, isabelle_files::IsabelleThyFile,
    lemma_accpet::AcceptLemma, lemma_accpet_init::AcceptInitLemma, lemma_closed::ClosedLemma,
    lemma_contains::ContainsLemma, lemma_invariant::InvariantLemma, nfa_def::IAutomataDef,
    pcp_instance_def::PCPInstanceDef, prover_config::ProverConfig,
    step_autconf_tile::StepAutConfTileOps,
};
use crate::{
    automaton::BaseAutomaton,
    dep::PCPConfDepGraph,
    pcp::{PCPConfig, PCPDir, PCP},
};
use std::{collections::BTreeMap, fs, rc::Rc};

pub struct PCPConfDefNode {
    pub conf: Rc<AutConfDef>,
    pub deps: Vec<Vec<usize>>,
}
pub struct PCPConfDefDepGraph {
    pub nodes: BTreeMap<usize, PCPConfDefNode>,
    pub starts: Vec<usize>,
}

pub trait Organizer {
    fn get_config(&self) -> ProverConfig;

    fn save_all(&self, session_name: &str, dir: &str, lib_path: &str);

    fn set_theory(&mut self, name: &str, theory: IsabelleThyFile);
    fn get_theory<'a>(&'a mut self, name: &str) -> &'a IsabelleThyFile;

    fn define_aut(&mut self, aut: BaseAutomaton<Option<char>>) -> Rc<dyn IAutomataDef>;
    fn define_autconf(&mut self, aut: Rc<dyn IAutomataDef>, dir: PCPDir) -> Rc<AutConfDef>;
    fn define_autconfset(
        &mut self,
        autset: Vec<Rc<AutConfDef>>,
        theory_name: String,
    ) -> Rc<AutSetDef>;
    fn define_pcp_instance(&mut self, pcp: PCP) -> Rc<PCPInstanceDef>;

    fn append_word(&mut self, aut: Rc<dyn IAutomataDef>, w: String) -> Rc<dyn IAutomataDef>;
    fn pref_quotient(&mut self, aut: Rc<dyn IAutomataDef>, pref: String) -> Rc<dyn IAutomataDef>;

    fn step_autconf_tile(
        &mut self,
        autconf: Rc<AutConfDef>,
        instance: Rc<PCPInstanceDef>,
        idx: usize,
    ) -> Rc<StepAutConfTileOps>;
    fn union_def(
        &mut self,
        aut1: Rc<dyn IAutomataDef>,
        aut2: Rc<dyn IAutomataDef>,
    ) -> Rc<dyn IAutomataDef>;
    fn contains_lemma(
        &mut self,
        aut: Rc<dyn IAutomataDef>,
        aut2: Rc<dyn IAutomataDef>,
    ) -> Rc<ContainsLemma>;
    fn accept_lemma(&mut self, aut: Rc<AutConfDef>, conf: &PCPConfig) -> Rc<AcceptLemma>;
    fn accept_init_lemma(
        &mut self,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> Rc<AcceptInitLemma>;
    fn closed_lemma(
        &mut self,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> Rc<ClosedLemma>;
    fn invariant_lemma(
        &mut self,
        instance: Rc<PCPInstanceDef>,
        depgraph: &PCPConfDefDepGraph,
    ) -> Rc<InvariantLemma>;
}
impl dyn Organizer {
    fn depgraph_map(&mut self, depgraph: &PCPConfDepGraph) -> PCPConfDefDepGraph {
        let mut nodes = BTreeMap::new();
        for (idx, n) in depgraph.nodes.iter() {
            let aut = self.define_aut(n.conf.conf.clone());
            let autconf = self.define_autconf(aut, n.conf.dir.clone());
            nodes.insert(
                *idx,
                PCPConfDefNode {
                    conf: autconf,
                    deps: n.deps.clone(),
                },
            );
        }
        PCPConfDefDepGraph {
            nodes,
            starts: depgraph.starts.clone(),
        }
    }

    pub fn proof_has_no_solution_eff(
        &mut self,
        pcp: PCP,
        depgraph: &PCPConfDepGraph,
    ) -> Rc<InvariantLemma> {
        let config = self.get_config();
        let pcp_def = self.define_pcp_instance(pcp.clone());
        let depgraph: PCPConfDefDepGraph = self.depgraph_map(depgraph);
        self.invariant_lemma(pcp_def, &depgraph)
    }
}
