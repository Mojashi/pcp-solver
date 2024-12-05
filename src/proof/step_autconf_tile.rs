use super::autconf_def::AutConfDef;
use super::isabelle_files::IsabelleThyMeta;
use super::organizer::Organizer;
use super::pcp_instance_def::PCPInstanceDef;
use crate::automaton::BaseAutomaton;
use crate::pcp::{PCPConfig, PCPDir, Tile};
use itertools::Itertools;
use std::rc::Rc;
fn simulate_enumerate_splits(s: &str) -> Vec<(String, String)> {
    (0..s.len())
        .map(|i| (s[..i].to_string(), s[i..].to_string()))
        .collect()
}
fn simulate_enumerate_splits_all(s: &str) -> Vec<(String, String)> {
    (0..=s.len())
        .map(|i| (s[..i].to_string(), s[i..].to_string()))
        .collect()
}

#[cfg(test)]
mod simtests {
    use super::*;

    #[test]
    fn test_enumerate_splits() {
        let s = "abc";
        let res = simulate_enumerate_splits(s);
        assert_eq!(
            res,
            vec![
                ("".to_string(), "abc".to_string()),
                ("a".to_string(), "bc".to_string()),
                ("ab".to_string(), "c".to_string())
            ]
        );
    }

    #[test]
    fn test_enumerate_splits_all() {
        let s = "abc";
        let res = simulate_enumerate_splits_all(s);
        assert_eq!(
            res,
            vec![
                ("".to_string(), "abc".to_string()),
                ("a".to_string(), "bc".to_string()),
                ("ab".to_string(), "c".to_string()),
                ("abc".to_string(), "".to_string())
            ]
        );
    }
}

fn simulate_step_autconf_strings_until_filter(
    aut: &BaseAutomaton<Option<char>>,
    dir: PCPDir,
    tile: Tile,
) -> Vec<(String, String)> {
    let res = match dir {
        PCPDir::UP => simulate_enumerate_splits(&tile.dn),
        PCPDir::DN => simulate_enumerate_splits_all(&tile.up),
    }
    .into_iter()
    .filter(|(s, p)| aut.accept(&s.chars().collect_vec()) && p.starts_with(&tile.by_dir(dir)))
    .collect_vec();

    res
}

fn simulate_step_autconf_strings(
    aut: &BaseAutomaton<Option<char>>,
    dir: PCPDir,
    tile: Tile,
) -> Vec<PCPConfig> {
    let res = match dir {
        PCPDir::UP => simulate_enumerate_splits(&tile.dn),
        PCPDir::DN => simulate_enumerate_splits_all(&tile.up),
    }
    .into_iter()
    .filter(|(s, p)| aut.accept(&s.chars().collect_vec()) && p.starts_with(&tile.by_dir(dir)))
    .map(|(_, p)| p.chars().skip(tile.by_dir(dir).len()).collect::<String>())
    .map(|seq| PCPConfig {
        seq,
        dir: dir.opposite(),
    })
    .collect_vec();

    res
}

pub struct StepAutConfTileOps {
    pub stepped_autconf: Rc<AutConfDef>, // langの意味で同じやつ
    pub stepped_configs: Vec<PCPConfig>,

    pub stepped_autconf_unfold_method: String,
    pub stepped_configs_unfold_method: String,

    pub needed_theories: Vec<IsabelleThyMeta>,
}

impl StepAutConfTileOps {
    pub fn new(
        organizer: &mut dyn Organizer,
        autconf: Rc<AutConfDef>,
        instance: Rc<PCPInstanceDef>,
        tile_idx: usize,
    ) -> StepAutConfTileOps {
        let tile = &instance.pcp.tiles[tile_idx];
        let stepped_configs =
            simulate_step_autconf_strings(&autconf.aut.get_app_aut(), autconf.dir, tile.clone());

        let samedir_str = tile.by_dir(autconf.dir);
        let oppdir_str = tile.by_dir(autconf.dir.opposite());
        let append_ops = organizer.append_word(autconf.aut.clone(), samedir_str.to_string());
        let stepped_aut_ops = organizer.pref_quotient(append_ops.clone(), oppdir_str.to_string());
        let stepped_autconf = organizer.define_autconf(stepped_aut_ops.clone(), autconf.dir);

        StepAutConfTileOps {
            needed_theories: vec![
                autconf.aut.get_needed_theories(),
                append_ops.get_needed_theories(),
                stepped_aut_ops.get_needed_theories(),
                stepped_autconf.get_needed_theories(),
            ]
            .concat(),
            stepped_autconf_unfold_method: format!(
                "({append_unfold_lemma}?,{pref_quot_unfold_lemma}?)",
                append_unfold_lemma = append_ops.get_aut_unfolding_method(),
                pref_quot_unfold_lemma = stepped_aut_ops.get_aut_unfolding_method(),
            ),
            stepped_autconf,
            stepped_configs,
            stepped_configs_unfold_method: format!("({})", autconf.aut.get_aut_unfolding_method(),),
        }
    }
}
