use crate::pcp::{PCPConfig, PCP};
use itertools::Itertools;
use std::collections::BTreeMap;

use super::{isabelle_files::{IsabelleThyMeta, IsabelleThySameSession}, organizer::Organizer};

pub struct PCPInstanceDef {
    pub meta: IsabelleThySameSession,

    pub pcp: PCP,
    pub tiles: Vec<String>,
    pub instance: String,
    pub init_eq_lemma: String,
}

impl PCPInstanceDef {
    pub fn new(organizer: &mut dyn Organizer, pcp: PCP) -> PCPInstanceDef {
        let config = organizer.get_config();
        let theory_name = "pcp_instance".to_string();
        let instance_name = "pcp_instance".to_string();
        let mut theory = organizer.get_theory(theory_name.as_str()).clone();
        theory.add_import(&IsabelleThyMeta::new_another_sess_thy("PCPDef", "PCP"));
        theory.add_import(&IsabelleThyMeta::new_another_sess_thy("PCPLib", "PCPTrans"));

        let initial_confs = pcp.get_init_config();
        let mut initial_conf_names: BTreeMap<String, PCPConfig> = BTreeMap::new();
        for (i, conf) in initial_confs.iter().enumerate() {
            initial_conf_names.insert(format!("init_conf_{}", i), conf.clone());
        }

        let pcp_str = pcp
            .tiles
            .iter()
            .map(|t| {
                format!(
                    "({},{})",
                    config.map_string(&t.up),
                    config.map_string(&t.dn)
                )
            })
            .collect::<Vec<String>>()
            .join(", ");

        theory.add_content(&format!(
            "definition {instance_name}::\"pcp\" where \"{instance_name} \\<equiv> [{pcp_str}]\"",
            instance_name = instance_name,
            pcp_str = pcp_str,
        ));

        for (idx, t) in pcp.tiles.iter().enumerate() {
            let up = config.map_string(&t.up);
            let dn = config.map_string(&t.dn);
            let name = format!("tile_{idx}");
            theory.add_content(&format!(
                "definition {name}::\"tile\" where \"{name} \\<equiv> ({up},{dn})\"",
            ));
        }
        let tiles = (0..pcp.tiles.len())
            .map(|i| format!("{}.tile_{}", theory_name, i))
            .collect_vec();
        let tile_defs = tiles.iter().map(|t| format!("{}_def", t)).collect_vec();

        let init_eq_lemma_name = "init_eq".to_string();
        theory.add_content(&format!(
            "lemma {init_eq_lemma_name}: \"pcp_init_set {instance_name} = {{ {init_names} }}\"\
            apply (simp only: {instance_name}_def {tile_defs})\
            using starts_with_def by auto",
            init_names = initial_confs
                .iter()
                .map(|c| format!(
                    "({dir} {s})",
                    dir = config.map_dir(c.dir),
                    s = config.map_string(&c.seq)
                ))
                .join(", "),
            tile_defs = tile_defs.join(" "),
        ));

        organizer.set_theory(&theory_name, theory.clone());
        PCPInstanceDef {
            meta: theory.get_meta(),
            pcp,
            tiles: tiles,
            instance: format!("{}.{}", theory_name.clone(), instance_name.clone()),
            init_eq_lemma: format!("{}.{}", theory_name, init_eq_lemma_name.clone()),
        }
    }
}
