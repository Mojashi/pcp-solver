use std::{iter::once, rc::Rc};

use itertools::Itertools;

use crate::automaton::NFA;

use super::{
    autconf_def::AutConfDef,
    isabelle_files::{IsabelleThyMeta, IsabelleThySameSession},
    organizer::Organizer,
    pcp_instance_def::PCPInstanceDef,
};

pub struct StepCoveringLemma {
    pub meta: IsabelleThySameSession,

    pub autconf: Rc<AutConfDef>,
    pub coverings: Vec<Rc<AutConfDef>>,

    pub lemma: String,
}

impl StepCoveringLemma {
    pub fn new(
        organizer: &mut dyn Organizer,
        autconf: Rc<AutConfDef>,
        instance: Rc<PCPInstanceDef>,
        coverings: Vec<Vec<Rc<AutConfDef>>>,
    ) -> StepCoveringLemma {
        let theory_name = format!(
            "step_covering_{}_{}",
            autconf.aut.get_id(),
            organizer.get_config().map_dir(autconf.dir)
        );
        let mut theory = organizer.get_theory(&theory_name).clone();
        theory.add_import(&IsabelleThyMeta::new_another_sess_thy("PCPLib", "PCPNFA"));
        theory.add_import(&IsabelleThyMeta::SameSession(instance.meta.clone()));

        let dir = theory.dir_path.clone();
        theory.add_imports(autconf.get_needed_theories());
        theory.add_imports(
            coverings
                .iter()
                .flatten()
                .flat_map(|c| c.get_needed_theories().into_iter())
                .collect_vec(),
        );

        theory.add_content("declare PCPNFA.config_set_accept_eq [simp]");

        let autconf_expr = autconf.autconf_expr.clone();
        let members_langs_union = coverings
            .iter()
            .flatten()
            .unique_by(|a| (a.aut.get_id(), a.dir))
            .map(|c| format!("(lang_autconf {})", c.autconf_expr))
            .chain(once("{}".to_string()))
            .join(" \\<union> ");

        let lemma_hd = format!("lemma {theory_name}:");
        let statement = format!(
            "\"pcp_step_configs {instance} (lang_autconf {autconf_expr}) \\<subseteq> {members_langs_union}\"",
            instance = instance.instance,
        );
        theory.add_content(&lemma_hd);
        theory.add_content(&statement);
        theory.add_content("proof -");

        let empty_aut_def = organizer.define_aut(NFA::new());
        let mut havecount = 0;
        for i in 0..instance.tiles.len() {
            let tile = instance.tiles[i].clone();
            let stepped_autconfs: Rc<crate::proof::step_autconf_tile::StepAutConfTileOps> =
                organizer.step_autconf_tile(autconf.clone(), instance.clone(), i);
            theory.add_imports(stepped_autconfs.needed_theories.clone());

            let same_side_covering = coverings[i]
                .iter()
                .filter(|c| c.dir == stepped_autconfs.stepped_autconf.dir)
                .collect_vec();

            if !(same_side_covering
                .iter()
                .fold(NFA::new(), |acc, b| acc.union(b.aut.get_app_aut(), true))
                .includes(&stepped_autconfs.stepped_autconf.aut.get_app_aut()))
            {   
                println!("{:?}", autconf.dir);
                autconf.aut.get_app_aut().show_dot("appaut");
                assert!(false, "Stepped autconf not covered by same side coverings");
            }

            let mut union_ops = vec![];
            let sameside_union = same_side_covering
                .iter()
                .unique_by(|a| (a.aut.get_id(), a.dir))
                .map(|c| c.aut.clone())
                .reduce(|a, b| {
                    let op = organizer.union_def(a, b);
                    union_ops.push(op.clone());
                    op.clone()
                })
                .unwrap_or_else(|| empty_aut_def.clone());
            theory.add_imports(
                union_ops
                    .iter()
                    .flat_map(|o| o.get_needed_theories())
                    .collect_vec(),
            );
            let contains_lemma = organizer.contains_lemma(
                sameside_union.clone(),
                stepped_autconfs.stepped_autconf.aut.clone(),
            );

            theory.add_import(&&IsabelleThyMeta::SameSession(contains_lemma.meta.clone()));

            let sameside_proof = format!(
                "have A{havecount}:\"lang_autconf (fst (step_autconf_tile {autconf_expr} {tile})) \\<subseteq> lang_autconf ({} {})\"\n\
                unfolding {tile}_def step_autconf_tile.simps fst_conv lang_autconf.simps config_set_eq\n\
                using {} by simp",
                organizer.get_config().map_dir(stepped_autconfs.stepped_autconf.dir),
                sameside_union.get_automaton(),
                contains_lemma.lemma_name,
            );
            // } else {
            //     format!(
            //         "have A{havecount}:\"lang_autconf (fst (step_autconf_tile {autconf_expr} {tile})) = {{}}\"\n\
            //         unfolding {tile}_def step_autconf_tile.simps fst_conv lang_autconf.simps config_set_eq\n\
            //         apply {} by ({}, simp?)",
            //         stepped_autconfs.stepped_autconf_unfold_method,
            //         stepped_autconfs.stepped_autconf.aut.get_aut_unfolding_method(),
            //     )
            // };
            havecount += 1;

            let config_covers = stepped_autconfs
                .stepped_configs
                .iter()
                .map(|c| {
                    coverings[i]
                        .iter()
                        .filter(|conf| conf.dir != autconf.dir)
                        .find(|a| a.aut.get_app_aut().accept(&c.seq.chars().collect_vec()))
                        .unwrap()
                })
                .collect_vec();

            // let accept_lemmas = config_covers
            //     .iter()
            //     .zip(stepped_autconfs.stepped_configs.iter())
            //     .map(|(&c, conf)| organizer.accept_lemma(c.clone(), conf))
            // .collect_vec();

            let accept_proof = format!(
                "have A{havecount}:\"snd (step_autconf_tile {autconf_expr} {tile}) \\<subseteq> {}\"\n\
                unfolding {tile}_def lang_autconf.simps\n\
                unfolding step_autconf_tile_configs_simp\n\
                unfolding enumerate_splits'_eq\n\
                unfolding enumerate_splits_all.simps enumerate_splits'.simps apply simp\n\
                unfolding starts_with_def\n\
                apply (rule, rule)\n\
                apply (intro conjI)?\n\
                by (match conclusion in _ \\<Rightarrow> \\<open>({}, {}?, {})\\<close>)+
                ",
                config_covers
                    .iter()
                    .map(|c| format!("(lang_autconf {})", c.autconf_expr))
                    .chain(once("{}".to_string()))
                    .join(" \\<union> "),
                autconf.aut.get_aut_unfolding_method(),
                autconf.aut.get_transition_proceed_method(),
                config_covers
                    .iter()
                    .map(|c| format!("({},{})?",
                        c.aut.get_aut_unfolding_method(),
                        c.aut.get_transition_proceed_method()
                    ))
                    .into_iter()
                    .chain(once("simp?".to_string()))
                    .join(", ")
            );
            havecount += 1;

            theory.add_content(&sameside_proof);
            theory.add_content(&accept_proof);
        }

        theory.add_content(&format!(
            "show ?thesis\n\
            apply (rule HOL.no_atp(11)[of _ \"{members_langs_union}\",\n\
            OF _ step_autconf_eq[OF prod.collapse[of \"step_autconf {autconf_expr} {instance}\"]]\n\
            ])\n\
            unfolding {instance}_def {tile_defs}\n\
            unfolding fst_step_autconf_insert snd_step_autconf_insert fst_step_autconf_empty snd_step_autconf_empty \n\
            image_insert image_empty Un_empty_right\n\
            using {Un_monos} unfolding union_langautconf\n\
            unfolding union_langautconf empty_aut_langconf_sanity Union_insert Union_empty Un_empty_right Un_empty_left\n\
            apply(fold {tile_defs})\n\
             by blast",
            instance = instance.instance,
            Un_monos = (0..havecount).map(|i| format!("A{}", i)).reduce(|a, b| format!("Un_mono[OF {} {}]", a, b)).unwrap(),
            tile_defs = instance
                .tiles
                .iter()
                .map(|tile| format!("{}_def", tile))
                .join(" "),
        ));

        theory.add_content("qed");

        organizer.set_theory(&theory_name, theory.clone());

        StepCoveringLemma {
            meta: theory.get_meta(),
            autconf,
            coverings: coverings.iter().flatten().cloned().collect_vec(),
            lemma: format!("{theory_name}.{theory_name}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        automaton::AppRegex,
        pcp::{PCPDir, Tile, PCP},
        proof::{lemma_step_contained::StepCoveringLemma, OrganizerImpl},
    };

    #[test]
    fn test_step_covering_lemma() {
        use crate::automaton::NFA;
        use crate::proof::organizer::Organizer;
        let mut organizer = OrganizerImpl::default();

        let a = NFA::from_regex(&AppRegex::parse("01(01)*"));
        let aut = organizer.define_aut(a);
        let autconf = organizer.define_autconf(aut.clone(), PCPDir::DN);

        let instance = PCP {
            tiles: vec![Tile {
                up: "01010".to_string(),
                dn: "01".to_string(),
            }],
        };
        let instance = organizer.define_pcp_instance(instance);

        let b1 = organizer.define_aut(NFA::from_regex(&AppRegex::parse("(0|1)*")));
        let b1 = organizer.define_autconf(b1, PCPDir::DN);
        let b2 = organizer.define_aut(NFA::from_regex(&AppRegex::parse("0101")));
        let b2 = organizer.define_autconf(b2, PCPDir::DN);
        let b3 = organizer.define_aut(NFA::from_regex(&AppRegex::parse("10100*1")));
        let b3 = organizer.define_autconf(b3, PCPDir::DN);
        let c = NFA::from_regex(&AppRegex::parse("0"));
        let c = organizer.define_aut(c);

        let c_conf = organizer.define_autconf(c.clone(), PCPDir::UP);
        let coverings = vec![vec![b1, b2, b3, c_conf]];

        StepCoveringLemma::new(&mut organizer, autconf, instance, coverings);

        // organizer.save_all();
    }
}

/* apply (simp only: pcp_instance.tile_0_def)
unfolding step_autconf_tile.simps fst_conv
unfolding lang_autconf.simps

unfolding pref_quotient_hom[OF append_word_lang_to_ch_single[symmetric, of aut1.aut C0], of "[C0, C1, C0, C1]", symmetric]
unfolding pref_quotient_hom[OF aut1_append_ch_0_naive_eq_aut4, of "[C0, C1, C0, C1]"]
unfolding aut4_pref_quotient_0101_naive_eq_aut5
apply(aut5.unfold_aut)
apply(simp add: aut5.transition_def)
 */
