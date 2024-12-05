use std::collections::{BTreeSet, HashMap, HashSet};

use handlebars::Handlebars;
use itertools::Itertools;

use crate::pcp::PCPDir;

#[derive(Debug, Clone)]
pub struct ProverConfig {
    pub alphabet_datatype_name: String,
    pub alphabet_map: HashMap<char, String>,
    pub state_prefix: String,
}

impl ProverConfig {
    pub fn default() -> Self {
        let mut alphabet_map = HashMap::new();
        alphabet_map.insert('0', "C0".to_string());
        alphabet_map.insert('1', "C1".to_string());
        let base_path = "proof".to_string();
        ProverConfig {
            alphabet_datatype_name: "PCP.alphabet".to_string(),
            alphabet_map: alphabet_map,
            state_prefix: "S_".to_string(),
        }
    }

    pub fn get_alphabet(&self) -> BTreeSet<char> {
        return self.alphabet_map.keys().into_iter().cloned().collect()
    }
    pub fn map_string_to_list(&self, s: &str) -> String {
        let c = s.chars().map(|c| self.alphabet_map.get(&c).unwrap().clone()).collect_vec().join(",");
        format!("[{}]", c)
    }
    pub fn get_alphabet_opt(&self) -> BTreeSet<Option<char>> {
        return self.get_alphabet().iter().cloned().map(Some).collect()
    }
    
    pub fn map_string(&self, s: &str) -> String {
        let c = s.chars().map(|c| self.alphabet_map.get(&c).unwrap().clone()).collect_vec().join(",");
        format!("[{}]", c)
    }
    pub fn map_char(&self, c: char) -> String {
        self.alphabet_map.get(&c).unwrap().clone()
    }

    pub fn map_dir(&self, dir: PCPDir) -> String {
        match dir {
            PCPDir::UP => "UP".to_string(),
            PCPDir::DN => "DN".to_string(),
        }
    }
}


pub fn get_relative_path(from: &String, to: &String) -> String {
    let from = from.split("/").collect::<Vec<&str>>();
    let to = to.split("/").collect::<Vec<&str>>();
    let mut i = 0;
    while i < from.len() && i < to.len() && from[i] == to[i] {
        i += 1;
    }
    let mut res = vec![".."; from.len() - i];
    res.extend_from_slice(&to[i..]);
    return res.join("/");
}

pub fn get_handlebars() -> Handlebars<'static> {
    let mut handlebars = Handlebars::new();
    handlebars.register_template_file("automata", "proof/templates/automata.thy").unwrap();
    handlebars.register_template_file("contains", "proof/templates/contains.thy").unwrap();
    handlebars.register_template_file("autconf", "proof/templates/autconf.thy").unwrap();
    handlebars.register_template_file("accept_init", "proof/templates/accept_init.thy").unwrap();
    handlebars.register_template_file("accept", "proof/templates/accept.thy").unwrap();
    handlebars.register_template_file("pcp_instance", "proof/templates/pcp_instance.thy").unwrap();
    handlebars.register_template_file("aut_step", "proof/templates/aut_step.thy").unwrap();
    handlebars.register_template_file("equality", "proof/templates/equality.thy").unwrap();
    handlebars.register_template_file("pref_quotient", "proof/templates/pref_quotient.thy").unwrap();
    handlebars.register_template_file("pref_quotient_automata", "proof/templates/pref_quotient_automata.thy").unwrap();
    handlebars.register_template_file("append_ch_automata", "proof/templates/append_ch_automata.thy").unwrap();
    handlebars.register_template_file("append_ch", "proof/templates/append_ch.thy").unwrap();
    handlebars.register_template_file("append_word", "proof/templates/append_word.thy").unwrap();
    handlebars.register_template_file("closed", "proof/templates/closed.thy").unwrap();
    handlebars.register_template_file("autset", "proof/templates/autset.thy").unwrap();
    handlebars.register_template_file("invariant", "proof/templates/invariant.thy").unwrap();
    handlebars.register_template_file("union", "proof/templates/union_lemma.thy").unwrap();
    handlebars.register_template_file("intersect", "proof/templates/intersect_lemma.thy").unwrap();
    handlebars.register_template_file("root", "proof/templates/ROOT").unwrap();
    handlebars.register_template_file("union_autmata", "proof/templates/union_autmata.thy").unwrap();

    return handlebars;
}