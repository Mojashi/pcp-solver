use super::isabelle_files::{IsabelleThyFile, IsabelleThyMeta, IsabelleThySameSession};
use super::organizer::Organizer;
use crate::automaton::{BaseAutomaton, State, NFA};
use itertools::Itertools;
use once_cell::sync::Lazy;
use std::rc::Rc;
use std::{collections::BTreeMap, sync::Mutex};

static AUT_COUNTER: Lazy<Mutex<u32>> = Lazy::new(|| Mutex::new(0));

fn get_unique_nfa_name() -> String {
    let mut counter = AUT_COUNTER.lock().unwrap();
    *counter += 1;
    let ret = "nfa".to_string() + &counter.to_string();
    return ret;
}

pub trait IAutomataDef {
    fn get_id(&self) -> String; // for human
    fn get_needed_theories(&self) -> Vec<IsabelleThyMeta>;
    fn get_automaton(&self) -> String; // full path or some complete way to indicate
    fn get_state_type(&self) -> String;
    fn get_app_aut(&self) -> &NFA<char>;
    fn get_aut_unfolding_method(&self) -> String;
    fn get_transition_proceed_method(&self) -> String;
    fn get_state_map(&self) -> &BTreeMap<State, String>;
}

impl dyn IAutomataDef {
    pub fn get_needed_theories_from(
        &self,
        organizer: &mut dyn Organizer,
        dir: &str,
    ) -> Vec<IsabelleThyMeta> {
        self.get_needed_theories().into_iter().collect()
    }
}

struct StateDef {
    state_name: String,
    state_list: Vec<State>,
}

fn usize_to_bitnum(n: usize) -> String {
    if n == 1 {
        "Num.One".to_string()
    } else if n % 2 == 0 {
        format!("(Num.Bit0 {})", usize_to_bitnum(n / 2))
    } else {
        format!("(Num.Bit1 {})", usize_to_bitnum(n / 2))
    }
}

fn gen_state_def_and_state_map_bitnum(theory_name: String, num_states: usize) -> (Vec<String>, StateDef) {
    let ids = (1..=num_states).map(|i| usize_to_bitnum(i)).collect_vec();
    (vec![], StateDef {
        state_name: "Num.num".to_string(),
        state_list: ids.iter().map(|id| id.parse().unwrap()).collect(),
    })
}
fn gen_state_def_and_state_map(theory_name: String, num_states: usize) -> (Vec<String>, StateDef) {
    struct Contents {
        datatype_defs: Vec<String>,
    }

    fn rec(theory_name: String, depth: usize, size: usize, contents: &mut Contents) -> Vec<String> {
        let width = 10;

        let name = format!("state_{depth}");
        let mut constructors: Vec<String> = Vec::new();
        let mut ret_ids = Vec::new();

        for w in 0..size % width {
            let cname = format!("Leaf{w}");
            let quantified = format!("{name}.{cname}");
            constructors.push(cname.clone());
            ret_ids.push(format!("{theory_name}.{quantified}"));
        }
        if size >= width {
            let next_type = format!("state_{}", depth + 1);
            let child_ids = rec(theory_name.clone(), depth + 1, size / width, contents);

            for w in 0..width {
                let cname: String = format!("Node{w}");
                let quantified = format!("{name}.{cname}");
                constructors.push(format!("{cname} {next_type}"));
                for id in child_ids.iter() {
                    ret_ids.push(format!("({theory_name}.{quantified} {})", id));
                }
            }
        }
        let def = format!("datatype {} = {}", name, constructors.join(" | "));
        contents.datatype_defs.push(def);
        ret_ids
    }

    let mut contents = Contents {
        datatype_defs: Vec::new(),
    };
    let ids = rec(theory_name.clone(), 0, num_states, &mut contents);
    (
        contents.datatype_defs,
        StateDef {
            state_name: format!("{theory_name}.state_0"),
            state_list: ids.iter().map(|id| id.parse().unwrap()).collect(),
        },
    )
}

pub struct ConcreteNFADef {
    pub meta: IsabelleThySameSession,
    pub aut: BaseAutomaton<Option<char>>,
    pub state_map: BTreeMap<State, String>,
    pub state_def: StateDef,
}

pub struct EmptyAutDef {
    aut: NFA<char>,
}
impl IAutomataDef for EmptyAutDef {
    fn get_id(&self) -> String {
        "empty_aut".to_string()
    }

    fn get_needed_theories(&self) -> Vec<IsabelleThyMeta> {
        vec![IsabelleThyMeta::new_another_sess_thy(
            "PCPLib",
            "NFAPCPUtil",
        )]
    }

    fn get_automaton(&self) -> String {
        "NFAPCPUtil.empty_aut".to_string()
    }

    fn get_state_type(&self) -> String {
        "nat".to_string()
    }

    fn get_app_aut(&self) -> &NFA<char> {
        &self.aut
    }

    fn get_aut_unfolding_method(&self) -> String {
        "(unfold empty_aut_def)".to_string()
    }

    fn get_transition_proceed_method(&self) -> String {
        "(simp?)".to_string()
    }

    fn get_state_map(&self) -> &BTreeMap<State, String> {
        todo!()
    }
}

impl ConcreteNFADef {
    pub fn new_content(
        organizer: &dyn Organizer,
        aut: BaseAutomaton<Option<char>>,
        theory: &mut IsabelleThyFile,
    ) -> Rc<dyn IAutomataDef> {
        let config = organizer.get_config();
        let aut = aut.remove_eps().reduce_size();
        assert!(aut.is_eps_free());
        //println!("{:?}", aut.labels());

        let state_order = aut.states.iter().collect_vec();

        theory.add_imports(vec![
            IsabelleThyMeta::new_another_sess_thy("PCPDef", "PCP"),
            IsabelleThyMeta::new_another_sess_thy("PCPLib", "NFA"),
            IsabelleThyMeta::new_another_sess_thy("HOL", "Num"),
            IsabelleThyMeta::new_another_sess_thy("HOL-Eisbach", "Eisbach"),
        ]);
        let (state_def_contens, state_def) =
            gen_state_def_and_state_map_bitnum(theory.theory_name.clone(), state_order.len());
        let state_map: BTreeMap<State, String> = state_order
            .iter()
            .zip(state_def.state_list.iter())
            .map(|(s, id)| ((*s).clone(), id.clone()))
            .collect();
        theory.add_content(&state_def_contens.join("\n\n"));

        let state_name = state_def.state_name.clone();
        theory.add_content(&format!(
            "definition transition:: \"alphabet \\<Rightarrow> {state_name} \\<Rightarrow> {state_name} list\" where"
        ));
        theory.add_content(&format!("\"transition c s == case (c, s) of"));
        let is_total = aut.is_total(&organizer.get_config().get_alphabet_opt());
        theory.add_content(
            aut.transition
                .iter()
                .flat_map(|(from, v)| {
                    v.iter()
                        .group_by(|t| t.label)
                        .into_iter()
                        .map(|(label, t)| {
                            let tos = t
                                .into_iter()
                                .map(|t| state_map.get(&t.to).unwrap())
                                .join(", ");
                            format!(
                                "({}, {}) => [{tos}]",
                                config.alphabet_map.get(&label.unwrap()).unwrap(),
                                state_map.get(from).unwrap(),
                            )
                        })
                        .collect_vec()
                })
                .chain(if !is_total {
                    vec!["(_, _) => []".to_string()].into_iter()
                } else {
                    Vec::new().into_iter()
                })
                .join("|\n")
                .as_str(),
        );
        theory.add_content("\"");
        theory.break_line();

        theory.add_content(&format!(
            "definition aut :: \"(alphabet, {state_name}) NA\" where"
        ));
        theory.add_content(&format!(
            "\"aut == NA [{}] transition [{}]\"",
            state_map.get(&aut.start).unwrap(),
            aut.accept
                .iter()
                .map(|s| state_map.get(s).unwrap())
                .join(", ")
        ));
        Rc::new(ConcreteNFADef {
            meta: IsabelleThySameSession::new(&theory.theory_name, &theory.dir_path),
            aut,
            state_map,
            state_def,
        })
    }
    pub fn new(
        organizer: &mut dyn Organizer,
        aut: BaseAutomaton<Option<char>>,
    ) -> Rc<dyn IAutomataDef> {
        if aut.is_empty() {
            return Rc::new(EmptyAutDef { aut: NFA::new() });
        }

        let theory_name = get_unique_nfa_name();
        let mut theory = organizer.get_theory(&theory_name).clone();
        let ret = Self::new_content(organizer, aut, &mut theory);
        organizer.set_theory(&theory_name, theory.clone());
        ret
    }
}

impl IAutomataDef for ConcreteNFADef {
    fn get_id(&self) -> String {
        self.meta.theory_name.clone()
    }
    fn get_needed_theories(&self) -> Vec<IsabelleThyMeta> {
        vec![IsabelleThyMeta::SameSession(self.meta.clone())]
    }

    fn get_state_type(&self) -> String {
        self.state_def.state_name.clone()
    }

    fn get_app_aut(&self) -> &NFA<char> {
        &self.aut
    }

    fn get_automaton(&self) -> String {
        format!("{}.aut", self.meta.theory_name.clone(),)
    }

    fn get_aut_unfolding_method(&self) -> String {
        format!(
            "(unfold {theory_name}.aut_def {theory_name}.transition_def)",
            theory_name = self.meta.theory_name.clone()
        )
    }

    fn get_transition_proceed_method(&self) -> String {
        format!(
            "(simp add:{theory_name}.transition_def)",
            theory_name = self.meta.theory_name.clone()
        )
    }

    fn get_state_map(&self) -> &BTreeMap<State, String> {
        &self.state_map
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        automaton::{AppRegex, NFA},
        proof::organizer_impl::OrganizerImpl,
    };

    use super::*;

    #[test]
    fn test_prover() {
        let mut organizer = OrganizerImpl::default();
        let a = NFA::from_regex(&AppRegex::parse("((111|011)*)1"));
        let a = NFA::from_regex(&AppRegex::parse("((111|011)*)|(((01011|01*01)*))000|(((01011|01*01)*))000((111|011)*)|(((01011|01*01)*))((111|011)*)|(((01011|01*01)*))000((111|011)*)|(((01011|01*01)*))((111|011)*)|(((01011|01*01)*))000((111|011)*)|(((01011|01*01)*))((111|011)*)|(((01011|01*01)*))000((111|011)*)|(((01011|01*01)*))((111|011)*)|(((01011|01*01)*))000((111|011)*)|(((01011|01*01)*))((111|011)*)|(((01011|01*01)*))000((111|011)*)|(((01011|01*01)*))((111|011)*)|(((01011|01*01)*))000((111|011)*)|(((01011|01*01)*))00101((111|011)*)|(((01011|01*01)*))"));
        ConcreteNFADef::new(&mut organizer, a);
        // organizer.save_all();
    }
}

/*
method process =
  (drule_tac accept_from_iff_antichain,
   (unfold nfa72.aut_def NA.sel image_insert image_empty)?,
   (unfold nfa73.aut_def NA.sel image_insert image_empty)?,
   (simp add:nfa72.transition_def)?,
   (simp add:nfa73.transition_def)?
  )

lemma SELF_CONTAIN:
  assumes "inv_cond
    (append_word nfa72.aut [C0,C1,C0,C1])
    (append_word nfa72.aut [C0,C1,C0,C1])
    ((init_explore_state (append_word nfa72.aut [C0,C1,C0,C1]) (append_word nfa72.aut [C0,C1,C0,C1])), {})
  "
  shows False
  using assms apply simp
  by(process)+
*/
