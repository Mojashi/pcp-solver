use super::prover_config::get_relative_path;
use std::collections::HashSet;
use std::fs::File;
use std::io::Write;
use std::iter::once;

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct IsabelleThySameSession {
    pub theory_name: String,
    pub dir_path: String,
}
impl IsabelleThySameSession {
    pub fn new(theory_name: &str, dir_path: &str) -> IsabelleThySameSession {
        IsabelleThySameSession {
            theory_name: theory_name.to_string(),
            dir_path: dir_path.to_string(),
        }
    }
    pub fn thy_path(&self) -> String {
        format!("{}/{}", self.dir_path, self.theory_name)
    }
    pub fn file_path(&self) -> String {
        format!("{}/{}.thy", self.dir_path, self.theory_name)
    }
    pub fn import_path_from(&self, other: &IsabelleThySameSession) -> String {
        get_relative_path(&other.dir_path, &self.thy_path())
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub struct IsabelleThyAnotherSession {
    pub theory_name: String,
    pub session: String,
}
impl IsabelleThyAnotherSession {
    pub fn new(session: &str, theory_name: &str) -> IsabelleThyAnotherSession {
        IsabelleThyAnotherSession {
            theory_name: theory_name.to_string(),
            session: session.to_string(),
        }
    }
    pub fn import_path(&self) -> String {
        format!("{}.{}", self.session, self.theory_name)
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq)]
pub enum IsabelleThyMeta {
    SameSession(IsabelleThySameSession),
    AnotherSession(IsabelleThyAnotherSession),
    StandardThy(String),
}

impl IsabelleThyMeta {
    pub fn import_path_from(&self, other: &IsabelleThySameSession) -> String {
        match self {
            IsabelleThyMeta::SameSession(same) => same.import_path_from(other),
            IsabelleThyMeta::AnotherSession(s) => s.import_path(),
            IsabelleThyMeta::StandardThy(s) => s.to_string(),
        }
    }
    pub fn new_another_sess_thy(session: &str, theory_name: &str) -> IsabelleThyMeta {
        IsabelleThyMeta::AnotherSession(IsabelleThyAnotherSession::new(session, theory_name))
    }
    pub fn new_same_sess_thy(dir_path: &str, theory_name: &str) -> IsabelleThyMeta {
        IsabelleThyMeta::SameSession(IsabelleThySameSession {
            theory_name: theory_name.to_string(),
            dir_path: dir_path.to_string(),
        })
    }
}

#[derive(Debug, Clone)]
pub struct IsabelleThyFile {
    pub theory_name: String,
    pub dir_path: String,
    pub imports: HashSet<IsabelleThyMeta>,
    pub contents: Vec<String>,
}

pub fn main_thy() -> IsabelleThyMeta {
    IsabelleThyMeta::StandardThy("Main".to_string())
}
pub fn eisbach_thy() -> IsabelleThyMeta {
    IsabelleThyMeta::StandardThy("Eisbach".to_string())
}

impl IsabelleThyFile {
    pub fn new(theory_name: &str, dir_path: &str) -> IsabelleThyFile {
        IsabelleThyFile {
            theory_name: theory_name.to_string(),
            dir_path: dir_path.to_string(),
            imports: once(main_thy()).collect(),
            contents: Vec::new(),
        }
    }

    pub fn get_meta(&self) -> IsabelleThySameSession {
        IsabelleThySameSession {
            theory_name: self.theory_name.clone(),
            dir_path: self.dir_path.clone(),
        }
    }

    pub fn get_file_content(&self) -> String {
        let mut ret = format!("theory {}\n  imports", self.theory_name);
        // I dont know why, but Eisbach should be the last import
        for import in self.imports.iter().filter(|x| !x.import_path_from(&self.get_meta()).contains("Eisbach")) {
            ret.push_str(&format!(
                " \"{}\"",
                import.import_path_from(&self.get_meta())
            ));
        }
        for import in self.imports.iter().filter(|x| x.import_path_from(&self.get_meta()).contains("Eisbach")) {
            ret.push_str(&format!(
                " \"{}\"",
                import.import_path_from(&self.get_meta())
            ));
        }
        ret.push_str("\nbegin\n");
        for content in &self.contents {
            ret.push_str(content);
            ret.push_str("\n");
        }
        ret.push_str("end");
        ret
    }

    pub fn save(&self, base_dir: &str) {
        let mut file = File::create(format!("{base_dir}/{}", &self.get_meta().file_path())).unwrap();
        writeln!(file, "{}", self.get_file_content()).unwrap();
        file.flush().unwrap();
    }

    pub fn add_import(&mut self, import: &IsabelleThyMeta) {
        self.imports.insert(import.clone());
    }
    pub fn add_imports(&mut self, imports: Vec<IsabelleThyMeta>) {
        self.imports.extend(imports);
    }

    pub fn add_content(&mut self, content: &str) {
        self.contents.push(content.to_string());
    }

    pub fn break_line(&mut self) {
        self.contents.push("".to_string());
    }
}
