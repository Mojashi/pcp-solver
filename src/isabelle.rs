
#[derive(Debug, Clone)]
pub struct IsabelleRef {
    pub dir_path: String,
    pub theory_name: String,
    pub name: String,
}

impl IsabelleRef {
    pub fn import_path(&self) -> String {
        if self.dir_path.is_empty() {
            return self.theory_name.clone();
        }
        return format!("{}.{}", self.dir_path, self.theory_name);
    }
    pub fn full_name(&self) -> String {
        return format!("{}.{}", self.theory_name, self.name);
    }
}

pub fn gen_definition(content: &str, name: &str, type_annot: &str) -> String {
    let type_annot = if type_annot.is_empty() {
        "".to_string()
    } else {
        format!(" :: \"{}\"", type_annot)
    };
    format!(
        "definition {name}{type_annot} where\n  \"{name} \\<equiv> {content}\"",
        name = name,
        type_annot = type_annot,
        content = content,
    )
}

pub fn gen_abbreviation(content: &str, name: &str, type_annot: &str) -> String {
    let type_annot = if type_annot.is_empty() {
        "".to_string()
    } else {
        format!(" :: \"{}\"", type_annot)
    };
    format!(
        "abbreviation {name}{type_annot} where\n  \"{name} \\<equiv> {content}\"",
        name = name,
        type_annot = type_annot,
        content = content,
    )
}
