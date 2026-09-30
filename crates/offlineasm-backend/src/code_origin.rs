use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct SourceFile {
    pub name: String,
    pub basename: String,
    pub file_number: usize,
}

#[derive(Clone, Debug, Default)]
pub struct FileRegistry {
    names: Vec<String>,
    index: HashMap<String, usize>,
}

impl FileRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, file_name: &str) -> SourceFile {
        let key = file_name.to_string();
        if let Some(&n) = self.index.get(&key) {
            return SourceFile {
                name: key.clone(),
                basename: basename_of(&key),
                file_number: n,
            };
        }
        self.names.push(key.clone());
        let n = self.names.len();
        self.index.insert(key.clone(), n);
        SourceFile {
            name: key.clone(),
            basename: basename_of(&key),
            file_number: n,
        }
    }

    pub fn dot_file_list(&self) -> Vec<String> {
        self.names
            .iter()
            .enumerate()
            .map(|(i, n)| format!("\".file {} \\\"{}\\\"\\n\"", i + 1, n))
            .collect()
    }
}

fn basename_of(path: &str) -> String {
    path.rsplit(['/', '\\']).next().unwrap_or(path).to_string()
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CodeOrigin {
    pub file_name: String,
    pub basename: String,
    pub file_number: usize,
    pub line: usize,
}

impl CodeOrigin {
    pub fn new(file: &SourceFile, line: usize) -> Self {
        Self {
            file_name: file.name.clone(),
            basename: file.basename.clone(),
            file_number: file.file_number,
            line,
        }
    }

    pub fn origin_string(&self) -> String {
        format!("{}:{}", self.basename, self.line)
    }

    pub fn debug_directive(&self) -> String {
        format!("\".loc {} {}\\n\"", self.file_number, self.line)
    }

    pub fn label_string_extension(&self) -> String {
        format!("{}_{}", self.basename.replace('.', "_"), self.line)
    }
}

impl std::fmt::Display for CodeOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.origin_string())
    }
}
