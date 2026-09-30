#[derive(Clone, Debug)]
pub struct Config {
    pub preferred_comment_start_column: usize,
    pub preferred_debug_annotation_columns: usize,
    pub enable_label_count_comments: bool,
    pub enable_code_origin_comments: bool,
    pub enable_instr_annotations: bool,
    pub enable_debug_annotations: bool,
    pub platform: Option<String>,
    pub binary_format: Option<String>,
    pub emit_elf_debug_directives: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            preferred_comment_start_column: 40,
            preferred_debug_annotation_columns: 18,
            enable_label_count_comments: false,
            enable_code_origin_comments: true,
            enable_instr_annotations: false,
            enable_debug_annotations: false,
            platform: None,
            binary_format: None,
            emit_elf_debug_directives: false,
        }
    }
}

impl Config {
    pub fn is_win(&self) -> bool {
        self.platform.as_deref() == Some("Windows")
    }

    pub fn with_binary_format(mut self, format: Option<String>) -> Self {
        self.emit_elf_debug_directives = format.as_deref() == Some("ELF");
        self.binary_format = format;
        self
    }
}
