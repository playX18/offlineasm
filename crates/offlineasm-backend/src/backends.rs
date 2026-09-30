//! Lowers resolved trees to assembly text or RLoop Rust.

use crate::ast::Node;
use crate::driver::AsmEmitter;
use crate::settings::SettingsMap;
use offlineasm_ir::{ExternId, Label, Reach};
use std::collections::HashSet;

pub mod backend_rloop;
pub mod frontend;
pub mod text;
pub mod text_arm64;
pub mod text_riscv64;
pub mod text_x86;

pub const BACKENDS: &[&str] = &["X86_64", "ARM64", "ARM64E", "RISCV64", "RLOOP"];

pub const WORKING_BACKENDS: &[&str] = &["X86_64", "ARM64", "ARM64E", "RISCV64", "RLOOP"];

pub type LabelFlags<'a> = &'a dyn Fn(&str) -> (bool, bool, bool, bool, Option<String>);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Backend {
    X86_64,
    Arm64,
    Arm64e,
    Riscv64,
    RLoop,
}

impl Backend {
    pub fn name(&self) -> &'static str {
        match self {
            Backend::X86_64 => "X86_64",
            Backend::Arm64 => "ARM64",
            Backend::Arm64e => "ARM64E",
            Backend::Riscv64 => "RISCV64",
            Backend::RLoop => "RLOOP",
        }
    }

    pub fn parse(name: &str) -> Result<Self, String> {
        match canonicalize_backend_name(name).as_str() {
            "X86_64" => Ok(Backend::X86_64),
            "ARM64" => Ok(Backend::Arm64),
            "ARM64E" => Ok(Backend::Arm64e),
            "RISCV64" => Ok(Backend::Riscv64),
            "RLOOP" => Ok(Backend::RLoop),
            other => Err(format!("unknown backend {}", other)),
        }
    }
}

pub fn canonicalize_backend_name(name: &str) -> String {
    let upper = name.to_uppercase();
    if upper == "ARM64_32" {
        return "ARM64".to_string();
    }
    upper
}

pub fn canonicalize_backend_names(names: &[String]) -> Vec<String> {
    let mut out: Vec<String> = names.iter().map(|n| canonicalize_backend_name(n)).collect();
    out.dedup();
    out
}

#[derive(Clone, Debug)]
pub struct BackendSet {
    valid: HashSet<String>,
}

impl Default for BackendSet {
    fn default() -> Self {
        Self {
            valid: BACKENDS.iter().map(|s| s.to_string()).collect(),
        }
    }
}

impl BackendSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn include_only(&mut self, list: &[String]) {
        let mut next = HashSet::new();
        for backend in list {
            if self.valid.contains(backend) {
                next.insert(backend.clone());
            }
        }
        self.valid = next;
    }

    pub fn is_valid(&self, backend: &str) -> bool {
        self.valid.contains(backend)
    }

    pub fn valid_backends(&self) -> Vec<String> {
        let mut v: Vec<String> = self.valid.iter().cloned().collect();
        v.sort();
        v
    }
}

pub fn is_backend(name: &str) -> bool {
    BACKENDS.contains(&name)
}

pub fn is_valid_backend(name: &str) -> bool {
    BackendSet::new().is_valid(name)
}

#[derive(Debug, Clone)]
pub struct LoweringError {
    pub message: String,
    pub origin: String,
}

impl std::fmt::Display for LoweringError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (due to {})", self.message, self.origin)
    }
}

impl std::error::Error for LoweringError {}

pub struct LowerCtx<'a> {
    pub backend: Backend,
    pub emitter: &'a mut AsmEmitter,
    pub referenced_extern: Vec<String>,
    pub globals: std::collections::HashMap<String, (bool, bool)>,
    pub is_win: bool,
    pub macho: bool,
    pub local_strings: std::collections::HashMap<String, String>,
    pub known_labels: std::collections::HashSet<String>,
    settings: SettingsMap,
    synth_counter: usize,
    pub ir_labels: Vec<String>,
    ir_label_ids: std::collections::HashMap<String, u32>,
    pub ir_syms: Vec<String>,
    ir_sym_ids: std::collections::HashMap<String, u32>,
    pub ir_fresh: std::collections::HashMap<u32, String>,
    pub declared_externs: std::collections::HashMap<String, Reach>,
    pub ir_externs: Vec<String>,
    ir_extern_ids: std::collections::HashMap<String, u32>,
    pub extern_slots: std::collections::HashMap<u32, String>,
}

impl<'a> LowerCtx<'a> {
    pub fn new(backend: Backend, emitter: &'a mut AsmEmitter) -> Self {
        Self {
            backend,
            emitter,
            referenced_extern: Vec::new(),
            globals: std::collections::HashMap::new(),
            is_win: false,
            macho: false,
            local_strings: std::collections::HashMap::new(),
            known_labels: std::collections::HashSet::new(),
            settings: SettingsMap::new(),
            synth_counter: 0,
            ir_labels: Vec::new(),
            ir_label_ids: std::collections::HashMap::new(),
            ir_syms: Vec::new(),
            ir_sym_ids: std::collections::HashMap::new(),
            ir_fresh: std::collections::HashMap::new(),
            declared_externs: std::collections::HashMap::new(),
            ir_externs: Vec::new(),
            ir_extern_ids: std::collections::HashMap::new(),
            extern_slots: std::collections::HashMap::new(),
        }
    }

    pub fn intern_extern(&mut self, text: String) -> ExternId {
        if let Some(&id) = self.ir_extern_ids.get(&text) {
            return ExternId(id);
        }
        let id = self.ir_externs.len() as u32;
        self.ir_externs.push(text.clone());
        self.ir_extern_ids.insert(text, id);
        ExternId(id)
    }

    pub fn coff(&self) -> bool {
        !self.macho && (self.setting("WINDOWS") || self.is_win)
    }

    pub fn intern_label(&mut self, text: String) -> Label {
        if let Some(&id) = self.ir_label_ids.get(&text) {
            return Label(id);
        }
        let id = self.ir_labels.len() as u32;
        self.ir_labels.push(text.clone());
        self.ir_label_ids.insert(text, id);
        Label(id)
    }

    pub fn intern_sym(&mut self, text: String) -> u32 {
        if let Some(&id) = self.ir_sym_ids.get(&text) {
            return id;
        }
        let id = self.ir_syms.len() as u32;
        self.ir_syms.push(text.clone());
        self.ir_sym_ids.insert(text, id);
        id
    }

    pub fn set_settings(&mut self, settings: SettingsMap) {
        self.settings = settings;
    }

    pub fn setting(&self, name: &str) -> bool {
        self.settings.get(name) == Some(&true)
    }

    pub fn global_symbol(&self, name: &str) -> String {
        if self.macho {
            format!("_{}", name)
        } else {
            name.to_string()
        }
    }

    pub fn local_symbol(&self, name: &str) -> String {
        if self.macho {
            format!("L{}", name)
        } else {
            name.to_string()
        }
    }

    pub fn mark_used(&mut self, name: &str, is_extern: bool) {
        if is_extern && !self.referenced_extern.contains(&name.to_string()) {
            self.referenced_extern.push(name.to_string());
        }
    }

    pub fn local_label_string(name: &str, origin: &crate::code_origin::CodeOrigin) -> String {
        let stripped = name.get(1..).unwrap_or("");
        format!(
            "__offlineasm_{}_{}",
            stripped,
            origin.label_string_extension()
        )
    }

    pub fn local_string(&self, name: &str) -> Result<String, String> {
        self.local_strings
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown local label {}", name))
    }

    pub fn unique_local(
        &mut self,
        comment: &str,
        origin: &crate::code_origin::CodeOrigin,
    ) -> (Node, Node) {
        let mut candidate = format!("_{}", comment);
        if self.known_labels.contains(&candidate) {
            loop {
                candidate = format!("_{}_{}", self.synth_counter, comment);
                self.synth_counter += 1;
                if !self.known_labels.contains(&candidate) {
                    break;
                }
            }
        }
        self.known_labels.insert(candidate.clone());
        let string = Self::local_label_string(&candidate, origin);
        self.local_strings.insert(candidate.clone(), string);
        (
            Node::LocalLabel {
                origin: origin.clone(),
                name: candidate.clone(),
            },
            Node::LocalLabelReference {
                origin: origin.clone(),
                label: candidate,
            },
        )
    }

    pub fn lower_synth(
        &mut self,
        nodes: &[Node],
        label_flags: LabelFlags<'_>,
    ) -> Result<(), String> {
        for node in nodes {
            lower_node_inner(node, self, label_flags)?;
        }
        Ok(())
    }
}

pub fn lower_node(
    node: &Node,
    ctx: &mut LowerCtx,
    label_flags: LabelFlags<'_>,
) -> Result<(), LoweringError> {
    let origin = node.origin_string();
    lower_node_inner(node, ctx, label_flags).map_err(|message| LoweringError { message, origin })
}

fn lower_node_inner(
    node: &Node,
    ctx: &mut LowerCtx,
    label_flags: LabelFlags<'_>,
) -> Result<(), String> {
    match node {
        Node::Label { name, .. } => {
            let raw = name.strip_prefix('_').unwrap_or(name);
            let (global, export, aligned, is_extern, align_to) = label_flags(name);
            let symbol = if global || is_extern {
                ctx.global_symbol(raw)
            } else {
                ctx.local_symbol(raw)
            };
            ctx.emitter
                .puts_label(&symbol, global, export, aligned, align_to);
            Ok(())
        }
        Node::LocalLabel { name, origin } => {
            let label_string = ctx
                .local_strings
                .get(name)
                .cloned()
                .unwrap_or_else(|| LowerCtx::local_label_string(name, origin));
            let symbol = ctx.local_symbol(&label_string);
            ctx.emitter.puts_local_label(&symbol);
            Ok(())
        }
        Node::Skip { .. } => Ok(()),
        Node::Sequence { list, .. } => {
            if ctx.backend == Backend::RLoop {
                return backend_rloop::lower_sequence(list, ctx, label_flags);
            }
            for item in list {
                lower_node_inner(item, ctx, label_flags)?;
            }
            Ok(())
        }
        Node::Instruction { .. } => match ctx.backend {
            Backend::RLoop => backend_rloop::lower_instruction(node, ctx, label_flags),
            Backend::X86_64 => {
                frontend::lower_instruction(node, ctx, label_flags, text::TextTarget::X86_64, false)
            }
            Backend::Arm64 => frontend::lower_instruction(
                node,
                ctx,
                label_flags,
                text::TextTarget::Aarch64,
                false,
            ),
            Backend::Arm64e => {
                frontend::lower_instruction(node, ctx, label_flags, text::TextTarget::Aarch64, true)
            }
            Backend::Riscv64 => frontend::lower_instruction(
                node,
                ctx,
                label_flags,
                text::TextTarget::Riscv64,
                false,
            ),
        },
        other => Err(format!("cannot lower {} (validate first)", other.dump())),
    }
}

pub fn local_ref_name(node: &Node, ctx: &LowerCtx) -> Result<String, String> {
    match node {
        Node::LocalLabelReference { label, .. } => Ok(ctx.local_symbol(&ctx.local_string(label)?)),
        other => Err(format!("not a local label reference: {}", other.dump())),
    }
}

pub fn extern_or_global_ref(stripped: &str) -> String {
    stripped.to_string()
}

pub fn local_ref(stripped: &str) -> String {
    stripped.to_string()
}
