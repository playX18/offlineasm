//! The instruction reference, parsed from `docs/reference.md`.
//!
//! Every `` ### `mnemonic operands` `` heading in that file is one entry: its
//! body (pseudocode and notes) becomes the rustdoc of the `mnem` constant and,
//! in `onlineasm`, of the typed `Assembler` method. Each numbered section's
//! `### Scratch registers` block adds the clobber table for the entry's
//! group, and the trailing `## Availability` section says which mnemonics
//! only `offlineasm` accepts.

use std::sync::OnceLock;

const REFERENCE: &str = include_str!("../docs/reference.md");

/// Which assemblers accept a mnemonic.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Availability {
    /// Both `offlineasm` and `onlineasm` accept it.
    Both,
    /// Only `offlineasm` accepts it.
    OfflineasmOnly,
    /// Only `offlineasm`'s `rloop` backend accepts it.
    RloopOnly,
}

/// The crate a rendered reference is for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Audience {
    Offlineasm,
    Onlineasm,
}

impl Audience {
    pub fn includes(self, availability: Availability) -> bool {
        self == Audience::Offlineasm || availability == Availability::Both
    }
}

/// One `### ...` entry of the reference.
#[derive(Clone, Debug)]
pub struct Entry {
    /// Every spelling the heading names, first one first.
    pub mnemonics: Vec<&'static str>,
    /// Operand form shared by all spellings, such as `O1, O2`. Empty for
    /// bare mnemonics like `ret`.
    pub form: &'static str,
    /// Everything between the heading and the next one, trimmed.
    pub body: &'static str,
    /// The scratch registers the entry clobbers: its section's scratch
    /// intro plus its group's table and notes. Empty if the reference has
    /// none.
    pub scratch: String,
    pub availability: Availability,
}

/// Returns every entry, in document order.
pub fn entries() -> &'static [Entry] {
    static ENTRIES: OnceLock<Vec<Entry>> = OnceLock::new();
    ENTRIES.get_or_init(parse)
}

/// Returns the entry covering `mnemonic`, if the reference has one.
pub fn entry_for(mnemonic: &str) -> Option<&'static Entry> {
    entries()
        .iter()
        .find(|entry| entry.mnemonics.contains(&mnemonic))
}

/// Returns the contents of each `` `...` `` span in `text`.
fn code_spans(text: &str) -> impl Iterator<Item = &str> {
    text.split('`').skip(1).step_by(2)
}

fn parse() -> Vec<Entry> {
    // Split into (heading, body start, body end) sections. `#` lines inside
    // code fences are not headings.
    let mut sections: Vec<(&'static str, usize, usize)> = Vec::new();
    let mut in_fence = false;
    let mut offset = 0;
    for line in REFERENCE.split_inclusive('\n') {
        let start = offset;
        offset += line.len();
        if line.trim_start().starts_with("```") {
            in_fence = !in_fence;
        }
        if in_fence || !line.starts_with('#') {
            continue;
        }
        if let Some(last) = sections.last_mut() {
            last.2 = start;
        }
        sections.push((line.trim_end(), offset, REFERENCE.len()));
    }

    let mut entries = Vec::new();
    let mut entry_sections = Vec::new();
    let mut scratch_bodies = Vec::new();
    let mut restricted: Vec<(&str, Availability)> = Vec::new();
    let mut section = 0;
    for &(heading, start, end) in &sections {
        let body = REFERENCE[start..end].trim();
        if heading.starts_with("## ") {
            section += 1;
        }
        if heading == "### Scratch registers" {
            scratch_bodies.push((section, body));
            continue;
        }
        if heading == "## Availability" {
            for line in body.lines().filter(|line| line.starts_with("- ")) {
                let (label, names) = line.split_once(':').unwrap_or(("", line));
                let availability = if label.contains("rloop") {
                    Availability::RloopOnly
                } else {
                    Availability::OfflineasmOnly
                };
                restricted.extend(code_spans(names).map(|name| (name, availability)));
            }
            continue;
        }
        if !heading.starts_with("### `") {
            continue;
        }
        // `tls_loadb O1, O2` / `tls_loadh` / ...: the first span carries the
        // operand form, later spans are more spellings.
        let mut spans = code_spans(heading);
        let first = spans.next().unwrap_or_default();
        let (head, form) = first.split_once(' ').unwrap_or((first, ""));
        let mut mnemonics = vec![head];
        mnemonics.extend(spans);
        entries.push(Entry {
            mnemonics,
            form: form.trim(),
            body,
            scratch: String::new(),
            availability: Availability::Both,
        });
        entry_sections.push(section);
    }

    let known: Vec<&str> = entries.iter().flat_map(|e| e.mnemonics.clone()).collect();
    for (section, body) in scratch_bodies {
        let (intro, groups) = scratch_groups(body, &known);
        for (entry, _) in entries
            .iter_mut()
            .zip(&entry_sections)
            .filter(|(_, s)| **s == section)
        {
            let group = groups
                .iter()
                .find(|(names, _)| entry.mnemonics.iter().any(|m| names.iter().any(|n| n == m)));
            let parts: Vec<&str> = match group {
                Some((_, text)) => [intro.as_str(), text].into(),
                None if groups.is_empty() => vec![intro.as_str()],
                None => continue,
            };
            let parts: Vec<&str> = parts.into_iter().filter(|p| !p.is_empty()).collect();
            entry.scratch = parts.join("\n\n");
        }
    }

    for entry in &mut entries {
        if let Some(&(_, availability)) = restricted
            .iter()
            .find(|(name, _)| entry.mnemonics.contains(name))
        {
            entry.availability = availability;
        }
    }
    entries
}

/// Splits a `### Scratch registers` body into its intro and its groups.
///
/// A group starts at a `Label: \`name\`, ...` paragraph, or at a paragraph
/// saying its names "clobber no scratch register", and runs to the next one.
/// Each group pairs the mnemonics it names with its table and notes.
fn scratch_groups(body: &str, known: &[&str]) -> (String, Vec<(Vec<String>, String)>) {
    let is_start = |block: &str| {
        let lead = block.split('`').next().unwrap_or_default();
        block.contains('`')
            && (lead.trim_end().ends_with(':') || block.contains("clobber no scratch register"))
    };
    let blocks: Vec<&str> = body
        .split("\n\n")
        .map(str::trim)
        .filter(|block| !block.is_empty())
        .collect();
    let first = blocks
        .iter()
        .position(|b| is_start(b))
        .unwrap_or(blocks.len());
    let intro = blocks[..first].join("\n\n");
    let mut groups = Vec::new();
    let mut index = first;
    while index < blocks.len() {
        let head = blocks[index];
        let end = blocks[index + 1..]
            .iter()
            .position(|b| is_start(b))
            .map_or(blocks.len(), |p| index + 1 + p);
        let rest = &blocks[index + 1..end];
        // The name list ends at the paragraph's first sentence; anything
        // after it is a note about the group.
        let split = head.find(". ").or_else(|| head.find(".\n"));
        let (list, note) = match split {
            Some(at) => (&head[..at], head[at + 2..].trim()),
            None => (head, ""),
        };
        let names = group_names(list, known);
        let mut parts: Vec<&str> = Vec::new();
        if rest.is_empty() {
            parts.push(head);
        } else {
            if !note.is_empty() {
                parts.push(note);
            }
            parts.extend(rest);
        }
        groups.push((names, parts.join("\n\n")));
        index = end;
    }
    (intro, groups)
}

/// Expands the names a group paragraph lists into known mnemonics.
///
/// Handles `atomicxchg{b,h,i,q}` suffix sets and `cb*` wildcards, which
/// reuse the conditions of the paragraph's explicit names (`cieq` and
/// `cineq` give `cbeq` and `cbneq`).
fn group_names(list: &str, known: &[&str]) -> Vec<String> {
    let mut explicit = Vec::new();
    let mut wildcards = Vec::new();
    for span in code_spans(list) {
        if let Some(prefix) = span.strip_suffix('*') {
            wildcards.push(prefix);
        } else if let Some((stem, suffixes)) =
            span.strip_suffix('}').and_then(|s| s.split_once('{'))
        {
            explicit.extend(suffixes.split(',').map(|suffix| format!("{stem}{suffix}")));
        } else {
            explicit.push(span.to_string());
        }
    }
    // The conditions are what follows the explicit names' common stem:
    // `baddio`, `baddis`, ... give `o`, `s`, ..., so `bori*` means `borio`, ...
    let stem =
        explicit
            .iter()
            .skip(1)
            .fold(explicit.first().map_or(0, String::len), |len, name| {
                let first = &explicit[0];
                first
                    .bytes()
                    .zip(name.bytes())
                    .take(len)
                    .take_while(|(a, b)| a == b)
                    .count()
            });
    let mut names = explicit.clone();
    for prefix in wildcards {
        for name in &explicit {
            names.push(format!("{prefix}{}", &name[stem..]));
        }
    }
    names.retain(|name| known.contains(&name.as_str()));
    names
}

/// Builds the rustdoc for one mnemonic: its signature, its entry's body, and
/// its scratch registers.
///
/// Returns `None` for unknown spellings and entries `audience` excludes.
pub fn mnemonic_doc(mnemonic: &str, audience: Audience) -> Option<String> {
    let entry = entry_for(mnemonic).filter(|entry| audience.includes(entry.availability))?;
    let signature = if entry.form.is_empty() {
        mnemonic.to_string()
    } else {
        format!("{} {}", mnemonic, entry.form)
    };
    let mut doc = format!("`{}`\n\n{}", signature, entry.body);
    if !entry.scratch.is_empty() {
        doc.push_str("\n\n# Scratch registers\n\n");
        doc.push_str(&entry.scratch);
    }
    Some(doc)
}

/// Builds the rustdoc body for `onlineasm`'s typed `Assembler` method.
pub fn method_doc(mnemonic: &str) -> Option<String> {
    mnemonic_doc(mnemonic, Audience::Onlineasm)
}

/// Returns every mnemonic `audience` accepts, in reference order.
pub fn mnemonics(audience: Audience) -> Vec<&'static str> {
    let mut names: Vec<&'static str> = Vec::new();
    for entry in entries() {
        if !audience.includes(entry.availability) {
            continue;
        }
        for name in &entry.mnemonics {
            if !names.contains(name) {
                names.push(name);
            }
        }
    }
    names
}

/// Reports whether `name` is a Rust keyword, which needs raw form (`r#move`).
fn is_keyword(name: &str) -> bool {
    matches!(
        name,
        "as" | "async"
            | "await"
            | "break"
            | "const"
            | "continue"
            | "crate"
            | "dyn"
            | "else"
            | "enum"
            | "extern"
            | "false"
            | "fn"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "let"
            | "loop"
            | "match"
            | "mod"
            | "move"
            | "mut"
            | "pub"
            | "ref"
            | "return"
            | "self"
            | "static"
            | "struct"
            | "super"
            | "trait"
            | "true"
            | "type"
            | "unsafe"
            | "use"
            | "where"
            | "while"
            | "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "macro"
            | "override"
            | "priv"
            | "try"
            | "typeof"
            | "unsized"
            | "virtual"
            | "yield"
    )
}

/// Formats `name` as a Rust identifier.
fn const_ident(name: &str) -> String {
    if is_keyword(name) {
        format!("r#{}", name)
    } else {
        name.to_string()
    }
}

/// Renders the documented `mnem` module for `audience`.
///
/// `onlineasm` constants re-export `offlineasm_ir::mnem`; `offlineasm`
/// constants are the spellings themselves.
pub fn render_mnem_module(audience: Audience) -> String {
    let mut out = String::new();
    let names = mnemonics(audience);
    for name in &names {
        for line in mnemonic_doc(name, audience).unwrap_or_default().lines() {
            if line.is_empty() {
                out.push_str("///\n");
            } else {
                out.push_str("/// ");
                out.push_str(line);
                out.push('\n');
            }
        }
        let ident = const_ident(name);
        out.push_str(&match audience {
            Audience::Onlineasm => format!(
                "pub const {ident}: ::offlineasm_ir::Mnemonic = ::offlineasm_ir::mnem::{ident};\n\n"
            ),
            Audience::Offlineasm => format!("pub const {ident}: &str = \"{name}\";\n\n"),
        });
    }
    out.push_str("/// Every mnemonic this module has a constant for, in reference order.\n");
    out.push_str("pub const TABLE: &[&str] = &[\n");
    for name in &names {
        out.push_str(&format!("    \"{name}\",\n"));
    }
    out.push_str("];\n");
    out
}
