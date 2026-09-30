use crate::ast::{builtin_origin, LabelTable, Node};
use crate::code_origin::{CodeOrigin, FileRegistry, SourceFile};
use crate::instructions as mnemonics;
use crate::registers as reg;
use proc_macro2::Span;
use std::path::{Path, PathBuf};
use syn::parse::ParseStream;
use syn::Token;

mod kw {
    syn::custom_keyword!(then);
    syn::custom_keyword!(elsif);
    syn::custom_keyword!(end);
    syn::custom_keyword!(and);
    syn::custom_keyword!(or);
    syn::custom_keyword!(not);
    syn::custom_keyword!(global);
    syn::custom_keyword!(globalexport);
    syn::custom_keyword!(unalignedglobal);
    syn::custom_keyword!(unalignedglobalexport);
    syn::custom_keyword!(aligned);
    syn::custom_keyword!(near);
    syn::custom_keyword!(sizeof);
    syn::custom_keyword!(constexpr);
    syn::custom_keyword!(include);
    syn::custom_keyword!(error);
}

#[derive(Clone, Debug, Default)]
pub struct ParserOptions {
    pub include_dirs: Vec<String>,
}

#[derive(Debug, Default)]
pub struct ParseSession {
    pub files: FileRegistry,
    pub labels: LabelTable,
    pub sources: Vec<String>,
    pub options: ParserOptions,
}

impl ParseSession {
    pub fn new(options: ParserOptions) -> Self {
        Self {
            files: FileRegistry::new(),
            labels: LabelTable::new(),
            sources: Vec::new(),
            options,
        }
    }

    fn note_source(&mut self, file_name: &str) {
        if !self.sources.contains(&file_name.to_string()) {
            self.sources.push(file_name.to_string());
        }
    }
}

pub fn read_text_file(path: &Path) -> Result<String, syn::Error> {
    let data = std::fs::read(path)
        .map_err(|e| err_here(format!("cannot read {}: {}", path.display(), e)))?;
    if !data.is_ascii() {
        return Err(err_here(format!(
            "{} contains non-ASCII characters",
            path.display()
        )));
    }
    let mut text = String::from_utf8(data).map_err(|e| err_here(format!("bad utf8: {}", e)))?;
    text.retain(|c| c != '\r');
    Ok(text)
}

fn err_here(msg: impl Into<String>) -> syn::Error {
    syn::Error::new(Span::call_site(), msg.into())
}

fn resolve_include_file(
    module: &str,
    options: &ParserOptions,
    current_file_dir: Option<&Path>,
) -> Option<PathBuf> {
    for dir in &options.include_dirs {
        let candidate = Path::new(dir).join(format!("{}.asm", module));
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    if let Some(dir) = current_file_dir {
        let candidate = dir.join(format!("{}.asm", module));
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    let fallback = Path::new(module).with_extension("asm");
    if fallback.is_file() {
        return Some(fallback);
    }
    None
}

pub fn parse_data(data: &str, file_name: &str, session: &mut ParseSession) -> syn::Result<Node> {
    let token_stream: proc_macro2::TokenStream = data
        .parse()
        .map_err(|e| err_here(format!("tokenizer error in {}: {}", file_name, e)))?;
    parse_tokens(token_stream, file_name, session)
}

pub fn parse_tokens(
    tokens: proc_macro2::TokenStream,
    file_name: &str,
    session: &mut ParseSession,
) -> syn::Result<Node> {
    session.note_source(file_name);
    let file: SourceFile = session.files.intern(file_name);
    let parser = move |input: ParseStream| -> syn::Result<Node> {
        let mut ctx = Ctx {
            session,
            current_file: file,
        };
        let result = ctx.parse_sequence(input, &[], "")?;
        if !input.is_empty() {
            return Err(input.error("unexpected trailing tokens"));
        }
        Ok(result)
    };
    syn::parse::Parser::parse2(parser, tokens)
}

pub fn parse_file(path: &Path, session: &mut ParseSession) -> syn::Result<Node> {
    let name = path.to_string_lossy().to_string();
    let data = read_text_file(path)?;
    parse_data(&data, &name, session)
}

pub fn parse_includes(path: &Path, session: &mut ParseSession) -> syn::Result<Vec<String>> {
    let name = path.to_string_lossy().to_string();
    let data = read_text_file(path)?;
    let mut file_list = vec![name.clone()];
    collect_includes(&data, path, &session.options.clone(), &mut file_list)?;
    Ok(file_list)
}

fn collect_includes(
    data: &str,
    file_path: &Path,
    options: &ParserOptions,
    out: &mut Vec<String>,
) -> syn::Result<()> {
    let tokens: proc_macro2::TokenStream = data
        .parse()
        .map_err(|e| err_here(format!("tokenizer error: {}", e)))?;
    let current_dir = file_path.parent().map(|p| p.to_path_buf());
    scan_includes_in_stream(tokens, options, current_dir.as_deref(), out)
}

fn scan_includes_in_stream(
    tokens: proc_macro2::TokenStream,
    options: &ParserOptions,
    current_dir: Option<&Path>,
    out: &mut Vec<String>,
) -> syn::Result<()> {
    let mut iter = tokens.into_iter().peekable();
    while let Some(tt) = iter.next() {
        match tt {
            proc_macro2::TokenTree::Ident(id) if id == "include" => {
                if let Some(proc_macro2::TokenTree::Punct(p)) = iter.peek() {
                    if p.as_char() == '?' {
                        iter.next();
                    }
                }
                let Some(proc_macro2::TokenTree::Ident(module)) = iter.next() else {
                    continue;
                };
                let module = module.to_string();
                if let Some(resolved) = resolve_include_file(&module, options, current_dir) {
                    let rname = resolved.to_string_lossy().to_string();
                    if !out.contains(&rname) {
                        out.push(rname.clone());
                        let data = read_text_file(&resolved)?;
                        let inner_tokens: proc_macro2::TokenStream =
                            data.parse().map_err(|e: proc_macro2::LexError| {
                                err_here(format!("tokenizer error: {}", e))
                            })?;
                        scan_includes_in_stream(inner_tokens, options, resolved.parent(), out)?;
                    }
                }
            }
            proc_macro2::TokenTree::Group(g) => {
                scan_includes_in_stream(g.stream(), options, current_dir, out)?;
            }
            _ => {}
        }
    }
    Ok(())
}

struct Ctx<'a> {
    session: &'a mut ParseSession,
    current_file: SourceFile,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Term {
    End,
    Else,
    Elsif,
}

fn peek_terminator(input: ParseStream) -> Option<Term> {
    if input.peek(kw::end) {
        Some(Term::End)
    } else if input.peek(Token![else]) {
        Some(Term::Else)
    } else if input.peek(kw::elsif) {
        Some(Term::Elsif)
    } else {
        None
    }
}

#[allow(clippy::unwrap_used)]
fn try_parse_word(input: ParseStream) -> Option<(String, Span)> {
    if input.is_empty() {
        return None;
    }
    input
        .step(|cursor| {
            let mut cur = *cursor;
            let mut text = String::new();
            let mut first_span: Option<Span> = None;

            if let Some((punct, rest)) = cur.punct() {
                if punct.as_char() == '%' {
                    text.push('%');
                    first_span = Some(punct.span());
                    cur = rest;
                }
            }

            // Exactly one leading core: a bare identifier, or `$ident`.
            let mut got_piece = false;
            if let Some((ident, rest)) = cur.ident() {
                text.push_str(&ident.to_string());
                first_span.get_or_insert(ident.span());
                cur = rest;
                got_piece = true;
            } else if let Some((punct, rest)) = cur.punct() {
                if punct.as_char() == '$' {
                    if let Some((ident, rest2)) = rest.ident() {
                        text.push('$');
                        text.push_str(&ident.to_string());
                        first_span.get_or_insert(punct.span());
                        cur = rest2;
                        got_piece = true;
                    }
                }
            }
            if !got_piece {
                return Err(cursor.error("expected identifier"));
            }

            while let Some((punct, rest)) = cur.punct() {
                if punct.as_char() != '$' {
                    break;
                }
                let Some((ident, rest2)) = rest.ident() else {
                    break;
                };
                text.push('$');
                text.push_str(&ident.to_string());
                cur = rest2;
            }
            Ok(((text, first_span.unwrap()), cur))
        })
        .ok()
}

fn peek_word(input: ParseStream) -> Option<String> {
    let fork = input.fork();
    try_parse_word(&fork).map(|(s, _)| s)
}

fn try_parse_local_label(input: ParseStream) -> Option<(String, Span)> {
    if input.is_empty() {
        return None;
    }
    input
        .step(|cursor| {
            let Some((dot, rest)) = cursor.punct() else {
                return Err(cursor.error("expected `.`"));
            };
            if dot.as_char() != '.' {
                return Err(cursor.error("expected `.`"));
            }
            let Some((ident, rest2)) = rest.ident() else {
                return Err(cursor.error("expected label name"));
            };
            Ok(((format!(".{}", ident), dot.span()), rest2))
        })
        .ok()
}

fn peek_local_label(input: ParseStream) -> bool {
    let fork = input.fork();
    try_parse_local_label(&fork).is_some()
}

/// Reports whether `word` is a global label spelling (`_foo`).
fn is_global_label_word(word: &str) -> bool {
    word.starts_with('_')
}

/// Reports whether `word` is a physical-register escape (`%xmm8`).
fn is_special_register_word(word: &str) -> bool {
    word.starts_with('%')
}

/// Reports whether the upcoming token(s) start a value that could stand in
/// operand position: a unary op, a parenthesized group, a literal, a
/// register/identifier/label, `sizeof`, or a `const { ... }` block.
fn starts_operand(input: ParseStream) -> bool {
    if input.is_empty() {
        return false;
    }
    if input.peek(Token![-])
        || input.peek(Token![~])
        || input.peek(syn::token::Paren)
        || input.peek(syn::token::Brace)
        || input.peek(kw::sizeof)
        || input.peek(syn::Lit)
    {
        return true;
    }
    if peek_local_label(input) {
        return true;
    }
    peek_word(input).is_some()
}

/// Reports whether `input` starts a label definition (`name:` or `.name:`).
fn starts_label_def(input: ParseStream) -> bool {
    let fork = input.fork();
    let named = if peek_local_label(&fork) {
        try_parse_local_label(&fork).is_some()
    } else {
        try_parse_word(&fork).is_some()
    };
    named && fork.peek(Token![:]) && !fork.peek(Token![::])
}

fn starts_new_statement(input: ParseStream) -> bool {
    if input.is_empty() {
        return true;
    }
    if peek_terminator(input).is_some() {
        return true;
    }
    if input.peek(Token![const])
        || input.peek(Token![macro])
        || input.peek(Token![if])
        || input.peek(kw::global)
        || input.peek(kw::globalexport)
        || input.peek(kw::unalignedglobal)
        || input.peek(kw::unalignedglobalexport)
        || input.peek(kw::aligned)
        || input.peek(Token![extern])
        || input.peek(kw::include)
        || input.peek(kw::error)
    {
        return true;
    }
    // Without this, an operand-less mnemonic swallows the next label:
    // `ret` followed by `_next:` would read as `ret _next`.
    if starts_label_def(input) {
        return true;
    }
    if let Some(word) = peek_word(input) {
        if mnemonics::lookup(&word) {
            return true;
        }

        let fork = input.fork();
        if try_parse_word(&fork).is_some() && fork.peek(syn::token::Paren) {
            return true;
        }
    }
    false
}

impl Ctx<'_> {
    fn origin_at(&self, span: Span) -> CodeOrigin {
        CodeOrigin::new(&self.current_file, span.start().line)
    }

    fn parse_predicate_atom(&mut self, input: ParseStream) -> syn::Result<Node> {
        if input.peek(kw::not) {
            let k: kw::not = input.parse()?;
            return Ok(Node::NotPred {
                origin: self.origin_at(k.span),
                child: Box::new(self.parse_predicate_atom(input)?),
            });
        }
        if input.peek(syn::token::Paren) {
            let inner;
            syn::parenthesized!(inner in input);
            return self.parse_predicate(&inner);
        }
        if input.peek(syn::LitBool) {
            let lit: syn::LitBool = input.parse()?;
            return Ok(if lit.value { Node::True } else { Node::False });
        }
        if let Some((word, span)) = try_parse_word(input) {
            return Ok(Node::Setting {
                origin: self.origin_at(span),
                name: word,
            });
        }
        Err(input.error("expected a predicate"))
    }

    fn parse_predicate_and(&mut self, input: ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_predicate_atom(input)?;
        while input.peek(kw::and) {
            let k: kw::and = input.parse()?;
            let right = self.parse_predicate_atom(input)?;
            result = Node::AndPred {
                origin: self.origin_at(k.span),
                left: Box::new(result),
                right: Box::new(right),
            };
        }
        Ok(result)
    }

    fn parse_predicate(&mut self, input: ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_predicate_and(input)?;
        while input.peek(kw::or) {
            let k: kw::or = input.parse()?;
            let right = self.parse_predicate_and(input)?;
            result = Node::OrPred {
                origin: self.origin_at(k.span),
                left: Box::new(result),
                right: Box::new(right),
            };
        }
        Ok(result)
    }

    fn parse_variable(&mut self, input: ParseStream) -> syn::Result<Node> {
        let (word, span) =
            try_parse_word(input).ok_or_else(|| input.error("expected a variable"))?;
        let origin = self.origin_at(span);
        if reg::is_register_name(&word) {
            if reg::is_vec(&word) {
                return Ok(Node::VecRegister { origin, name: word });
            } else if reg::is_fpr(&word) {
                return Ok(Node::FpRegister { origin, name: word });
            }
            return Ok(Node::Register { origin, name: word });
        }
        // A `%`-prefixed word names a physical register directly
        // (`%xmm8`, `%x13`, ...), bypassing the portable vreg vocabulary.
        if is_special_register_word(&word) {
            return Ok(Node::SpecialRegister { name: word });
        }
        Ok(Node::Variable {
            origin,
            name: word.clone(),
            original_name: word,
        })
    }

    fn at_const_block(&self, input: ParseStream) -> bool {
        if !input.peek(Token![const]) {
            return false;
        }
        let fork = input.fork();
        let _ = fork.parse::<Token![const]>();
        fork.peek(syn::token::Brace)
    }

    fn parse_const_block(&mut self, input: ParseStream) -> syn::Result<Node> {
        let k: Token![const] = input.parse()?;
        let origin = self.origin_at(k.span);
        let content;
        syn::braced!(content in input);
        let value: proc_macro2::TokenStream = content.parse()?;
        Ok(Node::ConstExpr { origin, value })
    }

    /// Parses the `constexpr(...)`/`constexpr a::b::c` forms used only in
    /// an address's scale position (see `parse_address`).
    fn parse_constexpr_atom(&mut self, input: ParseStream) -> syn::Result<Node> {
        let k: kw::constexpr = input.parse()?;
        let origin = self.origin_at(k.span);
        if input.peek(syn::token::Paren) {
            let inner;
            syn::parenthesized!(inner in input);
            let value: proc_macro2::TokenStream = inner.parse()?;
            return Ok(Node::ConstExpr { origin, value });
        }
        let names = self.parse_colon_colon(input)?;
        let value: proc_macro2::TokenStream = names.join("::").parse().unwrap_or_default();
        Ok(Node::ConstExpr { origin, value })
    }

    fn parse_colon_colon(&mut self, input: ParseStream) -> syn::Result<Vec<String>> {
        let (first, _) = try_parse_word(input).ok_or_else(|| input.error("expected a name"))?;
        let mut names = vec![first];
        while input.peek(Token![::]) {
            input.parse::<Token![::]>()?;
            let (next, _) = try_parse_word(input).ok_or_else(|| input.error("expected a name"))?;
            names.push(next);
        }
        Ok(names)
    }

    fn parse_address(&mut self, input: ParseStream, offset: Node) -> syn::Result<Node> {
        let content;
        let bracket = syn::bracketed!(content in input);
        let origin = self.origin_at(bracket.span.open());
        if content.is_empty() {
            return Ok(Node::AbsoluteAddress {
                origin,
                address: Box::new(offset),
            });
        }
        let a = self.parse_variable(&content)?;
        if content.is_empty() {
            return Ok(Node::Address {
                origin,
                base: Box::new(a),
                offset: Box::new(offset),
            });
        }
        content.parse::<Token![,]>()?;
        let b = self.parse_variable(&content)?;
        if content.is_empty() {
            let one = Node::Immediate {
                origin: origin.clone(),
                value: 1,
            };
            return Ok(Node::BaseIndex {
                origin,
                base: Box::new(a),
                index: Box::new(b),
                scale: Box::new(one),
                offset: Box::new(offset),
            });
        }
        content.parse::<Token![,]>()?;
        let c = if let Some(lit) = content.parse::<Option<syn::LitInt>>()? {
            let v: i128 = lit
                .base10_parse()
                .map_err(|_| syn::Error::new(lit.span(), "expected a scale of 1, 2, 4, or 8"))?;
            if ![1, 2, 4, 8].contains(&v) {
                return Err(syn::Error::new(
                    lit.span(),
                    "expected a scale of 1, 2, 4, or 8",
                ));
            }
            Node::Immediate {
                origin: origin.clone(),
                value: v,
            }
        } else if content.peek(kw::constexpr) {
            self.parse_constexpr_atom(&content)?
        } else if self.at_const_block(&content) {
            self.parse_const_block(&content)?
        } else {
            self.parse_variable(&content)?
        };
        Ok(Node::BaseIndex {
            origin,
            base: Box::new(a),
            index: Box::new(b),
            scale: Box::new(c),
            offset: Box::new(offset),
        })
    }

    #[allow(clippy::expect_used)]
    fn parse_expression_atom(&mut self, input: ParseStream) -> syn::Result<Node> {
        if input.peek(Token![-]) {
            let t: Token![-] = input.parse()?;
            return Ok(Node::Neg {
                origin: self.origin_at(t.span),
                child: Box::new(self.parse_expression_atom(input)?),
            });
        }
        if input.peek(Token![~]) {
            let t: Token![~] = input.parse()?;
            return Ok(Node::Bitnot {
                origin: self.origin_at(t.span),
                child: Box::new(self.parse_expression_atom(input)?),
            });
        }
        if input.peek(syn::token::Paren) {
            let inner;
            syn::parenthesized!(inner in input);
            let result = self.parse_expression(&inner)?;
            if !inner.is_empty() {
                return Err(inner.error("unexpected token inside `(...)`"));
            }
            return Ok(result);
        }
        if let Some(lit) = input.parse::<Option<syn::LitInt>>()? {
            let origin = self.origin_at(lit.span());
            let value = parse_int_literal(&lit)?;
            return Ok(Node::Immediate { origin, value });
        }
        if let Some(lit) = input.parse::<Option<syn::LitStr>>()? {
            return Ok(Node::StringLiteral {
                origin: self.origin_at(lit.span()),
                value: lit.value(),
            });
        }
        if self.at_const_block(input) {
            return self.parse_const_block(input);
        }
        if peek_local_label(input) {
            let (name, span) = try_parse_local_label(input)
                .ok_or_else(|| syn::Error::new(input.span(), "mus be parsed"))?;
            let origin = self.origin_at(span);
            self.session
                .labels
                .local_label_for_name(&origin, &name)
                .map_err(|e| syn::Error::new(span, e))?;
            return Ok(Node::LocalLabelReference {
                origin,
                label: name,
            });
        }
        if input.peek(kw::sizeof) {
            let k: kw::sizeof = input.parse()?;
            let names = self.parse_colon_colon(input)?;
            return Ok(Node::Sizeof {
                origin: self.origin_at(k.span),
                struct_name: names.join("::"),
            });
        }
        if let Some((word, span)) = peek_word(input).map(|w| (w, input.span())) {
            if is_special_register_word(&word) {
                let _ = try_parse_word(input);
                return Ok(Node::SpecialRegister { name: word });
            }
            if reg::is_register_name(&word) {
                return self.parse_variable(input);
            }
            if is_global_label_word(&word) {
                let _ = try_parse_word(input);
                let origin = self.origin_at(span);
                self.session
                    .labels
                    .label_for_name(&word, false)
                    .map_err(|e| syn::Error::new(span, e))?;
                return Ok(Node::LabelReference {
                    origin,
                    label: word,
                    offset: 0,
                });
            }
            let names = self.parse_colon_colon(input)?;
            let origin = self.origin_at(span);
            if names.len() > 1 {
                let field = names.last().cloned().expect("at least one value");
                let struct_name = names[..names.len() - 1].join("::");
                return Ok(Node::StructOffset {
                    origin,
                    struct_name,
                    field,
                });
            }
            return Ok(Node::Variable {
                origin,
                name: names[0].clone(),
                original_name: names[0].clone(),
            });
        }
        Err(input.error("expected an operand"))
    }

    fn parse_expression_mul(&mut self, input: ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_atom(input)?;
        while input.peek(Token![*]) {
            let t: Token![*] = input.parse()?;
            let rhs = self.parse_expression_atom(input)?;
            result = Node::Mul {
                origin: self.origin_at(t.span),
                left: Box::new(result),
                right: Box::new(rhs),
            };
        }
        Ok(result)
    }

    fn parse_expression_add(&mut self, input: ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_mul(input)?;
        loop {
            if input.peek(Token![+]) {
                let t: Token![+] = input.parse()?;
                let rhs = self.parse_expression_mul(input)?;
                result = Node::Add {
                    origin: self.origin_at(t.span),
                    left: Box::new(result),
                    right: Box::new(rhs),
                };
            } else if input.peek(Token![-]) {
                let t: Token![-] = input.parse()?;
                let rhs = self.parse_expression_mul(input)?;
                result = Node::Sub {
                    origin: self.origin_at(t.span),
                    left: Box::new(result),
                    right: Box::new(rhs),
                };
            } else {
                break;
            }
        }
        Ok(result)
    }

    fn parse_expression_and(&mut self, input: ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_add(input)?;
        while input.peek(Token![&]) {
            let t: Token![&] = input.parse()?;
            let rhs = self.parse_expression_add(input)?;
            result = Node::And {
                origin: self.origin_at(t.span),
                left: Box::new(result),
                right: Box::new(rhs),
            };
        }
        Ok(result)
    }

    fn parse_expression(&mut self, input: ParseStream) -> syn::Result<Node> {
        let mut result = self.parse_expression_and(input)?;
        loop {
            if input.peek(Token![|]) {
                let t: Token![|] = input.parse()?;
                let rhs = self.parse_expression_and(input)?;
                result = Node::Or {
                    origin: self.origin_at(t.span),
                    left: Box::new(result),
                    right: Box::new(rhs),
                };
            } else if input.peek(Token![^]) {
                let t: Token![^] = input.parse()?;
                let rhs = self.parse_expression_and(input)?;
                result = Node::Xor {
                    origin: self.origin_at(t.span),
                    left: Box::new(result),
                    right: Box::new(rhs),
                };
            } else {
                break;
            }
        }
        Ok(result)
    }

    fn parse_operand(&mut self, input: ParseStream, comment: &str) -> syn::Result<Node> {
        if starts_operand(input) {
            let expr = self.parse_expression(input)?;
            if input.peek(syn::token::Bracket) {
                return self.parse_address(input, expr);
            }
            return Ok(expr);
        }
        if input.peek(syn::token::Bracket) {
            let zero = Node::Immediate {
                origin: self.origin_at(input.span()),
                value: 0,
            };
            return self.parse_address(input, zero);
        }
        Err(input.error(format!("expected an operand {}", comment)))
    }

    fn parse_macro_variables(&mut self, input: ParseStream) -> syn::Result<Vec<Node>> {
        let content;
        syn::parenthesized!(content in input);
        let mut variables = Vec::new();
        while !content.is_empty() {
            let (name, span) = try_parse_word(&content)
                .ok_or_else(|| content.error("expected a macro parameter name"))?;
            variables.push(Node::Variable {
                origin: self.origin_at(span),
                name: name.clone(),
                original_name: name,
            });
            if content.is_empty() {
                break;
            }
            content.parse::<Token![,]>()?;
        }
        Ok(variables)
    }

    fn parse_sequence(
        &mut self,
        input: ParseStream,
        terminators: &[Term],
        comment: &str,
    ) -> syn::Result<Node> {
        let first_origin = self.origin_at(input.span());
        let mut list: Vec<Node> = Vec::new();
        loop {
            if input.is_empty() {
                if terminators.is_empty() {
                    break;
                }
                return Err(input.error(format!("expected end of block {}", comment)));
            }
            if let Some(t) = peek_terminator(input) {
                if terminators.contains(&t) {
                    break;
                }
            }

            if input.peek(Token![const]) {
                let k: Token![const] = input.parse()?;
                let (name, span) = try_parse_word(input)
                    .ok_or_else(|| input.error("expected a name after `const`"))?;
                let variable = Node::Variable {
                    origin: self.origin_at(span),
                    name: name.clone(),
                    original_name: name.clone(),
                };
                input.parse::<Token![=]>()?;
                let value =
                    self.parse_operand(input, &format!("while inside of const {}", name))?;
                list.push(Node::ConstDecl {
                    origin: self.origin_at(k.span),
                    variable: Box::new(variable),
                    value: Box::new(value),
                });
                continue;
            }

            if input.peek(kw::error) {
                let k: kw::error = input.parse()?;
                list.push(Node::Error {
                    origin: self.origin_at(k.span),
                });
                continue;
            }

            if input.peek(Token![if]) {
                self.parse_if(input, &mut list)?;
                continue;
            }

            if input.peek(Token![macro]) {
                let k: Token![macro] = input.parse()?;
                let (name, _) =
                    try_parse_word(input).ok_or_else(|| input.error("expected a macro name"))?;
                let variables = self.parse_macro_variables(input)?;
                let body = self.parse_sequence(
                    input,
                    &[Term::End],
                    &format!("while inside of macro {}", name),
                )?;
                input.parse::<kw::end>()?;
                list.push(Node::Macro {
                    origin: self.origin_at(k.span),
                    name: Some(name),
                    variables,
                    body: Box::new(body),
                });
                continue;
            }

            if input.peek(kw::global) {
                input.parse::<kw::global>()?;
                let (name, span) =
                    try_parse_word(input).ok_or_else(|| input.error("expected a label name"))?;
                if !is_global_label_word(&name) {
                    return Err(syn::Error::new(span, "expected a global label (`_name`)"));
                }
                self.session
                    .labels
                    .set_as_global(&name)
                    .map_err(|e| syn::Error::new(span, e))?;
                continue;
            }
            if input.peek(kw::globalexport) {
                input.parse::<kw::globalexport>()?;
                let (name, span) =
                    try_parse_word(input).ok_or_else(|| input.error("expected a label name"))?;
                self.session
                    .labels
                    .set_as_global_export(&name)
                    .map_err(|e| syn::Error::new(span, e))?;
                continue;
            }
            if input.peek(kw::unalignedglobal) {
                input.parse::<kw::unalignedglobal>()?;
                let (name, span) =
                    try_parse_word(input).ok_or_else(|| input.error("expected a label name"))?;
                self.session
                    .labels
                    .set_as_unaligned_global(&name)
                    .map_err(|e| syn::Error::new(span, e))?;
                continue;
            }
            if input.peek(kw::unalignedglobalexport) {
                input.parse::<kw::unalignedglobalexport>()?;
                let (name, span) =
                    try_parse_word(input).ok_or_else(|| input.error("expected a label name"))?;
                self.session
                    .labels
                    .set_as_unaligned_global_export(&name)
                    .map_err(|e| syn::Error::new(span, e))?;
                continue;
            }
            if input.peek(Token![extern]) {
                input.parse::<Token![extern]>()?;
                let reach = if input.peek(kw::near) {
                    input.parse::<kw::near>()?;
                    offlineasm_ir::Reach::Near
                } else {
                    offlineasm_ir::Reach::Far
                };
                let (name, span) =
                    try_parse_word(input).ok_or_else(|| input.error("expected a label name"))?;
                if !is_global_label_word(&name) {
                    return Err(syn::Error::new(span, "expected an extern label (`_name`)"));
                }
                self.session
                    .labels
                    .set_as_extern(&name, reach)
                    .map_err(|e| syn::Error::new(span, e))?;
                continue;
            }
            if input.peek(kw::aligned) {
                let k: kw::aligned = input.parse()?;
                let (name, span) =
                    try_parse_word(input).ok_or_else(|| input.error("expected a label name"))?;
                let origin = self.origin_at(k.span);
                let align = if let Some(lit) = input.parse::<Option<syn::LitInt>>()? {
                    Node::Immediate {
                        origin: origin.clone(),
                        value: lit.base10_parse().unwrap_or(0),
                    }
                } else {
                    let (align_name, _) = try_parse_word(input)
                        .ok_or_else(|| input.error("expected an alignment"))?;
                    Node::Variable {
                        origin: origin.clone(),
                        name: align_name.clone(),
                        original_name: align_name,
                    }
                };
                self.session
                    .labels
                    .set_as_aligned(&name, Some(align))
                    .map_err(|e| syn::Error::new(span, e))?;
                continue;
            }

            if let Some(word) = peek_word(input) {
                if mnemonics::lookup(&word) {
                    self.parse_instruction(input, &mut list)?;
                    continue;
                }
            }

            if peek_local_label(input) || peek_word(input).is_some_and(|w| is_global_label_word(&w))
            {
                let fork = input.fork();
                let is_local = peek_local_label(&fork);
                let is_label_def = {
                    let f2 = fork.fork();
                    if is_local {
                        try_parse_local_label(&f2).is_some() && f2.peek(Token![:])
                    } else {
                        try_parse_word(&f2).is_some() && f2.peek(Token![:])
                    }
                };
                if is_label_def {
                    if is_local {
                        let (name, span) = try_parse_local_label(input)
                            .ok_or_else(|| syn::Error::new(input.span(), "must be parsed"))?;
                        input.parse::<Token![:]>()?;
                        let origin = self.origin_at(span);
                        self.session
                            .labels
                            .local_label_for_name(&origin, &name)
                            .map_err(|e| syn::Error::new(span, e))?;
                        list.push(Node::LocalLabel { origin, name });
                    } else {
                        let (name, span) = try_parse_word(input)
                            .ok_or_else(|| syn::Error::new(input.span(), "must be parsed"))?;
                        input.parse::<Token![:]>()?;
                        let origin = self.origin_at(span);
                        self.session
                            .labels
                            .label_for_name(&name, true)
                            .map_err(|e| syn::Error::new(span, e))?;
                        list.push(Node::Label { origin, name });
                    }
                    continue;
                }
            }

            if input.peek(kw::include) {
                input.parse::<kw::include>()?;
                if input.peek(Token![?]) {
                    input.parse::<Token![?]>()?;
                    let (module, _) = try_parse_word(input)
                        .ok_or_else(|| input.error("expected a module name"))?;
                    self.do_include(input, &module, true, &mut list)?;
                } else {
                    let (module, _) = try_parse_word(input)
                        .ok_or_else(|| input.error("expected a module name"))?;
                    self.do_include(input, &module, false, &mut list)?;
                }
                continue;
            }

            if let Some((word, _span)) = peek_word(input).map(|w| (w, input.span())) {
                let fork = input.fork();
                if try_parse_word(&fork).is_some() && fork.peek(syn::token::Paren) {
                    self.parse_macro_call(input, &mut list)?;
                    continue;
                }
                let _ = word;
            }

            return Err(input.error(format!("unexpected token {}", comment)));
        }
        Ok(Node::Sequence {
            origin: first_origin,
            list,
        })
    }

    fn do_include(
        &mut self,
        _input: ParseStream,
        module: &str,
        optional: bool,
        list: &mut Vec<Node>,
    ) -> syn::Result<()> {
        let current_dir = Path::new(&self.current_file.name)
            .parent()
            .map(|p| p.to_path_buf());
        let resolved = resolve_include_file(module, &self.session.options, current_dir.as_deref());
        match resolved {
            Some(path) => {
                let rname = path.to_string_lossy().to_string();
                self.session.note_source(&rname);
                let data = read_text_file(&path)?;
                let inner = parse_data(&data, &rname, self.session)?;
                list.push(inner);
            }
            None if optional => {}
            None => return Err(err_here(format!("File not found: {}.asm", module))),
        }
        Ok(())
    }

    fn parse_if(&mut self, input: ParseStream, list: &mut Vec<Node>) -> syn::Result<()> {
        let k: Token![if] = input.parse()?;
        let origin = self.origin_at(k.span);
        let predicate = self.parse_predicate(input)?;
        if input.peek(kw::then) {
            input.parse::<kw::then>()?;
        }
        let then_case = self.parse_sequence(
            input,
            &[Term::Else, Term::End, Term::Elsif],
            &format!("while inside of \"if {}\"", predicate.dump()),
        )?;
        let mut top = Node::IfThenElse {
            origin,
            predicate: Box::new(predicate),
            then_case: Box::new(then_case),
            else_case: Box::new(Node::Skip {
                origin: builtin_origin(),
            }),
        };
        while input.peek(kw::elsif) {
            let ek: kw::elsif = input.parse()?;
            let pred = self.parse_predicate(input)?;
            if input.peek(kw::then) {
                input.parse::<kw::then>()?;
            }
            let body = self.parse_sequence(
                input,
                &[Term::Else, Term::End, Term::Elsif],
                &format!("while inside of \"if {}\"", pred.dump()),
            )?;
            let nested = Node::IfThenElse {
                origin: self.origin_at(ek.span),
                predicate: Box::new(pred),
                then_case: Box::new(body),
                else_case: Box::new(Node::Skip {
                    origin: builtin_origin(),
                }),
            };
            set_else_case(&mut top, nested);
        }
        if input.peek(Token![else]) {
            input.parse::<Token![else]>()?;
            let else_case =
                self.parse_sequence(input, &[Term::End], "while inside of else case")?;
            set_else_case(&mut top, else_case);
            input.parse::<kw::end>()?;
        } else {
            input.parse::<kw::end>()?;
        }
        list.push(top);
        Ok(())
    }

    fn parse_instruction(&mut self, input: ParseStream, list: &mut Vec<Node>) -> syn::Result<()> {
        let (name, span) = try_parse_word(input)
            .ok_or_else(|| syn::Error::new(input.span(), "already peeked mnemonic"))?;
        let origin = self.origin_at(span);
        // `[base, ...]` with no offset is an operand too (`jmp [t0, t1, 8]`).
        let has_operand = starts_operand(input) || input.peek(syn::token::Bracket);
        if !has_operand || starts_new_statement(input) {
            list.push(Node::Instruction {
                origin,
                opcode: name,
                operands: vec![],
                annotation: None,
            });
            return Ok(());
        }
        let mut operands = Vec::new();
        loop {
            let operand =
                self.parse_operand(input, &format!("while inside of instruction {}", name))?;
            operands.push(operand);
            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
                continue;
            }
            break;
        }
        list.push(Node::Instruction {
            origin,
            opcode: name,
            operands,
            annotation: None,
        });
        Ok(())
    }

    #[allow(clippy::expect_used)]
    fn parse_macro_call(&mut self, input: ParseStream, list: &mut Vec<Node>) -> syn::Result<()> {
        let (name, span) = try_parse_word(input)
            .ok_or_else(|| syn::Error::new(input.span(), "already peeked `(`"))?;
        let origin = self.origin_at(span);
        let content;
        syn::parenthesized!(content in input);
        let mut operands = Vec::new();
        while !content.is_empty() {
            if content.peek(Token![macro]) {
                let ik: Token![macro] = content.parse()?;
                let variables = self.parse_macro_variables(&content)?;
                let body = self.parse_sequence(
                    &content,
                    &[Term::End],
                    &format!(
                        "while inside of anonymous macro passed as argument to {}",
                        name
                    ),
                )?;
                content.parse::<kw::end>()?;
                operands.push(Node::Macro {
                    origin: self.origin_at(ik.span),
                    name: None,
                    variables,
                    body: Box::new(body),
                });
            } else {
                operands.push(
                    self.parse_operand(
                        &content,
                        &format!("while inside of macro call to {}", name),
                    )?,
                );
            }
            if content.is_empty() {
                break;
            }
            content.parse::<Token![,]>()?;
        }
        list.push(Node::MacroCall {
            origin,
            name: name.clone(),
            operands,
            annotation: None,
            original_name: name,
        });
        Ok(())
    }
}

/// Parses an integer literal's value from its own raw text, matching
/// offlineasm's legacy lexer rather than trusting `syn`'s literal-value
/// interpretation: `0x`/`0X` is hex, a leading `0` followed by more
/// digits is C-style octal, anything else is decimal.
fn parse_int_literal(lit: &syn::LitInt) -> syn::Result<i128> {
    let text = lit.base10_digits().to_string();
    let raw = lit.token().to_string();
    let raw = raw.split(['u', 'i', 'U', 'I']).next().unwrap_or(&raw);
    if let Some(hex) = raw.strip_prefix("0x").or_else(|| raw.strip_prefix("0X")) {
        return u128::from_str_radix(hex, 16)
            .map(|v| v as i128)
            .map_err(|e| syn::Error::new(lit.span(), format!("bad hex literal: {e}")));
    }
    if raw.len() > 1 && raw.starts_with('0') && raw[1..].bytes().all(|b| (b'0'..=b'7').contains(&b))
    {
        return u128::from_str_radix(&raw[1..], 8)
            .map(|v| v as i128)
            .map_err(|e| syn::Error::new(lit.span(), format!("bad octal literal: {e}")));
    }
    text.parse::<i128>()
        .or_else(|_| text.parse::<u128>().map(|v| v as i128))
        .map_err(|e| syn::Error::new(lit.span(), format!("bad integer literal: {e}")))
}

fn set_else_case(top: &mut Node, else_case: Node) {
    if let Node::IfThenElse {
        else_case: slot, ..
    } = top
    {
        if matches!(slot.as_ref(), Node::Skip { .. }) {
            **slot = else_case;
        } else {
            set_else_case(slot, else_case);
        }
    }
}
