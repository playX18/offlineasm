use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
    let audience = offlineasm_backend::reference::Audience::Onlineasm;
    let mnemonics = offlineasm_backend::reference::render_mnem_module(audience);
    fs::write(out_dir.join("mnem.rs"), mnemonics).expect("write mnemonic module");
    // One doc body per typed method, included by `src/insn.rs` below its
    // `Emit ...` line. Each file holds exactly `method_doc`'s output for
    // that spelling, so a missing entry fails the build instead of leaving
    // a method undocumented.
    let method_docs = out_dir.join("method-docs");
    fs::create_dir_all(&method_docs).expect("create method-docs dir");
    for name in offlineasm_backend::reference::mnemonics(audience) {
        let doc = offlineasm_backend::reference::method_doc(name)
            .unwrap_or_else(|| panic!("onlineasm accepts `{name}` but has no method doc for it"));
        fs::write(method_docs.join(format!("{name}.md")), doc).expect("write method doc");
    }
    println!("cargo:rerun-if-changed=build.rs");
}
