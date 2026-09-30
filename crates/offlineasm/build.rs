//! Renders the documented `mnem` module into `OUT_DIR`.
//!
//! The `reference` table in `offlineasm-backend` holds the mnemonic data
//! once. This build script selects the entries an `offlineasm` reader sees.

use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR set by cargo"));
    let mnemonics = offlineasm_backend::reference::render_mnem_module(
        offlineasm_backend::reference::Audience::Offlineasm,
    );
    fs::write(out_dir.join("mnem.rs"), mnemonics).expect("write mnemonic module");
    println!("cargo:rerun-if-changed=build.rs");
}
