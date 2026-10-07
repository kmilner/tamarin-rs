//! Embed the upstream web assets and compiled graph renderer in the executable.
#![allow(clippy::disallowed_macros)] // Cargo build directives.

use std::collections::{hash_map::DefaultHasher, BTreeMap};
use std::fs;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;

fn collect(dir: &Path, prefix: &str, assets: &mut BTreeMap<String, PathBuf>, watch: bool) {
    if watch {
        println!("cargo:rerun-if-changed={}", dir.display());
    }
    for entry in fs::read_dir(dir).expect("read GUI asset directory") {
        let path = entry.expect("read GUI asset").path();
        let name = path
            .file_name()
            .unwrap()
            .to_str()
            .expect("UTF-8 asset name");
        let key = format!("{prefix}{name}");
        if path.is_dir() {
            collect(&path, &format!("{key}/"), assets, watch);
        } else {
            assets.insert(key, path);
        }
    }
}

fn main() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    // The shared build dependency has initialized missing upstream sources
    // before this script or tamarin-term/theory can embed them.
    let upstream = Path::new(tamarin_build::UPSTREAM_DIR);
    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR"));
    let script = root.join("scripts/build_gui.sh");
    println!("cargo:rerun-if-changed={}", script.display());
    for input in [
        "src",
        "package.json",
        "package-lock.json",
        "tsconfig.json",
        "vite.config.js",
    ] {
        println!(
            "cargo:rerun-if-changed={}",
            upstream.join("frontend").join(input).display()
        );
    }
    // Keep generated files inside Cargo's output directory. Separate profiles,
    // target directories and concurrent builds must not replace each other's GUI.
    // Watch source inputs only: watching dist would make our own output trigger
    // another frontend build.
    let gui = out.join("gui");
    let status = Command::new("bash")
        .arg(&script)
        .arg(&gui)
        .status()
        .expect("Could not run the GUI build; install Bash, Node.js and npm");
    assert!(
        status.success(),
        "GUI build failed ({status}); see the npm output above"
    );
    let dist = gui.join("frontend/dist");
    for name in [
        "intdot-graph.es.js",
        "intdot-staticgraph.es.js",
        "intdot-dynamicgraph.es.js",
        "intdot-style.css",
    ] {
        assert!(
            fs::metadata(dist.join(name)).is_ok_and(|metadata| metadata.len() > 0),
            "GUI build did not produce {name}"
        );
    }
    let mut assets = BTreeMap::new();
    collect(&upstream.join("data"), "", &mut assets, true);
    let mut frontend = BTreeMap::new();
    collect(&dist, "", &mut frontend, false);
    for (name, path) in frontend {
        let prefix = if name.ends_with(".css") { "css" } else { "js" };
        assets.insert(format!("{prefix}/{name}"), path);
    }

    // Include the same CSS correction as the on-disk override route.
    let patch = Path::new("src/handlers/lemma_instructions.css");
    println!("cargo:rerun-if-changed={}", patch.display());
    let instructions = fs::read(patch).expect("lemma CSS");
    let css = assets.get_mut("css/tamarin-prover-ui.css").expect("UI CSS");
    let mut bytes = fs::read(&css).expect("read UI CSS");
    if !bytes.ends_with(&instructions) {
        bytes.extend_from_slice(&instructions);
    }
    *css = out.join("tamarin-prover-ui.css");
    fs::write(&css, bytes).expect("write patched UI CSS");

    let mut generated = String::from("const EMBEDDED_ASSETS: &[(&str, &[u8], &str)] = &[\n");
    for (name, path) in assets {
        let bytes = fs::read(&path).expect("read asset");
        let mut hash = DefaultHasher::new();
        bytes.hash(&mut hash);
        let etag = format!("\"{:016x}\"", hash.finish());
        generated.push_str(&format!(
            "({name:?}, include_bytes!({path:?}), {etag:?}),\n"
        ));
    }
    generated.push_str("];\n");
    fs::write(out.join("gui_assets.rs"), generated).expect("write asset table");
}
