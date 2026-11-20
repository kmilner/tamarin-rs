//! Ensure upstream sources exist before compiling tests that embed Haskell files.
#![allow(clippy::disallowed_macros)] // Cargo build directives.

fn main() {
    println!(
        "cargo:rerun-if-changed={}/lib/term/src/Term/Term/Raw.hs",
        tamarin_build::UPSTREAM_DIR
    );
    if std::env::var_os("CARGO_FEATURE_LEAN_UNIFICATION").is_some() {
        build_lean_backend();
    }
}

fn checked_output(command: &mut std::process::Command) -> std::process::Output {
    let output = command.output().unwrap_or_else(|error| {
        panic!(
            "could not run {command:?}: {error}; the lean-unification feature requires elan/Lake"
        )
    });
    assert!(
        output.status.success(),
        "{command:?} failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn build_lean_backend() {
    use std::path::PathBuf;
    use std::process::Command;

    let host = std::env::var("HOST").unwrap();
    let target = std::env::var("TARGET").unwrap();
    assert_eq!(
        host, target,
        "lean-unification currently supports native host builds only"
    );
    assert!(
        target == "x86_64-unknown-linux-gnu",
        "lean-unification currently supports x86_64 Linux GNU; other native link configurations are not yet validated"
    );

    let crate_dir = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let lean_dir = crate_dir.join("../../lean").canonicalize().unwrap();
    let out_dir = PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    let lake = std::env::var_os("TAMARIN_LAKE").unwrap_or_else(|| "lake".into());
    println!("cargo:rerun-if-env-changed=TAMARIN_LAKE");
    println!("cargo:rerun-if-env-changed=LEAN_CC");
    println!("cargo:rerun-if-changed=native/lean_unification.c");
    for source in [
        "lean-toolchain",
        "lakefile.toml",
        "lake-manifest.json",
        "TamarinWire.lean",
        "TamarinRuntime.lean",
        "TamarinRuntime",
    ] {
        println!("cargo:rerun-if-changed={}", lean_dir.join(source).display());
    }

    // Local builds compile the runtime candidate and its imports. The required CI job
    // builds TamarinCI, which checks this exact candidate/export pair against
    // the fixed semantic contract and audits executable replacements.
    let archive_output = checked_output(
        Command::new(&lake)
            .current_dir(&lean_dir)
            .args(["query", "TamarinRuntime:static"]),
    );
    let archive_text = String::from_utf8(archive_output.stdout).expect("Lake output is UTF-8");
    let archive = PathBuf::from(archive_text.trim());
    assert!(
        archive.is_file(),
        "Lake did not return a native archive: {archive_text}"
    );
    let runtime_archive = out_dir.join("libtamarin_lean_runtime.a");
    std::fs::copy(archive, &runtime_archive).unwrap();

    // Lake's library archive contains only modules owned by TamarinRuntime.
    // Include precisely the imported reference modules and track their source
    // files for Cargo. The proof-only CI target stays outside the runtime.
    let imports = checked_output(
        Command::new(&lake)
            .current_dir(&lean_dir)
            .args(["query", "+TamarinRuntime:transImports"]),
    );
    let imports = String::from_utf8(imports.stdout).expect("Lake module names are UTF-8");
    let mut targets = Vec::new();
    for module in imports.lines().filter(|m| m.starts_with("Tamarin.")) {
        println!(
            "cargo:rerun-if-changed={}.lean",
            lean_dir.join(module.replace('.', "/")).display()
        );
        targets.push(format!("+{module}:o"));
    }
    if !targets.is_empty() {
        let objects = checked_output(
            Command::new(&lake)
                .current_dir(&lean_dir)
                .arg("query")
                .args(&targets),
        );
        let objects = String::from_utf8(objects.stdout).expect("Lake object paths are UTF-8");
        let paths: Vec<_> = objects.lines().collect();
        assert_eq!(paths.len(), targets.len(), "missing Lean reference object");
        // ar and rustc identify members by basename. For example both
        // Tamarin.ACBasis and TamarinRuntime.ACBasis compile to ACBasis.c.o.
        let mut ar = Command::new("ar");
        ar.arg("qs").arg(&runtime_archive);
        for (target, object) in targets.iter().zip(paths) {
            let module = target
                .strip_prefix('+')
                .unwrap()
                .strip_suffix(":o")
                .unwrap();
            let named = out_dir.join(format!("{module}.o"));
            std::fs::copy(object, &named).unwrap();
            ar.arg(named);
        }
        checked_output(&mut ar);
    }

    let prefix_output = checked_output(Command::new(&lake).current_dir(&lean_dir).args([
        "env",
        "lean",
        "--print-prefix",
    ]));
    let prefix = PathBuf::from(String::from_utf8(prefix_output.stdout).unwrap().trim());
    let shim = out_dir.join("lean_unification.o");
    checked_output(
        Command::new(&lake)
            .current_dir(&lean_dir)
            .args(["env", "leanc", "-O3", "-DNDEBUG", "-c"])
            .arg(crate_dir.join("native/lean_unification.c"))
            .arg("-o")
            .arg(&shim),
    );
    checked_output(
        Command::new("ar")
            .arg("crs")
            .arg(out_dir.join("libtamarin_lean_bridge.a"))
            .arg(shim),
    );

    // Lean and the prover each bundle mimalloc. They must not share allocator
    // globals or resolve each other's mi_* calls: versions and heap ownership
    // are independent. Namespace both definitions AND references throughout
    // the Lean-owned archives, including generated code and the C shim.
    // All copies stay in OUT_DIR; the installed toolchain remains untouched.
    let mut lean_archives = vec![
        out_dir.join("libtamarin_lean_bridge.a"),
        out_dir.join("libtamarin_lean_runtime.a"),
    ];
    for name in ["Std", "Init", "leanrt", "leancpp"] {
        let filename = format!("lib{name}.a");
        let copy = out_dir.join(&filename);
        std::fs::copy(prefix.join("lib/lean").join(filename), &copy).unwrap();
        lean_archives.push(copy);
    }
    let symbols = checked_output(
        Command::new("nm")
            .args(["-g", "--format=posix"])
            .args(&lean_archives),
    );
    let allocator_symbols: std::collections::BTreeSet<_> = std::str::from_utf8(&symbols.stdout)
        .expect("nm symbol names are UTF-8")
        .lines()
        .filter_map(|line| line.split_whitespace().next())
        .filter(|name| name.trim_start_matches('_').starts_with("mi_"))
        .collect();
    assert!(
        allocator_symbols.contains("mi_malloc"),
        "Lean allocator layout changed: review allocator isolation before linking"
    );
    let map = out_dir.join("lean_allocator_symbols.map");
    std::fs::write(
        &map,
        allocator_symbols
            .iter()
            .map(|name| format!("{name} tamarin_lean_alloc_{name}\n"))
            .collect::<String>(),
    )
    .unwrap();
    for archive in &lean_archives {
        checked_output(
            Command::new("objcopy")
                .arg(format!("--redefine-syms={}", map.display()))
                .arg(archive),
        );
    }

    println!("cargo:rustc-link-search=native={}", out_dir.display());
    println!(
        "cargo:rustc-link-search=native={}",
        prefix.join("lib/lean").display()
    );
    println!(
        "cargo:rustc-link-search=native={}",
        prefix.join("lib").display()
    );
    for library in [
        "tamarin_lean_bridge",
        "tamarin_lean_runtime",
        "Std",
        "Init",
        "leanrt",
        "leancpp",
        "c++",
        "c++abi",
        "gmp",
        "uv",
        "ssl",
        "crypto",
        "unwind",
    ] {
        println!("cargo:rustc-link-lib=static={library}");
    }
    for library in ["pthread", "dl", "m", "rt"] {
        println!("cargo:rustc-link-lib=dylib={library}");
    }
}
