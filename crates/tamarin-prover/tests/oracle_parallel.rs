//! Real oracle rendezvous: prove overlap and prompt failure without timing
//! speedup assumptions. The test executable doubles as the oracle subprocess.
#![cfg(unix)]

mod common;

use std::fs;
use std::io::{Read, Write};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Output, Stdio};
use std::time::{Duration, Instant};
use tempfile::TempDir;

const LEMMAS: &str = r#"
theory ParallelLemmas begin
rule Send: [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]
rule Recv: [ In(x) ] --[ R(x) ]-> []
lemma left: exists-trace "Ex k #i #j. S(k) @ i & R(k) @ j"
lemma right: exists-trace "Ex k #i #j. S(k) @ i & R(k) @ j"
end
"#;

const BRANCHES: &str = r#"
theory ParallelBranches begin
rule GenL: [ Fr(~x) ] --> [ L(~x) ]
rule GenR: [ Fr(~x) ] --> [ R(~x) ]
rule Left: [ L(x) ] --[ End(x) ]-> []
rule Right: [ R(x) ] --[ End(x) ]-> []
lemma test: "All x #i. End(x) @ i ==> F"
end
"#;

struct Fixture {
    dir: TempDir,
    child: Option<Child>,
    lemma_filter: Option<&'static str>,
}

impl Fixture {
    fn new(theory: &str) -> Self {
        let dir = tempfile::Builder::new()
            .permissions(fs::Permissions::from_mode(0o700))
            .tempdir()
            .unwrap();
        fs::write(dir.path().join("input.spthy"), theory).unwrap();
        let oracle = dir.path().join("oracle");
        fs::write(&oracle, "#!/bin/sh\nexport ORACLE_TEST_LEMMA=\"$1\"\nexec \"$ORACLE_TEST_EXE\" --exact oracle_helper --ignored --nocapture\n").unwrap();
        fs::set_permissions(oracle, fs::Permissions::from_mode(0o755)).unwrap();
        Self {
            dir,
            child: None,
            lemma_filter: None,
        }
    }

    fn run(&mut self, mode: &str, processors: usize) -> Output {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
        tamarin_utils::process::isolate_process_group(&mut cmd);
        if let Some(maude) = common::maude_arg() {
            cmd.arg(maude);
        }
        cmd.args(["--heuristic=o", "--oraclename=./oracle"])
            .current_dir(self.dir.path())
            .args(["--prove", "input.spthy"])
            .arg(format!("--processors={processors}"))
            .env("ORACLE_TEST_EXE", std::env::current_exe().unwrap())
            .env("ORACLE_TEST_DIR", self.dir.path())
            .env("ORACLE_TEST_MODE", mode)
            .env_remove("TAM_RS_NO_SOURCE_CACHE")
            .env_remove("TAM_RS_DISABLE_PARALLEL_EXPAND")
            .env_remove("TAM_PROVE_DEADLINE_MS")
            .stdout(Stdio::from(
                fs::File::create(self.dir.path().join("stdout")).unwrap(),
            ))
            .stderr(Stdio::from(
                fs::File::create(self.dir.path().join("stderr")).unwrap(),
            ));
        if mode == "deadline_branches" {
            cmd.env("TAM_PROVE_DEADLINE_MS", "3000");
        }
        if let Some(lemma) = self.lemma_filter {
            cmd.arg(format!("--lemma={lemma}"));
        }
        cmd.env(
            "ORACLE_TEST_RENDEZVOUS",
            if processors > 1 { "1" } else { "0" },
        );
        self.child = Some(cmd.spawn().unwrap());
        let deadline = Instant::now() + Duration::from_secs(30);
        let status = loop {
            if let Some(status) = self.child.as_mut().unwrap().try_wait().unwrap() {
                break status;
            }
            assert!(
                Instant::now() < deadline,
                "parallel oracle job hung: {}",
                fs::read_to_string(self.dir.path().join("stderr")).unwrap()
            );
            std::thread::sleep(Duration::from_millis(10));
        };
        self.child = None;
        Output {
            status,
            stdout: fs::read(self.dir.path().join("stdout")).unwrap(),
            stderr: fs::read(self.dir.path().join("stderr")).unwrap(),
        }
    }
}

fn assert_blocked_process_exited(dir: &Path) {
    let pid: i32 = fs::read_to_string(dir.join("blocked.pid"))
        .unwrap()
        .parse()
        .unwrap();
    assert!(pid > 0);
    assert_eq!(
        unsafe { libc::kill(pid, 0) },
        -1,
        "blocked subprocess survived"
    );
    assert_eq!(
        std::io::Error::last_os_error().raw_os_error(),
        Some(libc::ESRCH)
    );
}

impl Drop for Fixture {
    fn drop(&mut self) {
        if let Some(mut child) = self.child.take() {
            tamarin_utils::process::kill_process_group(&mut child);
            let _ = child.wait();
        }
    }
}

fn wait_file(path: &Path) {
    let deadline = Instant::now() + Duration::from_secs(15);
    while !path.exists() {
        assert!(
            Instant::now() < deadline,
            "timed out waiting for {}",
            path.display()
        );
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
#[ignore]
fn oracle_helper() {
    let dir = PathBuf::from(std::env::var_os("ORACLE_TEST_DIR").unwrap());
    let mode = std::env::var("ORACLE_TEST_MODE").unwrap();
    let lemma = std::env::var("ORACLE_TEST_LEMMA").unwrap();
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let side = if mode.ends_with("branches") {
        if input.contains("L(") {
            "left"
        } else if input.contains("R(") {
            "right"
        } else {
            ""
        }
    } else {
        lemma.as_str()
    };
    let rendezvous = std::env::var("ORACLE_TEST_RENDEZVOUS").unwrap() == "1";
    if mode != "plain" && !side.is_empty() {
        if mode == "capacity" {
            fs::write(dir.join(side), "").unwrap();
            for index in 0..8 {
                wait_file(&dir.join(format!("job{index}")));
            }
            return;
        }
        let blocked = (mode == "fail_lemmas" && side == "left")
            || (matches!(mode.as_str(), "fail_branches" | "solve_branches") && side == "right");
        if mode == "deadline_branches" {
            fs::write(dir.join(side), "").unwrap();
            if side == "left" {
                std::thread::sleep(Duration::from_millis(3300));
            } else {
                std::process::exit(23);
            }
        } else if blocked {
            let marker = dir.join("blocked.tmp");
            fs::write(&marker, std::process::id().to_string()).unwrap();
            fs::rename(marker, dir.join("blocked.pid")).unwrap();
            // On failure the fixture removes its private directory. Exit without
            // relying on a PID file to signal this process during teardown.
            let deadline = Instant::now() + Duration::from_secs(60);
            while dir.exists() {
                assert!(
                    Instant::now() < deadline,
                    "blocked oracle was not cancelled"
                );
                std::thread::sleep(Duration::from_millis(20));
            }
            return;
        } else if mode.starts_with("fail") {
            wait_file(&dir.join("blocked.pid"));
            std::process::exit(23);
        } else if mode == "skip_branches" {
            if side == "right" {
                fs::write(dir.join("right"), "ready").unwrap();
                std::process::exit(23);
            }
            if rendezvous {
                wait_file(&dir.join("right"));
            }
        } else if mode == "solve_branches" {
            if rendezvous {
                wait_file(&dir.join("blocked.pid"));
            }
        } else {
            fs::write(dir.join(side), "ready").unwrap();
            wait_file(&dir.join(if side == "left" { "right" } else { "left" }));
        }
    }
    let mut stdout = std::io::stdout().lock();
    for line in input.lines() {
        if let Some((index, _)) = line.split_once(':') {
            writeln!(stdout, "{index}").unwrap();
        }
    }
}

fn proof(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    common::normalize_stdout(&String::from_utf8_lossy(&output.stdout))
}

#[test]
fn oracle_branches_overlap_and_match_sequential_proofs() {
    if !common::maude_available() {
        return;
    }
    // With two workers, Right can reach Left's rendezvous only after the
    // other worker closes Middle and takes the third case.
    let branches = BRANCHES.replace(
        "rule Right:",
        "rule Middle: [ Missing(x)[no_precomp] ] --[ End(x) ]-> []\nrule Right:",
    );
    let theory = branches.replace(
        "end",
        "lemma unused: exists-trace \"Ex #i. End('unused') @ i\"\nend",
    );
    let witness = branches.replace(
        "\"All x #i. End(x) @ i ==> F\"",
        "exists-trace \"Ex x #i. End(x) @ i\"",
    );
    // These branches fork in the first depth round and reach L and R in a later one.
    let mut deep = witness.clone();
    for side in ["L", "R"] {
        let mut rules = String::new();
        let mut fact = side.to_string();
        for i in 1..=5 {
            let next = format!("{side}{i}");
            rules.push_str(&format!(
                "rule Step{next}: [ {fact}(x)[no_precomp] ] --> [ {next}(x) ]\n"
            ));
            fact = next;
        }
        deep = deep.replace(
            &format!("[ {side}(x) ]"),
            &format!("[ {fact}(x)[no_precomp] ]"),
        );
        deep = deep.replace("lemma test:", &format!("{rules}lemma test:"));
    }
    for (input, filter) in [
        (branches.as_str(), None),
        (witness.as_str(), None),
        (deep.as_str(), None),
        (theory.as_str(), Some("test")),
    ] {
        let mut fixture = Fixture::new(input);
        fixture.lemma_filter = filter;
        let parallel = proof(fixture.run("overlap_branches", 2));
        assert!(
            fixture.dir.path().join("left").exists() && fixture.dir.path().join("right").exists(),
            "both branch oracles must run for {input}"
        );
        assert_eq!(parallel, proof(fixture.run("plain", 1)), "{input}");
    }
}

#[test]
fn concurrent_proofs_report_each_saturation_pass_once() {
    if !common::maude_available() {
        return;
    }
    // The source lemma forces a second saturation pass for refined sources.
    let theory = include_str!("fixtures/cli_flags_tutorial.spthy")
        .replace("\nend\n", "\nlemma types [sources]: \"T\"\nend\n");
    let mut fixture = Fixture::new(&theory);
    for processors in [1, 4] {
        let output = fixture.run("plain", processors);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stderr = String::from_utf8(output.stderr).unwrap();
        let progress: Vec<_> = stderr
            .lines()
            .filter(|line| line.starts_with("[Saturating Sources]"))
            .collect();
        assert_eq!(
            progress,
            [
                "[Saturating Sources] Step 1 (Max 5)",
                "[Saturating Sources] Done",
                "[Saturating Sources] Done",
            ],
            "{processors} workers"
        );
    }
}

// Parallel runs build sources that a serial run may never need. That can
// change progress output, but not whether the run succeeds or what it proves.
#[test]
fn eager_sources_do_not_change_the_outcome() {
    if !common::maude_available() {
        return;
    }
    let theory = |sources: &str| {
        format!(
            "theory EagerSources begin\n\
             rule Send: [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]\n\
             rule Recv: [ In(x) ] --[ R(x) ]-> []\n\
             lemma a: \"T\"\n\
             lemma b: \"T\"\n\
             lemma types [sources]: \"{sources}\"\n\
             end\n"
        )
    };
    let mut sound = Fixture::new(&theory("All k #i. R(k) @ i ==> Ex #j. KU(k) @ j"));
    let serial = sound.run("plain", 1);
    let parallel = sound.run("plain", 4);
    assert!(serial.status.success() && parallel.status.success());
    assert_eq!(proof(serial), proof(parallel));

    let mut unguarded = Fixture::new(&theory("All x. not (Ex #i. R(x) @ i)"));
    for processors in [1, 4] {
        assert!(
            !unguarded.run("plain", processors).status.success(),
            "{processors} workers"
        );
    }
}

#[test]
fn oracle_error_cancels_blocked_lemma_and_branch_without_masking_failure() {
    if !common::maude_available() {
        return;
    }
    for (theory, mode) in [(LEMMAS, "fail_lemmas"), (BRANCHES, "fail_branches")] {
        let mut fixture = Fixture::new(theory);
        let output = fixture.run(mode, 2);
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty(), "failed proof leaked output");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("oracle process exited with status") && stderr.contains("23"),
            "{stderr}"
        );
        assert!(
            !stderr.contains("request cancelled"),
            "cancellation masked original error: {stderr}"
        );
        assert_blocked_process_exited(fixture.dir.path());
    }
}

#[test]
fn earlier_counterexample_discards_failed_or_blocked_speculative_oracle() {
    if !common::maude_available() {
        return;
    }
    for (mode, marker) in [
        ("skip_branches", "right"),
        ("solve_branches", "blocked.pid"),
    ] {
        let mut fixture = Fixture::new(BRANCHES);
        let serial = proof(fixture.run(mode, 1));
        assert!(
            !fixture.dir.path().join(marker).exists(),
            "serial DFS visited the later branch"
        );
        assert_eq!(proof(fixture.run(mode, 2)), serial, "{mode}");
        assert!(
            fixture.dir.path().join(marker).exists(),
            "{mode}: speculative oracle never ran"
        );
        if mode == "solve_branches" {
            assert_blocked_process_exited(fixture.dir.path());
        }
    }
}

#[test]
fn deadline_preserves_the_serial_prefix_without_starting_a_later_oracle() {
    if !common::maude_available() {
        return;
    }
    let mut serial = Fixture::new(BRANCHES);
    let expected = proof(serial.run("deadline_branches", 1));
    assert!(expected.contains("analysis incomplete"));
    let mut parallel = Fixture::new(BRANCHES);
    assert_eq!(proof(parallel.run("deadline_branches", 2)), expected);
    assert!(parallel.dir.path().join("left").exists());
    assert!(!parallel.dir.path().join("right").exists());
}

#[test]
fn cold_batch_can_run_eight_independent_oracles_at_once() {
    if !common::maude_available() {
        return;
    }
    let mut theory =
        String::from("theory Capacity begin\nrule Send: [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]\n");
    for index in 0..8 {
        theory.push_str(&format!(
            "lemma job{index}: exists-trace \"Ex k #i. S(k) @ i\"\n"
        ));
    }
    theory.push_str("end\n");
    let mut fixture = Fixture::new(&theory);
    let result = proof(fixture.run("capacity", 8));
    for index in 0..8 {
        assert!(
            fixture.dir.path().join(format!("job{index}")).exists(),
            "oracle job{index} never ran"
        );
    }
    assert_eq!(result.matches("(exists-trace): verified").count(), 8);
    assert_eq!(result, proof(fixture.run("plain", 1)));
}

#[test]
fn stalled_maude_startup_is_cancelled_when_the_batch_finishes_or_fails() {
    let Some(real) = tamarin_test_support::require_maude_path() else {
        return;
    };
    for restart in [false, true] {
        for fail in [false, true] {
            check_stalled_startup(&real, restart, fail);
        }
    }
}

fn check_stalled_startup(real: &str, restart: bool, fail: bool) {
    use std::sync::Arc;
    use tamarin_term::maude_proc::{MaudeHandle, MaudePool, SharedMaudeCaches};
    use tamarin_theory::prove::{ProverSession, ProverSessionOptions};

    let input = r#"theory T begin
        heuristic: {missing}
        rule Send: [ Fr(~k) ] --[ S(~k) ]-> [ Out(~k) ]
        lemma left: "T"
        lemma problem: exists-trace "Ex k #i. S(k) @ i"
        lemma right: "T" by sorry
        end"#;
    let scratch = tempfile::tempdir().unwrap();
    let dir = scratch.path();
    let helper = dir.join("maude");
    // Maude finds its prelude beside the path it was started by.
    let real_path = fs::canonicalize(real).unwrap();
    fs::write(
        &helper,
        format!("#!/bin/sh\nexec '{}' \"$@\"\n", real_path.display()),
    )
    .unwrap();
    fs::set_permissions(&helper, fs::Permissions::from_mode(0o755)).unwrap();
    let theory = Arc::new(
        tamarin_theory::elaborate::elaborate(&tamarin_parser::parse_theory(input, &[]).unwrap())
            .unwrap(),
    );
    let caches = Arc::new(SharedMaudeCaches::default());
    let pool = Arc::new(
        MaudePool::new(
            helper.to_str().unwrap(),
            theory.signature.clone(),
            if restart { 1 } else { 2 },
            caches.clone(),
        )
        .unwrap(),
    );
    let primary = MaudeHandle::start_with_caches(real, theory.signature.clone(), caches).unwrap();
    let session = ProverSession::build(
        theory,
        primary,
        ProverSessionOptions {
            maude_pool: Some(pool.clone()),
            ..Default::default()
        },
    )
    .unwrap();

    // Keeping the eager lease forces a fresh start. Returning it with its
    // process retired forces a restart through the same executable.
    let _held = if restart {
        pool.acquire().kill_subprocess();
        None
    } else {
        Some(pool.acquire())
    };
    fs::remove_file(&helper).unwrap();
    fs::write(
        &helper,
        r#"#!/bin/sh
cd "${0%/*}" || exit 1
printf %s "$$" > blocked.tmp
mv blocked.tmp blocked.pid
sleep 15
touch startup-resumed
"#,
    )
    .unwrap();
    fs::set_permissions(&helper, fs::Permissions::from_mode(0o755)).unwrap();
    let marker = dir.join("blocked.pid");
    let workers = rayon::ThreadPoolBuilder::new()
        .num_threads(2)
        .build()
        .unwrap();
    // One selected lemma and a stored replay exercise cold proof admission.
    let selected = if fail { "problem" } else { "left" };
    let result = workers.install(|| {
        session.map_lemma_proofs(
            |lemma| (lemma.name == selected).then_some(usize::MAX),
            move |lemma, _| {
                if lemma.name == "left" {
                    wait_file(&marker);
                }
                std::thread::current().id()
            },
        )
    });
    if fail {
        // The last lemma is still queued, so only the peer error can cancel startup.
        let error = result.unwrap_err().to_string();
        assert!(error.contains("No tactic has been written"), "{error}");
    } else {
        let threads = result.unwrap();
        assert_eq!(threads.len(), 3);
        assert!(threads.iter().all(|id| *id == threads[0]));
    }
    assert!(!dir.join("startup-resumed").exists());
    assert_blocked_process_exited(dir);
}
