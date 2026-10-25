//! Real subprocess tests, also run on macOS. A shell shim launches this test
//! executable as a fake Maude, so no Python, real Maude, or large proof is needed.
#![cfg(any(target_os = "linux", target_os = "macos"))]

use std::fs::{self, File};
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::PathBuf;
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

static NEXT: AtomicUsize = AtomicUsize::new(0);

struct Fixture {
    dir: PathBuf,
    child: Option<Child>,
}

impl Fixture {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!(
            "tamarin-memory-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&dir).unwrap();
        fs::write(dir.join("input.spthy"), "theory MemoryTest begin\nend\n").unwrap();
        let shim = dir.join("maude");
        fs::write(
            &shim,
            "#!/bin/sh\nexec \"$MEMORY_TEST_EXE\" --exact memory_helper --ignored --nocapture\n",
        )
        .unwrap();
        fs::set_permissions(shim, fs::Permissions::from_mode(0o755)).unwrap();
        Self { dir, child: None }
    }

    fn command(&self) -> Command {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_tamarin-rs"));
        cmd.current_dir(&self.dir)
            .env_remove("TAMARIN_MEMORY_SUPERVISOR_PID")
            .env_remove("MIMALLOC_RESERVE_OS_MEMORY")
            .env_remove("MIMALLOC_DISALLOW_OS_ALLOC");
        cmd
    }

    fn start(&mut self, mode: &str, limit_flags: &[&str]) {
        self.start_with_stderr(mode, limit_flags, Stdio::piped());
    }

    fn start_with_stderr(&mut self, mode: &str, limit_flags: &[&str], stderr: Stdio) {
        let mut cmd = self.command();
        cmd.args(limit_flags)
            .args(["--processors=1", "--prove", "input.spthy"])
            .arg(format!("--with-maude={}", self.dir.join("maude").display()))
            .env("MEMORY_TEST_EXE", std::env::current_exe().unwrap())
            .env("MEMORY_TEST_DIR", &self.dir)
            .env("MEMORY_TEST_MODE", mode)
            .stdout(Stdio::piped())
            .stderr(stderr);
        self.child = Some(cmd.spawn().unwrap());
    }

    fn wait_file(&self, name: &str) {
        let until = Instant::now() + Duration::from_secs(15);
        while !self.dir.join(name).exists() {
            assert!(Instant::now() < until, "fixture never created {name}");
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    fn finish(&mut self) -> Output {
        let until = Instant::now() + Duration::from_secs(15);
        while self.child.as_mut().unwrap().try_wait().unwrap().is_none() {
            assert!(Instant::now() < until, "supervisor hung");
            std::thread::sleep(Duration::from_millis(10));
        }
        self.child.take().unwrap().wait_with_output().unwrap()
    }

    fn pids(&self) -> Vec<libc::pid_t> {
        fs::read_dir(&self.dir)
            .unwrap()
            .filter_map(|entry| {
                let path = entry.unwrap().path();
                (path.extension().and_then(|s| s.to_str()) == Some("pid"))
                    .then(|| fs::read_to_string(path).unwrap().parse().unwrap())
            })
            .collect()
    }

    fn assert_helpers_gone(&self) {
        let pids = self.pids();
        assert!(pids.len() >= 3, "fixture did not start its process tree");
        let until = Instant::now() + Duration::from_secs(5);
        loop {
            let alive: Vec<_> = pids
                .iter()
                .filter(|&&pid| unsafe { libc::kill(pid, 0) } == 0)
                .collect();
            if alive.is_empty() {
                return;
            }
            assert!(Instant::now() < until, "helpers survived: {alive:?}");
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        // Keep failed tests bounded, even if supervision itself is broken.
        for pid in self.pids() {
            unsafe { libc::kill(pid, libc::SIGKILL) };
        }
        if let Some(mut child) = self.child.take() {
            for worker in child_pids(child.id() as libc::pid_t) {
                unsafe { libc::kill(-worker, libc::SIGKILL) };
            }
            let _ = child.kill();
            let _ = child.wait();
        }
        let _ = fs::remove_dir_all(&self.dir);
    }
}

#[cfg(target_os = "linux")]
fn child_pids(pid: libc::pid_t) -> Vec<libc::pid_t> {
    fs::read_to_string(format!("/proc/{pid}/task/{pid}/children"))
        .unwrap_or_default()
        .split_whitespace()
        .map(|pid| pid.parse().unwrap())
        .collect()
}

#[cfg(target_os = "macos")]
fn child_pids(pid: libc::pid_t) -> Vec<libc::pid_t> {
    let mut pids: Vec<libc::pid_t> = vec![0; 64];
    let count = unsafe {
        libc::proc_listchildpids(
            pid,
            pids.as_mut_ptr().cast(),
            (pids.len() * std::mem::size_of::<libc::pid_t>()) as libc::c_int,
        )
    };
    assert!(count >= 0 && (count as usize) < pids.len());
    pids.truncate(count as usize);
    pids
}

fn close_on_exec(fd: libc::c_int) {
    assert_ne!(
        unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) },
        -1
    );
}

fn full_stderr_pipe() -> (File, File) {
    let mut fds = [0; 2];
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    for fd in fds {
        close_on_exec(fd);
    }
    let reader = unsafe { File::from_raw_fd(fds[0]) };
    let mut writer = unsafe { File::from_raw_fd(fds[1]) };
    let flags = unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_GETFL) };
    assert_ne!(
        unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) },
        -1
    );
    loop {
        match writer.write(&[b'x'; 4096]) {
            Ok(_) => {}
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
            Err(e) => panic!("fill stderr pipe: {e}"),
        }
    }
    assert_ne!(
        unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_SETFL, flags) },
        -1
    );
    (reader, writer)
}

fn wait_for_blocked_diagnostic(fixture: &mut Fixture) {
    // The worker blocks on its first stderr write; the supervisor eventually
    // blocks reporting the limit. Cleanup must precede that blocked report.
    std::thread::sleep(Duration::from_millis(300));
    let supervisor = fixture.child.as_ref().unwrap().id() as libc::pid_t;
    let until = Instant::now() + Duration::from_secs(5);
    while !child_pids(supervisor).is_empty() {
        assert!(
            Instant::now() < until,
            "stderr backpressure left the prover alive"
        );
        std::thread::sleep(Duration::from_millis(10));
    }
    assert!(fixture
        .child
        .as_mut()
        .unwrap()
        .try_wait()
        .unwrap()
        .is_none());
}

#[test]
fn blocked_stderr_cannot_delay_memory_enforcement() {
    let (mut reader, writer) = full_stderr_pipe();
    let mut fixture = Fixture::new();
    fixture.start_with_stderr("idle", &["--memory-limit=1"], writer.into());
    wait_for_blocked_diagnostic(&mut fixture);
    let drain = std::thread::spawn(move || {
        let mut bytes = Vec::new();
        reader.read_to_end(&mut bytes).unwrap();
        bytes
    });
    assert_eq!(fixture.finish().status.code(), Some(251));
    assert!(String::from_utf8_lossy(&drain.join().unwrap()).contains("memory limit exceeded"));
}

#[test]
fn blocked_diagnostic_remains_interruptible_after_cleanup() {
    for signal in [libc::SIGTERM, libc::SIGINT] {
        let (_reader, writer) = full_stderr_pipe();
        let mut fixture = Fixture::new();
        fixture.start_with_stderr("idle", &["--memory-limit=1"], writer.into());
        wait_for_blocked_diagnostic(&mut fixture);
        let supervisor = fixture.child.as_ref().unwrap().id() as libc::pid_t;
        assert_eq!(unsafe { libc::kill(supervisor, signal) }, 0);
        // Do not drain stderr: the signal must interrupt the blocked report.
        assert_eq!(fixture.finish().status.signal(), Some(signal));
    }
}

#[test]
fn closed_stderr_preserves_memory_limit_exit_status() {
    let mut fds = [0; 2];
    assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
    for fd in fds {
        close_on_exec(fd);
    }
    let reader = unsafe { File::from_raw_fd(fds[0]) };
    let writer = unsafe { File::from_raw_fd(fds[1]) };
    drop(reader);
    let mut fixture = Fixture::new();
    // Keep stdin open: the worker waits for input without writing to stderr,
    // so it cannot itself panic on EPIPE before the monitor stops it.
    fixture.child = Some(
        fixture
            .command()
            .args(["--memory-limit=1", "--parse-only", "/dev/stdin"])
            .stdin(Stdio::piped())
            .stderr(writer)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap(),
    );
    assert_eq!(fixture.finish().status.code(), Some(251));
}

#[test]
fn inherited_ignored_signals_survive_in_supervisor_and_worker() {
    for signal in [libc::SIGHUP, libc::SIGINT, libc::SIGTERM] {
        let mut fixture = Fixture::new();
        let mut command = fixture.command();
        command
            .args(["--memory-limit=1GiB", "--parse-only", "/dev/stdin"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        unsafe {
            command.pre_exec(move || {
                let mut action: libc::sigaction = std::mem::zeroed();
                action.sa_sigaction = libc::SIG_IGN;
                libc::sigemptyset(&mut action.sa_mask);
                if libc::sigaction(signal, &action, std::ptr::null_mut()) == -1 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        fixture.child = Some(command.spawn().unwrap());
        let supervisor = fixture.child.as_ref().unwrap().id() as libc::pid_t;
        let until = Instant::now() + Duration::from_secs(5);
        let workers = loop {
            let workers = child_pids(supervisor);
            if !workers.is_empty() {
                break workers;
            }
            assert!(Instant::now() < until, "supervisor did not start worker");
            std::thread::sleep(Duration::from_millis(10));
        };
        assert_eq!(workers.len(), 1);
        for pid in [supervisor, workers[0]] {
            assert_eq!(unsafe { libc::kill(pid, signal) }, 0);
        }
        let mut input = fixture.child.as_mut().unwrap().stdin.take().unwrap();
        input
            .write_all(b"theory IgnoredSignal begin\nend\n")
            .unwrap();
        drop(input);
        let output = fixture.finish();
        assert_eq!(
            output.status.code(),
            Some(0),
            "signal {signal}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

/// Start a command as foreground owner of a new controlling PTY, with TOSTOP
/// enabled. A background worker will stop on either input or output.
fn spawn_terminal(mut command: Command) -> (Child, File) {
    let mut master = 0;
    let mut slave = 0;
    assert_eq!(
        unsafe {
            libc::openpty(
                &mut master,
                &mut slave,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            )
        },
        0
    );
    close_on_exec(master);
    close_on_exec(slave);
    let master = unsafe { File::from_raw_fd(master) };
    let slave = unsafe { File::from_raw_fd(slave) };
    let mut term: libc::termios = unsafe { std::mem::zeroed() };
    assert_eq!(unsafe { libc::tcgetattr(slave.as_raw_fd(), &mut term) }, 0);
    term.c_lflag |= libc::TOSTOP;
    assert_eq!(
        unsafe { libc::tcsetattr(slave.as_raw_fd(), libc::TCSANOW, &term) },
        0
    );
    command
        .stdin(slave.try_clone().unwrap())
        .stdout(slave.try_clone().unwrap())
        .stderr(slave);
    unsafe {
        command.pre_exec(|| {
            if libc::setsid() == -1 || libc::ioctl(0, libc::TIOCSCTTY as _, 0) == -1 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    (command.spawn().unwrap(), master)
}

#[test]
fn monitored_job_can_read_and_write_inherited_terminal_streams() {
    for input in ["input.spthy", "/dev/stdin"] {
        let mut fixture = Fixture::new();
        let mut command = fixture.command();
        command.args(["--memory-limit=1GiB", "--parse-only", input]);
        let (child, mut terminal) = spawn_terminal(command);
        fixture.child = Some(child);
        if input == "/dev/stdin" {
            terminal
                .write_all(b"theory TerminalTest begin\nend\n\x04")
                .unwrap();
        }
        assert!(fixture.finish().status.success(), "terminal input: {input}");
    }
}

fn wait_stopped(pid: libc::pid_t) {
    let until = Instant::now() + Duration::from_secs(5);
    loop {
        let mut status = 0;
        let result = unsafe { libc::waitpid(pid, &mut status, libc::WUNTRACED | libc::WNOHANG) };
        assert!(result >= 0);
        if result == pid {
            assert!(libc::WIFSTOPPED(status));
            return;
        }
        assert!(Instant::now() < until, "supervisor did not suspend");
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn terminal_ctrl_z_stops_supervisor_and_resumes_worker() {
    let mut fixture = Fixture::new();
    let mut command = fixture.command();
    command.args(["--memory-limit=1GiB", "--parse-only", "/dev/stdin"]);
    let (child, mut terminal) = spawn_terminal(command);
    let supervisor = child.id() as libc::pid_t;
    fixture.child = Some(child);
    let until = Instant::now() + Duration::from_secs(5);
    while child_pids(supervisor).is_empty() {
        assert!(Instant::now() < until, "worker did not start");
        std::thread::sleep(Duration::from_millis(10));
    }
    terminal.write_all(b"\x1a").unwrap(); // Terminal-generated SIGTSTP.
    wait_stopped(supervisor);
    assert_eq!(unsafe { libc::tcgetpgrp(terminal.as_raw_fd()) }, supervisor);
    assert_eq!(unsafe { libc::kill(supervisor, libc::SIGCONT) }, 0);
    terminal
        .write_all(b"theory ResumeTest begin\nend\n\x04")
        .unwrap();
    assert!(fixture.finish().status.success());
}

#[test]
fn monitoring_does_not_steal_the_terminal_from_a_pipeline() {
    let mut fixture = Fixture::new();
    let mut command = Command::new("/bin/bash");
    // Use a clean interactive shell so it establishes terminal job control at
    // startup, as a user's shell would.
    command.current_dir(&fixture.dir)
        .args(["--noprofile", "--norc", "-i", "-c", "\"$1\" --memory-limit=1GiB --parse-only input.spthy | cat; printf '\\nPIPELINE_DONE\\n'", "monitor-pipeline"])
        .arg(env!("CARGO_BIN_EXE_tamarin-rs"));
    let (child, mut terminal) = spawn_terminal(command);
    fixture.child = Some(child);
    assert!(fixture.finish().status.success());
    let mut output = Vec::new();
    let mut buffer = [0u8; 4096];
    loop {
        match terminal.read(&mut buffer) {
            Ok(0) => break,
            Ok(n) => output.extend_from_slice(&buffer[..n]),
            Err(e) if e.raw_os_error() == Some(libc::EIO) => break, // Linux PTY EOF.
            Err(e) => panic!("read pipeline terminal: {e}"),
        }
    }
    let output = String::from_utf8_lossy(&output);
    assert!(
        output.contains("theory MemoryTest"),
        "lost pipeline output: {output}"
    );
    assert!(
        output.contains("PIPELINE_DONE"),
        "pipeline did not finish: {output}"
    );
    assert!(
        !output.contains("Stopped"),
        "pipeline was stopped: {output}"
    );
}

#[test]
fn successful_and_failed_runs_preserve_output_and_status() {
    let fixture = Fixture::new();
    for input in ["input.spthy", "missing.spthy"] {
        let baseline = fixture
            .command()
            .args(["--parse-only", input])
            .output()
            .unwrap();
        assert_eq!(baseline.status.success(), input == "input.spthy");
        for flags in [
            vec!["--memory-limit=1GiB"],
            vec!["+RTS", "-N1", "-M1G", "-RTS"],
            vec!["--memory-limit=1", "+RTS", "-M0", "-RTS"],
        ] {
            let output = fixture
                .command()
                .args(&flags)
                .args(["--parse-only", input])
                .output()
                .unwrap();
            assert_eq!(output.status, baseline.status, "{flags:?}");
            assert_eq!(output.stdout, baseline.stdout, "{flags:?}");
            assert_eq!(output.stderr, baseline.stderr, "{flags:?}");
        }
    }
}

#[test]
fn help_does_not_start_a_limited_job() {
    let fixture = Fixture::new();
    let out = fixture
        .command()
        .args(["--memory-limit=1", "--help"])
        .output()
        .unwrap();
    assert!(out.status.success());
    assert!(out.stderr.is_empty());
    assert!(String::from_utf8_lossy(&out.stdout).contains("--memory-limit"));
}

#[test]
fn combined_descendant_memory_trips_limit_and_cleans_up() {
    for flags in [
        vec!["--memory-limit=128MiB"],
        vec!["+RTS", "-M128M", "-RTS"],
    ] {
        let mut fixture = Fixture::new();
        fixture.start("allocate", &flags);
        let out = fixture.finish();
        assert_eq!(
            out.status.code(),
            Some(251),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(String::from_utf8_lossy(&out.stderr).contains("memory limit exceeded"));
        fixture.assert_helpers_gone();
    }
}

#[test]
fn signals_forward_and_escalate_for_unresponsive_helpers() {
    for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP, libc::SIGQUIT] {
        let mut fixture = Fixture::new();
        fixture.start("idle", &["--memory-limit=1GiB"]);
        fixture.wait_file("ready");
        assert_eq!(
            unsafe { libc::kill(fixture.child.as_ref().unwrap().id() as i32, signal) },
            0
        );
        let out = fixture.finish();
        assert_eq!(
            out.status.code(),
            Some(128 + signal),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        fixture.assert_helpers_gone();
    }
}

#[test]
fn worker_crash_cleans_up_orphaned_helpers() {
    let mut fixture = Fixture::new();
    fixture.start("idle", &["--memory-limit=1GiB"]);
    fixture.wait_file("ready");
    let worker: i32 = fs::read_to_string(fixture.dir.join("worker.pid"))
        .unwrap()
        .parse()
        .unwrap();
    assert_eq!(unsafe { libc::kill(worker, libc::SIGKILL) }, 0);
    let out = fixture.finish();
    assert_eq!(out.status.code(), Some(137));
    fixture.assert_helpers_gone();
}

#[test]
fn suspending_supervisor_also_suspends_helpers() {
    let mut fixture = Fixture::new();
    fixture.start("idle", &["--memory-limit=1GiB"]);
    fixture.wait_file("ready");
    fixture.wait_file("first.ticks");
    let pid = fixture.child.as_ref().unwrap().id() as libc::pid_t;
    assert_eq!(unsafe { libc::kill(pid, libc::SIGTSTP) }, 0);
    wait_stopped(pid);
    std::thread::sleep(Duration::from_millis(100));
    let before = fs::read(fixture.dir.join("first.ticks")).unwrap();
    std::thread::sleep(Duration::from_millis(200));
    assert_eq!(fs::read(fixture.dir.join("first.ticks")).unwrap(), before);
    assert_eq!(unsafe { libc::kill(pid, libc::SIGCONT) }, 0);
    let until = Instant::now() + Duration::from_secs(5);
    while fs::read(fixture.dir.join("first.ticks")).unwrap() == before {
        assert!(Instant::now() < until, "helpers did not resume");
        std::thread::sleep(Duration::from_millis(10));
    }
    assert_eq!(unsafe { libc::kill(pid, libc::SIGTERM) }, 0);
    assert_eq!(fixture.finish().status.code(), Some(143));
    fixture.assert_helpers_gone();
}

// Invoked only in subprocesses by the fake Maude shell shim. Rust's test
// harness supplies a convenient portable helper executable for these tests.
#[test]
#[ignore]
fn memory_helper() {
    let dir = PathBuf::from(std::env::var_os("MEMORY_TEST_DIR").unwrap());
    let role = std::env::var("MEMORY_TEST_ROLE").unwrap_or_else(|_| "parent".into());
    for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP, libc::SIGQUIT] {
        unsafe { libc::signal(signal, libc::SIG_IGN) };
    }
    fs::write(
        dir.join(format!("{role}.pid")),
        std::process::id().to_string(),
    )
    .unwrap();
    let allocation = if role == "parent" {
        fs::write(
            dir.join("worker.pid"),
            unsafe { libc::getppid() }.to_string(),
        )
        .unwrap();
        let mut children = Vec::new();
        for role in ["first", "second"] {
            children.push(
                Command::new(std::env::current_exe().unwrap())
                    .args(["--exact", "memory_helper", "--ignored", "--nocapture"])
                    .env("MEMORY_TEST_ROLE", role)
                    .spawn()
                    .unwrap(),
            );
        }
        while !dir.join("first.pid").exists() || !dir.join("second.pid").exists() {
            std::thread::sleep(Duration::from_millis(5));
        }
        fs::write(dir.join("ready"), "").unwrap();
        for mut child in children {
            let _ = child.wait();
        }
        Vec::new()
    } else if std::env::var("MEMORY_TEST_MODE").unwrap() == "allocate" {
        // Each descendant alone stays below the limit; together they exceed
        // it. Touch every page and retain the data to ensure real RSS growth.
        vec![0xa5u8; 96 * 1024 * 1024]
    } else {
        Vec::new()
    };
    let mut ticks = 0u64;
    loop {
        std::hint::black_box(&allocation);
        ticks += 1;
        fs::write(dir.join(format!("{role}.ticks")), ticks.to_string()).unwrap();
        std::thread::sleep(Duration::from_millis(100));
    }
}
