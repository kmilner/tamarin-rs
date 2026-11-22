//! Subprocess output with cancellation, pipe draining, and child cleanup.

use crate::cancellation;
use std::io::{self, Read, Write};
use std::process::{Child, Command, ExitStatus, Output, Stdio};
use std::sync::{Arc, Mutex};

fn interrupted() -> io::Error {
    io::Error::new(io::ErrorKind::Interrupted, "request cancelled")
}

/// Give a subprocess its own process group so wrappers and their children
/// can be stopped together. On non-Unix platforms only the direct child is killed.
pub fn isolate_process_group(command: &mut Command) {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    #[cfg(not(unix))]
    let _ = command;
}

/// Kill a child started with `isolate_process_group`, including descendants
/// holding its pipes. The caller must still own the unreaped child: reaping
/// first would allow its PID (and thus process group ID) to be reused.
pub fn kill_process_group(child: &mut Child) {
    #[cfg(unix)]
    unsafe {
        libc::kill(-(child.id() as i32), libc::SIGKILL);
    }
    let _ = child.kill();
}

/// Check readiness without releasing a Unix process group leader's PID.
pub fn child_is_running(child: &mut Child) -> io::Result<bool> {
    std::cfg_select! {
        unix => child_has_exited(child.id(), true).map(|exited| !exited),
        _ => child.try_wait().map(|status| status.is_none()),
    }
}

#[cfg(unix)]
fn child_has_exited(pid: u32, nonblocking: bool) -> io::Result<bool> {
    std::cfg_select! {
        any(target_os = "linux", target_os = "android", target_vendor = "apple",
            target_os = "freebsd", target_os = "dragonfly", target_os = "netbsd",
            target_os = "openbsd", target_os = "solaris", target_os = "illumos",
            target_os = "aix", target_os = "haiku", target_os = "hurd",
            target_os = "nto", target_os = "fuchsia") => {
            let flags = libc::WEXITED | libc::WNOWAIT | if nonblocking { libc::WNOHANG } else { 0 };
            loop {
                let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::zeroed();
                let result = unsafe {
                    libc::waitid(libc::P_PID, pid as libc::id_t, info.as_mut_ptr(), flags)
                };
                if result == 0 {
                    // waitid reports SIGCHLD on exit. With WNOHANG, zero means
                    // that no event is ready. WNOWAIT preserves the process group.
                    return Ok(unsafe { info.assume_init().si_signo != 0 });
                }
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
        _ => {
            // Without a non-reaping probe, leave the slot for callers that can
            // perform startup. A reaped PID is unsafe for group cleanup.
            let _ = (pid, nonblocking);
            Err(io::ErrorKind::Unsupported.into())
        }
    }
}

struct ChildState {
    child: Child,
    reaped: bool,
}
struct ChildGuard(Mutex<ChildState>);
impl ChildGuard {
    fn kill(&self) {
        let mut state = self.0.lock().unwrap();
        if state.reaped {
            return;
        }
        kill_process_group(&mut state.child);
    }

    fn wait(&self, cancellable: bool) -> io::Result<ExitStatus> {
        if cancellable {
            self.wait_until_exited()?;
        }
        let mut state = self.0.lock().unwrap();
        let status = state.child.wait()?;
        state.reaped = true;
        Ok(status)
    }

    #[cfg(any(target_os = "linux", target_vendor = "apple"))]
    fn wait_until_exited(&self) -> io::Result<()> {
        let pid = self.0.lock().unwrap().child.id();
        child_has_exited(pid, false).map(|_| ())
    }

    // Preserve the portable cancellation path on other hosts. Uncancellable
    // commands always use the blocking Child::wait above, on every platform.
    #[cfg(not(any(target_os = "linux", target_vendor = "apple")))]
    fn wait_until_exited(&self) -> io::Result<()> {
        loop {
            cancellation::check().map_err(|_| interrupted())?;
            let mut state = self.0.lock().unwrap();
            if state.child.try_wait()?.is_some() {
                state.reaped = true;
                return Ok(());
            }
            drop(state);
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
}
impl Drop for ChildGuard {
    fn drop(&mut self) {
        self.kill();
        let _ = self.0.get_mut().unwrap().child.wait();
    }
}

// Service both directions on the calling worker so the lifetime of a pipe
// held by another process cannot prevent this request from being cancelled.
#[cfg(unix)]
fn exchange(
    stdin: impl std::os::fd::AsFd + Write,
    mut stdout: impl std::os::fd::AsFd + Read,
    mut input: &[u8],
) -> io::Result<Vec<u8>> {
    use rustix::event::{poll, PollFd, PollFlags};
    use rustix::fs::{fcntl_getfl, fcntl_setfl, OFlags};

    for fd in [stdin.as_fd(), stdout.as_fd()] {
        fcntl_setfl(fd, fcntl_getfl(fd)? | OFlags::NONBLOCK)?;
    }
    let wake = cancellation::current()
        .map(|token| -> io::Result<_> {
            let (reader, writer) = io::pipe()?;
            let registration = token.on_cancel(move || {
                let _ = (&writer).write_all(&[1]);
            });
            Ok((registration, reader))
        })
        .transpose()?;
    let mut stdin = Some(stdin);
    let mut bytes = Vec::new();
    let mut reading = true;
    let mut buf = [0; 8192];
    loop {
        cancellation::check().map_err(|_| interrupted())?;
        if input.is_empty() {
            stdin.take();
        }
        if stdin.is_none() && !reading {
            return Ok(bytes);
        }
        let mut fds = Vec::with_capacity(3);
        if reading {
            fds.push(PollFd::new(&stdout, PollFlags::IN));
        }
        if let Some(stdin) = &stdin {
            fds.push(PollFd::new(stdin, PollFlags::OUT));
        }
        if let Some((_, reader)) = &wake {
            fds.push(PollFd::new(reader, PollFlags::IN));
        }
        match poll(&mut fds, None) {
            Err(rustix::io::Errno::INTR) => continue,
            result => result?,
        };
        cancellation::check().map_err(|_| interrupted())?;
        let read = reading && !fds[0].revents().is_empty();
        let write = stdin.is_some() && !fds[usize::from(reading)].revents().is_empty();
        drop(fds);
        if read {
            match stdout.read(&mut buf) {
                Ok(0) => reading = false,
                Ok(n) => bytes.extend_from_slice(&buf[..n]),
                Err(e) if retry_io(&e) => continue,
                Err(e) => return Err(e),
            }
        }
        if write {
            match stdin.as_mut().unwrap().write(input) {
                Ok(0) => return Err(io::ErrorKind::WriteZero.into()),
                Ok(n) => input = &input[n..],
                Err(e) if retry_io(&e) => continue,
                // The child stopped reading. Like HS `readProcess`, keep
                // collecting whatever it writes before it exits.
                Err(e) if e.kind() == io::ErrorKind::BrokenPipe => input = &[],
                Err(e) => return Err(e),
            }
        }
    }
}

#[cfg(unix)]
fn retry_io(error: &io::Error) -> bool {
    matches!(
        error.kind(),
        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
    )
}

// Windows pipe handles support nonblocking writes and querying the number
// of bytes available to the sole reader. Observe cancellation between transfers.
#[cfg(windows)]
fn exchange(
    stdin: impl std::os::windows::io::AsRawHandle + Write,
    mut stdout: impl std::os::windows::io::AsRawHandle + Read,
    mut input: &[u8],
) -> io::Result<Vec<u8>> {
    use std::ptr::{null, null_mut};
    use windows_sys::Win32::Foundation::{ERROR_BROKEN_PIPE, ERROR_PIPE_NOT_CONNECTED};
    use windows_sys::Win32::System::Pipes::{PeekNamedPipe, SetNamedPipeHandleState, PIPE_NOWAIT};
    // The handle remains owned here and the optional parameters are unused.
    if !input.is_empty()
        && unsafe { SetNamedPipeHandleState(stdin.as_raw_handle(), &PIPE_NOWAIT, null(), null()) }
            == 0
    {
        return Err(io::Error::last_os_error());
    }
    let mut stdin = Some(stdin);
    let mut reading = true;
    let mut bytes = Vec::new();
    let mut buf = [0; 8192];
    loop {
        cancellation::check().map_err(|_| interrupted())?;
        if input.is_empty() {
            stdin.take();
        }
        if stdin.is_none() && !reading {
            return Ok(bytes);
        }
        let mut progress = false;
        if reading {
            let mut available = 0;
            // This worker owns the only reader, so bytes reported here remain available.
            if unsafe {
                PeekNamedPipe(
                    stdout.as_raw_handle(),
                    null_mut(),
                    0,
                    null_mut(),
                    &mut available,
                    null_mut(),
                )
            } == 0
            {
                let error = io::Error::last_os_error();
                match error.raw_os_error().map(|code| code as u32) {
                    Some(ERROR_BROKEN_PIPE | ERROR_PIPE_NOT_CONNECTED) => reading = false,
                    _ => return Err(error),
                }
            } else if available > 0 {
                let len = buf.len().min(available as usize);
                let n = stdout.read(&mut buf[..len])?;
                bytes.extend_from_slice(&buf[..n]);
                reading = n != 0;
                progress = true;
            }
        }
        if let Some(writer) = &mut stdin {
            // A byte-mode pipe returns a short (possibly zero) write when full.
            let n = writer.write(input)?;
            input = &input[n..];
            progress |= n > 0;
        }
        if !progress && (reading || !input.is_empty()) {
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
    }
}

#[cfg(not(any(unix, windows)))]
fn exchange(
    mut stdin: std::process::ChildStdin,
    mut stdout: std::process::ChildStdout,
    input: &[u8],
    child: &Arc<ChildGuard>,
) -> io::Result<Vec<u8>> {
    std::thread::scope(|scope| {
        let writer = scope.spawn(move || {
            let result = stdin.write_all(input);
            if result.is_err() {
                child.kill();
            }
            result
        });
        let mut bytes = Vec::new();
        let read = stdout.read_to_end(&mut bytes);
        if read.is_err() {
            child.kill();
        }
        writer.join().expect("stdin writer panicked")?;
        read?;
        Ok(bytes)
    })
}

/// Run a command with piped stdin/stdout and inherited stderr. The callback
/// only owns this invocation's child, never a subsequent request's process.
pub fn output(command: &mut Command, input: &[u8]) -> io::Result<Output> {
    cancellation::check().map_err(|_| interrupted())?;
    isolate_process_group(command);
    let mut child = command
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()?;
    let stdin = child.stdin.take().expect("piped stdin");
    let stdout = child.stdout.take().expect("piped stdout");
    let child = Arc::new(ChildGuard(Mutex::new(ChildState {
        child,
        reaped: false,
    })));
    let killing_child = child.clone();
    let registration =
        cancellation::current().map(|token| token.on_cancel(move || killing_child.kill()));
    #[cfg(any(unix, windows))]
    let bytes = exchange(stdin, stdout, input);
    #[cfg(not(any(unix, windows)))]
    let bytes = exchange(stdin, stdout, input, &child);
    cancellation::check().map_err(|_| interrupted())?;
    let bytes = bytes?;
    let status = child.wait(registration.is_some())?;
    drop(registration);
    cancellation::check().map_err(|_| interrupted())?;
    Ok(Output {
        status,
        stdout: bytes,
        stderr: Vec::new(),
    })
}

#[cfg(all(test, any(unix, windows)))]
#[test]
fn cancellation_releases_pipes_held_by_an_independent_process() {
    use crate::cancellation::{CancellationGuard, CancellationToken};
    use std::{sync::mpsc, time::Duration};

    let (mut remote_stdin, stdin) = io::pipe().unwrap();
    let (stdout, remote_stdout) = io::pipe().unwrap();
    let token = CancellationToken::default();
    let worker_token = token.clone();
    let (done, result) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        let _guard = CancellationGuard::new(Some(worker_token));
        done.send(exchange(stdin, stdout, &vec![0; 1024 * 1024]))
            .unwrap();
    });
    remote_stdin.read_exact(&mut [0]).unwrap();
    token.cancel();
    let stopped = result.recv_timeout(Duration::from_secs(5));
    drop((remote_stdin, remote_stdout));
    worker.join().unwrap();
    assert_eq!(
        stopped.unwrap().unwrap_err().kind(),
        io::ErrorKind::Interrupted
    );
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use crate::cancellation::{CancellationGuard, CancellationToken};
    use std::sync::mpsc;
    use std::time::Duration;

    #[test]
    fn output_waits_for_exit_after_stdout_closes() {
        for token in [None, Some(CancellationToken::default())] {
            let _guard = CancellationGuard::new(token);
            let result = output(
                Command::new("sh").args(["-c", "cat; exec 1>&-; sleep 0.01; exit 7"]),
                b"oracle result\n",
            )
            .unwrap();
            assert_eq!(result.stdout, b"oracle result\n");
            assert_eq!(result.status.code(), Some(7));
        }
    }

    #[test]
    fn cancellation_interrupts_exit_wait() {
        let mut command = Command::new("sh");
        command.args(["-c", "sleep 60 & wait"]);
        isolate_process_group(&mut command);
        let child = Arc::new(ChildGuard(Mutex::new(ChildState {
            child: command.spawn().unwrap(),
            reaped: false,
        })));
        let waiting_child = child.clone();
        let (done_tx, done_rx) = mpsc::channel();
        let waiter = std::thread::spawn(move || {
            done_tx.send(waiting_child.wait(true).unwrap()).unwrap();
        });
        assert!(done_rx.recv_timeout(Duration::from_millis(100)).is_err());
        child.kill();
        assert!(!done_rx
            .recv_timeout(Duration::from_secs(5))
            .unwrap()
            .success());
        waiter.join().unwrap();
        assert!(child.0.lock().unwrap().reaped);
    }

    #[test]
    fn a_child_that_stops_reading_still_returns_its_output() {
        let input = vec![b'x'; 1024 * 1024];
        let result = output(
            Command::new("sh").args(["-c", "exec 0<&-; echo done"]),
            &input,
        )
        .unwrap();
        assert!(result.status.success());
        assert_eq!(result.stdout, b"done\n");
    }

    #[test]
    fn cancellation_kills_descendants_and_releases_blocked_pipes() {
        let pid_file = std::env::temp_dir().join(format!(
            "tamarin-process-test-{}-descendant.pid",
            std::process::id()
        ));
        let _ = std::fs::remove_file(&pid_file);
        let script = format!("sleep 60 & echo $! > '{}'; wait", pid_file.display());
        let token = CancellationToken::default();
        let worker_token = token.clone();
        let (done_tx, done_rx) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let _guard = CancellationGuard::new(Some(worker_token));
            let input = vec![b'x'; 1024 * 1024];
            let result = output(Command::new("sh").args(["-c", &script]), &input);
            done_tx.send(result.unwrap_err().kind()).unwrap();
        });
        // Cancel only once the descendant exists.
        let deadline = std::time::Instant::now() + Duration::from_secs(5);
        let descendant: libc::pid_t = loop {
            if let Some(pid) = std::fs::read_to_string(&pid_file)
                .ok()
                .and_then(|text| text.trim().parse().ok())
            {
                break pid;
            }
            assert!(std::time::Instant::now() < deadline, "no descendant");
            std::thread::sleep(Duration::from_millis(5));
        };
        let _ = std::fs::remove_file(&pid_file);
        token.cancel();
        assert_eq!(
            done_rx.recv_timeout(Duration::from_secs(5)).unwrap(),
            io::ErrorKind::Interrupted
        );
        // SAFETY: signal 0 only probes whether the process still exists.
        while unsafe { libc::kill(descendant, 0) } == 0 {
            assert!(
                std::time::Instant::now() < deadline,
                "descendant survived cancellation"
            );
            std::thread::sleep(Duration::from_millis(5));
        }
        worker.join().unwrap();
        let result = output(&mut Command::new("cat"), b"next request").unwrap();
        assert!(result.status.success());
        assert_eq!(result.stdout, b"next request");
    }
}
