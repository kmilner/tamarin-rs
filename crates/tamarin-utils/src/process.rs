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
        loop {
            // Wait without holding the mutex needed by cancellation. WNOWAIT
            // leaves the child unreaped, so its PID cannot be reused before
            // wait() takes the mutex and disarms kill() alongside reaping.
            let mut info = std::mem::MaybeUninit::<libc::siginfo_t>::uninit();
            let result = unsafe {
                libc::waitid(
                    libc::P_PID,
                    pid as libc::id_t,
                    info.as_mut_ptr(),
                    libc::WEXITED | libc::WNOWAIT,
                )
            };
            if result == 0 {
                return Ok(());
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
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
    let mut stdin = child.stdin.take().expect("piped stdin");
    let mut stdout = child.stdout.take().expect("piped stdout");
    let child = Arc::new(ChildGuard(Mutex::new(ChildState {
        child,
        reaped: false,
    })));
    let killing_child = child.clone();
    let registration =
        cancellation::current().map(|token| token.on_cancel(move || killing_child.kill()));
    let (write, read, bytes) = std::thread::scope(|scope| {
        let writing_child = child.clone();
        let writer = scope.spawn(move || {
            let result = stdin.write_all(input);
            if result.is_err() {
                writing_child.kill();
            }
            result
        });
        let mut bytes = Vec::new();
        let read = stdout.read_to_end(&mut bytes);
        if read.is_err() {
            child.kill();
        }
        (writer.join().expect("stdin writer panicked"), read, bytes)
    });
    let status = child.wait(registration.is_some())?;
    drop(registration);
    cancellation::check().map_err(|_| interrupted())?;
    write?;
    read?;
    Ok(Output {
        status,
        stdout: bytes,
        stderr: Vec::new(),
    })
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
    fn cancellation_kills_descendants_and_releases_blocked_pipes() {
        let token = CancellationToken::default();
        let worker_token = token.clone();
        let (done_tx, done_rx) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let _guard = CancellationGuard::new(Some(worker_token));
            let input = vec![b'x'; 1024 * 1024];
            let result = output(Command::new("sh").args(["-c", "sleep 60 & wait"]), &input);
            done_tx.send(result.unwrap_err().kind()).unwrap();
        });
        std::thread::sleep(Duration::from_millis(100));
        token.cancel();
        assert_eq!(
            done_rx.recv_timeout(Duration::from_secs(5)).unwrap(),
            io::ErrorKind::Interrupted
        );
        worker.join().unwrap();
        let result = output(&mut Command::new("cat"), b"next request").unwrap();
        assert!(result.status.success());
        assert_eq!(result.stdout, b"next request");
    }
}
