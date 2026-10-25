use std::io::{self, Write};
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::process::{Child, Command};
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::{Duration, Instant};
use sysinfo::{ProcessRefreshKind, ProcessesToUpdate, System};

const PARENT_ENV: &str = "TAMARIN_MEMORY_SUPERVISOR_PID";
const SAMPLE_INTERVAL: Duration = Duration::from_millis(100);
const STOP_GRACE: Duration = Duration::from_millis(500);
// Match GHC's uncaught HeapOverflow exit status, including +RTS -M failures.
const LIMIT_EXIT: u8 = 251;
static TERMINATION_SIGNAL: AtomicI32 = AtomicI32::new(0);
static JOB_CONTROL_SIGNAL: AtomicI32 = AtomicI32::new(0);

pub(super) fn is_worker() -> bool {
    // Validate the marker against the actual parent. An inherited marker must
    // not disable supervision for a subsequent, unrelated tamarin invocation.
    std::env::var(PARENT_ENV)
        .ok()
        .and_then(|v| v.parse::<libc::pid_t>().ok())
        .is_some_and(|pid| pid > 0 && pid == unsafe { libc::getppid() })
}

pub(super) fn run(raw: &[String], limit: u64) -> io::Result<u8> {
    // Reap orphaned Maude/helpers ourselves on Linux, including in containers
    // whose PID 1 may not reap zombies. macOS reparents them to launchd.
    #[cfg(target_os = "linux")]
    if unsafe { libc::prctl(libc::PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) } == -1 {
        return Err(io::Error::last_os_error());
    }
    let signals = SignalHandlers::install()?;
    let mut command = Command::new(std::env::current_exe()?);
    command
        .args(raw)
        .env(PARENT_ENV, std::process::id().to_string());
    // Keep the supervisor in the shell's foreground group, including when it
    // belongs to a pipeline. A separate worker session owns an isolated group
    // but no controlling terminal: inherited stdio still works, without
    // SIGTTIN/SIGTTOU or stealing the terminal from a downstream pager.
    // SAFETY: setsid is async-signal-safe; no allocation or locking after fork.
    unsafe {
        command.pre_exec(|| {
            if libc::setsid() == -1 {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let child = command.spawn()?;
    let mut job = Job { child: Some(child) };
    let mut exceeded = None;
    let result = supervise(&mut job, limit, &mut exceeded);
    // On control errors, kill and reap before attempting diagnostics.
    drop(job);
    // The loop no longer consumes pending signals. Restore normal dispositions
    // before any diagnostic can block on a caller's full stderr pipe.
    drop(signals);
    if let Some(used) = exceeded {
        // Inherited stderr can be a full pipe. Never let reporting delay
        // enforcement; the prover and helpers have already been stopped.
        // Reporting failures (e.g. EPIPE) must not replace exit 251 with a panic.
        let _ = writeln!(io::stderr().lock(), "error: memory limit exceeded: job RSS {used} bytes > {limit} bytes; stopped prover and helpers");
    }
    result
}

fn supervise(job: &mut Job, limit: u64, exceeded: &mut Option<u64>) -> io::Result<u8> {
    let mut system = System::new();
    let mut stopping: Option<(Instant, u8)> = None;
    loop {
        let signal = take_signal();
        if signal == libc::SIGTSTP && stopping.is_none() {
            // Ctrl-Z reaches the foreground supervisor. Suspend the isolated
            // worker group before suspending memory monitoring itself.
            job.signal(libc::SIGSTOP)?;
            unsafe { libc::kill(libc::getpid(), libc::SIGSTOP) };
            job.signal(libc::SIGCONT)?;
            continue;
        }
        if signal == libc::SIGCONT {
            job.signal(libc::SIGCONT)?;
        }
        if signal != 0 && signal != libc::SIGCONT {
            if stopping.is_some() {
                return job.finish(stopping.map(|(_, code)| code));
            }
            job.signal(signal)?;
            stopping = Some((Instant::now(), (128 + signal) as u8));
        }

        // Observe exit without reaping: keeping the leader's PID reserved
        // until we kill the remaining group prevents signalling a reused PGID.
        if job.exited()? {
            return job.finish(stopping.map(|(_, code)| code));
        }
        if let Some((since, code)) = stopping {
            if since.elapsed() >= STOP_GRACE {
                return job.finish(Some(code));
            }
        } else {
            let used = group_rss(&mut system, job.pid());
            if used > limit {
                *exceeded = Some(used);
                job.signal(libc::SIGTERM)?;
                stopping = Some((Instant::now(), LIMIT_EXIT));
            }
        }
        std::thread::sleep(SAMPLE_INTERVAL);
    }
}

fn group_rss(system: &mut System, group: libc::pid_t) -> u64 {
    // Refresh memory only, excluding Linux threads so shared address spaces
    // aren't counted once per thread. sysinfo handles platform-specific reads;
    // unavailable samples may be omitted or retain their previous values.
    system.refresh_processes_specifics(
        ProcessesToUpdate::All,
        true,
        ProcessRefreshKind::nothing().with_memory().without_tasks(),
    );
    system
        .processes()
        .iter()
        // sysinfo's group_id is a Unix user group, not a process group.
        .filter(|(pid, _)| unsafe { libc::getpgid(pid.as_u32() as libc::pid_t) } == group)
        .map(|(_, process)| process.memory())
        .fold(0, u64::saturating_add)
}

struct Job {
    child: Option<Child>,
}

impl Job {
    fn pid(&self) -> libc::pid_t {
        self.child.as_ref().expect("unreaped child").id() as libc::pid_t
    }

    fn signal(&self, signal: libc::c_int) -> io::Result<()> {
        // Negative PID addresses only the dedicated prover process group.
        if unsafe { libc::kill(-self.pid(), signal) } == -1 {
            let err = io::Error::last_os_error();
            if err.raw_os_error() != Some(libc::ESRCH) {
                return Err(err);
            }
        }
        Ok(())
    }

    fn exited(&self) -> io::Result<bool> {
        // SAFETY: zero-initialized siginfo is valid storage for waitid, which
        // writes it before we read si_pid. WNOWAIT leaves the child waitable.
        let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
        let result = unsafe {
            libc::waitid(
                libc::P_PID,
                self.pid() as libc::id_t,
                &mut info,
                libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
            )
        };
        if result == -1 {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::Interrupted {
                return Ok(false);
            }
            return Err(err);
        }
        Ok(unsafe { info.si_pid() } != 0)
    }

    fn finish(&mut self, code: Option<u8>) -> io::Result<u8> {
        self.signal(libc::SIGKILL)?;
        let group = self.pid();
        let status = self.child.as_mut().expect("unreaped child").wait()?;
        self.child = None;
        reap_group(group)?;
        Ok(code.unwrap_or_else(|| {
            status
                .code()
                .unwrap_or_else(|| 128 + status.signal().unwrap_or(1)) as u8
        }))
    }
}

impl Drop for Job {
    fn drop(&mut self) {
        if self.child.is_some() {
            // Also clean up on control errors, I/O failures, and unwinding.
            let _ = self.signal(libc::SIGKILL);
            if let Some(mut child) = self.child.take() {
                let group = child.id() as libc::pid_t;
                let _ = child.wait();
                let _ = reap_group(group);
            }
        }
    }
}

fn reap_group(group: libc::pid_t) -> io::Result<()> {
    loop {
        let result = unsafe { libc::waitpid(-group, std::ptr::null_mut(), 0) };
        if result == -1 {
            let err = io::Error::last_os_error();
            if err.raw_os_error() == Some(libc::ECHILD) {
                return Ok(());
            }
            if err.kind() != io::ErrorKind::Interrupted {
                return Err(err);
            }
        }
    }
}

extern "C" fn record_signal(signal: libc::c_int) {
    // Only lock-free atomic work in the handler; all I/O and process control
    // happens in the supervisor loop. Job-control traffic must never consume
    // the slot for a termination request (e.g. SIGCONT immediately followed
    // by SIGTERM). Keep the latest stop/continue state independently.
    if matches!(signal, libc::SIGTSTP | libc::SIGCONT) {
        JOB_CONTROL_SIGNAL.store(signal, Ordering::Relaxed);
    } else {
        let _ =
            TERMINATION_SIGNAL.compare_exchange(0, signal, Ordering::Relaxed, Ordering::Relaxed);
    }
}

fn take_signal() -> libc::c_int {
    let signal = TERMINATION_SIGNAL.swap(0, Ordering::Relaxed);
    if signal != 0 {
        signal
    } else {
        JOB_CONTROL_SIGNAL.swap(0, Ordering::Relaxed)
    }
}

struct SignalHandlers(Vec<(libc::c_int, libc::sigaction)>);

impl SignalHandlers {
    fn install() -> io::Result<Self> {
        let mut saved = Self(Vec::new());
        for signal in [
            libc::SIGINT,
            libc::SIGTERM,
            libc::SIGHUP,
            libc::SIGQUIT,
            libc::SIGTSTP,
            libc::SIGCONT,
        ] {
            // SAFETY: sigaction's zeroed mask is initialized with sigemptyset;
            // record_signal has the required C ABI and async-signal-safe body.
            let mut action: libc::sigaction = unsafe { std::mem::zeroed() };
            let mut old: libc::sigaction = unsafe { std::mem::zeroed() };
            if unsafe { libc::sigaction(signal, std::ptr::null(), &mut old) } == -1 {
                return Err(io::Error::last_os_error());
            }
            // nohup and shells launching background jobs deliberately ignore
            // signals. Preserve that contract for both supervisor and worker:
            // ignored handlers survive exec, whereas caught handlers reset.
            if old.sa_sigaction == libc::SIG_IGN {
                continue;
            }
            action.sa_sigaction = record_signal as *const () as usize;
            action.sa_flags = libc::SA_RESTART;
            unsafe { libc::sigemptyset(&mut action.sa_mask) };
            if unsafe { libc::sigaction(signal, &action, std::ptr::null_mut()) } == -1 {
                return Err(io::Error::last_os_error());
            }
            saved.0.push((signal, old));
        }
        Ok(saved)
    }
}

impl Drop for SignalHandlers {
    fn drop(&mut self) {
        for (signal, old) in self.0.iter().rev() {
            unsafe { libc::sigaction(*signal, old, std::ptr::null_mut()) };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn job_control_cannot_discard_pending_termination() {
        for control in [libc::SIGCONT, libc::SIGTSTP] {
            for termination in [libc::SIGTERM, libc::SIGINT] {
                for termination_first in [false, true] {
                    let sequence = if termination_first {
                        [termination, control]
                    } else {
                        [control, termination]
                    };
                    for signal in sequence {
                        record_signal(signal);
                    }
                    assert_eq!(take_signal(), termination);
                    assert_eq!(take_signal(), control);
                    assert_eq!(take_signal(), 0);
                }
            }
        }
    }
}
