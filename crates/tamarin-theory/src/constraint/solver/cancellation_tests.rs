//! Test-only rendezvous during solver work. The gate pauses workers
//! before their next solver step; it neither installs nor checks cancellation.

use std::sync::{
    atomic::{AtomicUsize, Ordering},
    mpsc, Arc, Condvar, Mutex,
};
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Work {
    Search,
    Sources,
    Terminal,
}

#[derive(Debug)]
pub(crate) struct WorkerGate {
    work: Work,
    participants: usize,
    entered: mpsc::Sender<std::thread::ThreadId>,
    entered_count: AtomicUsize,
    released: Mutex<bool>,
    ready: Condvar,
}

impl WorkerGate {
    pub(crate) fn new(
        work: Work,
        participants: usize,
    ) -> (Arc<Self>, mpsc::Receiver<std::thread::ThreadId>) {
        let (entered, receiver) = mpsc::channel();
        (
            Arc::new(Self {
                work,
                participants,
                entered,
                entered_count: AtomicUsize::new(0),
                released: Mutex::new(false),
                ready: Condvar::new(),
            }),
            receiver,
        )
    }

    pub(crate) fn release(&self) {
        *self.released.lock().unwrap() = true;
        self.ready.notify_all();
    }
}

pub(crate) fn checkpoint(ctx: &super::ProofContext, work: Work) {
    let gate = ctx.worker_gate.lock().unwrap().clone();
    let Some(gate) = gate else { return };
    if gate.work != work || gate.entered_count.fetch_add(1, Ordering::Relaxed) >= gate.participants
    {
        return;
    }
    gate.entered.send(std::thread::current().id()).unwrap();
    let (released, _) = gate
        .ready
        .wait_timeout_while(
            gate.released.lock().unwrap(),
            Duration::from_secs(10),
            |released| !*released,
        )
        .unwrap();
    assert!(*released, "test did not release the active solver worker");
}
