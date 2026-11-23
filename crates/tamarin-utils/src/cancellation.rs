//! Request-scoped cancellation shared by solver workers and blocking I/O.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Condvar, Mutex,
};
use std::time::Duration;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Cancelled;

impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("request cancelled")
    }
}
impl std::error::Error for Cancelled {}

/// A failure that a parallel job ran into and could not return, held by
/// the scope of that job. See [`CancellationScope::job`].
pub trait JobFailure: std::any::Any + Send + Sync {
    /// The failure has left the outermost job: its work is part of the
    /// result of a caller that no job encloses, and there is no scope left
    /// to hold it. The implementation records it where that caller looks.
    fn escalate(&self);

    /// For the owner of the failure to read it back.
    fn as_any(&self) -> &dyn std::any::Any;
}

/// A shared [`JobFailure`].
pub type Failure = Arc<dyn JobFailure>;

/// Written once and only read afterwards, so a panic cannot leave it half
/// updated: a token stays usable across `catch_unwind` whatever the failure
/// type holds.
#[derive(Default)]
struct FailureSlot(std::sync::OnceLock<Failure>);
impl std::panic::UnwindSafe for FailureSlot {}
impl std::panic::RefUnwindSafe for FailureSlot {}

#[derive(Default)]
struct State {
    parent: Option<CancellationToken>,
    /// Whether this scope is one parallel job, which holds its own failures.
    job: bool,
    /// The first failure of this job. Only a job scope holds one.
    failure: FailureSlot,
    cancelled: AtomicBool,
    callbacks: Mutex<BTreeMap<u64, Box<dyn Fn() + Send>>>,
    next_id: std::sync::atomic::AtomicU64,
    callbacks_fired: AtomicBool,
    /// The scopes directly below this token, for `request_cancel` to raise
    /// their own flags. Ancestry alone answers `is_cancelled`, but foreign
    /// code polls one flag byte (`flag_ptr`) and cannot walk it.
    children: Mutex<BTreeMap<u64, std::sync::Weak<State>>>,
}

impl State {
    /// Raise this flag and the flags of all scopes below.
    fn raise(&self) {
        self.cancelled.store(true, Ordering::Relaxed);
        // A scope registered after this snapshot reads the flag just set.
        let children: Vec<_> = self
            .children
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .values()
            .filter_map(std::sync::Weak::upgrade)
            .collect();
        for child in children {
            child.raise();
        }
    }
}

#[derive(Clone, Default)]
pub struct CancellationToken(Arc<State>);

impl CancellationToken {
    /// Mark cancellation without running potentially blocking cleanup.
    /// Work that polls `check` stops, but anything blocked on a subprocess
    /// or a parallel wait is only woken by callbacks: follow up with `cancel`.
    ///
    /// The flag of every scope below this token is raised too, so foreign
    /// code that polls a descendant's `flag_ptr` stops without waiting for
    /// `cancel`. This takes only the short locks of the scope lists.
    pub fn request_cancel(&self) {
        self.0.raise();
    }

    pub fn cancel(&self) {
        self.request_cancel();
        // Serialize callback execution with deregistration. Once a blocking
        // operation drops its registration, no late callback can kill a
        // subprocess that has since been handed to another request.
        let callbacks = self.0.callbacks.lock().unwrap();
        if !self.0.callbacks_fired.swap(true, Ordering::Relaxed) {
            for callback in callbacks.values() {
                callback();
            }
        }
    }

    pub(crate) fn descends_from(&self, ancestor: &Self) -> bool {
        std::iter::successors(Some(self), |token| token.0.parent.as_ref())
            .any(|token| Arc::ptr_eq(&token.0, &ancestor.0))
    }

    fn scopes(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(Some(self), |token| token.0.parent.as_ref())
    }

    /// Record a failure of the work running under this token, on the
    /// innermost enclosing job, and return the failure that job now holds:
    /// its first. `None` when no job encloses this token. Such work is not
    /// speculative, and the caller records the failure for the whole run.
    ///
    /// A job is discarded together with its scope, and its failure with it.
    /// A job whose result is used hands the failure to the job around it
    /// ([`Self::inherit`]).
    pub fn fail(&self, failure: impl FnOnce() -> Failure) -> Option<Failure> {
        let job = self.scopes().find(|token| token.0.job)?;
        Some(job.0.failure.0.get_or_init(failure).clone())
    }

    /// The failure of the innermost failed job around this token, if any.
    /// Work under a failed job may rest on a placeholder: it must not
    /// publish anything outside the job.
    pub fn failure(&self) -> Option<Failure> {
        self.scopes()
            .find_map(|token| token.0.failure.0.get().cloned())
    }

    /// The failure this very scope holds, if it is a failed job.
    pub fn own_failure(&self) -> Option<Failure> {
        self.0.failure.0.get().cloned()
    }

    /// Take over the failure of a job whose result is used by the work
    /// under this token: the innermost enclosing job holds it from now on,
    /// unless it has failed already. Without an enclosing job the failure
    /// is escalated.
    pub fn inherit(&self, failure: Failure) {
        let escalated = failure.clone();
        if self.fail(move || failure).is_none() {
            escalated.escalate();
        }
    }

    pub fn is_cancelled(&self) -> bool {
        // Read ancestors directly: request_cancel() must reach descendants
        // before potentially blocking cleanup callbacks are dispatched.
        let mut state = &*self.0;
        loop {
            if state.cancelled.load(Ordering::Relaxed) {
                return true;
            }
            match &state.parent {
                Some(parent) => state = &parent.0,
                None => return false,
            }
        }
    }
    /// The address of the flag for foreign code that polls it: the byte is
    /// zero until the token is cancelled and nonzero from then on, whether
    /// this token was cancelled itself or through an enclosing one. The
    /// address stays valid while this token or a clone of it is alive.
    pub fn flag_ptr(&self) -> *const u8 {
        self.0.cancelled.as_ptr().cast_const().cast()
    }
    pub fn check(&self) -> Result<(), Cancelled> {
        if self.is_cancelled() {
            Err(Cancelled)
        } else {
            Ok(())
        }
    }
    pub fn on_cancel(&self, callback: impl Fn() + Send + 'static) -> Registration {
        let mut callbacks = self.0.callbacks.lock().unwrap();
        let id = self.0.next_id.fetch_add(1, Ordering::Relaxed);
        if self.is_cancelled() {
            callback();
        } else {
            callbacks.insert(id, Box::new(callback));
        }
        Registration {
            token: self.clone(),
            id,
        }
    }
}

/// A local cancellation token linked to an optional enclosing request.
/// Keep the scope alive until its workers have joined so parent cancellation
/// can interrupt their blocking I/O as well as their cooperative checkpoints.
pub struct CancellationScope {
    token: CancellationToken,
    _parent_callback: Option<Registration>,
    /// This scope's entry in its parent's list of scopes.
    listed: Option<u64>,
}

impl Drop for CancellationScope {
    fn drop(&mut self) {
        if let (Some(id), Some(parent)) = (self.listed, &self.token.0.parent) {
            parent
                .0
                .children
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .remove(&id);
        }
    }
}

impl CancellationScope {
    pub fn new(parent: Option<CancellationToken>) -> Self {
        Self::build(parent, false)
    }

    /// The scope of one parallel job whose result its caller may discard.
    ///
    /// A failure that the job cannot return ([`CancellationToken::fail`]) is
    /// held by this scope instead of by the whole run. The caller that uses
    /// the job's result must hand the failure on with
    /// [`CancellationToken::inherit`]; a caller that discards the result
    /// drops the failure with the scope.
    pub fn job(parent: Option<CancellationToken>) -> Self {
        Self::build(parent, true)
    }

    fn build(parent: Option<CancellationToken>, job: bool) -> Self {
        let token = CancellationToken(Arc::new(State {
            parent: parent.clone(),
            job,
            ..State::default()
        }));
        // The child keeps its ancestry alive for checks, but the parent's
        // callback must not form a reference cycle back to the child.
        let child = Arc::downgrade(&token.0);
        // List the scope before reading the parent's state: a request that
        // misses the entry has already set a flag this read sees.
        let listed = parent.as_ref().map(|parent| {
            let id = parent.0.next_id.fetch_add(1, Ordering::Relaxed);
            parent
                .0
                .children
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .insert(id, child.clone());
            if parent.is_cancelled() {
                token.0.cancelled.store(true, Ordering::Relaxed);
            }
            id
        });
        let parent_callback = parent.map(|parent| {
            parent.on_cancel(move || {
                if let Some(child) = child.upgrade() {
                    CancellationToken(child).cancel();
                }
            })
        });
        Self {
            token,
            _parent_callback: parent_callback,
            listed,
        }
    }

    pub fn token(&self) -> CancellationToken {
        self.token.clone()
    }
}

pub struct Registration {
    token: CancellationToken,
    id: u64,
}
impl Drop for Registration {
    fn drop(&mut self) {
        self.token.0.callbacks.lock().unwrap().remove(&self.id);
    }
}

thread_local! {
    static CURRENT: RefCell<Option<CancellationToken>> = const { RefCell::new(None) };
}

pub fn current() -> Option<CancellationToken> {
    CURRENT.with(|cell| cell.borrow().clone())
}
#[inline]
pub fn check() -> Result<(), Cancelled> {
    CURRENT.with(|cell| {
        cell.borrow()
            .as_ref()
            .map_or(Ok(()), CancellationToken::check)
    })
}

/// Record a failure of the work on this thread on its innermost enclosing
/// job. See [`CancellationToken::fail`].
pub fn fail_job(failure: impl FnOnce() -> Failure) -> Option<Failure> {
    CURRENT.with(|cell| cell.borrow().as_ref()?.fail(failure))
}

/// The failure of the innermost failed job around the work on this thread.
/// See [`CancellationToken::failure`].
#[inline]
pub fn job_failure() -> Option<Failure> {
    CURRENT.with(|cell| cell.borrow().as_ref()?.failure())
}

/// Hand `failure` to the job around the work on this thread, or escalate it
/// when there is none. See [`CancellationToken::inherit`].
pub fn inherit_failure(failure: Failure) {
    match current() {
        Some(token) => token.inherit(failure),
        None => failure.escalate(),
    }
}

/// Must be installed explicitly on each Rayon/scoped worker, including when
/// the inherited token is None, and dropped on the thread that installed it.
#[must_use]
pub struct CancellationGuard {
    previous: Option<CancellationToken>,
    _not_send: std::marker::PhantomData<std::rc::Rc<()>>,
}
impl CancellationGuard {
    pub fn new(token: Option<CancellationToken>) -> Self {
        Self {
            previous: CURRENT.with(|cell| cell.replace(token)),
            _not_send: std::marker::PhantomData,
        }
    }
}
impl Drop for CancellationGuard {
    fn drop(&mut self) {
        CURRENT.with(|cell| cell.replace(self.previous.take()));
    }
}

/// A cancelled waiter must not kill the request which owns the mutex.
#[inline]
pub fn lock<T>(mutex: &parking_lot::Mutex<T>) -> Result<parking_lot::MutexGuard<'_, T>, Cancelled> {
    // Cached Maude operations frequently take an uncontended lock. Keep this
    // path free of token refcount changes and timed-wait setup.
    if let Some(guard) = mutex.try_lock() {
        check()?;
        return Ok(guard);
    }
    lock_contended(mutex)
}

#[cold]
fn lock_contended<T>(
    mutex: &parking_lot::Mutex<T>,
) -> Result<parking_lot::MutexGuard<'_, T>, Cancelled> {
    let Some(token) = current() else {
        return Ok(mutex.lock());
    };
    loop {
        token.check()?;
        // Wake on unlock, just like an ordinary mutex. The timeout only
        // bounds cancellation latency when an unrelated owner stays busy.
        if let Some(guard) = mutex.try_lock_for(Duration::from_secs(1)) {
            token.check()?;
            return Ok(guard);
        }
    }
}

enum CellState<T, E> {
    Empty,
    Building,
    Ready(Result<T, E>),
}

/// Single-flight initialization. Cancellation/panics leave the slot empty;
/// other waiters retry using their own request rather than inheriting its error.
/// Completed values and ordinary errors retain the original OnceLock policy,
/// except under a failed job ([`job_failure`]): what it built is returned to
/// it and not kept.
pub struct CancellableOnce<T, E> {
    state: Mutex<CellState<T, E>>,
    ready: Condvar,
}
impl<T, E> Default for CancellableOnce<T, E> {
    fn default() -> Self {
        Self {
            state: Mutex::new(CellState::Empty),
            ready: Condvar::new(),
        }
    }
}
impl<T: Clone, E: Clone + From<Cancelled>> CancellableOnce<T, E> {
    pub fn from_result(value: Result<T, E>) -> Self {
        Self {
            state: Mutex::new(CellState::Ready(value)),
            ready: Condvar::new(),
        }
    }

    pub fn get(&self) -> Option<Result<T, E>> {
        match &*self.state.lock().unwrap() {
            CellState::Ready(value) => Some(value.clone()),
            _ => None,
        }
    }
    pub fn get_or_init(&self, build: impl FnOnce() -> Result<T, E>) -> Result<T, E> {
        let mut state = self.state.lock().unwrap();
        loop {
            check()?;
            match &*state {
                CellState::Ready(value) => return value.clone(),
                CellState::Building => {
                    state = if current().is_some() {
                        self.ready
                            .wait_timeout(state, Duration::from_millis(250))
                            .unwrap()
                            .0
                    } else {
                        self.ready.wait(state).unwrap()
                    }
                }
                CellState::Empty => {
                    *state = CellState::Building;
                    break;
                }
            }
        }
        drop(state);
        struct Reset<'a, T, E>(&'a CancellableOnce<T, E>);
        impl<T, E> Drop for Reset<'_, T, E> {
            fn drop(&mut self) {
                let mut state = self.0.state.lock().unwrap();
                if matches!(*state, CellState::Building) {
                    *state = CellState::Empty;
                }
                self.0.ready.notify_all();
            }
        }
        let _reset = Reset(self);
        let value = build();
        check()?;
        // A failed job may have built the value on a placeholder: it keeps
        // the value to itself, and the next caller builds its own.
        if job_failure().is_none() {
            *self.state.lock().unwrap() = CellState::Ready(value.clone());
        }
        value
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;

    #[test]
    fn child_checkpoints_see_parent_request_before_cleanup() {
        let parent = CancellationToken::default();
        let child = CancellationScope::new(Some(parent.clone()));
        let grandchild = CancellationScope::new(Some(child.token()));
        let (fired, wait) = mpsc::channel();
        let _registration = grandchild
            .token()
            .on_cancel(move || fired.send(()).unwrap());
        parent.request_cancel();
        assert_eq!(grandchild.token().check(), Err(Cancelled));
        assert!(matches!(wait.try_recv(), Err(mpsc::TryRecvError::Empty)));
        parent.cancel();
        wait.recv_timeout(Duration::from_secs(5)).unwrap();
    }

    /// Foreign code polls one byte. A request on an enclosing token must
    /// raise it at once, for scopes made before and after the request, and
    /// a dropped scope leaves nothing behind in its parent.
    #[test]
    fn request_raises_the_flag_bytes_of_scopes_below() {
        let read = |token: &CancellationToken| unsafe { *token.flag_ptr() };
        let parent = CancellationToken::default();
        let child = CancellationScope::new(Some(parent.clone()));
        let grandchild = CancellationScope::new(Some(child.token()));
        let peer = CancellationToken::default();
        drop(CancellationScope::new(Some(parent.clone())));
        assert_eq!(parent.0.children.lock().unwrap().len(), 1);
        assert_eq!(read(&grandchild.token()), 0);
        parent.request_cancel();
        assert_ne!(read(&child.token()), 0);
        assert_ne!(read(&grandchild.token()), 0);
        assert_eq!(read(&peer), 0);
        let late = CancellationScope::new(Some(child.token()));
        assert_ne!(read(&late.token()), 0);
        // Callbacks still wait for `cancel`.
        assert!(!grandchild.token().0.callbacks_fired.load(Ordering::Relaxed));
    }

    #[test]
    fn child_cancellation_does_not_cancel_parent_or_peer() {
        let parent = CancellationToken::default();
        let child = CancellationScope::new(Some(parent.clone()));
        let peer = CancellationScope::new(Some(parent.clone()));
        child.token().cancel();
        assert!(!parent.is_cancelled());
        assert!(!peer.token().is_cancelled());
    }

    #[test]
    fn cancelled_initializer_is_not_cached_and_waiter_retries() {
        let cell = Arc::new(CancellableOnce::<usize, Cancelled>::default());
        let token = CancellationToken::default();
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let owner_cell = cell.clone();
        let owner_token = token.clone();
        let owner = std::thread::spawn(move || {
            let _guard = CancellationGuard::new(Some(owner_token));
            owner_cell.get_or_init(|| {
                started_tx.send(()).unwrap();
                release_rx.recv().unwrap();
                // Even a superficially successful partial result cannot escape.
                Ok(13)
            })
        });
        started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        let waiter_cell = cell.clone();
        let waiter = std::thread::spawn(move || waiter_cell.get_or_init(|| Ok(42)));
        token.cancel();
        release_tx.send(()).unwrap();
        assert_eq!(owner.join().unwrap(), Err(Cancelled));
        assert_eq!(waiter.join().unwrap(), Ok(42));
        assert_eq!(cell.get(), Some(Ok(42)));
    }

    #[test]
    fn cancelled_waiter_leaves_initializer_alone() {
        let cell = Arc::new(CancellableOnce::<usize, Cancelled>::default());
        let (started_tx, started_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let owner_cell = cell.clone();
        let owner = std::thread::spawn(move || {
            owner_cell.get_or_init(|| {
                started_tx.send(()).unwrap();
                release_rx.recv().unwrap();
                Ok(42)
            })
        });
        started_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        let token = CancellationToken::default();
        let waiter_token = token.clone();
        let waiter_cell = cell.clone();
        let (done_tx, done_rx) = mpsc::channel();
        let waiter = std::thread::spawn(move || {
            let _guard = CancellationGuard::new(Some(waiter_token));
            done_tx
                .send(waiter_cell.get_or_init(|| panic!("waiter became initializer")))
                .unwrap();
        });
        token.cancel();
        assert_eq!(
            done_rx.recv_timeout(Duration::from_secs(5)).unwrap(),
            Err(Cancelled)
        );
        release_tx.send(()).unwrap();
        waiter.join().unwrap();
        assert_eq!(owner.join().unwrap(), Ok(42));
        assert_eq!(cell.get(), Some(Ok(42)));
    }

    /// A failure that counts how often it was escalated.
    struct Probe(std::sync::atomic::AtomicUsize);

    impl Probe {
        fn new() -> Arc<Self> {
            Arc::new(Self(Default::default()))
        }
        fn escalations(&self) -> usize {
            self.0.load(Ordering::Relaxed)
        }
    }

    impl JobFailure for Probe {
        fn escalate(&self) {
            self.0.fetch_add(1, Ordering::Relaxed);
        }
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
    }

    fn same(held: &Failure, probe: &Arc<Probe>) -> bool {
        std::ptr::addr_eq(Arc::as_ptr(held), Arc::as_ptr(probe))
    }

    #[test]
    fn a_job_holds_its_first_failure_and_its_peers_do_not_see_it() {
        let request = CancellationToken::default();
        let job = CancellationScope::job(Some(request.clone()));
        let peer = CancellationScope::job(Some(request.clone()));
        // Scopes that are not jobs pass a failure on to the job around them.
        let inner = CancellationScope::new(Some(job.token()));
        let nested = CancellationScope::job(Some(inner.token()));
        let (first, second) = (Probe::new(), Probe::new());

        assert!(job.token().failure().is_none());
        let held = inner.token().fail(|| first.clone()).unwrap();
        assert!(same(&held, &first));
        // The first failure stays, and the later one is not even built.
        let held = job
            .token()
            .fail(|| -> Failure { panic!("already failed") })
            .unwrap();
        assert!(same(&held, &first));

        assert!(same(&job.token().own_failure().unwrap(), &first));
        assert!(inner.token().own_failure().is_none());
        // Work started by the failed job is failed as well.
        assert!(same(&nested.token().failure().unwrap(), &first));
        assert!(nested.token().own_failure().is_none());
        // A job below records its own failure and still reports it first.
        let held = nested.token().fail(|| second.clone()).unwrap();
        assert!(same(&held, &second));
        assert!(same(&nested.token().failure().unwrap(), &second));
        assert!(same(&job.token().failure().unwrap(), &first));

        assert!(peer.token().failure().is_none());
        assert!(request.failure().is_none());
        assert_eq!(first.escalations() + second.escalations(), 0);
    }

    #[test]
    fn work_outside_every_job_has_no_scope_for_a_failure() {
        let request = CancellationToken::default();
        let scope = CancellationScope::new(Some(request.clone()));
        assert!(scope
            .token()
            .fail(|| -> Failure { panic!("no job to hold it") })
            .is_none());
        assert!(scope.token().failure().is_none());
        assert!(fail_job(|| -> Failure { panic!("no token") }).is_none());
        assert!(job_failure().is_none());
    }

    #[test]
    fn a_used_job_hands_its_failure_on_and_the_last_one_escalates_it() {
        let request = CancellationToken::default();
        let outer = CancellationScope::job(Some(request.clone()));
        let map = CancellationScope::new(Some(outer.token()));
        let used = CancellationScope::job(Some(map.token()));
        let dropped = CancellationScope::job(Some(map.token()));
        let (kept, lost) = (Probe::new(), Probe::new());
        used.token().fail(|| kept.clone()).unwrap();
        dropped.token().fail(|| lost.clone()).unwrap();
        assert!(outer.token().failure().is_none());

        // The caller of the map uses one job and discards the other.
        map.token().inherit(used.token().own_failure().unwrap());
        drop(dropped);
        assert!(same(&outer.token().own_failure().unwrap(), &kept));
        assert_eq!(kept.escalations(), 0);

        // Nothing encloses the outer job's caller.
        request.inherit(outer.token().own_failure().unwrap());
        assert_eq!(kept.escalations(), 1);
        assert_eq!(lost.escalations(), 0);

        // The thread's own token decides where a failure goes.
        let other = Probe::new();
        inherit_failure(other.clone());
        assert_eq!(other.escalations(), 1);
        let job = CancellationScope::job(None);
        let _guard = CancellationGuard::new(Some(job.token()));
        let third = Probe::new();
        inherit_failure(third.clone());
        assert_eq!(third.escalations(), 0);
        assert!(same(&job_failure().unwrap(), &third));
        assert!(same(&fail_job(|| other.clone()).unwrap(), &third));
    }

    #[test]
    fn a_failed_job_does_not_fill_a_shared_cell() {
        let cell = CancellableOnce::<usize, Cancelled>::default();
        {
            let job = CancellationScope::job(None);
            let _guard = CancellationGuard::new(Some(job.token()));
            // Failed before the build or during it: either way the value
            // may rest on a placeholder.
            assert_eq!(
                cell.get_or_init(|| {
                    fail_job(|| Probe::new()).unwrap();
                    Ok(13)
                }),
                Ok(13)
            );
            assert_eq!(cell.get(), None);
            assert_eq!(cell.get_or_init(|| Ok(14)), Ok(14));
            assert_eq!(cell.get(), None);
        }
        assert_eq!(cell.get_or_init(|| Ok(42)), Ok(42));
        assert_eq!(cell.get(), Some(Ok(42)));
    }

    #[test]
    fn deregistered_callback_cannot_affect_later_work() {
        let token = CancellationToken::default();
        let called = Arc::new(AtomicBool::new(false));
        let flag = called.clone();
        let registration = token.on_cancel(move || {
            flag.store(true, Ordering::Relaxed);
        });
        drop(registration);
        token.cancel();
        assert!(!called.load(Ordering::Relaxed));
        let flag = called.clone();
        let _registration = token.on_cancel(move || {
            flag.store(true, Ordering::Relaxed);
        });
        assert!(called.load(Ordering::Relaxed));
    }
}
