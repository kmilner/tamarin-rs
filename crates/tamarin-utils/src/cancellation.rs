//! Request-scoped cancellation shared by solver workers and blocking I/O.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc, Mutex,
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

#[derive(Default)]
struct State {
    parent: Option<CancellationToken>,
    cancelled: AtomicBool,
    callbacks: Mutex<BTreeMap<u64, Box<dyn Fn() + Send>>>,
    next_id: std::sync::atomic::AtomicU64,
    callbacks_fired: AtomicBool,
}

#[derive(Clone, Default)]
pub struct CancellationToken(Arc<State>);

impl CancellationToken {
    /// Mark cancellation without running potentially blocking cleanup.
    /// Work that polls `check` stops, but anything blocked on a subprocess
    /// or a parallel wait is only woken by callbacks: follow up with `cancel`.
    pub fn request_cancel(&self) {
        self.0.cancelled.store(true, Ordering::Relaxed);
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
}

impl CancellationScope {
    pub fn new(parent: Option<CancellationToken>) -> Self {
        let token = CancellationToken(Arc::new(State {
            parent: parent.clone(),
            ..State::default()
        }));
        // The child keeps its ancestry alive for checks, but the parent's
        // callback must not form a reference cycle back to the child.
        let child = Arc::downgrade(&token.0);
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
