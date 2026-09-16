//! Stack growth for recursive compiler and parser walks.
//!
//! Stack switching uses `stacker`'s Windows fiber backend on Windows and its
//! `psm` backend on other supported targets. Unsupported targets execute the
//! closure in place; these helpers cannot add stack there.

/// Run `f` with enough native stack for another recursive section.
///
/// These values follow rustc's `ensure_sufficient_stack`: leave a 100 KiB
/// red zone and allocate a 1 MiB segment when it is crossed. AIX needs the
/// larger segment because LLVM does not provide tail-call optimisation there.
#[inline]
pub fn ensure_sufficient_stack<T>(f: impl FnOnce() -> T) -> T {
    let segment = if cfg!(target_os = "aix") {
        16 * 1024 * 1024
    } else {
        1024 * 1024
    };
    stacker::maybe_grow(100 * 1024, segment, f)
}

/// Run a compiler phase with enough stack for recursive temporary values whose
/// derived destructors cannot call [`ensure_sufficient_stack`].
///
/// The 64 MiB red zone matches this project's Rayon and server worker stacks
/// and covers the larger frames used by SAPIC typing and translation. The
/// extra MiB keeps nested phase wrappers on the same freshly allocated stack.
#[inline]
pub fn with_compiler_stack<T>(f: impl FnOnce() -> T) -> T {
    stacker::maybe_grow(64 * 1024 * 1024, 65 * 1024 * 1024, f)
}

/// Preserve ordinary pretty Debug, switching deep subtrees to complete compact
/// output. Standard pretty builders chain indentation writers whose recursive
/// writes bypass guards on tree traversal. Bound that chain across all our tree
/// types, including trees nested inside other types' fields.
/// The compact suffix uses default Debug flags: numeric hex, width and other
/// caller formatting options are not forwarded beyond the pretty-depth budget.
#[inline]
pub fn bounded_debug<T: std::fmt::Debug + ?Sized>(
    value: &T,
    f: &mut std::fmt::Formatter<'_>,
    render: impl FnOnce(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
) -> std::fmt::Result {
    if !f.alternate() {
        return render(f);
    }
    thread_local! {
        static DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    }
    const PRETTY_DEPTH: usize = 16;
    let depth = DEPTH.get();
    if depth == PRETTY_DEPTH {
        return write!(f, "{value:?}");
    }
    struct ResetDepth(usize);
    impl Drop for ResetDepth {
        fn drop(&mut self) {
            DEPTH.set(self.0);
        }
    }
    DEPTH.set(depth + 1);
    let _reset = ResetDepth(depth);
    render(f)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Nested(usize, bool);
    impl std::fmt::Debug for Nested {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            bounded_debug(self, f, |f| {
                ensure_sufficient_stack(|| {
                    if self.0 == 0 {
                        assert!(!self.1, "payload panic");
                        f.write_str("Leaf")
                    } else {
                        f.debug_tuple("Nested")
                            .field(&Nested(self.0 - 1, self.1))
                            .finish()
                    }
                })
            })
        }
    }

    #[test]
    fn pretty_debug_budget_restores_after_errors_and_panics() {
        struct Fail(usize);
        impl std::fmt::Write for Fail {
            fn write_str(&mut self, text: &str) -> std::fmt::Result {
                if text.contains("Nested") {
                    self.0 = self.0.saturating_sub(1);
                }
                if self.0 == 0 {
                    Err(std::fmt::Error)
                } else {
                    Ok(())
                }
            }
        }
        let expected = "Nested(\n    Nested(\n        Leaf,\n    ),\n)";
        for _ in 0..32 {
            assert!(std::panic::catch_unwind(|| format!("{:#?}", Nested(32, true))).is_err());
            assert!(
                std::fmt::write(&mut Fail(24), format_args!("{:#?}", Nested(32, false))).is_err()
            );
            assert_eq!(format!("{:#?}", Nested(2, false)), expected);
        }
    }

    #[test]
    fn stack_switch_preserves_panic_payload_and_cleanup() {
        struct Token;
        struct Count<'a>(&'a std::sync::atomic::AtomicUsize);
        impl Drop for Count<'_> {
            fn drop(&mut self) {
                self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            }
        }
        fn descend(depth: usize, drops: &std::sync::atomic::AtomicUsize) {
            ensure_sufficient_stack(|| {
                let _count = Count(drops);
                if depth == 0 {
                    std::panic::panic_any(Token);
                }
                descend(depth - 1, drops);
                std::hint::black_box(&_count);
            });
        }
        let drops = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let worker_drops = drops.clone();
        let panic = std::panic::catch_unwind(|| {
            tamarin_test_support::on_stack(256 * 1024, move || descend(8192, &worker_drops));
        })
        .unwrap_err();
        assert!(panic.is::<Token>());
        assert_eq!(drops.load(std::sync::atomic::Ordering::Relaxed), 8193);
    }

    #[test]
    fn deep_pretty_debug_keeps_all_nodes_on_small_stack() {
        tamarin_test_support::on_stack(256 * 1024, || {
            let rendered = format!("{:#?}", Nested(8192, false));
            assert_eq!(rendered.matches("Nested(").count(), 8192);
            assert_eq!(rendered.matches("Leaf").count(), 1);
            assert!(rendered.len() < 100_000);
        });
    }
}
