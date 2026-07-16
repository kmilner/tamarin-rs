//! [`RenderSystem`] — a write-sealed, display-only wrapper around a prover
//! [`System`].
//!
//! The interactive graph-render pipeline (`graph::simplify`,
//! `handlers::dot`) works on a **clone** of a prover `System` that it mutates
//! for display: it drops entailed order constraints, hides intruder/coerce
//! nodes, and transitively reduces the `less` relation.  Those mutations go
//! through `content_mut()`, which leaves the system's verified-identity
//! `subst_system` stamps meaningless — so a mutated display copy must NEVER be
//! fed back into the prover.
//!
//! `RenderSystem` makes that unrepresentable at the type level: it is
//! constructed **only** by [`RenderSystem::from_prover`] (a one-way door from a
//! prover `System`), and it exposes the inner `System` **only** by shared/unique
//! reference through `Deref`/`DerefMut` — there is deliberately **no**
//! `into_inner`, and no accessor hands the inner `System` back by value.  So a
//! `RenderSystem` cannot be passed to any prover entry point that consumes a
//! `System` by value; the render pipeline is typed with `RenderSystem` from the
//! clone-for-render boundary onwards.
//!
//! Reads (`rs.nodes`, `rs.less_atoms`, …) and the display-only mutators
//! (`rs.content_mut()`, `rs.goals_mut()`, `rs.nodes_mut()`, …) keep working
//! unchanged via the deref coercions, and any function taking `&System`
//! (e.g. `compute_basic_graph_repr`) accepts `&RenderSystem` directly.

use tamarin_theory::constraint::system::System;

/// A prover [`System`] clone dedicated to graph rendering.  See the module
/// docs: constructed one-way via [`RenderSystem::from_prover`], never yields
/// its inner `System` by value, so it cannot re-enter the prover.
pub struct RenderSystem(System);

impl RenderSystem {
    /// The ONLY constructor: wrap a (cloned) prover `System` for display
    /// mutation.  One-way — there is no inverse that returns the inner
    /// `System` by value.
    #[inline]
    pub fn from_prover(sys: System) -> Self {
        RenderSystem(sys)
    }
}

impl std::ops::Deref for RenderSystem {
    type Target = System;
    #[inline]
    fn deref(&self) -> &System {
        &self.0
    }
}

impl std::ops::DerefMut for RenderSystem {
    #[inline]
    fn deref_mut(&mut self) -> &mut System {
        &mut self.0
    }
}
