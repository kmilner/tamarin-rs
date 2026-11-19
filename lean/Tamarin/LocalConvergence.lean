import Tamarin.ObservationRepresentative

namespace Tamarin.Rewriting
variable {s : Signature} {R : Root s}

/-- Every reduct can still reach the specified value, even after another
strategy has taken some steps. This property is local to the source term. -/
def Converges (R : Root s) (a n : Term s) := ∀ u, Reduces R a u → Reduces R u n

theorem Converges.normal {n : Term s} (hn : Normal R n) : Converges R n n :=
  fun _ red => .basis (normal_reduces_equiv red hn).symm

theorem Converges.follow {a b n : Term s} (h : Converges R a n) (red : Reduces R a b) :
    Converges R b n := fun _ next => h _ (red.trans next)

theorem Converges.agree {a n m : Term s} (l : Converges R a n) (r : Converges R a m)
    (hn : Normal R n) : EquivB n m :=
  normal_reduces_equiv (r _ (l _ (.basis (.refl _)))) hn

theorem Converges.free (f : s.FreeSym) (inert : ∀ xs u, ¬R (.free f xs) u)
    {xs ns : Fin (s.arity f) → Term s} (children : ∀ i, Converges R (xs i) (ns i)) :
    Converges R (.free f xs) (.free f ns) := by
  intro u red
  obtain ⟨ys,rfl,rs⟩ := StableVariants.reduces_free_view f inert red
  exact .free f ys ns (fun i => children i _ (rs i))

/-- If an inert constructor converges, every original argument converges to
the corresponding final argument. This holds after any local reduction. -/
theorem Converges.free_view (f : s.FreeSym) (inert : ∀ xs u, ¬R (.free f xs) u)
    {xs : Fin (s.arity f) → Term s} {n} (conv : Converges R (.free f xs) n) :
    ∃ ns, n = .free f ns ∧ ∀ i, Converges R (xs i) (ns i) := by
  obtain ⟨ns,rfl,_⟩ := StableVariants.reduces_free_view f inert (conv _ (.basis (.refl _)))
  refine ⟨ns,rfl,?_⟩
  intro i u step
  let ys j := if j = i then u else xs j
  have start : Reduces R (.free f xs) (.free f ys) := .free f xs ys fun j => by
    by_cases e : j = i
    · subst j; simpa [ys] using step
    · simp [ys,e]; exact .basis (.refl _)
  obtain ⟨zs,e,h⟩ := StableVariants.reduces_free_view f inert (conv _ start)
  cases e
  simpa [ys] using h i

/-- Children may change while the free head is still present. Once the
first root rule fires, its output may itself reduce. Checking those early
outputs against the same normal value is sufficient for every strategy. -/
theorem Converges.active_free (d : s.FreeSym) (xs : Fin (s.arity d) → Term s) (n : Term s)
    (finish : ∀ ys, (∀ i, Reduces R (xs i) (ys i)) → Reduces R (.free d ys) n)
    (early : ∀ ys, (∀ i, Reduces R (xs i) (ys i)) → ∀ u, R (.free d ys) u → Converges R u n) :
    Converges R (.free d xs) n := by
  let inside (t : Term s) := ∃ ys, t = .free d ys ∧ ∀ i, Reduces R (xs i) (ys i)
  have basis {a b : Term s} (h : inside a) (e : EquivB a b) : inside b := by
    obtain ⟨ys,rfl,rs⟩ := h
    obtain ⟨zs,rfl,eq⟩ := free_equiv_view e
    exact ⟨zs,rfl,fun i => (rs i).trans (.basis (eq i))⟩
  have go {a b : Term s} (red : Reduces R a b) : inside a → inside b ∨ Converges R b n := by
    induction red with
    | basis e => exact fun h => .inl (basis h e)
    | trans _ last ih ik => intro h; exact (ih h).elim ik (fun conv => .inr (conv.follow last))
    | free f a b rs _ =>
      rintro ⟨_,⟨⟩,hs⟩; exact .inl ⟨_,rfl,fun i => (hs i).trans (rs i)⟩
    | comm | ac => rintro ⟨_,⟨⟩,_⟩
    | step st =>
      intro h
      obtain ⟨s,t,e,step,out⟩ := st
      obtain ⟨ys,rfl,rs⟩ := basis h e
      cases step with
      | root r => exact .inr ((early _ rs _ r).follow (.basis out))
      | free _ _ i child =>
        apply Or.inl (basis _ out)
        refine ⟨_,rfl,fun j => (rs j).trans ?_⟩
        by_cases he : j = i
        · subst j; simpa using (Reduces.step ⟨_,_,.refl _,child,.refl _⟩)
        · simp [he]; exact .basis (.refl _)
  intro u red
  rcases go red ⟨xs,rfl,fun _ => .basis (.refl _)⟩ with ⟨ys,rfl,rs⟩|conv
  · exact finish ys rs
  · exact conv _ (.basis (.refl _))

end Tamarin.Rewriting
