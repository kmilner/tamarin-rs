import Tamarin.LocalConvergence
import Tamarin.SortClash

/-! Values exposed by an operation may themselves be compound and may have
changed before exposure. Quantify over every alternating sequence of descent
and reduction, so the invariant remains available at the newly exposed term. -/
namespace Tamarin.Rewriting
variable {s : Signature} {R : Root s}

inductive Immediate : Term s → Term s → Prop where
  | free (f : s.FreeSym) (xs : Fin (s.arity f) → Term s) (i) : Immediate (.free f xs) (xs i)
  | comm_left (g : s.CSym) (a b) : Immediate (.comm g a b) a
  | comm_right (g : s.CSym) (a b) : Immediate (.comm g a b) b
  | ac_left (g : s.ACSym) (a b) : Immediate (.ac g a b) a
  | ac_right (g : s.ACSym) (a b) : Immediate (.ac g a b) b

inductive Access (R : Root s) : Term s → Term s → Prop where
  | refl (t) : Access R t t
  | reduces {a b} : Reduces R a b → Access R a b
  | child {a b} : Immediate a b → Access R a b
  | trans {a b c} : Access R a b → Access R b c → Access R a c

def Settles (R : Root s) (t : Term s) := ∃ n, Normal R n ∧ HasSort n .msg ∧ Converges R t n
def Hereditary (R : Root s) (t : Term s) := ∀ u, Access R t u → Settles R u

theorem Hereditary.follow {a b : Term s} (h : Hereditary R a) (e : Access R a b) :
    Hereditary R b := fun _ next => h _ (e.trans next)

theorem Hereditary.settles {a : Term s} (h : Hereditary R a) : Settles R a := h _ (.refl _)

theorem Hereditary.of_invariant (P : Term s → Prop)
    (settle : ∀ t, P t → Settles R t)
    (reduce : ∀ a b, P a → Reduces R a b → P b)
    (child : ∀ a b, P a → Immediate a b → P b) {t : Term s} (h : P t) : Hereditary R t := by
  intro u path
  apply settle
  induction path with
  | refl => exact h
  | reduces r => exact reduce _ _ h r
  | child c => exact child _ _ h c
  | trans _ _ l r => exact r (l h)


/-- In the Maude term signature every constructor argument accepts a message
subsort. The separate Node sort is allowed on standalone queries. -/
structure MessageArguments (s : Signature) : Prop where
  free : ∀ f i, Subsort (s.inputSort f i) .msg
  comm : ∀ f, Subsort (s.cSort f) .msg
  ac : ∀ f, Subsort (s.acSort f) .msg

theorem Immediate.message (decl : MessageArguments s) {a b : Term s} (h : Immediate a b)
    (typed : HasSort a .msg) : HasSort b .msg := by
  have ok := Term.checkSort_complete typed
  cases h with
  | free f xs i =>
    simp only [Term.checkSort,Bool.and_eq_true,List.all_eq_true] at ok
    exact .widen (Term.checkSort_sound _ _ (ok.2 _ (List.mem_finRange i))) (decl.free f i)
  | comm_left f | ac_left f =>
    simp only [Term.checkSort,Bool.and_eq_true] at ok
    exact .widen (Term.checkSort_sound _ _ ok.1.2) (by first | exact decl.comm f | exact decl.ac f)
  | comm_right f | ac_right f =>
    simp only [Term.checkSort,Bool.and_eq_true] at ok
    exact .widen (Term.checkSort_sound _ _ ok.2) (by first | exact decl.comm f | exact decl.ac f)

theorem Hereditary.normal (decl : MessageArguments s) {n : Term s} (hn : Normal R n)
    (msg : HasSort n .msg) : Hereditary R n := by
  apply Hereditary.of_invariant (fun t => Normal R t ∧ HasSort t .msg) _ _ _ ⟨hn,msg⟩
  · intro t h; exact ⟨t,h.1,h.2,Converges.normal h.1⟩
  · intro a b h red
    have eq := normal_reduces_equiv red h.1
    exact ⟨(normal_equiv R eq).mp h.1,
      Term.checkSort_sound _ _ (SortClash.check_equiv eq _ ▸ Term.checkSort_complete h.2)⟩
  · intro a b h child
    refine ⟨?_,child.message decl h.2⟩
    cases child with
    | free _ _ i => exact normal_free_child _ _ h.1 i
    | comm_left => exact (normal_comm_children _ h.1).1
    | comm_right => exact (normal_comm_children _ h.1).2
    | ac_left => exact (normal_ac_children _ h.1).1
    | ac_right => exact (normal_ac_children _ h.1).2

/-- A defined free symbol can expose any hereditary subterm of its argument
tuple, including one that still rewrites or that opens as an AC product. -/
theorem Hereditary.free_active (d : s.FreeSym)
    (settle : ∀ ys, (∀ i, Hereditary R (ys i)) → Settles R (.free d ys))
    (root : ∀ ys, (∀ i, Hereditary R (ys i)) → ∀ u, R (.free d ys) u → Hereditary R u)
    (xs : Fin (s.arity d) → Term s) (kids : ∀ i, Hereditary R (xs i)) :
    Hereditary R (.free d xs) := by
  let P (t : Term s) := Hereditary R t ∨ ∃ ys, t = .free d ys ∧ ∀ i, Hereditary R (ys i)
  apply Hereditary.of_invariant P _ _ _ (.inr ⟨xs,rfl,kids⟩)
  · rintro t (h|⟨ys,rfl,hy⟩)
    · exact h.settles
    · exact settle ys hy
  · rintro a b (h|⟨ys,rfl,hy⟩) red
    · exact .inl (h.follow (.reduces red))
    · rcases reduces_free_until d ys (Hereditary R) (fun h step => h.follow (.reduces step))
        (fun zs rs => root zs (fun i => (hy i).follow (.reduces (rs i)))) red with ⟨zs,rfl,rs⟩|h
      · exact .inr ⟨zs,rfl,fun i => (hy i).follow (.reduces (rs i))⟩
      · exact .inl h
  · rintro a b (h|⟨ys,rfl,hy⟩) child
    · exact .inl (h.follow (.child child))
    · cases child with | free _ _ i => exact .inl (hy i)

theorem Hereditary.free_inert (rules : List (Equation s))
    (apps : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (f : s.FreeSym) (absent : Head.free f ∉ ConstructorVariants.ruleHeads rules)
    (slots : ∀ i, s.inputSort f i = .msg) (out : Subsort (s.outputSort f) .msg)
    (xs : Fin (s.arity f) → Term s) (kids : ∀ i, Hereditary (ruleRoot rules) (xs i)) :
    Hereditary (ruleRoot rules) (.free f xs) := by
  have inert ys t : ¬ruleRoot rules (.free f ys) t := by
    rintro ⟨r,mem,σ,e,_⟩
    apply absent
    change ConstructorVariants.head (.free f ys) ∈ ConstructorVariants.ruleHeads rules
    rw [(congrArg ConstructorVariants.head e).trans (ConstructorVariants.instance_head r (apps r mem) σ)]
    exact List.mem_map_of_mem mem
  apply Hereditary.free_active f _ (fun ys _ t fire => (inert ys t fire).elim) xs kids
  intro ys hy
  let ns i := (hy i).settles.choose
  have ok i := (hy i).settles.choose_spec
  exact ⟨.free f ns,ConstructorVariants.constructor_node_normal rules apps _ absent (fun i => (ok i).1),
    (HasSort.free f ns (fun i => slots i ▸ (ok i).2.1)).widen out,
    Converges.free f inert (fun i => (ok i).2.2)⟩

end Tamarin.Rewriting
