import TamarinRuntime.Residual
import Tamarin.Commutative
import Tamarin.FiniteOccurs
import Tamarin.VariableElimination
import Tamarin.MatchingFree

namespace Tamarin.Residual
variable {sig : Signature}

def kind : Term sig → UInt8
  | .var _ => 0 | .atom _ => 1 | .free .. => 2 | .comm .. => 3 | .ac .. => 4

private abbrev head (t : Term sig) := (headModel sig).eval Head.var t

/-- The flags are facts about the two current operands after applying all
prior bindings. Only root sorts of well-sorted terms are used. -/
inductive Input : Term sig → Term sig → UInt8 → UInt8 → Bool → Bool → Bool → Bool → Prop where
  | vars (v w : Variable) : Input (.var v) (.var w) 0 0 false
      (Subsort.check w.sort v.sort) (Subsort.check v.sort w.sort) false
  | left (v : Variable) (t : Term sig) (rigid : kind t ≠ 0) (typed : HasSort t t.rootSort)
      (o : Bool) (occ : o = true ↔ t.Occurs v) : Input (.var v) t 0 (kind t) false
        (Subsort.check t.rootSort v.sort) false o
  | right (v : Variable) (t : Term sig) (rigid : kind t ≠ 0) (typed : HasSort t t.rootSort)
      (o : Bool) (occ : o = true ↔ t.Occurs v) : Input t (.var v) (kind t) 0 false
        false (Subsort.check t.rootSort v.sort) o
  | different (a b : Term sig) (ra : kind a ≠ 0) (rb : kind b ≠ 0) (ne : head a ≠ head b) :
      Input a b (kind a) (kind b) false false false false
  | atom (a : sig.Atom) : Input (.atom a) (.atom a) 1 1 true false false false
  | free (f : sig.FreeSym) (xs ys : Fin (sig.arity f) → Term sig) :
      Input (.free f xs) (.free f ys) 2 2 true false false false
  | comm (f : sig.CSym) (a b c d : Term sig) :
      Input (.comm f a b) (.comm f c d) 3 3 true false false false
  | ac (f : sig.ACSym) (a b c d : Term sig) :
      Input (.ac f a b) (.ac f c d) 4 4 true false false false

/-- Every sorted pair has an admissible input description, including unequal
AC terms and terms sharing variables underneath different constructors. -/
theorem input_total (a b : Term sig) (ha : HasSort a a.rootSort) (hb : HasSort b b.rootSort) :
    ∃ h fl fr o, Input a b (kind a) (kind b) h fl fr o := by
  classical
  by_cases va : ∃ v, a = .var v
  · obtain ⟨v, rfl⟩ := va
    by_cases vb : ∃ w, b = .var w
    · obtain ⟨w, rfl⟩ := vb; exact ⟨_,_,_,_,.vars v w⟩
    · have rb : kind b ≠ 0 := by cases b <;> simp_all [kind]
      exact ⟨_,_,_,_,.left v b rb hb (decide (b.Occurs v)) (by simp)⟩
  have ra : kind a ≠ 0 := by cases a <;> simp_all [kind]
  by_cases vb : ∃ w, b = .var w
  · obtain ⟨w, rfl⟩ := vb
    exact ⟨_,_,_,_,.right w a ra ha (decide (a.Occurs w)) (by simp)⟩
  have rb : kind b ≠ 0 := by cases b <;> simp_all [kind]
  by_cases hh : head a = head b
  · refine ⟨true, false, false, false, ?_⟩
    cases a <;> cases b <;> simp_all [head, headModel, Model.eval, kind]
    all_goals subst_vars
    all_goals constructor
  · exact ⟨_,_,_,_,.different a b ra rb hh⟩

/-- Each action has an implementation-independent meaning. Either orientation
of a legal variable binding is allowed. Only an unresolved AC pair may defer. -/
inductive Justified : UInt8 → Term sig → Term sig → Prop where
  | defer (f : sig.ACSym) (a b c d : Term sig) : Justified 0 (.ac f a b) (.ac f c d)
  | clash {a b : Term sig} (impossible : ∀ σ : Substitution sig, ¬ EquivB (σ.apply a) (σ.apply b)) :
      Justified 1 a b
  | discard {a b : Term sig} (same : EquivB a b) : Justified 2 a b
  | bindLeft (v : Variable) (t : Term sig) (typed : HasSort t v.sort) (absent : ¬ t.Occurs v) :
      Justified 3 (.var v) t
  | bindRight (v : Variable) (t : Term sig) (typed : HasSort t v.sort) (absent : ¬ t.Occurs v) :
      Justified 4 t (.var v)
  | positional (f : sig.FreeSym) (xs ys : Fin (sig.arity f) → Term sig) :
      Justified 5 (.free f xs) (.free f ys)
  | orientations (f : sig.CSym) (a b c d : Term sig) :
      Justified 6 (.comm f a b) (.comm f c d)

def Correct (run : Kernel) : Prop :=
  ∀ {s : Signature} {a b : Term s} {l r h fl fr o}, Input a b l r h fl fr o →
  ∀ e : Bool, (a = b → e = true) → (e = true → EquivB a b) →
    Justified (run l r e h fl fr o) a b ∧ (e = true → run l r e h fl fr o ≠ 0)

private theorem fixedHead (t : Term sig) (r : kind t ≠ 0) (σ : Substitution sig) :
    head (σ.apply t) = head t := by cases t <;> first | rfl | exact False.elim (r rfl)

private theorem rigid_var_clash (v : Variable) (t : Term sig) (r : kind t ≠ 0)
    (bad : Subsort.check t.rootSort v.sort = false) (σ : Substitution sig) :
    ¬ EquivB (σ.image v) (σ.apply t) := by
  intro eq
  have fixed : (σ.apply t).rootSort = t.rootSort := by
    cases t <;> first | rfl | exact False.elim (r rfl)
  have le := Term.rootSort_le (σ.sorted v)
  rw [Term.rootSort_equiv eq, fixed] at le
  exact Bool.noConfusion (bad.symm.trans ((Subsort.check_iff ..).mpr le))

private theorem comparable {a b c : SortId} (ha : Subsort c a) (hb : Subsort c b) :
    Subsort a b ∨ Subsort b a := by cases ha <;> cases hb <;> first | exact Or.inl (by constructor) | exact Or.inr (by constructor)

theorem step_correct : Correct step := by
  intro s a b l r h fl fr o input eq identical sound
  cases eq with
  | true => exact ⟨.discard (sound rfl), by simp [step]⟩
  | false =>
    refine ⟨?_, by simp⟩
    have ne : a ≠ b := fun he => Bool.noConfusion (identical he)
    cases input with
    | vars v w =>
      simp only [step, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.true_or]
      split
      · next hw =>
          exact .bindLeft v _ (.widen (.var w) ((Subsort.check_iff ..).mp hw))
            (fun e => ne (congrArg Term.var e))
      · next hl =>
        split
        · next hv =>
            exact .bindRight w _ (.widen (.var v) ((Subsort.check_iff ..).mp hv))
              (fun e => ne (congrArg Term.var (Eq.symm e)))
        · next hr =>
          apply Justified.clash
          intro σ he
          have h := Term.rootSort_equiv he
          change (σ.image v).rootSort = (σ.image w).rootSort at h
          have hv := Term.rootSort_le (σ.sorted v)
          rw [h] at hv
          rcases comparable hv (Term.rootSort_le (σ.sorted w)) with x | x
          · exact hr ((Subsort.check_iff ..).mpr x)
          · exact hl ((Subsort.check_iff ..).mpr x)
    | left v t rigid typed o occ =>
      cases o
      · simp [step]
        split
        · next ok =>
            exact .bindLeft v _ (.widen typed ((Subsort.check_iff ..).mp ok))
              (fun ht => Bool.noConfusion (occ.mpr ht))
        · next bad => exact .clash (rigid_var_clash v _ rigid (by simpa using bad))
      · exact .clash (FiniteOccurs.not_equiv ⟨occ.mp rfl, Ne.symm ne⟩)
    | right v t rigid typed o occ =>
      cases o
      · simp [step]
        split
        · next ok =>
            exact .bindRight v _ (.widen typed ((Subsort.check_iff ..).mp ok))
              (fun ht => Bool.noConfusion (occ.mpr ht))
        · next bad => exact .clash (fun σ he => rigid_var_clash v _ rigid (by simpa using bad) σ he.symm)
      · simp [step]
        apply Justified.clash
        intro σ he
        exact FiniteOccurs.not_equiv ⟨occ.mp rfl, ne⟩ σ he.symm
    | different a b ra rb diff =>
      simp [step, ra, rb]
      exact .clash (fun σ he => diff ((fixedHead a ra σ).symm.trans (he.head_eq.trans (fixedHead b rb σ))))
    | atom => exact .discard (.refl _)
    | free => exact .positional ..
    | comm => exact .orientations ..
    | ac => exact .defer ..

end Tamarin.Residual
