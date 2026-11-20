import Tamarin.MixedSlotPartitions

namespace Tamarin.MixedUnification.RigidGraph
open LocalAnswers SolvedForm
variable {s : Signature}

def rigid : Constraint s → Bool
  | .ac .. => false
  | _ => true

def row (c : Constraint s) : Row s := (ref c.out,c.term (.var ∘ ref))

def graph (cs : List (Constraint s)) := (cs.filter rigid).map row

theorem mem {cs : List (Constraint s)} {d} : d ∈ graph cs ↔ ∃ c ∈ cs, rigid c ∧ row c = d := by
  simp [graph,List.mem_map,List.mem_filter,and_assoc]

theorem body (c : Constraint s) (θ : Env s) : (row c).2.subst θ = c.term (θ ∘ ref) := by
  cases c <;> rfl

theorem no_ac {c : Constraint s} (h : rigid c) (θ : Env s) (f : s.ACSym) :
    (headModel s).eval Head.var ((row c).2.subst θ) ≠ .ac f := by
  cases c <;> simp_all [rigid,row,Constraint.term,Term.subst,Model.eval,headModel]

def Separated (cs : List (Constraint s)) (V : Nat → Term s) :=
  ∀ i ∈ cs.flatMap Constraint.slots, ∀ j ∈ cs.flatMap Constraint.slots, EquivB (V i) (V j) → i = j

/-- In the exact source partition, equality of two free applications identifies
each corresponding child. Equality at a C head admits the two alignments. -/
theorem agree (cs : List (Constraint s)) (V : Nat → Term s)
    (model : ∀ c ∈ cs, c.Holds V) (sep : Separated cs V) : Agree (graph cs) := by
  intro d hd e he same
  obtain ⟨c,hc,rc,rfl⟩ := mem.mp hd
  obtain ⟨b,hb,rb,rfl⟩ := mem.mp he
  have out := congrArg Variable.id same
  change c.out = b.out at out
  have first := model c hc
  have second := model b hb
  unfold Constraint.Holds at first second
  rw [out] at first
  have eq := first.symm.trans second
  have heads := eq.head_eq
  have identify (i) (hi : i ∈ c.slots) (j) (hj : j ∈ b.slots) :=
    sep i (List.mem_flatMap.mpr ⟨c,hc,hi⟩) j (List.mem_flatMap.mpr ⟨b,hb,hj⟩)
  cases c <;> cases b <;> simp_all only [rigid,Bool.false_eq_true,Constraint.term,
    Model.eval,headModel,Head.atom.injEq,Head.free.injEq,Head.comm.injEq,reduceCtorEq]
  case atom.atom =>
    rename_i _ a _ b; have ab : a = b := heads; subst b; exact .refl _
  case free.free _ f xs _ g ys =>
    have fg : f = g := by simpa using heads
    subst g
    apply EquivB.free
    intro i
    have same := identify (xs i) (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
      (ys i) (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
      ((Matching.free_equiv_iff ..).mp eq i)
    change EquivB (.var (ref (xs i))) (.var (ref (ys i)))
    rw [same]; exact .refl _
  case comm.comm _ f i j _ g u v =>
    have fg : f = g := by simpa using heads
    subst g
    rcases (Commutative.equiv_iff ..).mp eq with ⟨left,right⟩ | ⟨left,right⟩
    · have h := identify i (by simp [Constraint.slots]) u (by simp [Constraint.slots]) left
      have k := identify j (by simp [Constraint.slots]) v (by simp [Constraint.slots]) right
      subst u; subst v; exact .refl _
    · have h := identify i (by simp [Constraint.slots]) v (by simp [Constraint.slots]) left
      have k := identify j (by simp [Constraint.slots]) u (by simp [Constraint.slots]) right
      subst u; subst v; exact .comm_swap _ _ _

end Tamarin.MixedUnification.RigidGraph
