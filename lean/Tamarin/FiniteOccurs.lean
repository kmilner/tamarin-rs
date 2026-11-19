import Tamarin.Models
import Tamarin.Substitution

/-! In the finite free/C/AC algebra, B-equivalence preserves node counts.
Consequently a variable cannot be instantiated by a proper context containing
its own image, including when further AC factors surround that context. -/
namespace Tamarin.FiniteOccurs
variable {sig : Signature}

def Proper (v : Variable) (t : Term sig) := t.Occurs v ∧ t ≠ .var v

/-- A reassociation of binary AC nodes preserves the number of nodes. -/
private def nodeModel (sig : Signature) : Model sig where
  Carrier := Nat
  atom := fun _ => 1
  free := fun _ children => (List.ofFn children).sum + 1
  comm := fun _ a b => a + b + 1
  ac := fun _ a b => a + b + 1
  comm_swap := by intros; omega
  ac_swap := by intros; omega
  ac_assoc := by intros; omega

def nodes (t : Term sig) : Nat := (nodeModel sig).eval (fun _ => (1 : Nat)) t

theorem nodes_equiv {a b : Term sig} (e : EquivB a b) : nodes a = nodes b :=
  e.eval_eq (nodeModel sig) (fun _ => (1 : Nat))

private theorem le_sum (n : Nat) (ns : List Nat) (h : n ∈ ns) : n ≤ ns.sum := by
  induction ns with
  | nil => cases h
  | cons m ms ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · have := ih hm; simp only [List.sum_cons]; omega

private theorem occurs_nodes (subst : Variable → Term sig) (v : Variable) (t : Term sig)
    (occurs : t.Occurs v) : nodes (subst v) ≤ nodes (t.subst subst) ∧
      (t ≠ .var v → nodes (subst v) < nodes (t.subst subst)) := by
  induction t with
  | var u => obtain rfl := occurs; exact ⟨Nat.le_refl _, fun h => False.elim (h rfl)⟩
  | atom => exact False.elim occurs
  | free f args ih =>
    obtain ⟨i, hi⟩ := occurs
    let weights := fun j => nodes ((args j).subst subst)
    have hb := le_sum (weights i) (List.ofFn weights) (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have below : nodes (subst v) ≤ weights i := (ih i hi).1
    change _ ≤ (List.ofFn weights).sum + 1 ∧ (_ → _ < (List.ofFn weights).sum + 1)
    omega
  | comm _ a b ia ib | ac _ a b ia ib =>
    change _ ≤ nodes (a.subst subst) + nodes (b.subst subst) + 1 ∧
      (_ → _ < nodes (a.subst subst) + nodes (b.subst subst) + 1)
    rcases occurs with ha | hb
    · have := (ia ha).1; omega
    · have := (ib hb).1; omega

theorem proper_nodes {x : Variable} {a : Term sig} (h : Proper x a) (σ : Substitution sig) :
    nodes (σ.image x) < nodes (σ.apply a) := (occurs_nodes σ.image x a h.1).2 h.2

theorem not_equiv {x : Variable} {a : Term sig} (h : Proper x a) (σ : Substitution sig) :
    ¬ EquivB (σ.image x) (σ.apply a) := by
  intro e; exact Nat.ne_of_lt (proper_nodes h σ) (nodes_equiv e)

theorem not_equiv_ac {x : Variable} {a : Term sig} (h : Proper x a) (σ : Substitution sig)
    (f : sig.ACSym) (r : Term sig) : ¬ EquivB (σ.image x) (.ac f (σ.apply a) r) := by
  intro e
  have he := nodes_equiv e
  change nodes (σ.image x) = nodes (σ.apply a) + nodes r + 1 at he
  have := proper_nodes h σ
  omega

theorem not_equiv_ac_swap {x : Variable} {a : Term sig} (h : Proper x a) (σ : Substitution sig)
    (f : sig.ACSym) (r : Term sig) : ¬ EquivB (σ.image x) (.ac f r (σ.apply a)) :=
  fun e => not_equiv_ac h σ f r (e.trans (.ac_swap f r (σ.apply a)))

end Tamarin.FiniteOccurs
