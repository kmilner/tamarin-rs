import Tamarin.ACReference
import Tamarin.FiniteOccurs
import Tamarin.ReferenceMatching
import Tamarin.TermEquality
import Tamarin.UnifierSorts

/-! Purification for simultaneous free, C and AC unification. Each distinct source
subterm has a slot. Equations identify their root slots before we emit the local
constructor constraints. Slots are shared between components and have no assigned
sort at this stage. -/
namespace Tamarin.MixedUnification
variable {s : Signature}

def subterms : Term s → List (Term s)
  | t@(.var _) | t@(.atom _) => [t]
  | t@(.free _ xs) => t :: (List.ofFn fun i => subterms (xs i)).flatten
  | t@(.comm _ a b) | t@(.ac _ a b) => t :: (subterms a ++ subterms b)

private theorem self_mem (t : Term s) : t ∈ subterms t := by
  cases t <;> simp [subterms]

private theorem var_mem {t : Term s} {v : Variable} (h : t.Occurs v) :
    .var v ∈ subterms t := by
  induction t with
  | var w => cases h; simp [subterms]
  | atom => exact False.elim h
  | free f xs ih =>
    obtain ⟨i,hi⟩ := h
    exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,ih i hi⟩)
  | comm f a b ia ib | ac f a b ia ib =>
    exact List.mem_cons_of_mem _ (List.mem_append.mpr (h.imp ia ib))

private theorem descend {t : Term s} (a : Term s) :
    t ∈ subterms a → ∀ u ∈ subterms t, u ∈ subterms a := by
  induction a with
  | var | atom => intro h; obtain rfl := List.mem_singleton.mp h; exact fun _ => id
  | free f xs ih =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · exact fun _ => id
    · obtain ⟨l,hl,hit⟩ := List.mem_flatten.mp h
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
      exact fun u hu => List.mem_cons_of_mem _ (List.mem_flatten.mpr
        ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,ih i hit u hu⟩)
  | comm f a b ia ib | ac f a b ia ib =>
    intro h
    rcases List.mem_cons.mp h with rfl | h
    · exact fun _ => id
    · rcases List.mem_append.mp h with ha | hb
      · exact fun u hu => List.mem_cons_of_mem _ (List.mem_append_left _ (ia ha u hu))
      · exact fun u hu => List.mem_cons_of_mem _ (List.mem_append_right _ (ib hb u hu))

private def redirect (lhs rhs slot : Nat) := if slot = lhs then rhs else slot

/-- Merge a pair of root slots globally. Every previous identification survives
the remaining merges, including cycles of variable aliases. -/
private def identify (key : Term s → Nat) : Problem s → Term s → Nat
  | [] => key
  | e :: es => identify (redirect (key e.lhs) (key e.rhs) ∘ key) es

private theorem identify_preserves (p : Problem s) (k : Term s → Nat) {a b} (h : k a = k b) :
    identify k p a = identify k p b := by
  induction p generalizing k with
  | nil => exact h
  | cons e es ih => apply ih; simp [h]

private theorem identify_links (p : Problem s) (k : Term s → Nat) :
    ∀ e ∈ p, identify k p e.lhs = identify k p e.rhs := by
  induction p generalizing k with
  | nil => simp
  | cons e es ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · unfold identify; apply identify_preserves; simp [redirect]
    · exact ih _ x hx

private theorem identify_values (p : Problem s) (k : Term s → Nat) (V : Nat → Term s)
    (links : ∀ e ∈ p, EquivB (V (k e.lhs)) (V (k e.rhs))) (t : Term s) :
    EquivB (V (k t)) (V (identify k p t)) := by
  induction p generalizing k with
  | nil => exact .refl _
  | cons e es ih =>
    let next := redirect (k e.lhs) (k e.rhs) ∘ k
    have step (x) : EquivB (V (k x)) (V (next x)) := by
      by_cases h : k x = k e.lhs
      · simpa [next,Function.comp_def,redirect,h] using links e List.mem_cons_self
      · simp [next,Function.comp_def,redirect,h]; exact .refl _
    exact (step t).trans (ih next (fun x hx => (step x.lhs).symm.trans
      ((links x (List.mem_cons_of_mem _ hx)).trans (step x.rhs))) )

inductive Constraint (s : Signature) where
  | atom (out : Nat) (a : s.Atom)
  | free (out : Nat) (f : s.FreeSym) (args : Fin (s.arity f) → Nat)
  | comm (out : Nat) (f : s.CSym) (lhs rhs : Nat)
  | ac (out : Nat) (f : s.ACSym) (lhs rhs : Nat)

def Constraint.out : Constraint s → Nat
  | .atom n _ | .free n .. | .comm n .. | .ac n .. => n

def Constraint.term (V : Nat → Term s) : Constraint s → Term s
  | .atom _ a => .atom a
  | .free _ f args => .free f fun i => V (args i)
  | .comm _ f a b => .comm f (V a) (V b)
  | .ac _ f a b => .ac f (V a) (V b)

def Constraint.Holds (V : Nat → Term s) (c : Constraint s) := EquivB (V c.out) (c.term V)

private def describe (k : Term s → Nat) : Term s → Option (Constraint s)
  | .var _ => none
  | t@(.atom a) => some (.atom (k t) a)
  | t@(.free f xs) => some (.free (k t) f fun i => k (xs i))
  | t@(.comm f a b) => some (.comm (k t) f (k a) (k b))
  | t@(.ac f a b) => some (.ac (k t) f (k a) (k b))

structure System (s : Signature) where
  slot : Term s → Nat
  constraints : List (Constraint s)

def System.Model (q : System s) (V : Nat → Term s) := ∀ c ∈ q.constraints, c.Holds V

def inventory [DecidableEq (Term s)] (p : Problem s) :=
  (p.flatMap fun e => subterms e.lhs ++ subterms e.rhs).eraseDups

def purify [DecidableEq (Term s)] (p : Problem s) : System s :=
  let ts := inventory p
  let k := identify ts.idxOf p
  ⟨k, ts.filterMap (describe k)⟩

private theorem inside [DecidableEq (Term s)] {p : Problem s} {e} (he : e ∈ p) {t}
    (ht : t ∈ subterms e.lhs ∨ t ∈ subterms e.rhs) : t ∈ inventory p :=
  List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨e,he,List.mem_append.mpr ht⟩)

private theorem interpret {k : Term s → Nat} {V : Nat → Term s} (t : Term s)
    (models : ∀ u ∈ subterms t, ∀ c ∈ describe k u, c.Holds V) :
    EquivB (V (k t)) (t.subst (fun v => V (k (.var v)))) := by
  induction t with
  | var => exact .refl _
  | atom a => exact models _ (self_mem _) _ rfl
  | free f xs ih =>
    apply (models _ (self_mem _) _ rfl).trans
    apply EquivB.free
    intro i
    apply ih i
    intro u hu
    exact models u (List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hu⟩))
  | comm f a b ia ib | ac f a b ia ib =>
    apply (models _ (self_mem _) _ rfl).trans
    first | apply EquivB.comm_congr | apply EquivB.ac_congr
    · apply ia
      exact fun u hu => models u (List.mem_cons_of_mem _ (List.mem_append_left _ hu))
    · apply ib
      exact fun u hu => models u (List.mem_cons_of_mem _ (List.mem_append_right _ hu))

section Purification
variable [DecidableEq (Term s)]

def project (q : System s) (V : Nat → Term s) : UnifierSorts.Template s :=
  fun v => V (q.slot (.var v))

theorem project_solves (p : Problem s) {V} (model : (purify p).Model V) :
    ∀ e ∈ p, EquivB (e.lhs.subst (project (purify p) V)) (e.rhs.subst (project (purify p) V)) := by
  intro e he
  have known (t) (ht : t ∈ inventory p) (c) (hc : c ∈ describe (purify p).slot t) :=
    model c (List.mem_filterMap.mpr ⟨t,ht,hc⟩)
  have left := interpret e.lhs (fun u hu => known u (inside he (.inl hu)))
  have right := interpret e.rhs (fun u hu => known u (inside he (.inr hu)))
  have same : (purify p).slot e.lhs = (purify p).slot e.rhs := identify_links p _ e he
  rw [← same] at right
  exact left.symm.trans right

/-- Every source solution gives the same value modulo B to subterms whose
slots coincide, including aliases forced by a chain of input equations. -/
theorem inventory_values (p : Problem s) (θ : UnifierSorts.Template s)
    (sol : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    ∃ V : Nat → Term s, ∀ t ∈ inventory p, EquivB (t.subst θ) (V ((purify p).slot t)) := by
  let ts := inventory p
  let V := fun (i : Nat) => ((ts[i]?).getD (Term.var ⟨0,.msg⟩)).subst θ
  have lookup (t : Term s) (ht : t ∈ ts) : V (ts.idxOf t) = t.subst θ := by
    simp [V,List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem ht),List.getElem_idxOf]
  have links (e) (he : e ∈ p) : EquivB (V (ts.idxOf e.lhs)) (V (ts.idxOf e.rhs)) := by
    rw [lookup _ (inside he (.inl (self_mem _))),lookup _ (inside he (.inr (self_mem _)))]
    exact sol e he
  exact ⟨V, fun t ht => lookup t ht ▸ identify_values p ts.idxOf V links t⟩

theorem extend_inventory (p : Problem s) (θ : UnifierSorts.Template s)
    (sol : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    ∃ V, (purify p).Model V ∧ ∀ t ∈ inventory p, EquivB (t.subst θ) (V ((purify p).slot t)) := by
  let ts := inventory p
  obtain ⟨V,val⟩ := inventory_values p θ sol
  refine ⟨V,?_,?_⟩
  · intro c hc
    obtain ⟨t,ht,eq⟩ := List.mem_filterMap.mp hc
    have children : ∀ u ∈ subterms t, u ∈ ts := by
      obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp ht)
      exact fun u hu => inside he ((List.mem_append.mp hm).imp
        (fun h => descend _ h u hu) (fun h => descend _ h u hu))
    have out := (val t ht).symm
    cases t with
    | var => simp [describe] at eq
    | atom a => cases eq; exact out
    | free f xs =>
      cases eq
      exact out.trans (.free _ _ _ (fun i => val _ (children _ (List.mem_cons_of_mem _
        (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,self_mem _⟩)))))
    | comm f a b | ac f a b =>
      cases eq
      have left := val a (children _ (List.mem_cons_of_mem _ (List.mem_append_left _ (self_mem a))))
      have right := val b (children _ (List.mem_cons_of_mem _ (List.mem_append_right _ (self_mem b))))
      first | exact out.trans (.comm_congr _ left right) | exact out.trans (.ac_congr _ left right)
  · exact val

theorem var_in_inventory {p : Problem s} {v} (h : p.Occurs v) : .var v ∈ inventory p := by
  obtain ⟨e,he,hv⟩ := h
  exact inside he (hv.imp var_mem var_mem)

theorem extend_solution (p : Problem s) (θ : UnifierSorts.Template s)
    (sol : ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)) :
    ∃ V, (purify p).Model V ∧ ∀ v, p.Occurs v → EquivB (θ v) (project (purify p) V v) := by
  obtain ⟨V,h,values⟩ := extend_inventory p θ sol
  exact ⟨V,h,fun _ hv => values _ (var_in_inventory hv)⟩

end Purification

private def inputs : Constraint s → List Nat
  | .atom .. => []
  | .free _ _ args => List.ofFn args
  | .comm _ _ a b | .ac _ _ a b => [a,b]

private theorem child_smaller {V : Nat → Term s} {c : Constraint s}
    (h : c.Holds V) {i} (hi : i ∈ inputs c) :
    FiniteOccurs.nodes (V i) < FiniteOccurs.nodes (V c.out) := by
  rw [FiniteOccurs.nodes_equiv h]
  cases c with
  | atom => cases hi
  | free n f args =>
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
    let weights := List.ofFn (fun j => FiniteOccurs.nodes (V (args j)))
    have le (xs : List Nat) (m : Nat) (hm : m ∈ xs) : m ≤ xs.sum := by
      induction xs with
      | nil => cases hm
      | cons a xs ih =>
        rcases List.mem_cons.mp hm with rfl | hm
        · simp
        · simp only [List.sum_cons]; have := ih hm; omega
    have := le weights _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    change _ < weights.sum + 1
    omega
  | ac _ f a b | comm _ f a b =>
    change _ < FiniteOccurs.nodes (V a) + FiniteOccurs.nodes (V b) + 1
    rcases List.mem_cons.mp hi with rfl | hi
    · omega
    · obtain rfl := List.mem_singleton.mp hi; omega

private def ready (todo : List (Constraint s)) (c : Constraint s) :=
  (inputs c).all fun i => !todo.any (fun d => d.out == i)

/-- In a finite-term model, some pending constructor of least output size
has all its inputs available. This holds across different component heads. -/
private theorem ready_exists {V : Nat → Term s} (todo : List (Constraint s))
    (model : ∀ c ∈ todo, c.Holds V) (c : Constraint s) (hc : c ∈ todo) :
    ∃ d ∈ todo, ready todo d := by
  by_cases ok : ready todo c
  · exact ⟨c,hc,ok⟩
  · simp [ready] at ok
    obtain ⟨i,hi,d,hd,eq⟩ := ok
    have lt := child_smaller (model c hc) hi
    rw [← eq] at lt
    exact ready_exists todo model d hd
termination_by FiniteOccurs.nodes (V c.out)

private def Factors (V images : Nat → Term s) (μ : Variable → Term s) :=
  ∀ i, EquivB (V i) ((images i).subst μ)

private def install (images : Nat → Term s) (c : Constraint s) (i : Nat) : Term s :=
  if i = c.out then c.term images else images i

private theorem install_factors {V images : Nat → Term s} {μ} {c : Constraint s}
    (h : Factors V images μ) (hc : c.Holds V) : Factors V (install images c) μ := by
  intro i
  by_cases eq : i = c.out
  · subst i
    simp only [install,ite_true]
    apply hc.trans
    cases c with
    | atom => exact .refl _
    | free => exact .free _ _ _ (fun i => h _)
    | comm => exact .comm_congr _ (h _) (h _)
    | ac => exact .ac_congr _ (h _) (h _)
  · simpa [install,eq] using h i

/-- Every defined slot has one constructor description. Arbitrarily many
constraints may share its value as an input, including in other components. -/
def SingleDefinition (cs : List (Constraint s)) :=
  ∀ c ∈ cs, ∀ d ∈ cs, c.out = d.out → c = d

/-- Several definitions of a slot can describe the same constructor value
under every valuation, for example after commutative alignment. -/
def AgreeingDefinitions (cs : List (Constraint s)) :=
  ∀ c ∈ cs, ∀ d ∈ cs, c.out = d.out → ∀ V, EquivB (c.term V) (d.term V)

private structure Reconstructed (todo : List (Constraint s)) (images : Nat → Term s)
    (r : Option (Nat → Term s)) : Prop where
  covers : ∀ V μ, (∀ c ∈ todo, c.Holds V) → Factors V images μ →
    ∃ row, r = some row ∧ Factors V row μ
  stable : ∀ row, r = some row → ∀ i, (∀ c ∈ todo, c.out ≠ i) → row i = images i
  solves : ∀ row, r = some row → AgreeingDefinitions todo → ∀ c ∈ todo, c.Holds row

private theorem term_agree (c : Constraint s) {V W : Nat → Term s}
    (h : ∀ i ∈ inputs c, V i = W i) : c.term V = c.term W := by
  cases c with
  | atom => rfl
  | free f g args =>
    apply congrArg (Term.free g)
    exact funext (fun i => h _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  | ac | comm =>
    simp [Constraint.term,h _ List.mem_cons_self,h _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))]

/-- Build a schematic valuation using a constructor for each defined slot.
Multiple definitions are constraints on the same output and are all checked
after construction. A dependency cycle with no ready constructor refutes
every finite valuation. -/
private def reconstruct (todo : List (Constraint s)) (images : Nat → Term s) :
    {r : Option (Nat → Term s) // Reconstructed todo images r} := by
  match todo with
  | [] => exact ⟨some images,⟨fun _ _ _ h => ⟨_,rfl,h⟩,
      fun _ eq _ _ => by cases eq; rfl, by simp⟩⟩
  | c :: cs =>
    let pending := c :: cs
    match found : pending.find? (ready pending) with
    | none =>
      refine ⟨none,⟨fun V μ model _ => ?_,by simp,by simp⟩⟩
      obtain ⟨d,hd,ok⟩ := ready_exists pending model c List.mem_cons_self
      exact False.elim ((List.find?_eq_none.mp found d hd) ok)
    | some d =>
      have hd := List.mem_of_find?_eq_some found
      let rest := pending.filter fun e => e.out != d.out
      have smaller : rest.length < pending.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨d,hd,by simp⟩
      let recursed := reconstruct rest (install images d)
      have subset {e} (he : e ∈ rest) := (List.mem_filter.mp he).1
      refine ⟨recursed.val,⟨fun V μ model h => recursed.property.covers V μ
        (fun e he => model e (subset he)) (install_factors h (model d hd)),?_,?_⟩⟩
      · intro row hr i external
        rw [recursed.property.stable row hr i (fun e he => external e (subset he))]
        simp [install,Ne.symm (external d hd)]
      · intro row hr unique e he
        by_cases same : e.out = d.out
        · unfold Constraint.Holds
          rw [same]
          apply EquivB.trans _ (unique d hd e he same.symm row)
          have chosen := List.find?_some found
          have available (i) (hi : i ∈ inputs d) : ∀ x ∈ pending, x.out ≠ i := by
            simpa [ready,List.all_eq_true] using (List.all_eq_true.mp chosen i hi)
          have kept (i) (hi : i ∈ inputs d) : row i = images i := by
            rw [recursed.property.stable row hr i (fun x hx => available i hi x (subset hx))]
            simp [install,Ne.symm (available i hi d hd)]
          rw [term_agree d kept,recursed.property.stable row hr d.out
            (fun x hx => by simpa using (List.mem_filter.mp hx).2)]
          simp [install]; exact .refl _
        · exact recursed.property.solves row hr (fun x hx y hy => unique x (subset hx) y (subset hy))
            e (List.mem_filter.mpr ⟨he,by simpa using same⟩)
termination_by todo.length

section Solve
variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

/-- A completed result is a mathematically complete raw family. If the
schematic valuation needs further unification among constructor definitions,
leave the query open for component solving. -/
def reconstruct? (p : Problem s) : Option (List (UnifierSorts.Template s)) :=
  let q := purify p
  match (reconstruct q.constraints (fun i => .var ⟨i,.msg⟩)).val with
  | none => some []
  | some row =>
    if q.constraints.all (fun c => ReferenceMatching.equal (row c.out) (c.term row))
    then some [project q row] else none

theorem reconstruct_correct {p : Problem s} {rows} (result : reconstruct? p = some rows) :
    UnifierSorts.CompleteTemplates p rows := by
  let q := purify p
  let r := reconstruct q.constraints (fun i => .var ⟨i,.msg⟩)
  have survives (ρ : Substitution s) (sol : p.Solves ρ) :
      ∃ row, r.val = some row ∧ ∃ μ, ∀ v, p.Occurs v →
        EquivB (ρ.image v) (((project q row) v).subst μ) := by
    obtain ⟨V,hV,agree⟩ := extend_solution p ρ.image sol
    let μ := fun (w : Variable) => V w.id
    obtain ⟨row,hr,hrow⟩ := r.property.covers V μ hV (fun i => .refl _)
    exact ⟨row,hr,μ,fun v hv => (agree v hv).trans (hrow _)⟩
  unfold reconstruct? at result
  change (match r.val with
    | none => some []
    | some row => if q.constraints.all (fun c => ReferenceMatching.equal (row c.out) (c.term row))
      then some [project q row] else none) = some rows at result
  cases hr : r.val with
  | none =>
    simp [hr] at result
    subst rows
    refine ⟨by simp,fun ρ h => ?_⟩
    obtain ⟨_,bad,_⟩ := survives ρ h
    simp [hr] at bad
  | some row =>
    simp only [hr] at result
    split at result
    next ok =>
      cases result
      have model : q.Model row := fun c hc =>
        (ReferenceMatching.equal_iff ..).mp (List.all_eq_true.mp ok c hc)
      refine ⟨?_,?_⟩
      · intro θ hθ
        obtain rfl := List.mem_singleton.mp hθ
        exact project_solves p model
      · intro ρ h
        obtain ⟨r',same,μ,agree⟩ := survives ρ h
        rw [hr] at same
        cases same
        exact ⟨_,List.mem_singleton_self _,μ,agree⟩
    next => contradiction

/-- A structural coverage guarantee independent of a successful run. When definitions of each slot
agree under every valuation, reconstruction produces a most general row or
refutes a constructor cycle, including across different operators. -/
theorem reconstructs_agreeing (p : Problem s)
    (h : AgreeingDefinitions (purify p).constraints) : (reconstruct? p).isSome := by
  let q := purify p
  let r := reconstruct q.constraints (fun i => .var ⟨i,.msg⟩)
  change (match r.val with
    | none => some []
    | some row =>
      if q.constraints.all (fun c => ReferenceMatching.equal (row c.out) (c.term row)) then
        some [project q row]
      else none).isSome = true
  cases hr : r.val with
  | none => rfl
  | some row =>
    have ok := List.all_eq_true.mpr (fun c hc => (ReferenceMatching.equal_iff ..).mpr
      (r.property.solves row hr h c hc))
    simp [ok]

theorem reconstructs_singleDefinition (p : Problem s)
    (h : SingleDefinition (purify p).constraints) : (reconstruct? p).isSome :=
  reconstructs_agreeing p (fun c hc d hd eq _ => (h c hc d hd eq) ▸ EquivB.refl _)

end Solve

namespace System
variable [DecidableEq s.ACSym]

private def coordinate (f : s.ACSym) (i : Nat) : Variable := ⟨i,s.acSort f⟩

private def asRow (f : s.ACSym) : Constraint s → Option ACSystem.Row
  | .ac n g a b => if f = g then
      some ⟨⟨coordinate f n,[]⟩,⟨coordinate f a,[coordinate f b]⟩⟩ else none
  | _ => none

/-- The equations of one AC operator form a single homogeneous system. Reused
slots keep the same coordinate on either side and across equations. -/
def rows (q : System s) (f : s.ACSym) : List ACSystem.Row := q.constraints.filterMap (asRow f)

def remaining (q : System s) (f : s.ACSym) : List (Constraint s) :=
  q.constraints.filter (fun c => (asRow f c).isNone)

theorem component_iff (q : System s) (f : s.ACSym) (V : Nat → Term s) :
    q.Model V ↔
      (∀ e ∈ ACSystem.problem f (q.rows f),
        EquivB (e.lhs.subst (fun v => V v.id)) (e.rhs.subst (fun v => V v.id))) ∧
      ∀ c ∈ q.remaining f, c.Holds V := by
  have represents (c : Constraint s) (r : ACSystem.Row) (h : asRow f c = some r) :
      c.Holds V ↔ EquivB ((r.equation f).lhs.subst (fun v => V v.id))
        ((r.equation f).rhs.subst (fun v => V v.id)) := by
    cases c with
    | atom | free | comm => contradiction
    | ac n g a b =>
      simp [asRow] at h
      obtain ⟨rfl,rfl⟩ := h
      rfl
  constructor
  · intro h
    refine ⟨?_,fun c hc => h c (List.mem_filter.mp hc).1⟩
    intro e he
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp he
    obtain ⟨c,hc,eq⟩ := List.mem_filterMap.mp hr
    exact (represents c r eq).mp (h c hc)
  · rintro ⟨hm,rest⟩ c hc
    cases h : asRow f c with
    | none => exact rest c (List.mem_filter.mpr ⟨hc,by simp [h]⟩)
    | some r =>
      exact (represents c r h).mpr (hm _ (List.mem_map_of_mem (List.mem_filterMap.mpr ⟨c,hc,h⟩)))

private theorem sorted (q : System s) (f : s.ACSym) :
    ∀ v ∈ ACSystem.variables (q.rows f), v.sort = s.acSort f := by
  intro v hv
  obtain ⟨r,hr,hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨c,_,eq⟩ := List.mem_filterMap.mp hr
  cases c with
  | atom | free | comm => contradiction
  | ac _ g a b =>
    simp [asRow] at eq
    obtain ⟨rfl,rfl⟩ := eq
    simp [ACSystem.Side.vars] at hv
    rcases hv with rfl | rfl | rfl <;> rfl

def solveComponent (q : System s) (f : s.ACSym) (avoid : List Variable) :=
  ACSystem.Reference.solve f (q.rows f) (sorted q f) avoid

theorem component_correct (q : System s) (f : s.ACSym) (avoid : List Variable) :
    (Outcome.complete (q.solveComponent f avoid)).CorrectIn (ACSystem.problem f (q.rows f)) avoid :=
  ACSystem.Reference.correct f (q.rows f) (sorted q f) avoid

end System
end Tamarin.MixedUnification
