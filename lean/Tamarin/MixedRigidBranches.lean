import Tamarin.MixedReconstruction

/-! Congruence constraints between rigid terms whose outputs have been
identified. Consume each pair once. Additional child equations may enable
previously unrelated pairs, including under different constructors. -/
namespace Tamarin.MixedUnification.RigidBranches
variable {s : Signature}

abbrev Solves (p : Problem s) (θ : UnifierSorts.Template s) :=
  ∀ e ∈ p, EquivB (e.lhs.subst θ) (e.rhs.subst θ)

private theorem append_iff (a b : Problem s) (θ) :
    Solves (a ++ b) θ ↔ Solves a θ ∧ Solves b θ := by
  simp [Solves,List.mem_append,or_imp,forall_and]

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym]

private def align : Term s → Term s → List (Problem s)
  | .free f xs,.free g ys =>
    if eq : f = g then [List.ofFn fun i => ⟨xs i,ys (eq ▸ i)⟩] else []
  | .comm f a b,.comm g c d =>
    if f = g then [[⟨a,c⟩,⟨b,d⟩],[⟨a,d⟩,⟨b,c⟩]] else []
  | _,_ => []

private theorem align_covers (a b : Term s) (θ : UnifierSorts.Template s)
    (active : align a b ≠ []) (eq : EquivB (a.subst θ) (b.subst θ)) :
    ∃ extra ∈ align a b, Solves extra θ := by
  cases a <;> cases b <;> try contradiction
  case free.free f xs g ys =>
    by_cases same : f = g
    · subst g
      simp only [align,↓reduceDIte]
      refine ⟨_,List.mem_singleton_self _,?_⟩

      intro e he
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      exact (Matching.free_equiv_iff ..).mp eq i
    · simp [align,same] at active
  case comm.comm f a b g c d =>
    by_cases same : f = g
    · subst g
      simpa [align,Solves] using (Commutative.equiv_iff ..).mp eq
    · simp [align,same] at active

variable [DecidableEq (Term s)]

private abbrev Pair (s : Signature) := Term s × Term s

private def rigid : Term s → Bool
  | .free .. | .comm .. => true
  | _ => false

/-- The input term list is already interned. Only unordered pairs can give
new obligations, and zero-arity and syntactically distinct heads never branch. -/
private def pairs : List (Term s) → List (Pair s)
  | [] => []
  | t :: ts => (ts.filterMap fun u => if (align t u).isEmpty then none else some (t,u)) ++ pairs ts

private def enabled (q : System s) (pair : Pair s) :=
  q.slot pair.1 == q.slot pair.2 &&
  !(align pair.1 pair.2).any (fun es => es.all fun e => q.slot e.lhs == q.slot e.rhs)

omit [DecidableEq s.FreeSym] [DecidableEq s.CSym] in
private theorem inventory_append (before p : Problem s) {t} (h : t ∈ inventory p) :
    t ∈ inventory (before ++ p) := by
  simpa [inventory] using Or.inr (a := t ∈ before.flatMap (fun e => subterms e.lhs ++ subterms e.rhs))
    (List.mem_eraseDups.mp h)

private def loop (todo : List (Pair s)) (p : Problem s)
    (inside : ∀ z ∈ todo, z.1 ∈ inventory p ∧ z.2 ∈ inventory p ∧ align z.1 z.2 ≠ []) :
    {ps : List (Problem s) // (∀ child ∈ ps, ∀ e ∈ p, e ∈ child) ∧
      ∀ θ, Solves p θ → ∃ child ∈ ps, Solves child θ} := by
  let q := purify p
  match hit : todo.find? (enabled q) with
  | none => exact ⟨[p],⟨by simp,fun _ h => ⟨_,List.mem_singleton_self _,h⟩⟩⟩
  | some z =>
    have hz := List.mem_of_find?_eq_some hit
    let rest := todo.filter (· != z)
    have lt : rest.length < todo.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨z,hz,by simp⟩
    let visit (extra : Problem s) := loop rest (extra ++ p) (fun t ht => by
      obtain ⟨ha,hb,ok⟩ := inside t (List.mem_filter.mp ht).1
      exact ⟨inventory_append _ _ ha,inventory_append _ _ hb,ok⟩)
    refine ⟨(align z.1 z.2).flatMap (fun es => (visit es).val),?_,?_⟩
    · intro child hc e he
      obtain ⟨es,_,hmem⟩ := List.mem_flatMap.mp hc
      exact (visit es).property.1 child hmem e (List.mem_append_right _ he)
    · intro θ sol
      obtain ⟨V,hV⟩ := inventory_values p θ sol
      obtain ⟨ha,hb,ok⟩ := inside z hz
      have yes := List.find?_some hit
      simp only [enabled,Bool.and_eq_true,beq_iff_eq] at yes
      have same : q.slot z.1 = q.slot z.2 := yes.1
      have eq := hV _ ha
      change EquivB _ (V (q.slot z.1)) at eq
      rw [same] at eq
      obtain ⟨extra,he,hs⟩ := align_covers _ _ θ ok (eq.trans (hV _ hb).symm)
      obtain ⟨c,hc,hsol⟩ := (visit extra).property.2 θ ((append_iff ..).mpr ⟨hs,sol⟩)
      exact ⟨c,List.mem_flatMap.mpr ⟨extra,he,hc⟩,hsol⟩
termination_by todo.length

def refineProblem (p : Problem s) :
    {ps : List (Problem s) // (∀ child ∈ ps, ∀ e ∈ p, e ∈ child) ∧
      ∀ θ, Solves p θ → ∃ child ∈ ps, Solves child θ} := by
  let ts := (inventory p).filter rigid
  have members (xs : List (Term s)) (z : Pair s) (hz : z ∈ pairs xs) :
      z.1 ∈ xs ∧ z.2 ∈ xs ∧ align z.1 z.2 ≠ [] := by
    induction xs with
    | nil => contradiction
    | cons x xs ih =>
      rcases List.mem_append.mp hz with hm | hm
      · obtain ⟨y,hy,eq⟩ := List.mem_filterMap.mp hm
        split at eq
        · contradiction
        next h =>
          cases eq
          exact ⟨List.mem_cons_self,List.mem_cons_of_mem _ hy,by simpa using h⟩
      · obtain ⟨ha,hb,ok⟩ := ih hm
        exact ⟨List.mem_cons_of_mem _ ha,List.mem_cons_of_mem _ hb,ok⟩
  exact loop (pairs ts) p (fun z hz => by
    obtain ⟨ha,hb,ok⟩ := members ts z hz
    exact ⟨(List.mem_filter.mp ha).1,(List.mem_filter.mp hb).1,ok⟩)

/-- A family of search children completes only if every child completes. -/
def collect {ι α : Type} (run : ι → Option (List α)) : (xs : List ι) →
    Option {ys : List α //
      (∀ x ∈ xs, ∃ a, run x = some a ∧ a ⊆ ys) ∧
      (∀ y ∈ ys, ∃ x ∈ xs, ∃ a, run x = some a ∧ y ∈ a)}
  | [] => some ⟨[],by simp⟩
  | x :: xs => do
    let a ← (run x).attach
    let b ← collect run xs
    return ⟨a.val ++ b.val,by
      constructor
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ⟨_,a.property,fun _ hm => List.mem_append_left _ hm⟩
        · obtain ⟨out,hr,sub⟩ := b.property.1 i hi
          exact ⟨out,hr,fun _ hm => List.mem_append_right _ (sub hm)⟩
      · intro y hy
        rcases List.mem_append.mp hy with ha | hb
        · exact ⟨_,List.mem_cons_self,_,a.property,ha⟩
        · obtain ⟨i,hi,out,hr,mem⟩ := b.property.2 y hb
          exact ⟨i,List.mem_cons_of_mem _ hi,out,hr,mem⟩⟩

theorem collect_completes {ι α : Type} (run : ι → Option (List α)) (xs : List ι)
    (h : ∀ i ∈ xs, (run i).isSome) : (collect run xs).isSome := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (ih (fun i hi => h i (List.mem_cons_of_mem _ hi)))
    simp [collect,ha,hb,Option.attach]

abbrev Certified (p : Problem s) := {r : Option (List (UnifierSorts.Template s)) //
  ∀ rows, r = some rows → UnifierSorts.CompleteTemplates p rows}

def refineWith (p : Problem s) (run : ∀ c : Problem s, Certified c) : Certified p := by
  let children := refineProblem p
  match collect (fun c => (run c).val) children.val with
  | none => exact ⟨none,by simp⟩
  | some out =>
    refine ⟨some out.val,?_⟩
    rintro _ ⟨⟩
    constructor
    · intro θ hθ e he
      obtain ⟨c,hc,rows,hr,mem⟩ := out.property.2 θ hθ
      exact ((run c).property rows hr).sound θ mem e (children.property.1 c hc e he)
    · intro ρ sol
      obtain ⟨c,hc,hs⟩ := children.property.2 ρ.image sol
      obtain ⟨ans,hr,sub⟩ := out.property.1 c hc
      obtain ⟨θ,hθ,μ,agree⟩ := ((run c).property ans hr).covers ρ hs
      refine ⟨θ,sub hθ,μ,?_⟩
      rintro v ⟨e,he,hv⟩
      exact agree v ⟨e,children.property.1 c hc e he,hv⟩

theorem refineWith_completes (p : Problem s) (run : ∀ c : Problem s, Certified c)
    (h : ∀ c ∈ (refineProblem p).val, (run c).val.isSome) : (refineWith p run).val.isSome := by
  obtain ⟨as,ha⟩ := Option.isSome_iff_exists.mp (collect_completes _ _ h)
  simp [refineWith,ha]

end Tamarin.MixedUnification.RigidBranches
