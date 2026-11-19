import TamarinRuntime.FactorCheck
import Tamarin.WholeOrdering

namespace Tamarin.FactorCheck
open Whole

/-- Interpret every rigid application in a value algebra. Free constructors
reflect equality. C and AC interpret their declared permutation and grouping laws. -/
structure Interpretation (α : Type) where
  leaf : UInt64 → UInt64 → UInt64 → α
  app : UInt64 → UInt64 → List α → α
  free_inj : ∀ id, Function.Injective (app 2 id)
  perm : ∀ k, (k = 3 ∨ k = 4) → ∀ i {xs ys : List α}, xs.Perm ys → app k i xs = app k i ys
  flatten : ∀ i (pre inner post : List α),
    app 4 i (pre ++ app 4 i inner :: post) = app 4 i (pre ++ inner ++ post)

namespace Interpretation
variable {α : Type} (m : Interpretation α)

mutual
  def eval : Tree → α
    | .leaf k i s => m.leaf k i s
    | .app k f xs => m.app k f (evalArgs xs)
  def evalArgs : List Tree → List α
    | [] => []
    | x :: xs => eval x :: evalArgs xs
end

def Solves (qs : Equations) : Prop :=
  ∀ e ∈ qs, m.eval e.1 = m.eval e.2

def bind (bs : Equations) : Interpretation α := { m with
  leaf := fun k v s => if k = 0 then m.eval (lookup bs (.leaf 0 v s)) else m.leaf k v s }

theorem evalArgs_map (xs : List Tree) : m.evalArgs xs = xs.map m.eval := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [evalArgs, List.map_cons, ih]

mutual
  theorem eval_bind (bs : Equations) (t : Tree) :
      (m.bind bs).eval t = m.eval (applyBindings bs t) := by
    cases t with
    | leaf k v s =>
      by_cases h : k = 0
      · subst k; simp [bind,eval,applyBindings]
      · simp [bind,eval,applyBindings,h]
    | app k f xs =>
      simp only [eval, applyBindings, bind]
      exact congrArg (m.app k f) (evalArgs_bind bs xs)
  theorem evalArgs_bind (bs : Equations) (xs : List Tree) :
      (m.bind bs).evalArgs xs = m.evalArgs (applyChildren bs xs) := by
    cases xs with
    | nil => rfl
    | cons x xs => simp only [evalArgs, applyChildren, eval_bind bs x, evalArgs_bind bs xs]
end

private theorem solves_lookup {bs : Equations} (hs : m.Solves bs) (t : Tree) :
    m.eval (lookup bs t) = m.eval t := by
  unfold lookup
  split
  next lhs rhs h =>
    have mem := List.mem_of_find?_eq_some h
    have eq := List.find?_some h
    have e : lhs = t := beq_iff_eq.mp eq
    subst lhs
    exact (hs _ mem).symm
  next => rfl

theorem bind_eq {bs : Equations} (hs : m.Solves bs) : m.bind bs = m := by
  cases m with
  | mk leaf app inj perm flatten =>
    unfold bind
    congr 1
    funext k v s
    by_cases h : k = 0
    · subst k; exact (solves_lookup _ hs (.leaf 0 v s))
    · simp [h]

private theorem map_eq_zip {xs ys : List Tree} (h : xs.length = ys.length) :
    xs.map m.eval = ys.map m.eval ↔ m.Solves (xs.zip ys) := by
  induction xs generalizing ys with
  | nil => obtain rfl : ys = [] := List.length_eq_zero_iff.mp h.symm; simp [Solves]
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp [Solves, ih h]

theorem expose_iff (fuel : Nat) (a b : Tree) :
    m.Solves (expose fuel a b) ↔ m.eval a = m.eval b := by
  induction fuel generalizing a b with
  | zero => simp [expose,Solves]
  | succ n ih =>
    cases a with
    | leaf => simp [expose, Solves]
    | app k f xs =>
      by_cases hk : k = 2
      · subst hk
        cases b with
        | leaf => simp [expose,Solves]
        | app k' g ys =>
          by_cases hk' : k' = 2
          · subst hk'
            rw [expose]
            by_cases h : f = g ∧ xs.length = ys.length
            · obtain ⟨rfl,hlen⟩ := h
              simp only [beq_self_eq_true, hlen, Bool.and_self, ↓reduceIte]
              rw [eval,eval, (m.free_inj f).eq_iff, m.evalArgs_map, m.evalArgs_map, m.map_eq_zip hlen]
              constructor
              · intro hs e he
                exact (ih e.1 e.2).mp (fun u hu => hs u (List.mem_flatMap.mpr ⟨e, he, hu⟩))
              · intro hs u hu
                obtain ⟨e, he, hu⟩ := List.mem_flatMap.mp hu
                exact (ih e.1 e.2).mpr (hs _ he) _ hu
            · simp [show (f == g && xs.length == ys.length) = false by simpa using h,Solves]
          · simp [expose,hk',Solves]
      · simp [expose,hk,Solves]

theorem flat_iff (p : Equations) (n : Nat) :
    m.Solves (p.flatMap (fun e => expose n e.1 e.2)) ↔ m.Solves p := by
  constructor
  · intro h e he
    exact (m.expose_iff n e.1 e.2).mp (fun u hu => h u (List.mem_flatMap.mpr ⟨e, he, hu⟩))
  · intro h e he
    obtain ⟨u,hu,he⟩ := List.mem_flatMap.mp he
    exact (m.expose_iff n u.1 u.2).mpr (h _ hu) _ he

private theorem same_eq {e e' : Tree × Tree} (he : same e e' = true)
    (h : m.eval e'.1 = m.eval e'.2) : m.eval e.1 = m.eval e.2 := by
  simp [same] at he
  rcases he with ⟨a,b⟩ | ⟨a,b⟩ <;> simp [a,b,h]

private theorem of_supported {p q : Equations} (h : p.all (supported q) = true)
    (sol : m.Solves q) : m.Solves p := by
  intro e he
  have h := List.all_eq_true.mp h e he
  simp [supported] at h
  rcases h with h | ⟨x, y, hu, he⟩
  · rw [h]
  · exact m.same_eq he (sol (x,y) hu)

private theorem eval_flat_parts (id : UInt64) (pre xs : List Tree) :
    m.app 4 id (m.evalArgs (pre ++ xs.flatMap (parts id))) =
      m.app 4 id (m.evalArgs (pre ++ xs)) := by
  induction xs generalizing pre with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, ← List.append_assoc]
    rw [ih]
    cases x with
    | leaf => simp [parts]
    | app k j cs =>
      by_cases hk : k = 4
      · subst k
        by_cases hj : id = j
        · subst j
          simp only [parts, ↓reduceIte, List.append_assoc, m.evalArgs_map,
            List.map_append, List.map_cons, Interpretation.eval]
          simpa only [List.append_assoc] using (m.flatten id (pre.map m.eval) (cs.map m.eval) (xs.map m.eval)).symm
        · simp [parts,hj]
      · simp [parts,hk]

private theorem eval_make (k i : UInt64) (xs : List Tree) :
    m.eval (make k i xs) = m.app k i (m.evalArgs xs) := by
  have perm (kind : k = 3 ∨ k = 4) (ts : List Tree) :
      m.app k i (m.evalArgs (order ts)) = m.app k i (m.evalArgs ts) := by
    simp only [m.evalArgs_map]
    exact m.perm k kind i ((order_perm ts).map m.eval)
  by_cases ac : k = 4
  · subst k
    simpa only [make,ite_true,Interpretation.eval,List.nil_append] using
      (perm (.inr rfl) _).trans (m.eval_flat_parts i [] xs)
  · by_cases comm : k = 3
    · simpa [make,ac,comm,Interpretation.eval] using perm (.inl comm) xs
    · simp [make,ac,comm,Interpretation.eval]

mutual
  theorem eval_canonical (a : Tree) : m.eval (canonical a) = m.eval a := by
    cases a with
    | leaf => rfl
    | app k i xs =>
      simp only [canonical, m.eval_make, evalArgs_canonical xs, Interpretation.eval]
  theorem evalArgs_canonical (xs : List Tree) : m.evalArgs (canonicalArgs xs) = m.evalArgs xs := by
    cases xs with
    | nil => rfl
    | cons x xs => simp only [canonicalArgs, Interpretation.evalArgs, eval_canonical x, evalArgs_canonical xs]
end

theorem substitute_iff (bs p : Equations) :
    m.Solves (substitute bs p) ↔ (m.bind bs).Solves p := by
  simp [Solves,substitute,eval_bind]
  grind

end Interpretation

theorem Interpretation.canonical_rows_iff {α : Type} (m : Interpretation α) (rows : Equations) :
    m.Solves (canonicalRows rows) ↔ m.Solves rows := by
  constructor
  · rintro sol ⟨a,b⟩ mem
    have h := sol _ (List.mem_map_of_mem (f := fun e : Tree × Tree => (canonical e.1,canonical e.2)) mem)
    simpa only [m.eval_canonical] using h
  · rintro sol e mem
    obtain ⟨⟨a,b⟩,ha,rfl⟩ := List.mem_map.mp mem
    exact (m.eval_canonical a).trans ((sol _ ha).trans (m.eval_canonical b).symm)

/-- Denotation of a proposed free factor under arbitrary assignments,
including nonground assignments into the free algebra modulo C/AC. -/
structure Valid (ds : List Decl) (p bs q : Equations) : Prop where
  typed : ∀ e ∈ bs, sortedBinding ds e = true
  stableImages : ∀ e ∈ bs, applyBindings bs e.2 = e.2
  stableResidual : ∀ e ∈ q, applyBindings bs e.1 = e.1 ∧ applyBindings bs e.2 = e.2
  equivalent : ∀ {α : Type} (m : Interpretation α), m.Solves p ↔ m.Solves bs ∧ m.Solves q
  lift : ∀ {α : Type} (m : Interpretation α), m.Solves q → (m.bind bs).Solves p

/-- An ordered derivation of binding equations. The left worklist contains
consequences of the original request. The right one contains the binding
equations proposed by the free solver.
Applying a justified raw binding to both allows its image to be specialized
by a later step. -/
inductive Replay : Equations → Equations → Prop where
  | done {active goals} (supportedGoals : goals.all (supported active) = true) :
      Replay active goals
  | canonical {active goals} (rest : Replay (canonicalRows active) (canonicalRows goals)) : Replay active goals
  | expose {active goals} (depth : Nat)
      (rest : Replay (active.flatMap fun e => FactorCheck.expose depth e.1 e.2) goals) :
      Replay active goals
  | bind {active goals} (e : Whole.Tree × Whole.Tree)
      (evidence : supported active e = true)
      (rest : Replay (substitute [e] active) (substitute [e] goals)) : Replay active goals

/-- Each replay step is sound under every interpretation of the wire graph.
In particular the argument does not appeal to the implementation's binding
order, any global confluence property, or groundness of the input. -/
theorem Replay.consequences {active goals : Equations} (r : Replay active goals)
    {α : Type} (m : Interpretation α) : m.Solves active → m.Solves goals := by
  induction r with
  | done support => exact m.of_supported support
  | canonical _ ih => exact fun hs => (m.canonical_rows_iff _).mp (ih ((m.canonical_rows_iff _).mpr hs))
  | expose depth _ ih => exact fun sol => ih ((m.flat_iff _ depth).mpr sol)
  | @bind active goals e evidence _ ih =>
    intro sol
    have hb : m.Solves [e] := m.of_supported (by simpa using evidence) sol
    have unchanged := m.bind_eq hb
    apply unchanged ▸ (m.substitute_iff [e] goals).mp _
    exact ih ((m.substitute_iff [e] active).mpr (by rwa [unchanged]))

theorem replay_checked (fuel : Nat) (active goals : Equations)
    (accepted : replay fuel active goals = true) : Replay active goals := by
  induction fuel generalizing active goals with
  | zero => contradiction
  | succ fuel ih =>
    simp only [replay] at accepted
    split at accepted <;> try contradiction
    apply Replay.canonical
    apply Replay.expose 128
    split at accepted
    · next supported => exact .done supported
    · split at accepted <;> try contradiction
      simp only [Bool.and_eq_true] at accepted
      obtain ⟨evidence,rest⟩ := accepted
      exact .bind _ evidence (ih _ _ rest)

/-- The residual comparison and the derivation of the bindings are
independent. A checker may expose additional free heads during either
check without changing the factorization meaning used downstream. -/
theorem valid_of_consequences {ds p bs q}
    (typed : ∀ e ∈ bs, sortedBinding ds e = true)
    (images : ∀ e ∈ bs, applyBindings bs e.2 = e.2)
    (residual : ∀ e ∈ q, applyBindings bs e.1 = e.1 ∧ applyBindings bs e.2 = e.2)
    (bindings : ∀ {α : Type} (m : Interpretation α), m.Solves p → m.Solves bs)
    (remaining : ∀ {α : Type} (m : Interpretation α), (m.bind bs).Solves p ↔ m.Solves q) :
    Valid ds p bs q where
  typed := typed
  stableImages := images
  stableResidual := residual
  lift m := (remaining m).mpr
  equivalent m := by
    constructor
    · intro sol
      have hb := bindings m sol
      exact ⟨hb,(remaining m).mp (by rwa [m.bind_eq hb])⟩
    · rintro ⟨hb,rest⟩
      exact m.bind_eq hb ▸ (remaining m).mpr rest

theorem valid_of_replay {ds p bs q} (accept : checkReplay ds p bs q = true) : Valid ds p bs q := by
  simp only [checkReplay] at accept
  split at accept <;> try contradiction
  split at accept <;> try contradiction
  simp only [Bool.and_eq_true,List.all_eq_true] at accept
  obtain ⟨⟨⟨⟨⟨⟨typed,_⟩,images⟩,residual⟩,checked⟩,forward⟩,reverse⟩ := accept
  apply valid_of_consequences typed (fun e he => beq_iff_eq.mp (images e he))
    (fun e he => ⟨beq_iff_eq.mp (residual e he).1,beq_iff_eq.mp (residual e he).2⟩)
  · exact fun m => (replay_checked _ _ _ checked).consequences m
  · intro α m
    rw [← m.substitute_iff,← m.canonical_rows_iff (substitute bs p),← m.flat_iff _ 128,← m.canonical_rows_iff q]
    exact ⟨m.of_supported (List.all_eq_true.mpr reverse),m.of_supported (List.all_eq_true.mpr forward)⟩

theorem valid_of_direct {ds p bs q} (accept : direct ds p bs q = true) : Valid ds p bs q := by
  let flat := p.flatMap fun e => expose 128 e.1 e.2
  let derived := substitute bs flat
  simp only [direct, Bool.and_eq_true, List.all_eq_true] at accept
  obtain ⟨⟨⟨⟨⟨typed, _⟩, binds⟩, stable⟩, pq⟩, qp⟩ := accept
  have lift {α} (m : Interpretation α) (h : m.Solves q) : (m.bind bs).Solves p := by
    apply ((m.bind bs).flat_iff p 128).mp
    apply (m.substitute_iff bs flat).mp
    exact m.of_supported (List.all_eq_true.mpr pq) h
  refine ⟨typed, fun e he => beq_iff_eq.mp (binds e he).1, ?_, ?_, @lift⟩
  · intro e he
    exact ⟨beq_iff_eq.mp (stable e he).1, beq_iff_eq.mp (stable e he).2⟩
  · intro α m
    constructor
    · intro hp
      have hf : m.Solves flat := (m.flat_iff p 128).mpr hp
      have hb : m.Solves bs := by
        intro e he
        obtain ⟨u,hu,eq⟩ := List.any_eq_true.mp (binds e he).2
        exact m.same_eq eq (hf _ hu)
      have hd : m.Solves derived := (m.substitute_iff bs flat).mpr (by simpa only [m.bind_eq hb] using hf)
      exact ⟨hb, m.of_supported (List.all_eq_true.mpr qp) hd⟩
    · rintro ⟨hb,hq⟩
      exact m.bind_eq hb ▸ lift m hq

theorem valid_of_check {ds p bs q} (accept : check ds p bs q = true) : Valid ds p bs q := by
  rcases Bool.or_eq_true_iff.mp accept with fast | replayed
  · exact valid_of_direct fast
  · exact valid_of_replay replayed

abbrev Kernel := Array UInt64 → Array (Array UInt64) →
  Array UInt64 → Array UInt64 → Array UInt64 → Bool

/-- An accepted proposal validates the same graph under a single declaration
table, and yields both implications of the factorization law. -/
def Correct (candidate : Kernel) : Prop :=
  ∀ ds ns os bs rs, candidate ds ns os bs rs = true →
    ∃ decl trees original bindings residual,
      declarations ds.toList = some decl ∧ decodeNodes decl ns = some trees ∧
      readEquations trees os.toList = some original ∧
      readEquations trees bs.toList = some bindings ∧
      readEquations trees rs.toList = some residual ∧ Valid decl original bindings residual

theorem run_correct : Correct run := by
  intro ds ns os bs rs h
  cases hd : declarations ds.toList with
  | none => simp [run,runWith, hd] at h
  | some decl =>
    cases hn : decodeNodes decl ns with
    | none => simp [run,runWith, hd, hn] at h
    | some trees =>
      cases hp : readEquations trees os.toList <;> simp [run,runWith, hd, hn, hp] at h
      next p =>
        cases hb : readEquations trees bs.toList <;> simp [hb] at h
        next b =>
          cases hr : readEquations trees rs.toList <;> simp [hr] at h
          next r => exact ⟨_, _, _, _, _, rfl, hn, hp, hb, hr, valid_of_check h⟩

end Tamarin.FactorCheck
