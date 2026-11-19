import Tamarin.DHSignedBlockSolutions
import Tamarin.DHGroupExistence
import Tamarin.VariantJoin

/-! Give each observed result its own message coordinate. Solving these graph
equations simultaneously preserves all sharing with the input coordinates. -/
namespace Tamarin.Rewriting.DHPeer.SignedMatrix
open ACBasis Balance Cancellation
variable {sig : Signature} {n : Nat} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

private theorem readings (env : Fin n → Term sig) (norm : ∀ i, Normal (ruleRoot T.rules) (env i))
    (e : Expr n) (k : Class sig) : ∃ z, read s (ruleRoot T.rules) k (e.term s env) = some z := by
  let val i := (defined s _ k (norm i)).choose
  exact ⟨_,e.read s _ k env val (fun i => (defined s _ k (norm i)).choose_spec)⟩

private theorem sort_result {env : Fin n → Term sig} (norm : ∀ i, Normal (ruleRoot T.rules) (env i))
    (e : Expr n) {out} (red : Reduces (ruleRoot T.rules) (e.term s env) out) (ty : HasSort out .msg) :
    ∀ a, HasSort (e.term s env) a → HasSort out a := by
  intro a h
  cases e with
  | input i => exact Term.checkSort_sound _ _ ((SortClash.check_equiv (normal_reduces_equiv red (norm i)) a) ▸ Term.checkSort_complete h)
  | unit => exact .widen ty (s.oneSort ▸ Term.rootSort_le h)
  | mul => exact .widen ty (s.mulSort ▸ Term.rootSort_le h)
  | inv => exact .widen ty (s.invSort ▸ Term.rootSort_le h)

private theorem evaluator [DecidableEq sig.ACSym] (inventory : Inventory E) (env : Fin n → Term sig)
    (norm : ∀ i, Normal (ruleRoot T.rules) (env i)) (typed : ∀ i, HasSort (env i) .msg) :
    ∃ val : Expr n → Term sig, (∀ e, NormalForm (ruleRoot T.rules) (e.term s env) (val e)) ∧
      ∀ e i, NormalForm (ruleRoot T.rules) (e.term s env) (env i) ↔ EquivB (val e) (val (.input i)) := by
  have ex (e : Expr n) := inventory.normal_exists (e.sorted s env typed) (readings env norm e (classOf s.product.one))
  let val (e : Expr n) := (ex e).choose
  have nf (e : Expr n) : NormalForm (ruleRoot T.rules) (e.term s env) (val e) := by
    obtain ⟨red,no,ty⟩ := (ex e).choose_spec
    exact ⟨red,no,sort_result norm e red ty⟩
  refine ⟨val,nf,?_⟩
  intro e i
  have atInput := normal_reduces_equiv (nf (.input i)).1 (norm i)
  constructor
  · intro h
    exact (normal_unique inventory E.presentation (fun _ => plain_of_inverse E) (readings env norm e)
      ((nf e).2.2 _ (e.sorted s env typed)) (typed i) (nf e).2.1 (norm i) (nf e).1 h.1).trans atInput
  · intro h
    have red := (nf e).1.trans (.basis (h.trans atInput.symm))
    exact ⟨red,norm i,sort_result norm e red (typed i)⟩

private theorem transport (e : Expr n) {a b : Fin n → Term sig} (eq : ∀ i, EquivB (a i) (b i)) :
    EquivB (e.term s a) (e.term s b) := by
  induction e with
  | input i => exact eq i
  | unit => exact .refl _
  | mul _ _ l r => exact .ac_congr _ l r
  | inv _ h => exact .free _ _ _ (fun _ => h)

/-- A finite family of normal symbolic tuples describes the entire graph
of an arbitrary simultaneous signed query, in both directions. A layout can
expose any coordinate as an input or as an observed output. The specializing
substitution is normalized and shared by every coordinate. -/
theorem exact_graph [DecidableEq sig.ACSym] (inventory : Inventory E) (mul : MulBucket E)
    (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (graph : List (Expr n × Fin n)) (basis : (Fin n → Bool) → List (Vec n))
    (valid : ∀ d, BasisCorrect (graph.map fun p => row d (p.1,.input p.2)) (basis d))
    (name : Column basis → Variable) (inj : Function.Injective name) (sort : ∀ g, (name g).sort = .msg)
    (env : Fin n → Term sig) (typed : ∀ i, HasSort (env i) .msg) (norm : ∀ i, Normal (ruleRoot T.rules) (env i)) :
    (∀ p ∈ graph, NormalForm (ruleRoot T.rules) (p.1.term s env) (env p.2)) ↔
      ∃ active ∈ FlatMatchSearch.sublists (columns basis), ∃ δ : Substitution sig,
        Normalized (ruleRoot T.rules) δ ∧ ∀ i, EquivB (env i) (δ.apply (template s basis active name i)) := by
  let system := graph.map fun p => (p.1,Expr.input p.2)
  have correct d : BasisCorrect (system.map (row d)) (basis d) := by simpa [system,List.map_map,Function.comp_def] using valid d
  constructor
  · intro forms
    obtain ⟨val,nf,rel⟩ := evaluator inventory env norm typed
    obtain ⟨active,h,δ,fit⟩ := factor_through_template inventory env system basis correct name inj sort typed norm
      val (fun _ _ e _ => nf e) (by
        rintro _ mem
        obtain ⟨p,h,rfl⟩ := List.mem_map.mp mem
        exact (rel ..).mp (forms p h))
    let q : VariantJoin.Row sig (Fin n) Empty := ⟨template s basis active name,Empty.elim⟩
    have hit : VariantJoin.Fits q env Empty.elim δ := ⟨fun i => (fit i).symm,fun a => a.elim⟩
    obtain ⟨δ,nd,fits⟩ := (VariantJoin.normal_witness (ConstructorVariants.constructor_normal _ inventory.1).1
      norm (fun x : Empty => x.elim) hit).2
    exact ⟨active,h,δ,nd,fits.inputs⟩
  · rintro ⟨active,branch,δ,_,fit⟩ p hp
    let t := template s basis active name
    have nt := template_normal mul inv unit basis active name inj sort
    obtain ⟨val,nf,rel⟩ := evaluator inventory t (fun i => (nt i).2) (fun i => (nt i).1)
    have equal := template_sound inventory mul inv unit system basis correct active branch name inj sort val (fun _ _ e _ => nf e)
    have form := (rel p.1 p.2).mpr (equal _ (List.mem_map_of_mem (f := fun p : Expr n × Fin n => (p.1,Expr.input p.2)) hp))
    have source := transport (s := s) p.1 fit
    rw [← p.1.subst_term] at source
    have red := (Reduces.basis source).trans ((SpecializedFresh.reduces_subst _ δ form.1).trans (.basis (fit p.2).symm))
    exact ⟨red,norm _,sort_result norm p.1 red (typed _)⟩

private def graphBasis (graph : List (Expr n × Fin n)) (d : Fin n → Bool) : List (Vec n) :=
  generate (graph.map fun p => row d (p.1,.input p.2))

local instance : DecidableEq (Fin n → Bool) := fun a b =>
  decidable_of_iff (∀ i, a i = b i) ⟨funext,congrFun⟩

private def param (basis : (Fin n → Bool) → List (Vec n)) (g : Column basis) : Variable :=
  ⟨(columns basis).idxOf g,.msg⟩

private theorem param_injective (basis : (Fin n → Bool) → List (Vec n)) : Function.Injective (param basis) := by
  have lookup (g : Column basis) : (columns basis)[(columns basis).idxOf g]? = some g := by
    simp [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (mem_columns basis g)),List.getElem_idxOf]
  intro a b h
  have same := congrArg Variable.id h
  change (columns basis).idxOf a = (columns basis).idxOf b at same
  exact Option.some.inj ((lookup a).symm.trans ((congrArg (fun i : Nat => (columns basis)[i]?) same).trans (lookup b)))

/-- Executable finite reference family with request-local parameter indices.
Materializing the powerset is expensive; the exactness theorem also accepts
other correct bases and permits a candidate to prove its own enumeration. -/
def referenceFamily (s : Symbols sig) (graph : List (Expr n × Fin n)) : List (Fin n → Term sig) :=
  let basis := graphBasis graph
  (FlatMatchSearch.sublists (columns basis)).map fun active => template s basis active (param basis)

/-- The reference enumeration needs no supplied basis, witness allocator, or
normalization oracle. Only the active theory and the normal input domain enter
its correctness statement. -/
theorem reference_exact [DecidableEq sig.ACSym] (inventory : Inventory E) (mul : MulBucket E)
    (inv : InverseBucket E) (unit : Normal (ruleRoot T.rules) s.product.one)
    (graph : List (Expr n × Fin n)) (env : Fin n → Term sig)
    (typed : ∀ i, HasSort (env i) .msg) (norm : ∀ i, Normal (ruleRoot T.rules) (env i)) :
    (∀ p ∈ graph, NormalForm (ruleRoot T.rules) (p.1.term s env) (env p.2)) ↔
      ∃ r ∈ referenceFamily s graph, ∃ δ : Substitution sig,
        Normalized (ruleRoot T.rules) δ ∧ ∀ i, EquivB (env i) (δ.apply (r i)) := by
  let basis := graphBasis graph
  rw [exact_graph inventory mul inv unit graph basis (fun _ => generate_correct _) (param basis)
    (param_injective _) (fun _ => rfl) env typed norm]
  constructor
  · rintro ⟨active,h,tail⟩
    exact ⟨_,List.mem_map_of_mem (f := fun active => template s basis active (param basis)) h,tail⟩
  · rintro ⟨r,hr,tail⟩
    obtain ⟨active,h,rfl⟩ := List.mem_map.mp hr
    exact ⟨active,h,tail⟩

end Tamarin.Rewriting.DHPeer.SignedMatrix
