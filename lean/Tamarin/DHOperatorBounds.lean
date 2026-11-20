import Tamarin.OperatorVariantBounds
import Tamarin.DHSignedVariantFamily
import Tamarin.DHBase

/-! Uniform short normalization paths for DH on message-sorted normal
operands. Signed products may contain arbitrarily many opaque factors. The
bound depends only on a finite symbolic graph family, independently of the
number or size of these factors. -/
namespace Tamarin.Rewriting.DHPeer
open ShortVariantPaths Balance SignedMatrix
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
variable [DecidableEq sig.ACSym] (inventory : Inventory E) (mul : MulBucket E) (inv : InverseBucket E)
  (unit : Normal (ruleRoot T.rules) s.product.one)

include inventory mul inv unit in
/-- Fix an expression over coordinate slots and its result slot. Every
normalized solution of this graph equation has a path no longer than the
longest *selected* derivation among its finitely many symbolic rows. -/
theorem graph_paths {n : Nat} (e : SignedMatrix.Expr n) (j : Fin n) :
    ∃ k, ∀ env : Fin n → Term sig, (∀ i, HasSort (env i) .msg) →
      (∀ i, Normal (ruleRoot T.rules) (env i)) →
      NormalForm (ruleRoot T.rules) (e.term s env) (env j) →
      Path (ruleRoot T.rules) k (e.term s env) (env j) := by
  classical
  let graph := [(e,j)]
  let rows := referenceFamily s graph
  have rep {r} (hr : r ∈ rows) (i) : HasSort (r i) .msg ∧ Normal (ruleRoot T.rules) (r i) := by
    obtain ⟨active,ha,rfl⟩ := List.mem_map.mp hr
    exact template_normal mul inv unit _ active (param _) (param_injective _) (fun _ => rfl) i
  have symbolic (row : {r // r ∈ rows}) : ∃ k, Path (ruleRoot T.rules) k (e.term s row.val) (row.val j) := by
    have real := (reference_exact inventory mul inv unit graph row.val
      (fun i => (rep row.property i).1) (fun i => (rep row.property i).2)).mpr
      ⟨row.val,row.property,.identity,(ConstructorVariants.constructor_normal _ inventory.1).1,
        fun i => by rw [Substitution.apply_identity]; exact .refl _⟩
    exact exists_path (real (e,j) List.mem_cons_self).1
  let lengths := rows.attach.map fun r => (symbolic r).choose
  refine ⟨lengths.sum,fun env typed norm form => ?_⟩
  have forms (p) (h : p ∈ graph) : NormalForm (ruleRoot T.rules) (p.1.term s env) (env p.2) :=
    (List.mem_singleton.mp h) ▸ form
  obtain ⟨r,hr,δ,_,fit⟩ := (reference_exact inventory mul inv unit graph env typed norm).mp forms
  let row : {r // r ∈ rows} := ⟨r,hr⟩
  have path := (symbolic row).choose_spec.subst δ
  have left := e.term_equiv (s := s) fit
  rw [← e.subst_term] at left
  exact ((path.rebase left).post (fit j).symm).weaken
    (FiniteOccurs.le_sum _ _ (List.mem_map_of_mem (f := fun r => (symbolic r).choose) (List.mem_attach _ row)))

omit [DecidableEq sig.ACSym] in
include inventory in
private theorem evaluated {n} (e : SignedMatrix.Expr n) (env : Fin n → Term sig)
    (typed : ∀ i, HasSort (env i) .msg) (norm : ∀ i, Normal (ruleRoot T.rules) (env i)) :
    ∃ y, HasSort y .msg ∧ NormalForm (ruleRoot T.rules) (e.term s env) y := by
  let key := Cancellation.classOf s.product.one
  let val i := (defined s _ key (norm i)).choose
  have read := e.read s _ key env val (fun i => (defined s _ key (norm i)).choose_spec)
  obtain ⟨y,red,no,ty⟩ := inventory.normal_exists (e.sorted s env typed) ⟨_,read⟩
  refine ⟨y,ty,red,no,fun sort h => ?_⟩
  cases e with
  | input i =>
    exact Term.checkSort_sound _ _ (SortClash.check_equiv (normal_reduces_equiv red (norm i)) sort ▸ Term.checkSort_complete h)
  | unit => exact .widen ty (s.oneSort ▸ Term.rootSort_le h)
  | mul => exact .widen ty (s.mulSort ▸ Term.rootSort_le h)
  | inv => exact .widen ty (s.invSort ▸ Term.rootSort_le h)

include inventory mul inv unit in
/-- One bound for all products of two well-sorted irreducible operands. -/
theorem product_paths : ∃ k, ∀ a b : Term sig, HasSort a .msg → HasSort b .msg →
    Normal (ruleRoot T.rules) a → Normal (ruleRoot T.rules) b →
    ∃ y, HasSort y .msg ∧ Path (ruleRoot T.rules) k (s.product.mul a b) y ∧ Normal (ruleRoot T.rules) y := by
  let e : SignedMatrix.Expr 3 := .mul (.input 0) (.input 1)
  obtain ⟨k,go⟩ := graph_paths inventory mul inv unit e 2
  refine ⟨k,fun a b ha hb na nb => ?_⟩
  let env (y : Term sig) (i : Fin 3) := if i=0 then a else if i=1 then b else y
  have ty y (hy : HasSort y .msg) (i) : HasSort (env y i) .msg := by
    dsimp [env]; split <;> first | assumption | split <;> assumption
  have nf y (hy : Normal (ruleRoot T.rules) y) (i) : Normal (ruleRoot T.rules) (env y i) := by
    dsimp [env]; split <;> first | assumption | split <;> assumption
  obtain ⟨y,hy,form⟩ := evaluated inventory e (env a) (ty _ ha) (nf _ na)
  have normal : NormalForm (ruleRoot T.rules) (s.product.mul a b) y := by simpa [e,env,SignedMatrix.Expr.term] using form
  have path := go (env y) (ty _ hy) (nf _ normal.2.1) (by simpa [e,env,SignedMatrix.Expr.term] using normal)
  exact ⟨y,hy,by simpa [e,env,SignedMatrix.Expr.term] using path,normal.2.1⟩

include inventory mul inv unit in
/-- One bound for all inverses of well-sorted irreducible operands. -/
theorem inverse_paths : ∃ k, ∀ a : Term sig, HasSort a .msg → Normal (ruleRoot T.rules) a →
    ∃ y, HasSort y .msg ∧ Path (ruleRoot T.rules) k (s.product.inv a) y ∧ Normal (ruleRoot T.rules) y := by
  let e : SignedMatrix.Expr 2 := .inv (.input 0)
  obtain ⟨k,go⟩ := graph_paths inventory mul inv unit e 1
  refine ⟨k,fun a ha na => ?_⟩
  obtain ⟨y,hy,form⟩ := evaluated inventory e (fun _ => a) (fun _ => ha) (fun _ => na)
  let env (i : Fin 2) := if i=0 then a else y
  have ty i : HasSort (env i) .msg := by dsimp [env]; split <;> assumption
  have nf i : Normal (ruleRoot T.rules) (env i) := by dsimp [env]; split; exact na; exact form.2.1
  have path := go env ty nf (by simpa [env,e,SignedMatrix.Expr.term] using form)
  exact ⟨y,hy,by simpa [env,e,SignedMatrix.Expr.term] using path,form.2.1⟩

omit [DecidableEq sig.ACSym] in
private theorem schema_path (r : Rule) (env : Fin 3 → Term sig) (typed : ∀ i, HasSort (env i) .msg) :
    Path (ruleRoot T.rules) 1 (r.instantiate s env).lhs (r.instantiate s env).rhs :=
  .step ⟨_,_,.refl _,.root (T.fireRoot r env typed),.refl _⟩ (.basis (.refl _))

include inventory mul inv unit in
/-- Tower flattening introduces only a product of two already normal
exponents; its uniform bound also covers powers with variable bases. -/
theorem power_paths (pow : PowerBucket T) : ∃ k, ∀ base e : Term sig, HasSort base .msg → HasSort e .msg →
    Normal (ruleRoot T.rules) base → Normal (ruleRoot T.rules) e →
    ∃ y, HasSort y .msg ∧ Path (ruleRoot T.rules) k (s.power base e) y ∧ Normal (ruleRoot T.rules) y := by
  obtain ⟨k,product⟩ := product_paths inventory mul inv unit
  refine ⟨1 + sig.arity s.pow*k + 1,fun base e tb te nb ne => ?_⟩
  by_cases un : ConstructorVariants.head e = .free s.one
  · obtain rfl : e = s.product.one := nullary s.oneArity un
    exact ⟨base,tb,(schema_path (T := T) .expOne (fun _ => base) (fun _ => tb)).weaken (by omega),nb⟩
  by_cases neutral : ConstructorVariants.head base = .free s.neutral
  · obtain rfl : base = s.neutralTerm := nullary s.neutralArity neutral
    exact ⟨_,tb,(schema_path (T := T) .neutral (fun _ => e) (fun _ => te)).weaken (by omega),nb⟩
  by_cases previous : ConstructorVariants.head base = .free s.pow
  · obtain ⟨b,p,rfl⟩ := splitPower s previous
    obtain ⟨hb,hp⟩ := DHTower.pow_types tb
    obtain ⟨bn,pn,plain,nonneutral,_⟩ := (pow.normal_iff hb hp).mp nb
    let args (i : Fin 3) := if i=0 then b else if i=1 then p else e
    have typed i : HasSort (args i) .msg := by dsimp [args]; split <;> first | assumption | split <;> assumption
    have first : Path (ruleRoot T.rules) 1 (s.power (s.power b p) e) (s.power b (s.product.mul p e)) :=
      schema_path (T := T) .tower args typed
    obtain ⟨y,hy,path,ny⟩ := product p e hp te pn ne
    have lifted : Path (ruleRoot T.rules) (sig.arity s.pow*k) (s.power b (s.product.mul p e)) (s.power b y) := by
      apply Path.free
      intro i; split
      · exact .basis (.refl _)
      · exact path
    by_cases same : ConstructorVariants.head y = .free s.one
    · obtain rfl : y = s.product.one := nullary s.oneArity same
      exact ⟨b,hb,(first.append lifted).append (schema_path (T := T) .expOne (fun _ => b) (fun _ => hb)),bn⟩
    · exact ⟨s.power b y,DHTower.powerSorted hb hy,(first.append lifted).weaken (by omega),
        (pow.normal_iff hb hy).mpr ⟨bn,ny,plain,nonneutral,same⟩⟩
  · exact ⟨_,DHTower.powerSorted tb te,.basis (.refl _),(pow.normal_iff tb te).mpr ⟨nb,ne,previous,neutral,un⟩⟩

end Tamarin.Rewriting.DHPeer
