import Tamarin.BilinearScalars
import Tamarin.BilinearUnitSplit
import Tamarin.RigidAllocation

/-! Lift both scalar input images and their normal product into a single point
row. Point parameters are opened apart from the scalar row. One substitution
therefore explains the two caller images and the folded point or map value. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer VariantJoin
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {rules : List (Equation sig)}

inductive LiftOp where | action | pairing

def LiftOp.inputs (op : LiftOp) (β : Operators sig) (x : Bool → Term sig) (p q : Term sig) : Bool → Term sig :=
  match op with
  | .action => fun | false => x false | true => β.point (x true) p
  | .pairing => fun | false => β.point (x false) p | true => β.point (x true) q

def LiftOp.base (op : LiftOp) (β : Operators sig) (p q : Term sig) : Term sig :=
  match op with | .action => p | .pairing => β.map p q

def LiftOp.wrap (op : LiftOp) (s : Symbols sig) (β : Operators sig) (base scalar : Term sig) : Term sig :=
  match op with | .action => β.point scalar base | .pairing => s.power base scalar

def LiftOp.row (op : LiftOp) (s : Symbols sig) (β : Operators sig) (k : Bool) (r : Row sig Bool Unit)
    (p q : Variable) : Row sig Bool Unit where
  input := op.inputs β r.input (.var p) (.var q)
  value _ := let b := op.base β (.var p) (.var q)
             if k then b else op.wrap s β b (r.value ())

/-- Extending the row's normalized witness substitution with concrete plain
points is simultaneous. The concrete points may themselves contain any
caller variables, including ones already in the original substitution. -/
private theorem extend_points {r : Row sig Bool Unit} {δ : Substitution sig} {x m}
    (hit : Fits r x (fun _ => m) δ) (clean : Normalized (ruleRoot rules) δ)
    {l t : Variable} (distinct : l ≠ t) (scope : ¬r.Uses l ∧ ¬r.Uses t)
    {p q : Term sig} (sp : HasSort p l.sort) (sq : HasSort q t.sort)
    (np : Normal (ruleRoot rules) p) (nq : Normal (ruleRoot rules) q) :
    ∃ η, Normalized (ruleRoot rules) η ∧ Fits r x (fun _ => m) η ∧ η.image l = p ∧ η.image t = q := by
  let a := RigidAllocation.Query.override δ l p sp
  let η := RigidAllocation.Query.override a t q sq
  have same (v : Variable) (used : r.Uses v) : η.image v = δ.image v := by
    have one : v ≠ l := fun e => scope.1 (e ▸ used)
    have two : v ≠ t := fun e => scope.2 (e ▸ used)
    simp [η,a,RigidAllocation.Query.override,one,two]
  refine ⟨η,?_,⟨?_,?_⟩,by simp [η,a,RigidAllocation.Query.override,distinct],by simp [η,RigidAllocation.Query.override]⟩
  · intro v; dsimp [η,a,RigidAllocation.Query.override]
    split <;> first | exact nq | split <;> first | exact np | exact clean v
  · intro i
    have eq : η.apply (r.input i) = δ.apply (r.input i) :=
      Term.subst_eq_of_agree _ _ _ (fun v h => same v (.inl ⟨i,h⟩))
    exact eq ▸ hit.inputs i
  · intro i
    have eq : η.apply (r.value i) = δ.apply (r.value i) :=
      Term.subst_eq_of_agree _ _ _ (fun v h => same v (.inr ⟨i,h⟩))
    exact eq ▸ hit.values i

/-- In the two-scalar branch, a complete product family covers the entire BP
row under one witness substitution, even if its open product becomes one.
Take the fold from the actual BP normal form via point_lift or map_lift. -/
theorem LiftOp.covers (op : LiftOp) {r : Row sig Bool Unit} {δ : Substitution sig}
    {x : Bool → Term sig} {m out p q : Term sig}
    (hit : Fits r x (fun _ => m) δ) (clean : Normalized (ruleRoot rules) δ)
    (normal : ∀ i, Normal (ruleRoot rules) (x i)) (nonunit : ∀ i, x i ≠ s.product.one)
    {l t : Variable} (distinct : l ≠ t) (scope : ¬r.Uses l ∧ ¬r.Uses t)
    (sp : HasSort p l.sort) (sq : HasSort q t.sort)
    (np : Normal (ruleRoot rules) p) (nq : Normal (ruleRoot rules) q)
    (fold : Fold s (op.wrap s β (op.base β p q)) (op.base β p q) m out) :
    ∃ k row, UnitCase s rules r k row ∧
      Denotes (ruleRoot rules) (op.row s β k row l t) (op.inputs β x p q) (fun _ => out) := by
  obtain ⟨η,nη,fit,hl,ht⟩ := extend_points hit clean distinct scope sp sq np nq
  obtain ⟨_,k,row,hr,fit,kUnit⟩ := unit_cases_cover r fit normal nonunit
  have pt (v : Variable) : η.apply (.var v) = η.image v := rfl
  have base : η.apply (op.base β (.var l) (.var t)) = op.base β p q := by
    cases op with
    | action => exact hl
    | pairing => change β.map (η.image l) (η.image t) = β.map p q; rw [hl,ht]
  refine ⟨k,row,hr,η,nη,⟨?_,?_⟩⟩
  · intro i
    cases op <;> cases i <;> simp only [LiftOp.row,LiftOp.inputs,Operators.point_subst,pt,hl,ht]
    all_goals first | exact fit.inputs _ | exact β.point_congr (fit.inputs _) (.refl _)
  · intro _
    change EquivB out (η.apply (if k then _ else _))
    rcases fold with ⟨eq,form⟩|⟨apart,form⟩
    · rw [kUnit.mpr eq,ite_eq_left rfl,base]; exact form
    · have nk : k ≠ true := fun h => apart ((kUnit.mp h) ▸ rfl)
      rw [ite_eq_right nk]
      apply form.trans
      cases op <;> simp only [LiftOp.wrap,Operators.point_subst,DHExponent.Caller.apply_pow] at *
      · exact β.point_congr (fit.values ()) (base ▸ .refl _)
      · exact DHExponent.Caller.equiv_pow s (base ▸ .refl _) (fit.values ())

/-- The assumptions supplied by a scalar-product variant and the nonunit
input filter. The equation list is shared by the scalar and point providers. -/
structure ScalarRow (s : Symbols sig) (rules : List (Equation sig)) (r : Row sig Bool Unit) : Prop where
  typed : ∀ i, HasSort (r.input i) .msg
  normal : ∀ i, Normal (ruleRoot rules) (r.input i)
  nonunit : ∀ i, r.input i ≠ s.product.one
  form : NormalForm (ruleRoot rules) (s.product.mul (r.input false) (r.input true)) (r.value ())

theorem UnitCase.scalar {r q : Row sig Bool Unit} {k : Bool} (h : UnitCase s rules r k q)
    (raw : ScalarRow s rules r) (unit : Normal (ruleRoot rules) s.product.one) : ScalarRow s rules q := by
  cases h with
  | literal => exact raw
  | ordinary => exact raw
  | specialize v typed rawValue sort clean =>
    let κ := Substitution.binding v s.product.one sort
    have value : κ.apply (r.value ()) = s.product.one := by
      rw [rawValue]; exact Substitution.binding_image_self ..
    have red := SpecializedFresh.reduces_subst rules κ raw.form.1
    change Reduces (ruleRoot rules) (s.product.mul (κ.apply (r.input false)) (κ.apply (r.input true))) _ at red
    rw [value] at red
    refine ⟨fun i => (raw.typed i).subst κ.image κ.sorted,fun i => (clean i).1,
      fun i => (clean i).2,red,unit,?_⟩
    intro j hj
    have unitSort : HasSort s.product.one .msg := by
      rw [← s.oneSort]; exact .free _ _ (fun i => Fin.elim0 (s.oneArity ▸ i))
    exact .widen unitSort (s.mulSort ▸ Term.rootSort_le hj)

def LiftOp.call (op : LiftOp) (β : Operators sig) (inputs : Bool → Term sig) : Term sig :=
  match op with | .action => β.point (inputs false) (inputs true) | .pairing => β.map (inputs false) (inputs true)

/-- Every retained two-scalar row has normal raw caller images, and its
predicted value is an actual normal form of the instantiated BP call. -/
theorem LiftOp.sound (op : LiftOp) {T : Table s} (inv : Inventory s β T.rules) (pow : PowerBucket T)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    {r row : Row sig Bool Unit} {k : Bool} (retain : UnitCase s T.rules r k row)
    (raw : ScalarRow s T.rules r)
    (l t : Variable) (sl : HasSort (.var l : Term sig) .msg) (st : HasSort (.var t : Term sig) .msg)
    (nl : Normal (ruleRoot T.rules) (.var l : Term sig)) (nt : Normal (ruleRoot T.rules) (.var t : Term sig)) :
    let lifted := op.row s β k row l t
    (∀ i, Normal (ruleRoot T.rules) (lifted.input i)) ∧
    NormalForm (ruleRoot T.rules) (op.call β lifted.input) (lifted.value ()) := by
  obtain ⟨typed,normal,nonunit,product⟩ := retain.scalar raw unit
  have non (i) : head (row.input i) ≠ .free s.one := fun e => nonunit i (nullary s.oneArity e)
  have plain (v : Variable) : head (.var v : Term sig) ≠ .free β.pmult := by intro h; cases h
  have np (i) (v : Variable) (tv : HasSort (.var v : Term sig) .msg) (nv : Normal (ruleRoot T.rules) (.var v : Term sig)) :
      Normal (ruleRoot T.rules) (β.point (row.input i) (.var v)) :=
    (inv.point_normal_iff (typed i) tv).mpr ⟨normal i,nv,non i,plain v⟩
  have flag := retain.instance.choose_spec.2.2
  have fold : Fold s (op.wrap s β (op.base β (.var l) (.var t))) (op.base β (.var l) (.var t))
      (row.value ()) ((op.row s β k row l t).value ()) := by
    cases k with
    | true => exact .inl ⟨flag.mp rfl,.refl _⟩
    | false => exact .inr ⟨fun e => Bool.noConfusion (flag.mpr (nullary s.oneArity e)),.refl _⟩
  cases op with
  | action =>
    refine ⟨fun | false => normal false | true => np true l sl nl,?_⟩
    exact (inv.point_lift (typed false) (typed true) sl (normal false) (np true l sl nl)
      (non false) unit).mpr ⟨_,product,fold⟩
  | pairing =>
    refine ⟨fun | false => np false l sl nl | true => np true t st nt,?_⟩
    exact (inv.map_lift pow (typed false) (typed true) sl st (np false l sl nl) (np true t st nt)
      unit).mpr ⟨_,product,fold⟩

end Tamarin.Rewriting.Bilinear
