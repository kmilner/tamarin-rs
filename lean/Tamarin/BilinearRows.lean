import Tamarin.BilinearFlatRows
import Tamarin.VariantJoinFamily

/-! Compile an arbitrary complete binary scalar-product family into point
action or commutative map rows. The point parameters are fresh for every
scalar row. Input and output columns always use the same witness scope. -/
namespace Tamarin.Rewriting.Bilinear
open ConstructorVariants DHPeer VariantJoin
variable {sig : Signature} {s : Symbols sig} {β : Operators sig} {rules : List (Equation sig)}

private theorem call_typed (op : LiftOp) {x : Bool → Term sig} (typed : ∀ i, HasSort (x i) .msg) :
    HasSort (op.call β x) .msg := by
  cases op
  · exact β.point_sorted (typed false) (typed true)
  · exact β.map_sorted (typed false) (typed true)

private theorem call_congr (op : LiftOp) {x y : Bool → Term sig} (tie : ∀ i, EquivB (x i) (y i)) :
    EquivB (op.call β x) (op.call β y) := by
  cases op
  · exact β.point_congr (tie false) (tie true)
  · exact .comm_congr _ (tie false) (tie true)

private theorem call_apply (op : LiftOp) (δ : Substitution sig) (x : Bool → Term sig) :
    δ.apply (op.call β x) = op.call β (fun i => δ.apply (x i)) := by
  cases op
  · exact β.point_subst ..
  · rfl

private theorem fitted_form (op : LiftOp) {r : Row sig Bool Unit} {x : Bool → Term sig} {out : Term sig}
    (typed : ∀ i, HasSort (r.input i) .msg) (form : NormalForm (ruleRoot rules) (op.call β r.input) (r.value ()))
    (den : Denotes (ruleRoot rules) r x (fun _ => out)) (normal : Normal (ruleRoot rules) out) :
    NormalForm (ruleRoot rules) (op.call β x) out := by
  obtain ⟨δ,_,fit⟩ := den
  have input := call_congr (β := β) op fit.inputs
  rw [← call_apply] at input
  have red := (Reduces.basis input).trans ((SpecializedFresh.reduces_subst rules δ form.1).trans (.basis (fit.values ()).symm))
  refine ⟨red,normal,?_⟩
  have ty := (form.2.2 .msg (call_typed op typed)).subst δ.image δ.sorted
  have result := Term.checkSort_sound _ _ ((SortClash.check_equiv (fit.values ()) .msg).symm ▸ Term.checkSort_complete ty)
  intro k h
  have le := Term.rootSort_le h
  cases op with
  | action => exact .widen result (β.pointSort ▸ le)
  | pairing => exact .widen result (β.mapSort ▸ le)

/-- The source promises normal sorted scalar images and a genuine product
normal form for each row, and coverage of every sorted normalized assignment.
The construction is independent of how the product solver obtained its rows. -/
structure ProductFamily (s : Symbols sig) (rules : List (Equation sig)) (rows : List (Row sig Bool Unit)) : Prop where
  sound : ∀ r ∈ rows, (∀ i, r.input i ≠ s.product.one) → ScalarRow s rules r
  covers : ∀ x : Bool → Term sig, (∀ i, HasSort (x i) .msg) → (∀ i, Normal (ruleRoot rules) (x i)) →
    ∀ m, NormalForm (ruleRoot rules) (s.product.mul (x false) (x true)) m →
    ∃ r ∈ rows, Denotes (ruleRoot rules) r x (fun _ => m)

/-- The ordinary join-family contract suffices as the source specification.
Two independent Msg keys can realize any pair of normalized scalar terms. -/
theorem ProductFamily.of_exact {rows : List (Row sig Bool Unit)} (ids : Bool → Variable)
    (apart : ids false ≠ ids true) (sort : ∀ i, (ids i).sort = .msg)
    (vars : Normalized (ruleRoot rules) Substitution.identity)
    (typed : ∀ r ∈ rows, ∀ i, HasSort (r.input i) .msg)
    (clean : ∀ r ∈ rows, r.IsNormal (ruleRoot rules))
    (correct : Exact (ruleRoot rules) ids (fun _ : Unit => s.product.mul (.var (ids false)) (.var (ids true))) rows) :
    ProductFamily s rules rows := by
  have valid (x : Bool → Term sig) (tx : ∀ i, HasSort (x i) .msg) (nx : ∀ i, Normal (ruleRoot rules) (x i))
      (m : Term sig) (nm : Normal (ruleRoot rules) m) :
      NormalForm (ruleRoot rules) (s.product.mul (x false) (x true)) m ↔
      ∃ r ∈ rows, Denotes (ruleRoot rules) r x (fun _ => m) := by
    let a := RigidAllocation.Query.override Substitution.identity (ids false) (x false) (sort false ▸ tx false)
    let ρ := RigidAllocation.Query.override a (ids true) (x true) (sort true ▸ tx true)
    have nρ : Normalized (ruleRoot rules) ρ := by
      intro v; dsimp [ρ,a,RigidAllocation.Query.override]
      split <;> first | exact nx true | split <;> first | exact nx false | exact vars _
    have input : (fun i => ρ.image (ids i)) = x := by
      funext i; cases i <;> simp [ρ,a,apart,RigidAllocation.Query.override]
    have cq := correct ρ nρ (fun _ => m) (fun _ => nm)
    rw [input] at cq
    have query : ρ.apply (s.product.mul (.var (ids false)) (.var (ids true))) = s.product.mul (x false) (x true) := by
      change s.product.mul (ρ.image (ids false)) (ρ.image (ids true)) = _
      rw [congrFun input false,congrFun input true]
    constructor
    · intro nf; exact cq.mp (fun _ => query ▸ nf)
    · intro rows; exact query ▸ cq.mpr rows ()
  refine ⟨?_,fun x tx nx m nf => (valid x tx nx m nf.2.1).mp nf⟩
  intro r mem non
  have norm := clean r mem
  refine ⟨typed r mem,norm.1,non,(valid r.input (typed r mem) norm.1 (r.value ()) (norm.2 ())).mpr ?_⟩
  refine ⟨r,mem,.identity,vars,⟨?_,?_⟩⟩
  · intro i; rw [Substitution.apply_identity]; exact .refl _
  · intro a; cases a; rw [Substitution.apply_identity]; exact .refl _

def LiftedMember (op : LiftOp) (s : Symbols sig) (β : Operators sig) (rules : List (Equation sig))
    (raw : List (Row sig Bool Unit)) (l t : Variable) (r : Row sig Bool Unit) : Prop :=
  ∃ source ∈ raw, (∀ i, source.input i ≠ s.product.one) ∧ ∃ k refined,
    UnitCase s rules source k refined ∧ r = op.row s β k refined l t

private theorem lifted_cover (op : LiftOp) {raw : List (Row sig Bool Unit)} (group : ProductFamily s rules raw)
    {x : Bool → Term sig} {m p q out : Term sig} (typed : ∀ i, HasSort (x i) .msg)
    (normal : ∀ i, Normal (ruleRoot rules) (x i)) (nonunit : ∀ i, x i ≠ s.product.one)
    (prod : NormalForm (ruleRoot rules) (s.product.mul (x false) (x true)) m)
    {l t : Variable} (distinct : l ≠ t) (apart : ∀ r ∈ raw, ¬r.Uses l ∧ ¬r.Uses t)
    (sp : HasSort p l.sort) (sq : HasSort q t.sort) (np : Normal (ruleRoot rules) p) (nq : Normal (ruleRoot rules) q)
    (fold : Fold s (op.wrap s β (op.base β p q)) (op.base β p q) m out) :
    ∃ r, LiftedMember op s β rules raw l t r ∧ Denotes (ruleRoot rules) r (op.inputs β x p q) (fun _ => out) := by
  obtain ⟨source,mem,δ,nd,fit⟩ := group.covers x typed normal m prod
  have guard := (unit_cases_cover source fit normal nonunit).1
  obtain ⟨k,q,case,den⟩ := op.covers fit nd normal nonunit distinct (apart source mem) sp sq np nq fold
  exact ⟨_,⟨source,mem,guard,k,q,case,rfl⟩,den⟩

private theorem lifted_sound (op : LiftOp) {T : Table s} (I : Inventory s β T.rules) (pow : PowerBucket T)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    {raw : List (Row sig Bool Unit)} (group : ProductFamily s T.rules raw)
    {l t : Variable} (sl : HasSort (.var l : Term sig) .msg) (st : HasSort (.var t : Term sig) .msg)
    (nl : Normal (ruleRoot T.rules) (.var l : Term sig)) (nt : Normal (ruleRoot T.rules) (.var t : Term sig))
    {r} (mem : LiftedMember op s β T.rules raw l t r) :
    (∀ i, HasSort (r.input i) .msg) ∧ (∀ i, Normal (ruleRoot T.rules) (r.input i)) ∧
    NormalForm (ruleRoot T.rules) (op.call β r.input) (r.value ()) := by
  obtain ⟨source,mem,guard,k,q,retain,rfl⟩ := mem
  have sr := group.sound source mem guard
  refine ⟨?_,op.sound I pow unit retain sr l t sl st nl nt⟩
  have typed := (retain.scalar sr unit).typed
  intro i
  cases op <;> cases i <;> first | exact typed _ | exact β.point_sorted (typed _) sl | exact β.point_sorted (typed _) st

/-- The action has two flat branches and the map has three. Every remaining
branch lifts a scalar product row. Enumeration and branch order are free. -/
def Member (op : LiftOp) (s : Symbols sig) (β : Operators sig) (rules : List (Equation sig))
    (raw : List (Row sig Bool Unit)) (keys : Fin 3 → Variable) (l t : Variable)
    (r : Row sig Bool Unit) : Prop :=
  (∃ f : Flat op, r = f.row s β keys) ∨ LiftedMember op s β rules raw l t r

theorem Member.sound [DecidableEq sig.ACSym] {T : Table s} {E : ExtraTable T}
    (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    {raw : List (Row sig Bool Unit)} (family : ProductFamily s T.rules raw)
    {keys : Fin 3 → Variable} (sort : ∀ i, (keys i).sort = .msg)
    {l t : Variable} (sl : l.sort = .msg) (st : t.sort = .msg)
    {op r} (mem : Member op s β T.rules raw keys l t r) :
    (∀ i, HasSort (r.input i) .msg) ∧ (∀ i, Normal (ruleRoot T.rules) (r.input i)) ∧
      NormalForm (ruleRoot T.rules) (op.call β r.input) (r.value ()) := by
  rcases mem with ⟨tag,rfl⟩|source
  · exact ⟨tag.typed s β keys sort,tag.sound I pow group unit keys sort⟩
  · have vars := (constructor_normal T.rules I.apps).1
    exact lifted_sound op I pow unit family (sl ▸ HasSort.var _) (st ▸ HasSort.var _) (vars _) (vars _) source

private def two (a b : Term sig) : Bool → Term sig | false => a | true => b

private theorem two_all {a b : Term sig} {P : Term sig → Prop} (l : P a) (r : P b) : ∀ i, P (two a b i)
  | false => l | true => r

/-- All normalized sorted input pairs and all normal proposed values are
covered together, in both directions. The only theory-specific premises
are the actual three BP and DH root inventories; the product family itself
may be implemented by any solver satisfying the ordinary row contract. -/
theorem family_iff [DecidableEq sig.ACSym] {T : Table s} {E : ExtraTable T}
    (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    {raw : List (Row sig Bool Unit)} (family : ProductFamily s T.rules raw)
    (keys : Fin 3 → Variable) (inj : Function.Injective keys) (sort : ∀ i, (keys i).sort = .msg)
    (l t : Variable) (distinct : l ≠ t) (sl : l.sort = .msg) (st : t.sort = .msg)
    (apart : ∀ r ∈ raw, ¬r.Uses l ∧ ¬r.Uses t)
    (op : LiftOp) (x : Bool → Term sig) (typed : ∀ i, HasSort (x i) .msg) (normal : ∀ i, Normal (ruleRoot T.rules) (x i))
    (out : Term sig) (nn : Normal (ruleRoot T.rules) out) :
    NormalForm (ruleRoot T.rules) (op.call β x) out ↔
      ∃ r, Member op s β T.rules raw keys l t r ∧ Denotes (ruleRoot T.rules) r x (fun _ => out) := by
  have notOne {a : Term sig} (h : head a ≠ .free s.one) : a ≠ s.product.one := by
    rintro rfl; exact h rfl
  have bothTyped {a b : Term sig} (sa : HasSort a .msg) (sb : HasSort b .msg) :
      ∀ i, HasSort (two a b i) .msg := two_all (P := fun t => HasSort t .msg) sa sb
  have flat {o : LiftOp} (f : Flat o) (matchCase : f.Matches s β x out) :
      ∃ r, Member o s β T.rules raw keys l t r ∧ Denotes (ruleRoot T.rules) r x (fun _ => out) :=
    ⟨_,.inl ⟨f,rfl⟩,f.covers keys inj sort (constructor_normal T.rules I.apps).1 typed normal nn matchCase⟩
  constructor
  · intro form
    cases op with
    | action =>
      cases (I.point_results group unit (typed false) (typed true) (normal false) (normal true)).mp form with
      | unit u val => exact flat .actionUnit ⟨u,val⟩
      | plain _ _ val => exact flat .actionPlain val
      | nested h eq prod fold =>
        rename_i b p m
        have ⟨sb,sp⟩ := β.point_types (eq ▸ typed true)
        have ⟨nb,np,nu,_⟩ := (I.point_normal_iff sb sp).mp (eq ▸ normal true)
        let a := x false
        have ⟨r,member,den⟩ := lifted_cover .action family (x := two a b)
          (bothTyped (typed false) sb) (two_all (normal false) nb)
          (two_all (P := fun u => u ≠ s.product.one) (notOne h) (notOne nu))
          prod distinct apart (sl ▸ sp) (st ▸ sp) np np fold
        have restore : LiftOp.action.inputs β (two a b) p p = x := by
          funext i; cases i; exact rfl; exact eq.symm
        exact ⟨r,.inr member,restore ▸ den⟩
    | pairing =>
      cases (I.map_results pow unit (typed false) (typed true) (normal false) (normal true)).mp form with
      | plain _ _ val => exact flat .mapPlain val
      | left inp _ val => exact flat .mapLeft ⟨_,_,inp,val⟩
      | right inp _ val => exact flat .mapRight ⟨_,_,inp,val⟩
      | both left right prod fold =>
        rename_i a b p q m
        have ⟨sa,sp⟩ := β.point_types (left ▸ typed false)
        have ⟨sb,sq⟩ := β.point_types (right ▸ typed true)
        have ⟨na,np,au,_⟩ := (I.point_normal_iff sa sp).mp (left ▸ normal false)
        have ⟨nb,nq,bu,_⟩ := (I.point_normal_iff sb sq).mp (right ▸ normal true)
        have ⟨r,member,den⟩ := lifted_cover .pairing family (x := two a b)
          (bothTyped sa sb) (two_all na nb) (two_all (P := fun u => u ≠ s.product.one) (notOne au) (notOne bu))
          prod distinct apart (sl ▸ sp) (st ▸ sq) np nq fold
        have restore : LiftOp.pairing.inputs β (two a b) p q = x := by
          funext i; cases i; exact left.symm; exact right.symm
        exact ⟨r,.inr member,restore ▸ den⟩
  · rintro ⟨r,mem,den⟩
    have ⟨ty,_,form⟩ := mem.sound I pow group unit family sort sl st
    exact fitted_form op ty form den nn

/-- The generated family meets the same indexed variant contract used to join
and subsumption-prune ordinary theory components. -/
theorem exact_family [DecidableEq sig.ACSym] {T : Table s} {E : ExtraTable T}
    (I : Inventory s β T.rules) (pow : PowerBucket T) (group : Balance.Inventory E)
    (unit : Normal (ruleRoot T.rules) s.product.one)
    {raw : List (Row sig Bool Unit)} (family : ProductFamily s T.rules raw)
    (keys : Fin 3 → Variable) (inj : Function.Injective keys) (sort : ∀ i, (keys i).sort = .msg)
    (l t : Variable) (distinct : l ≠ t) (sl : l.sort = .msg) (st : t.sort = .msg)
    (apart : ∀ r ∈ raw, ¬r.Uses l ∧ ¬r.Uses t)
    (op : LiftOp) (ids : Bool → Variable) (types : ∀ i, (ids i).sort = .msg)
    (result : List (Row sig Bool Unit))
    (members : ∀ r, r ∈ result ↔ Member op s β T.rules raw keys l t r) :
    Exact (ruleRoot T.rules) ids (fun _ : Unit => op.call β (fun i => .var (ids i))) result := by
  intro ρ nρ values nv
  let x (i : Bool) := ρ.image (ids i)
  have ty (i) : HasSort (x i) .msg := types i ▸ ρ.sorted _
  have single := family_iff I pow group unit family keys inj sort l t distinct sl st apart op x ty
    (fun i => nρ (ids i)) (values ()) (nv ())
  have query := call_apply (β := β) op ρ (fun i => .var (ids i))
  have eta : (fun _ : Unit => values ()) = values := funext (fun i => by cases i; rfl)
  constructor
  · intro fs
    obtain ⟨r,mem,den⟩ := single.mp (query ▸ fs ())
    exact ⟨r,(members r).mpr mem,eta ▸ den⟩
  · rintro ⟨r,mem,den⟩ i
    cases i
    exact query ▸ single.mpr ⟨r,(members r).mp mem,eta ▸ den⟩

end Tamarin.Rewriting.Bilinear
