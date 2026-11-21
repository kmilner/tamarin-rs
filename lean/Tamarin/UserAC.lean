import Tamarin.PresentationComponents
import Tamarin.ACSubproductReduction
import Tamarin.SortedACNormalAlgebra
import Tamarin.TableAmbient

/-! A user-declared AC operation with a unit equation. All consequences are
proved for the full table, including subproduct reductions at the common kind. -/
namespace Tamarin.UserAC
open Rewriting Cancellation ConstructorVariants PresentationComponents ShortVariantPaths
variable {s : Signature}

structure Schema (s : Signature) where
  f : s.ACSym
  z : s.FreeSym
  ar : s.arity z = 0
  zSort : s.outputSort z = .msg
  fSort : s.acSort f = .msg
  v : Variable
  vSort : v.sort = .msg

namespace Schema
variable (a : Schema s)

def unit : Term s := .free a.z fun i => Fin.elim0 (a.ar ▸ i)

def row : Equation s := ⟨.ac a.f (.var a.v) a.unit,.var a.v⟩

def part [DecidableEq s.FreeSym] [DecidableEq s.ACSym] : Part s where
  rows := [a.row]
  owns
    | .ac f => f == a.f
    | .free z => z == a.z
    | _ => false

private theorem unit_sort : HasSort a.unit .msg :=
  a.zSort ▸ HasSort.free a.z _ (fun i => Fin.elim0 (a.ar ▸ i))

private theorem fixes (σ : Substitution s) : σ.apply a.unit = a.unit :=
  (show a.unit.Ground from fun _ ⟨i,_⟩ => Fin.elim0 (a.ar ▸ i)).apply_eq σ

variable [DecidableEq s.FreeSym] [DecidableEq s.ACSym] {rs : Problem s}
variable (inc : Inventory a.part rs) (apps : ∀ r ∈ rs, Application r.lhs)
include inc

private theorem only {r : Equation s} (hr : r ∈ rs) (hd : head r.lhs = .ac a.f) : r = a.row :=
  List.mem_singleton.mp (inc.only _ hr (by simp [part,hd]))

private theorem unused : Head.free a.z ∉ ruleHeads rs := by
  rintro h
  obtain ⟨r,hr,hd⟩ := List.mem_map.mp h
  obtain rfl : r = a.row := List.mem_singleton.mp (inc.only _ hr (by simp [part,hd]))
  cases hd

private theorem fire {x : Term s} (ty : HasSort x .msg) : ruleRoot rs (.ac a.f x a.unit) x := by
  let σ : Substitution s := {
    image := fun v => if v = a.v then x else .var v
    support := [a.v]
    outside := by intro v h; simp_all
    sorted := by intro v; split <;> rename_i h
                 · simpa [h,a.vSort] using ty
                 · exact .var _ }
  refine ⟨a.row,inc.present a.row List.mem_cons_self,σ,?_,?_⟩
  · change _ = Term.ac a.f (σ.image a.v) (σ.apply a.unit)
    simp [σ,a.fixes]
  · change x = σ.image a.v; simp [σ]

include apps

private theorem root_unit {p q : Term s} (hd : head p = .ac a.f) (step : ruleRoot rs p q) :
    p = .ac a.f q a.unit ∧ HasSort q .msg := by
  obtain ⟨r,hr,σ,rfl,rfl⟩ := step
  rw [instance_head _ (apps _ hr) σ] at hd
  obtain rfl := a.only inc hr hd
  change Term.ac a.f (σ.image a.v) (σ.apply a.unit) = _ ∧ HasSort (σ.image a.v) .msg
  exact ⟨by rw [a.fixes]; rfl,a.vSort ▸ σ.sorted a.v⟩

private theorem redex_typed {p q : Term s} (hd : head p = .ac a.f) (step : ruleRoot rs p q) :
    HasSort p .msg := by
  obtain ⟨rfl,t⟩ := a.root_unit inc apps hd step
  exact a.fSort ▸ HasSort.ac _ _ _ (a.fSort ▸ t) (a.fSort ▸ a.unit_sort)

private theorem unit_normal : Normal (ruleRoot rs) a.unit :=
  constructor_node_normal _ apps _ (a.unused inc) (fun i => Fin.elim0 (a.ar ▸ i))

omit apps in
private theorem contains_unit {x : Term s} (tx : HasSort x .msg) (nx : Normal (ruleRoot rs) x)
    (mem : classOf a.unit ∈ flatten a.f x) : EquivB x a.unit := by
  rw [DHProduct.classes] at mem
  obtain ⟨u,hu,same⟩ := List.mem_map.mp mem
  have eq : EquivB u a.unit := Quotient.exact same
  rcases DHProduct.extract a.f a.fSort x u tx nx hu with h | ⟨rest,h,t,_⟩
  · exact h.trans eq
  · exact (nx _ ⟨_,_,h.trans (.ac_congr _ (.refl _) eq),.root (a.fire inc t),.refl _⟩).elim

omit [DecidableEq s.FreeSym] inc apps in
private theorem leaves {x y : Term s} (nx : Normal (ruleRoot rs) x) (ny : Normal (ruleRoot rs) y) :
    ∀ u ∈ ACRepresentation.flatten a.f (.ac a.f x y), Normal (ruleRoot rs) u := by
  intro u hu
  rcases List.mem_append.mp (by simpa [ACRepresentation.flatten] using hu) with l | r
  · exact ((DHProduct.subgroup_normal_iff a.f x).mp nx).1 u l
  · exact ((DHProduct.subgroup_normal_iff a.f y).mp ny).1 u r

private theorem unique : NormalAlgebra.UniqueRow rs a.row := by
  intro σ norm x y hx hy
  let t := σ.image a.v
  have ty : HasSort t .msg := a.vSort ▸ σ.sorted a.v
  have src : σ.apply a.row.lhs = .ac a.f t a.unit := by
    change Term.ac _ _ (σ.apply a.unit) = _; rw [a.fixes]; rfl
  rw [src] at hx hy
  have endpt {u} (nf : NormalForm (ruleRoot rs) (.ac a.f t a.unit) u) : EquivB u t := by
    rcases RootNarrowing.firstStep nf.1 with already | ⟨z,st,tail⟩
    · exact (((normal_equiv _ already).mpr nf.2.1) _ ⟨_,_,.refl _,.root (a.fire inc ty),.refl _⟩).elim
    obtain ⟨p,q,k,hd,red,l,r⟩ := (ACSubproductReduction.step_iff a.f _ _ (a.leaves (norm a.v) (a.unit_normal inc apps))).mp st
    obtain ⟨rfl,_⟩ := a.root_unit inc apps hd red
    have e : EquivB t z := by
      apply EquivB.ac_cancel_right a.f
      cases k with
      | none => exact l.trans (.ac_congr _ r (.refl _))
      | some rest =>
        exact l.trans (((EquivB.ac_assoc a.f q a.unit rest).trans
          ((EquivB.ac_congr _ (.refl q) (.ac_swap _ a.unit rest)).trans (EquivB.ac_assoc a.f q rest a.unit).symm)).trans
          (.ac_congr _ r (.refl _)))
    exact ((normal_reduces_equiv tail ((normal_equiv _ e).mp (norm a.v))).symm).trans e.symm
  exact (endpt hx).trans (endpt hy).symm

open scoped Classical

private noncomputable def pieces (xs : List (Class s)) : List (Class s) :=
  xs.filter (fun k => k != classOf a.unit)

omit [DecidableEq s.FreeSym] [DecidableEq s.ACSym] apps inc in
private theorem pieces_unit : a.pieces (flatten a.f a.unit) = [] := by
  change [classOf a.unit].filter _ = []; simp

omit apps in
private theorem normal_bag {x : Term s} (tx : HasSort x .msg) (nx : Normal (ruleRoot rs) x) :
    (flatten a.f x).Perm (if (a.pieces (flatten a.f x)).isEmpty then [classOf a.unit] else a.pieces (flatten a.f x)) := by
  by_cases h : classOf a.unit ∈ flatten a.f x
  · have perm := flatten_equiv a.f (a.contains_unit inc tx nx h)
    have rem := perm.filter (fun k => k != classOf a.unit)
    change (a.pieces _).Perm (a.pieces _) at rem
    rw [a.pieces_unit] at rem
    rw [rem.eq_nil]; exact perm
  · have same : a.pieces (flatten a.f x) = flatten a.f x := List.filter_eq_self.mpr (fun k hk => by
        have ne : k ≠ classOf a.unit := fun eq => h (eq ▸ hk)
        simp [ne])
    have ne : flatten a.f x ≠ [] := by
      rw [DHProduct.classes]; simpa using ACRepresentation.flatten_nonempty a.f x
    simp [same,List.isEmpty_iff,ne]

private noncomputable def invariant : SortedAC.ProductInvariant a.f (ruleRoot rs) where
  rel x y := (a.pieces x).Perm (a.pieces y)
  ofPerm p := p.filter _
  symm p := p.symm
  trans p q := p.trans q
  append h i := by simpa [pieces,List.filter_append] using h.append i
  distinguish {x y} tx ty nx ny h := by
    apply equiv_of_flatten_perm a.f
    have eq : (a.pieces (flatten a.f x)).isEmpty = (a.pieces (flatten a.f y)).isEmpty := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.isEmpty_iff]
      exact ⟨fun e => (e ▸ h).symm.eq_nil, fun e => (e ▸ h).eq_nil⟩
    refine (a.normal_bag inc tx nx).trans (List.Perm.trans ?_ (a.normal_bag inc ty ny).symm)
    rw [eq]; split
    · exact .refl _
    · exact h

private theorem sortedPaths : (a.invariant inc).SortedPaths 1 := by
  intro x y tx ty nx ny
  have drop {v w : Term s} (eq : EquivB w a.unit) (tv : HasSort v .msg) :
      Path (ruleRoot rs) 1 (.ac a.f v w) v :=
    .step ⟨_,_,.ac_congr _ (.refl _) eq,.root (a.fire inc tv),.refl _⟩ (.basis (.refl _))
  have unitPieces {t : Term s} (eq : EquivB t a.unit) : a.pieces (flatten a.f t) = [] := by
    have h := (flatten_equiv a.f eq).filter (fun k => k != classOf a.unit)
    exact (a.pieces_unit ▸ h : (a.pieces _).Perm []).eq_nil
  have app (l r : List (Class s)) : a.pieces (l ++ r) = a.pieces l ++ a.pieces r := List.filter_append l r
  by_cases hx : EquivB x a.unit
  · exact ⟨y,ty,(drop hx ty).rebase (.ac_swap ..),ny,by
      change (a.pieces _).Perm (a.pieces _)
      rw [flatten_ac,app,unitPieces hx,List.nil_append]⟩
  by_cases hy : EquivB y a.unit
  · exact ⟨x,tx,drop hy tx,nx,by
      change (a.pieces _).Perm (a.pieces _)
      rw [flatten_ac,app,unitPieces hy,List.append_nil]⟩
  refine ⟨_,a.fSort ▸ HasSort.ac _ _ _ (a.fSort ▸ tx) (a.fSort ▸ ty),.basis (.refl _),?_,.refl _⟩
  apply DHProduct.subgroup_normal a.f _ (a.leaves nx ny)
  rintro p q hd ⟨rest,perm⟩ red
  obtain ⟨rfl,_⟩ := a.root_unit inc apps hd red
  rw [flatten_ac,flatten_ac] at perm
  have hit := perm.mem_iff.mpr (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self (classOf a.unit))))
  exact (List.mem_append.mp hit).elim (fun h => hx (a.contains_unit inc tx nx h)) (fun h => hy (a.contains_unit inc ty ny h))

theorem localProof (h : Head s) (used : h ∈ ruleHeads rs) (owns : a.part.owns h) : Local rs h := by
  cases h with
  | ac f =>
    obtain rfl : f = a.f := eq_of_beq owns
    refine ⟨⟨(a.invariant inc).product a.fSort (a.redex_typed inc apps) (a.sortedPaths inc apps),?_,?_⟩⟩
    · intro r hr hd
      obtain rfl := a.only inc hr hd
      exact a.unique inc apps
    · refine ⟨1,fun x y nx ny => ?_⟩
      obtain ⟨u,path,norm,_⟩ := SortedAC.paths a.fSort (a.redex_typed inc apps) (fun _ _ => True)
        (fun _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (k := 1) (by
          intro l r tl tr nl nr
          obtain ⟨v,t,p,n,_⟩ := a.sortedPaths inc apps l r tl tr nl nr
          exact ⟨v,t,p,n,trivial⟩) x y nx ny
      exact ⟨u,path,norm⟩
  | free z =>
    obtain rfl : z = a.z := eq_of_beq owns
    exact (a.unused inc used).elim
  | _ => contradiction

end Schema

private def candidate {s : Signature} (r : Equation s) : Option (Schema s) := do
  let .ac f l k := r.lhs | none
  let (v,z) ← match l,k with
    | .var v,.free z _ | .free z _,.var v => some (v,z)
    | _,_ => none
  let .var w := r.rhs | none
  guard (v == w)
  if h : s.arity z = 0 ∧ s.outputSort z = .msg ∧ s.acSort f = .msg ∧ v.sort = .msg then
    return ⟨f,z,h.1,h.2.1,h.2.2.1,v,h.2.2.2⟩
  else none

/-- Keep a standalone unit-law candidate only if all equations at its AC head
agree with the row. Other component inventories may include their own unit law. -/
def candidates {d : TotalUnifyWire.Dictionary} (rs : Problem d.sig) : List (Schema d.sig) :=
  rs.filterMap fun r => do
    let a ← candidate (s := d.sig) r
    guard (rs.all fun q => match q.lhs with
      | .ac f .. => f != a.f || (ReferenceMatching.equal q.lhs a.row.lhs && ReferenceMatching.equal q.rhs a.row.rhs)
      | _ => true)
    return a

def liftSchema {d : TotalUnifyWire.Dictionary} (a : Schema d.sig) : Schema (TableAmbient.sig d) where
  f := .inl a.f
  z := .inl a.z
  ar := a.ar
  zSort := a.zSort
  fSort := a.fSort
  v := a.v
  vSort := a.vSort

end Tamarin.UserAC
