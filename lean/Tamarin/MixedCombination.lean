import Tamarin.MixedRigidGraph
import Tamarin.MixedLocalGraph

/-! Finite combination of free constructors, commutative constructors and any
number of ordinary AC operators. On the partition induced by a model, each
non-singleton local definition fixes the root of its slot. Distinct roots cannot
compete in that model. Equal AC roots have just one local image per slot. -/
namespace Tamarin.MixedUnification.Combination
open SolvedForm LocalAnswers
variable {s : Signature} [DecidableEq s.ACSym]

private def heads (cs : List (Constraint s)) : List s.ACSym :=
  (cs.filterMap fun c => match c with | .ac _ f .. => some f | _ => none).eraseDups

private def tag (fs : List s.ACSym) (f : s.ACSym) (w : Variable) : Variable :=
  ⟨fs.idxOf f + fs.length * (ComponentEncoding.name w).id,.pub⟩

private def environment (fs : List s.ACSym) (V : Nat → Term s) (μ : s.ACSym → Env s)
    (v : Variable) : Term s :=
  if v.sort = .msg then V v.id else
    match fs[v.id % fs.length]? with
    | some f => μ f (ComponentEncoding.original ⟨v.id / fs.length,.msg⟩)
    | none => .var v

private theorem at_tag (fs : List s.ACSym) {f : s.ACSym} (hf : f ∈ fs) (V μ w) :
    environment fs V μ (tag fs f w) = μ f w := by
  have lt := List.idxOf_lt_length_of_mem hf
  have pos : 0 < fs.length := by omega
  simp only [environment,tag,reduceCtorEq,↓reduceIte,Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt lt,Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt lt,Nat.zero_add,
    List.getElem?_eq_getElem lt,List.getElem_idxOf]
  exact congrArg (μ f) (ComponentEncoding.original_name w)

private def products {ι α : Type} (arms : ι → List (List α)) : List ι → List (List α)
  | [] => [[]]
  | i :: is => (arms i).flatMap fun a => (products arms is).map (a ++ ·)

private theorem product_mem {ι α : Type} (arms : ι → List (List α)) (pick : ι → List α)
    (is : List ι) (ok : ∀ i ∈ is, pick i ∈ arms i) : is.flatMap pick ∈ products arms is := by
  induction is with
  | nil => exact List.mem_singleton_self _
  | cons i is ih =>
    exact List.mem_flatMap.mpr ⟨_,ok i List.mem_cons_self,List.mem_map_of_mem
      (ih fun j hj => ok j (List.mem_cons_of_mem _ hj))⟩

def candidates (cs : List (Constraint s)) : List (Env s) :=
  let fs := heads cs
  let choices := fun f => (arms f (rows cs f)).map fun a => a.graph (tag fs f)
  (products choices fs).map fun ds => (assemble (RigidGraph.graph cs ++ ds)).val

theorem covers (cs : List (Constraint s)) (V : Nat → Term s)
    (model : ∀ c ∈ cs, c.Holds V) (sep : RigidGraph.Separated cs V) :
    ∃ θ ∈ candidates cs, (∀ c ∈ cs, c.Holds (θ ∘ ref)) ∧
      ∃ W, ∀ i, EquivB (V i) ((θ (ref i)).subst W) := by
  let fs := heads cs
  have localSolution (f : s.ACSym) := LocalAnswers.covers f (rows cs f) V
    (fun r hr => model _ (mem_rows.mp hr))
  let arm := fun f => (localSolution f).choose
  have returned (f) : arm f ∈ arms f (rows cs f) := (localSolution f).choose_spec.1
  let μ := fun f => (localSolution f).choose_spec.2.choose
  have factors (f) (i) (hi : i ∈ keys (rows cs f)) :
      EquivB (V i) (((arm f).image i).subst (μ f)) := (localSolution f).choose_spec.2.choose_spec i hi
  let block := fun f => (arm f).graph (tag fs f)
  let ds := RigidGraph.graph cs ++ fs.flatMap block
  let W := environment fs V μ
  have slotW (i) : W (ref i) = V i := rfl
  have localModel (f) (hf : f ∈ fs) : Models (block f) W :=
    (arm f).graph_model _ W slotW (at_tag fs hf V μ) (factors f)
  have all : Models ds W := by
    intro d hd
    rcases List.mem_append.mp hd with h|h
    · obtain ⟨c,hc,_,rfl⟩ := RigidGraph.mem.mp h
      rw [RigidGraph.body]; exact model c hc
    · obtain ⟨f,hf,hd⟩ := List.mem_flatMap.mp h
      exact localModel f hf d hd
  have equalBodies (d e : Row s) (hd : d ∈ ds) (he : e ∈ ds) (eq : d.1 = e.1) :
      EquivB (d.2.subst W) (e.2.subst W) := by
    have a := all d hd; rw [eq] at a
    exact a.symm.trans (all e he)
  have different (d e : Row s) (hd : d ∈ RigidGraph.graph cs)
      (he : e ∈ fs.flatMap block) (eq : d.1 = e.1) : False := by
    have h := (equalBodies d e (List.mem_append_left _ hd) (List.mem_append_right _ he) eq).head_eq
    obtain ⟨c,_,rig,rfl⟩ := RigidGraph.mem.mp hd
    obtain ⟨f,_,m⟩ := List.mem_flatMap.mp he
    obtain ⟨i,_,rfl,l,r,shape⟩ := (arm f).entry m
    simp only [shape,Term.subst,headModel,Model.eval] at h
    exact RigidGraph.no_ac rig W f h
  have agree : Agree ds := by
    intro d hd e he eq
    have hd' := List.mem_append.mp hd
    have he' := List.mem_append.mp he
    rcases hd' with h|h <;> rcases he' with k|k
    · exact RigidGraph.agree cs V model sep d h e k eq
    · exact (different d e h k eq).elim
    · exact (different e d k h eq.symm).elim
    · have same := (equalBodies d e hd he eq).head_eq
      obtain ⟨f,_,m⟩ := List.mem_flatMap.mp h
      obtain ⟨g,_,n⟩ := List.mem_flatMap.mp k
      obtain ⟨i,_,rfl,l,r,sh⟩ := (arm f).entry m
      obtain ⟨j,_,rfl,u,v,st⟩ := (arm g).entry n
      have ij : i = j := congrArg Variable.id eq
      have fg : f = g := by simpa [sh,st,Term.subst,Model.eval,headModel] using same
      subst j; subst g; exact .refl _
  let θ := (assemble ds).val
  obtain ⟨sol,fac⟩ := (assemble ds).property W all agree
  have picked := product_mem (fun f => (arms f (rows cs f)).map fun a => a.graph (tag fs f))
    block fs (fun f _ => List.mem_map_of_mem (returned f))
  refine ⟨θ,List.mem_map_of_mem picked,?_,W,fun i => fac (ref i)⟩
  intro c hc
  by_cases rig : RigidGraph.rigid c
  · have m := sol _ (List.mem_append_left _ (RigidGraph.mem.mpr ⟨c,hc,rig,rfl⟩))
    rw [RigidGraph.body] at m; exact m
  cases c with
  | atom | free | comm => contradiction
  | ac i f j k =>
    have hf : f ∈ fs := List.mem_eraseDups.mpr (List.mem_filterMap.mpr ⟨_,hc,rfl⟩)
    apply (arm f).graph_solves _ θ (fun d hd => sol d (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨_,hf,hd⟩))) (factors f) _ ⟨i,j,k⟩ (mem_rows.mpr hc)
    have inside (n) (hn : n ∈ keys (rows cs f)) : n ∈ cs.flatMap Constraint.slots := by
      obtain ⟨r,hr,hm⟩ := List.mem_flatMap.mp (List.mem_eraseDups.mp hn)
      exact List.mem_flatMap.mpr ⟨_,mem_rows.mp hr,hm⟩
    exact fun x hx y hy => sep x (inside _ hx) y (inside _ hy)

end Tamarin.MixedUnification.Combination
