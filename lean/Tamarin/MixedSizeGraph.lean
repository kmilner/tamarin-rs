import Tamarin.MixedSizeSystem
import Tamarin.CheckedFactoring
import Tamarin.ACBagSearch
import Tamarin.ACFeasibility
import Tamarin.MixedSizeGraphDecode

namespace Tamarin.MixedSizeGraph
open Whole WholeProblem FiniteOccurs ACBasis ACFeasibility
variable {sig : Signature}

/-- Source-side affine coefficients. Each variable occurrence is replaced by
the full size of its substitution image, leaving all other nodes fixed. -/
def fixed (t : Term sig) : Nat := nodes t - t.variables.length

def sourceKeys (c : Codec sig) (p : Problem sig) : List UInt64 :=
  (p.flatMap fun e => e.lhs.variables.map c.vars.put ++ e.rhs.variables.map c.vars.put).eraseDups

def sourceWeights (c : Codec sig) (ks : List UInt64) (t : Term sig) : Vec (ks.length + 1) :=
  prepend (fixed t) (fun i => (t.variables.map c.vars.put).count (ks.get i))

def sourceRows (c : Codec sig) (p : Problem sig) : List (Row ((sourceKeys c p).length + 1)) :=
  p.map fun e => Row.ofWeights (sourceWeights c (sourceKeys c p) e.lhs) (sourceWeights c (sourceKeys c p) e.rhs)

private def mass (p : Profile) := p.fixed + p.vars.length

private theorem children_vars (xs : List Tree) :
    (profiles xs).vars = xs.flatMap (fun t => (profile t).vars) := by
  induction xs with
  | nil => rfl
  | cons t ts ih => simp [profiles,Profile.plus,ih]

private theorem children_mass (xs : List Tree) :
    mass (profiles xs) = (xs.map fun t => mass (profile t)).sum := by
  induction xs with
  | nil => rfl
  | cons t ts ih =>
    simp only [profiles,Profile.plus,mass,List.length_append,List.map_cons,List.sum_cons] at ih ⊢
    omega

private theorem app_mass (k id : UInt64) (xs : List Tree) :
    mass (profile (.app k id xs)) = (xs.map fun t => mass (profile t)).sum +
      (if k = 4 then xs.length - 1 else 1) := by
  rw [←children_mass]
  simp only [mass,profile,Nat.add_right_comm]

private theorem encoded (c : Codec sig) (t : Term sig) :
    (profile (WholeProblem.encode c t)).vars = t.variables.map c.vars.put ∧
    mass (profile (WholeProblem.encode c t)) = nodes t := by
  induction t with
  | var v => exact ⟨rfl,rfl⟩
  | atom a => exact ⟨rfl,rfl⟩
  | comm f a b ia ib | ac f a b ia ib =>
    constructor
    · simp [WholeProblem.encode,profile,profiles,Profile.plus,ia.1,ib.1,Term.variables]
    · change mass (profile (.app _ _ [_,_])) = nodes a + nodes b + 1
      simp [app_mass,ia.2,ib.2]
  | free f args ih =>
    constructor
    · simp only [WholeProblem.encode,profile,children_vars,Term.variables,List.flatMap_def,List.map_flatten,List.map_ofFn,
        Function.comp_def]
      exact congrArg List.flatten (congrArg List.ofFn (funext fun i => (ih i).1))
    · change mass (profile (.app 2 _ _)) = (List.ofFn fun i => nodes (args i)).sum + 1
      simp only [app_mass,show (2 : UInt64) ≠ 4 by decide,↓reduceIte,List.map_ofFn]
      exact congrArg (fun v => (List.ofFn v).sum + 1) (funext fun i => (ih i).2)

private inductive Valid : Tree → Prop where
  | leaf (k id s) : Valid (.leaf k id s)
  | app (k id) (xs : List Tree) : (k = 4 → 2 ≤ xs.length) → (∀ t ∈ xs, Valid t) → Valid (.app k id xs)

private theorem valid_encode (c : Codec sig) (t : Term sig) : Valid (WholeProblem.encode c t) := by
  induction t with
  | var | atom => exact .leaf ..
  | comm f a b ia ib | ac f a b ia ib => exact .app _ _ _ (by simp) (by simpa using And.intro ia ib)
  | free f xs ih =>
    apply Valid.app _ _ _ (by intro eq; contradiction)
    intro t ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact ih i

private theorem profiles_append (xs ys : List Tree) : profiles (xs ++ ys) = (profiles xs).plus (profiles ys) := by
  induction xs with
  | nil => simp [profiles,Profile.plus]
  | cons x xs ih => simp [profiles,ih,Profile.plus,Nat.add_assoc,List.append_assoc]

private theorem layout_profile {a b : Tree} (lay : Layout a b) (good : Valid a) : Valid b ∧ profile a = profile b := by
  induction lay with
  | refl => exact ⟨good,rfl⟩
  | trans _ _ ih ij =>
    obtain ⟨mid,e⟩ := ih good
    obtain ⟨last,d⟩ := ij mid
    exact ⟨last,e.trans d⟩
  | child k id pre post _ ih =>
    cases good with
    | app _ _ _ len children =>
      obtain ⟨valid,eq⟩ := ih (children _ (by simp))
      constructor
      · apply Valid.app _ _ _ (by simpa using len)
        intro t ht
        simp only [List.mem_append,List.mem_cons] at ht
        rcases ht with inside | rfl | after
        · exact children t (by simp [inside])
        · exact valid
        · exact children t (by simp [after])
      · simp only [profile,profiles_append,profiles,List.length_append,List.length_cons,eq]
  | flatten id pre inner post =>
    cases good with
    | app _ _ _ outer children =>
      have nested := children (.app 4 id inner) (by simp)
      cases nested with
      | app _ _ _ innerSize innerValid =>
        have size := innerSize rfl
        constructor
        · apply Valid.app _ _ _ (by simp only [List.length_append]; omega)
          intro t ht
          simp only [List.mem_append] at ht
          rcases ht with (hp|hi)|hp
          · exact children t (by simp [hp])
          · exact innerValid t hi
          · exact children t (by simp [hp])
        · simp only [profile,profiles_append,profiles,Profile.plus,List.length_append,List.length_cons,
            ite_true,List.append_assoc]
          congr 1 <;> omega

private def sourceProfile (c : Codec sig) (t : Term sig) : Profile := ⟨fixed t,t.variables.map c.vars.put⟩

private theorem source_profile (c : Codec sig) (t : Term sig) {raw} (rep : Layout (WholeProblem.encode c t) raw) :
    profile raw = sourceProfile c t := by
  rw [←(layout_profile rep (valid_encode c t)).2]
  obtain ⟨vars,len⟩ := encoded c t
  cases h : profile (WholeProblem.encode c t) with
  | mk base ids =>
    rw [h] at vars len
    change ids = t.variables.map c.vars.put at vars
    change base + ids.length = nodes t at len
    have size := congrArg List.length vars
    simp only [List.length_map] at size
    simp only [sourceProfile,Profile.mk.injEq,fixed]
    exact ⟨by omega,vars⟩

private theorem source_system (c : Codec sig) (p : Problem sig) {raw}
    (rep : WholeProblem.RowLayout (encodeRows c p) raw) :
    system raw = p.map (fun e => (sourceProfile c e.lhs,sourceProfile c e.rhs)) := by
  induction p generalizing raw with
  | nil => cases rep; rfl
  | cons e es ih =>
    cases rep with
    | cons l r tail =>
      simp only [system,List.map_cons,source_profile c e.lhs l,source_profile c e.rhs r,List.cons.injEq,
        true_and]
      exact ih tail

private theorem read_keys (c : Codec sig) (p : Problem sig) :
    keys (p.map fun e => (sourceProfile c e.lhs,sourceProfile c e.rhs)) = sourceKeys c p := by
  simp [keys,sourceKeys,List.flatMap_map,sourceProfile]

private theorem source_rows (c : Codec sig) (p : Problem sig) :
    (p.map (fun e => (sourceProfile c e.lhs,sourceProfile c e.rhs))).map (row (sourceKeys c p)) =
      sourceRows c p := by
  simp [sourceRows,row,weights,sourceWeights,sourceProfile,List.map_map,Function.comp_def]

private def imageSize (c : Codec sig) (σ : Substitution sig) (id : UInt64) : Nat :=
  ((c.vars.get id).map fun v => nodes (σ.image v)).getD 1

private theorem variable_live (c : Codec sig) (t : Term sig) (live : Live c t) (v : Variable)
    (occurs : v ∈ t.variables) : c.vars.get (c.vars.put v) = some v := by
  rw [Term.mem_variables] at occurs
  induction t with
  | var w => cases occurs; exact live
  | atom => contradiction
  | free f args ih => obtain ⟨i,inside⟩ := occurs; exact ih i (live.2 i) inside
  | comm _ _ _ ia ib | ac _ _ _ ia ib => rcases occurs with a|b; exact ia live.2.1 a; exact ib live.2.2 b

private theorem nodes_positive (t : Term sig) : 0 < nodes t := by
  cases t with
  | var | atom => exact Nat.zero_lt_one
  | free | ac | comm => exact Nat.zero_lt_succ _

private theorem image_sum (σ : Substitution sig) (vs : List Variable) :
    (vs.map (fun v => nodes (σ.image v))).sum =
      (vs.map (fun v => nodes (σ.image v)-1)).sum + vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have := nodes_positive (σ.image v)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

private theorem eval_side (c : Codec sig) (σ : Substitution sig) (ks : List UInt64) (t : Term sig)
    (good : Live c t) (nd : ks.Nodup) (covered : (t.variables.map c.vars.put) ⊆ ks) :
    dot (sourceWeights c ks t) (prepend 1 (fun i => imageSize c σ (ks.get i))) = nodes (σ.apply t) := by
  have exactWeights := count_weight ks (t.variables.map c.vars.put) (imageSize c σ) nd covered
  have replace : (t.variables.map (fun v => imageSize c σ (c.vars.put v))) =
      t.variables.map (fun v => nodes (σ.image v)) := List.map_congr_left fun v hv => by
    simp [imageSize,variable_live c t good v hv]
  have count := (encoded c t).2
  change _ + (profile (WholeProblem.encode c t)).vars.length = nodes t at count
  rw [(encoded c t).1,List.length_map] at count
  have split (a : Nat) (v x : Vec ks.length) : dot (prepend a v) (prepend 1 x) = a + dot v x := by
    simp [dot,total,List.ofFn_succ,prepend]
  rw [sourceWeights,split,exactWeights,List.map_map,Function.comp_def,replace,image_sum,UnifierSize.substituted]
  unfold fixed
  omega

private theorem source_feasible (c : Codec sig) (p : Problem sig) (faithful : Faithful c p)
    (σ : Substitution sig) (sol : p.Solves σ) : Feasible (sourceRows c p) := by
  let ks := sourceKeys c p
  let x := prepend 1 (fun i : Fin ks.length => imageSize c σ (ks.get i))
  refine ⟨x,?_,?_⟩
  · intro row mem
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp mem
    have used : (e.lhs.variables.map c.vars.put ++ e.rhs.variables.map c.vars.put) ⊆ ks := by
      intro w hw
      exact List.mem_eraseDups.mpr (List.mem_flatMap.mpr ⟨e,he,hw⟩)
    have nd : ks.Nodup := by exact Matching.ACBagSearch.dedup_distinct _
    rw [Row.ofWeights_holds]
    exact (eval_side c σ ks e.lhs (faithful e he).1 nd (fun _ h => used (List.mem_append_left _ h))).trans
      ((nodes_equiv (sol e he)).trans
        (eval_side c σ ks e.rhs (faithful e he).2 nd (fun _ h => used (List.mem_append_right _ h))).symm)
  · intro k
    cases k using Fin.cases with
    | zero => exact Nat.zero_lt_one
    | succ i =>
      change 0 < imageSize c σ (ks.get i)
      unfold imageSize
      cases c.vars.get (ks.get i) with
      | none => exact Nat.zero_lt_one
      | some v => exact nodes_positive _

/-- Even when the graph reuses nodes or flattens individual AC subtrees,
the checked negative verdict concerns exactly the source equation sizes. -/
theorem decoded_iff (c : Codec sig) (p : Problem sig) {ns es raw}
    (representation : RowLayout (encodeRows c p) raw) :
    refutesDecoded ns es raw = true ↔ GraphWithin ns es ∧
      p.length ≤ 64 ∧ (sourceKeys c p).length + 1 ≤ 4096 ∧
      p.length * ((sourceKeys c p).length + 1) ≤ 8192 ∧ checkRows (sourceRows c p) = some false := by
  let src := p.map (fun e => (sourceProfile c e.lhs,sourceProfile c e.rhs))
  let test (s : List (Profile × Profile)) := checkRows (s.map (row (keys s)))
  have numeric : test (system raw) = checkRows (sourceRows c p) := calc
    test (system raw) = test src := congrArg test (source_system c p representation)
    _ = checkRows (src.map (row (sourceKeys c p))) :=
      congrArg (fun ks => checkRows (src.map (row ks))) (read_keys c p)
    _ = _ := congrArg checkRows (source_rows c p)
  have result := refutesDecoded_iff ns es raw
  change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ test (system raw) = some false at result
  rw [numeric] at result
  simpa only [source_system c p representation,read_keys,List.length_map] using result

theorem refutesDecoded_unsatisfiable (c : Codec sig) (p : Problem sig) {ns es raw}
    (represented : CheckedFactoring.Rows c p raw) (accepted : refutesDecoded ns es raw = true) :
    ¬ p.Satisfiable := by
  obtain ⟨_,_,_,_,negative⟩ := (decoded_iff c p represented.layout).mp accepted
  rintro ⟨σ,sol⟩
  exact Bool.noConfusion ((checkedRows _ _ negative).mpr (source_feasible c p represented.faithful σ sol))

theorem refutes_unsatisfiable (c : Codec sig) (p : Problem sig) {ds ns es raw}
    (decoded : Wire.decodeProblem ds ns es = some raw) (represented : CheckedFactoring.Rows c p raw)
    (accepted : refutes ds ns es = true) : ¬ p.Satisfiable := by
  obtain ⟨_,_,read,no⟩ := (refutes_iff ..).mp accepted
  cases decoded.symm.trans read
  exact refutesDecoded_unsatisfiable c p represented no

/-- Mandatory refutations use syntax counts on the original mathematical
terms and a certified numeric input domain. Their definition contains no
candidate graph preflight, profile traversal, or numeric verdict. -/
def Required (c : Codec sig) (p : Problem sig) (ns : Array (Array UInt64)) (es : Array UInt64) : Prop :=
  GraphWithin ns es ∧ p.length ≤ 64 ∧ (sourceKeys c p).length + 1 ≤ 4096 ∧
  p.length * ((sourceKeys c p).length + 1) ≤ 8192 ∧
  ACFeasibility.Required (sourceRows c p) ∧ ¬ Feasible (sourceRows c p)

theorem refutesDecoded_required (c : Codec sig) (p : Problem sig) {ns es raw}
    (represented : RowLayout (encodeRows c p) raw) (required : Required c p ns es) :
    refutesDecoded ns es raw = true := by
  obtain ⟨graph,rows,keys,cells,domain,impossible⟩ := required
  obtain ⟨b,returned⟩ := Option.isSome_iff_exists.mp (checkedRows_complete domain)
  have negative : b = false := by
    cases b with
    | false => rfl
    | true => exact False.elim (impossible ((checkedRows _ _ returned).mp rfl))
  exact (decoded_iff c p represented).mpr ⟨graph,rows,keys,cells,negative ▸ returned⟩

theorem refutes_required (c : Codec sig) (p : Problem sig) {ds ns es raw}
    (decoded : Wire.decodeProblem ds ns es = some raw) (represented : RowLayout (encodeRows c p) raw)
    (room : ds.size ≤ 32768) (required : Required c p ns es) : refutes ds ns es = true :=
  (refutes_iff ..).mpr ⟨room,raw,decoded,refutesDecoded_required c p represented required⟩

end Tamarin.MixedSizeGraph
