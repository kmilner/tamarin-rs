import TamarinRuntime.MaskedOperands
import Tamarin.IndivisibleOperands

namespace Tamarin.MaskedOperands
open ACBasis Homogeneous
variable {n : Nat} {α : Type}

private theorem mask_bit (mask : Mask n) (i : Fin n) :
    (maskBits mask).getLsbD i = mask i := by
  simp only [maskBits,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left i.isLt,Option.getD_some]

private theorem apart_iff (m : Mask n) (seen : BitVec n) (v : Vec n) :
    seen &&& Coverage.support v &&& maskBits m = 0 ↔
    ∀ i : Fin n, m i = true → seen.getLsbD i = true → v i = 0 := by
  constructor
  · intro h i mark hit
    have bit := congrArg (fun b : BitVec n => b.getLsbD i) h
    rw [show (0 : BitVec n).getLsbD i = false by simp] at bit
    simp only [BitVec.getLsbD_and,mask_bit,Coverage.support_bit,hit,mark] at bit
    simp at bit
    omega
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let j : Fin n := ⟨i,hi⟩
    change (seen &&& Coverage.support v &&& maskBits m).getLsbD j = _
    simp only [BitVec.getLsbD_and,mask_bit,Coverage.support_bit ]
    cases mark : m j <;> cases hit : seen.getLsbD j <;> simp [*]

private def allowed (get : α → Vec n) (m : Mask n) (seen : BitVec n) (xs : List α) :=
  decide (∀ i : Fin n, m i = true →
    (if seen.getLsbD i then 1 else 0) + (xs.map (fun j => get j i)).sum ≤ 1)

private theorem allowed_nil (get : α → Vec n) (m : Mask n) (seen : BitVec n) :
    allowed get m seen [] = true := by
  simp [allowed]; intro i _; split <;> decide

private theorem allowed_cons (get : α → Vec n) (m : Mask n) (seen : BitVec n) (x : α) (xs : List α) :
    allowed get m seen (x::xs) = true ↔
      (usable m (get x) = true ∧ seen &&& Coverage.support (get x) &&& maskBits m = 0) ∧
      allowed get m (seen ||| Coverage.support (get x)) xs = true := by
  simp only [allowed,usable,decide_eq_true_eq,apart_iff,List.map_cons,List.sum_cons,
    BitVec.getLsbD_or,Coverage.support_bit]
  constructor
  · intro h
    refine ⟨⟨fun i mark => ?_,fun i mark hit => ?_⟩,fun i mark => ?_⟩
    · have hi := h i mark; split at hi <;> omega
    · have hi := h i mark; simp [hit] at hi; omega
    · have hi := h i mark
      cases hit : seen.getLsbD i <;> by_cases live : 0 < get x i <;> simp [hit,live] at hi ⊢ <;> omega
  · rintro ⟨⟨small,apart⟩,tail⟩ i mark
    have step := small i mark
    have last := tail i mark
    have off := apart i mark
    cases hit : seen.getLsbD i <;> by_cases live : 0 < get x i <;> simp [hit,live] at last off ⊢ <;> omega

private theorem found {get : α → Vec n} (m : Mask n) (weight : α → Nat) (full : BitVec n)
    (items : List α) (seen : BitVec n) (cost credit left : Nat) (js : List (List α))
    (result : collect (fun x => usable m (get x)) weight (maskBits m) full
      (Coverage.prepare (fun x => Coverage.support (get x)) items) seen cost credit = some (left,js)) :
    js = (Coverage.enumerate full (Coverage.prepare (fun x => Coverage.support (get x)) items) seen).filter
      (allowed get m seen) := by
  induction items generalizing seen cost credit left js with
  | nil =>
    by_cases h : seen = full <;>
      simp [Coverage.prepare,collect,Coverage.enumerate,h,allowed_nil,Option.bind_eq_some_iff] at result ⊢ <;>
      grind
  | cons x xs ih =>
    let v := Coverage.support (get x)
    let tail := Coverage.prepare (fun x => Coverage.support (get x)) xs
    change (do
      let c ← spend credit 1
      if seen ||| (v ||| tail.available) ≠ full then pure (c,[]) else
        let (d,skip) ← collect _ weight (maskBits m) full tail seen cost c
        if !usable m (get x) || seen &&& v &&& maskBits m != 0 then pure (d,skip) else
          let (e,take) ← collect _ weight (maskBits m) full tail (seen ||| v) (cost+weight x) d
          pure (e,skip ++ take.map (x :: ·))) = _ at result
    obtain ⟨c,_,result⟩ := Option.bind_eq_some_iff.mp result
    by_cases live : seen ||| (v ||| tail.available) = full
    · simp only [live,ne_eq,not_true_eq_false,ite_false] at result
      obtain ⟨⟨d,skip⟩,hs,result⟩ := Option.bind_eq_some_iff.mp result
      obtain rfl := ih _ _ _ _ _ hs
      change _ = (if seen ||| (v ||| tail.available) = full then
        Coverage.enumerate full tail seen ++ (Coverage.enumerate full tail (seen ||| v)).map (x :: ·) else []).filter _
      simp only [live,ite_true,List.filter_append,List.filter_map]
      by_cases safe : usable m (get x) = true ∧ seen &&& v &&& maskBits m = 0
      · have take : (!usable m (get x) || seen &&& v &&& maskBits m != 0) = false := by simp [safe.1,safe.2]
        simp only [take,Bool.false_eq_true,ite_false] at result
        obtain ⟨⟨e,ts⟩,ht,out⟩ := Option.bind_eq_some_iff.mp result
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj out)
        rw [ih _ _ _ _ _ ht]
        congr 2
        apply List.filter_congr; intro ys _
        apply Bool.eq_iff_iff.mpr
        exact ((allowed_cons get m seen x ys).trans (and_iff_right safe)).symm
      · have skipOnly : (!usable m (get x) || seen &&& v &&& maskBits m != 0) = true := by
          simpa only [Bool.or_eq_true,Bool.not_eq_true',bne_iff_ne] using (by grind : usable m (get x) = false ∨ seen &&& v &&& maskBits m ≠ 0)
        simp only [skipOnly,ite_true] at result
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj result)
        have empty : ((Coverage.enumerate full tail (seen ||| v)).filter
            (fun ys => allowed get m seen (x::ys))) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro ys _
          exact fun h => safe ((allowed_cons get m seen x ys).mp h).1
        simp only [Function.comp_def,empty,List.map_nil,List.append_nil]
        rfl
    · simp [live] at result
      change js = (if seen ||| (v ||| tail.available) = full then _ else []).filter _
      simp [live,result]

private theorem accepted_cover (gs : List (Vec n)) (m : Mask n) (js : List (Fin gs.length))
    (mem : js ∈ coveringSelections gs) :
    allowed gs.get m 0 js = IndivisibleOperands.keeps m (arm gs js) := by
  rw [Coverage.coveringSelections_eq,selections] at mem
  have cover : ∀ i, ∃ j ∈ js, 0 < gs.get j i := by simpa [covers] using (List.mem_filter.mp mem).2
  apply Bool.eq_iff_iff.mpr
  rw [IndivisibleOperands.selection_iff]
  simp only [allowed,decide_eq_true_eq]
  constructor
  · intro h i hi
    obtain ⟨j,hj,pos⟩ := cover i
    have inc : 0 < (js.map (fun j => gs.get j i)).sum :=
      List.sum_pos_iff_exists_pos_nat.mpr ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,pos⟩
    have upper := h i hi
    rw [show (0 : BitVec n).getLsbD i = false by simp] at upper
    simp only [Bool.false_eq_true,ite_false,Nat.zero_add] at upper
    omega
  · intro h i hi
    rw [show (0 : BitVec n).getLsbD i = false by simp,h i hi]; decide

/-- Successful searches retain precisely the ordered covering selections
whose projected word counts are one on every marked column. -/
theorem takeSelections_eq (gs : List (Vec n)) (m : Mask n) {credit left js}
    (done : takeSelections gs m credit = some (left,js)) :
    js = (coveringSelections gs).filter (fun sel => IndivisibleOperands.keeps m (arm gs sel)) := by
  have h := found m (fun j => total (gs.get j)) _ (List.finRange gs.length) 0 (1+2*n) credit left js
    (get := gs.get) (by simpa [takeSelections] using done)
  exact h.trans (List.filter_congr (accepted_cover gs m))

/-- Independent of credit: the pair records the number of visited prefixes
and the choices that reach a full, admissible leaf. -/
private def trace (allow : α → Bool) (mask full : BitVec n) : Coverage.Plan α n → BitVec n →
    Nat × List (List α)
  | .done, seen => (1, if seen = full then [[]] else [])
  | .step x support suffix tail, seen =>
    if seen ||| suffix = full then
      let skip := trace allow mask full tail seen
      if allow x && seen &&& support &&& mask == 0 then
        let take := trace allow mask full tail (seen ||| support)
        (1 + skip.1 + take.1, skip.2 ++ take.2.map (x :: ·))
      else (1 + skip.1,skip.2)
    else (1,[])

private def words (weight : α → Nat) (cost : Nat) (ys : List (List α)) : Nat :=
  (ys.map (fun s => cost + (s.map weight).sum)).sum

private theorem words_split (w : α → Nat) (c : Nat) (x : α) (skip take : List (List α)) :
    words w c (skip ++ take.map (x :: ·)) = words w c skip + words w (c+w x) take := by
  simp [words,List.map_map,Function.comp_def,Nat.add_assoc]

private theorem funded (allow : α → Bool) (weight : α → Nat) (mask full : BitVec n)
    (plan : Coverage.Plan α n) (seen : BitVec n) (cost credit : Nat) :
    let t := trace allow mask full plan seen
    t.1 + words weight cost t.2 ≤ credit →
      collect allow weight mask full plan seen cost credit =
        some (credit - (t.1 + words weight cost t.2), t.2) := by
  induction plan generalizing seen cost credit with
  | done =>
    by_cases live : seen = full
    · simp only [trace,live,ite_true]
      simp only [words,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
      intro h
      simp [collect,spend,show 1 ≤ credit by omega,show cost ≤ credit-1 by omega,Nat.sub_sub]
    · simp only [trace,live,ite_false]
      simp only [words,List.map_nil,List.sum_nil,Nat.add_zero]
      intro h
      simp [collect,live,spend,h]
  | step x sup suffix tail ih =>
    by_cases live : seen ||| suffix = full
    · let s := trace allow mask full tail seen
      let t := trace allow mask full tail (seen ||| sup)
      let a := s.1 + words weight cost s.2
      let b := t.1 + words weight (cost + weight x) t.2
      by_cases ok : allow x = true ∧ seen &&& sup &&& mask = 0
      · have take : (!allow x || seen &&& sup &&& mask != 0) = false := by simp [ok.1,ok.2]
        simp only [trace,live,ite_true,ok.1,ok.2,beq_self_eq_true,Bool.and_self]
        change 1 + s.1 + t.1 + words weight cost (s.2 ++ t.2.map (x :: ·)) ≤ credit → _
        rw [words_split]
        intro h
        have ha : a ≤ credit-1 := by dsimp only [a]; omega
        have hb : b ≤ credit-1-a := by dsimp only [a,b] at *; omega
        have left := ih seen cost (credit-1) ha
        have right := ih (seen ||| sup) (cost+weight x) (credit-1-a) hb
        change collect .. = some (credit - (1+s.1+t.1 + (words weight cost s.2 +
          words weight (cost+weight x) t.2)),s.2 ++ t.2.map (x :: ·))
        simp only [collect,spend,show 1 ≤ credit by omega,ite_true,Option.bind_eq_bind,Option.bind_some,live,ne_eq,
          not_true_eq_false,ite_false,left,take,Bool.false_eq_true]
        change (do
          let (c,ys) ← collect allow weight mask full tail (seen ||| sup) (cost+weight x) (credit-1-a)
          pure (c,s.2 ++ ys.map (x :: ·))) = _
        rw [right]
        have equ : credit-1-a-b = credit - (1+s.1+t.1 + (words weight cost s.2 +
            words weight (cost+weight x) t.2)) := by
          simp only [Nat.sub_sub,a,b]
          congr 1
          omega
        change some (credit-1-a-b,s.2 ++ t.2.map (x :: ·)) = _
        rw [equ]
      · have skip : (!allow x || seen &&& sup &&& mask != 0) = true := by
          simpa only [Bool.or_eq_true,Bool.not_eq_true',bne_iff_ne] using
            (by grind : allow x = false ∨ seen &&& sup &&& mask ≠ 0)
        have blocked : (allow x && seen &&& sup &&& mask == 0) = false := by simpa using ok
        simp only [trace,live,ite_true,blocked,Bool.false_eq_true,ite_false]
        change 1+s.1+words weight cost s.2 ≤ credit → _
        intro h
        have ha : a ≤ credit-1 := by dsimp only [a]; omega
        have left := ih seen cost (credit-1) ha
        simp only [collect,spend,show 1 ≤ credit by omega,ite_true,Option.bind_eq_bind,Option.bind_some,live,ne_eq,
          not_true_eq_false,ite_false,left,skip,Option.pure_def]
        congr 2
        omega
    · simp [trace,live,collect,spend,words]
      grind

private def choices (get : α → Vec n) (m : Mask n) (seen : BitVec n) (items : List α) : Nat :=
  ((FlatMatchSearch.sublists items).filter (allowed get m seen)).length

private theorem choices_pos (get : α → Vec n) (m : Mask n) (seen : BitVec n) (items : List α) :
    0 < choices get m seen items := by
  apply List.length_pos_of_mem (a := [])
  apply List.mem_filter.mpr
  exact ⟨(FlatMatchSearch.mem_sublists _ _).mpr (List.nil_sublist _),allowed_nil ..⟩

private theorem choices_cons (get : α → Vec n) (m : Mask n) (seen : BitVec n) (x : α) (xs : List α) :
    choices get m seen (x::xs) = choices get m seen xs +
      if usable m (get x) && seen &&& Coverage.support (get x) &&& maskBits m == 0 then
        choices get m (seen ||| Coverage.support (get x)) xs else 0 := by
  simp only [choices,FlatMatchSearch.sublists,List.filter_append,List.filter_map,List.length_append,
    List.length_map,Function.comp_def]
  congr 1
  by_cases safe : usable m (get x) = true ∧ seen &&& Coverage.support (get x) &&& maskBits m = 0
  · simp only [safe.1,safe.2,beq_self_eq_true,Bool.and_self,ite_true]
    apply congrArg List.length
    apply List.filter_congr
    intro ys _
    exact Bool.eq_iff_iff.mpr ((allowed_cons get m seen x ys).trans (and_iff_right safe))
  · have off : (usable m (get x) && seen &&& Coverage.support (get x) &&& maskBits m == 0) = false :=
      by simpa using safe
    simp only [off,Bool.false_eq_true,ite_false,List.length_eq_zero_iff]
    apply List.filter_eq_nil_iff.mpr
    intro ys _ h
    exact safe ((allowed_cons get m seen x ys).mp h).1

private theorem visits_le (get : α → Vec n) (m : Mask n) (full : BitVec n)
    (xs : List α) (seen : BitVec n) :
    (trace (fun x => usable m (get x)) (maskBits m) full
      (Coverage.prepare (fun x => Coverage.support (get x)) xs) seen).1 ≤
        (xs.length+1) * choices get m seen xs := by
  induction xs generalizing seen with
  | nil => simp [Coverage.prepare,trace,choices,FlatMatchSearch.sublists,allowed_nil]
  | cons x xs ih =>
    let v := Coverage.support (get x)
    let t := Coverage.prepare (fun x => Coverage.support (get x)) xs
    let visit s := (trace (fun x => usable m (get x)) (maskBits m) full t s).1
    let options s := choices get m s xs
    have lo : visit seen ≤ (xs.length+1) * options seen := ih seen
    have hi : visit (seen ||| v) ≤ (xs.length+1) * options (seen ||| v) := ih _
    have nonempty : 0 < options seen := choices_pos ..
    rw [choices_cons]
    simp only [List.length_cons]
    rw [Nat.add_one_mul,Nat.mul_add]
    by_cases live : seen ||| (v ||| t.available) = full
    · by_cases safe : (usable m (get x) && seen &&& v &&& maskBits m == 0) = true
      · dsimp only [v] at safe
        change (if seen ||| (v ||| t.available) = full then _ else _ : Nat × List (List α)).1 ≤ _
        simp only [live,ite_true,safe]
        change 1 + visit seen + visit (seen ||| v) ≤
          (xs.length+1)*options seen + (xs.length+1)*options (seen ||| v) +
            (options seen + options (seen ||| v))
        omega
      · dsimp only [v] at safe
        have off := Bool.eq_false_iff.mpr safe
        change (if seen ||| (v ||| t.available) = full then _ else _ : Nat × List (List α)).1 ≤ _
        simp only [live,ite_true,off,Bool.false_eq_true,ite_false,Nat.mul_zero,Nat.add_zero]
        change 1 + visit seen ≤ (xs.length+1)*options seen + options seen
        omega
    · change (if seen ||| (v ||| t.available) = full then _ else _ : Nat × List (List α)).1 ≤ _
      simp only [live,ite_false]
      change 1 ≤ (xs.length+1)*options seen + _ + (options seen + _)
      omega

/-- An implementation-independent sufficient budget. A partial choice
cannot exceed a marked column even before all coordinates are covered.
At each depth there are at most as many viable prefixes as these subsets,
since each prefix can omit every remaining item. Output words are charged
only to complete surviving covers. -/
def WorkBound (gs : List (Vec n)) (m : Mask n) : Nat :=
  let subsets := FlatMatchSearch.sublists (List.finRange gs.length)
  let admissible := subsets.filter (fun js => decide (∀ i, m i = true → (js.map fun j => gs.get j i).sum ≤ 1))
  let complete := (selections gs).filter (fun js => IndivisibleOperands.keeps m (arm gs js))
  (gs.length+1)*admissible.length + (complete.map (selectionWords gs)).sum

theorem takeSelections_complete (gs : List (Vec n)) (m : Mask n) {credit : Nat}
    (budget : WorkBound gs m ≤ credit) : (takeSelections gs m credit).isSome := by
  let weight (j : Fin gs.length) := total (gs.get j)
  let indices := List.finRange gs.length
  let plan := Coverage.prepare (fun j => Coverage.support (gs.get j)) indices
  let t := trace (fun j => usable m (gs.get j)) (maskBits m) (BitVec.allOnes n) plan 0
  let need := t.1 + words weight (1+2*n) t.2
  have funded_at {b : Nat} (ok : need ≤ b) : takeSelections gs m b = some (b-need,t.2) := by
    simpa [takeSelections,indices,plan,weight,t,need] using
      funded (fun j => usable m (gs.get j)) weight (maskBits m) (BitVec.allOnes n) plan 0 (1+2*n) b ok
  have answers := takeSelections_eq gs m (funded_at (Nat.le_refl need))
  rw [Coverage.coveringSelections_eq] at answers
  have nodes : t.1 ≤ (gs.length+1) * choices gs.get m 0 indices := by
    simpa [t,plan,indices] using visits_le gs.get m (BitVec.allOnes n) indices 0
  have admit : allowed gs.get m 0 = fun js => decide (∀ i, m i = true → (js.map fun j => gs.get j i).sum ≤ 1) := by
    funext js
    simp [allowed]
  have cap : need ≤ WorkBound gs m := by
    unfold WorkBound
    dsimp only [need]
    rw [answers]
    apply Nat.add_le_add _ (Nat.le_refl _)
    simpa only [choices,admit,indices] using nodes
  rw [funded_at (Nat.le_trans cap budget)]
  rfl

end Tamarin.MaskedOperands
