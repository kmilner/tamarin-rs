import TamarinRuntime.ForcedOperandClasses
import Tamarin.ACForcedCoordinates
import Tamarin.ACForcedEquations
import Tamarin.OperandBatch

namespace Tamarin.ForcedOperandClasses
open ACBasis

/-- Equalities are about occurrence counts in the original alternating
rows, independent of any histogram or numeric search implementation. -/
def original (w : UInt64) : List (Array UInt64) → List (Row w.toNat)
  | l :: r :: rest => Row.ofWeights (fun i => l.toList.count i.val.toUInt64)
      (fun i => r.toList.count i.val.toUInt64) :: original w rest
  | _ => []

def SideValid (w : UInt64) (side : Array UInt64) : Prop :=
  0 < side.size ∧ side.size < UInt64.size ∧ ∀ k ∈ side, k < w

def Packet (w : UInt64) (sides : Array (Array UInt64)) : Prop :=
  sides.size % 2 = 0 ∧ ∀ side ∈ sides, SideValid w side

def Labels (w : UInt64) (out : Array UInt64) : Prop := out.size = w.toNat ∧ ∀ k ∈ out, k < w

/-- A nonzero multiple of the difference of the two coordinate units
is an integer combination of the original rows. This fixes the completion
floor even if the executable changes its pair queries or class labels. -/
def InSpan {n : Nat} (rs : List (Row n)) (i j : Fin n) : Prop :=
  ∃ d : Int, ∃ ws : List Int, d ≠ 0 ∧ ws.length = rs.length ∧ ∀ k : Fin n,
    d * ((if k = i then 1 else 0) - (if k = j then 1 else 0)) =
      ((ws.zip rs).map fun (w,r) => w * ((r.pos k : Int) - r.neg k)).sum

private theorem valid_of_span {n : Nat} (rs : List (Row n)) (i j : Fin n) (h : InSpan rs i j) :
    ∃ c, SpanCertificate.Valid rs (ForcedCoordinates.equation i j) c := by
  obtain ⟨d,ws,nonzero,len,eq⟩ := h
  refine ⟨⟨d,ws⟩,nonzero,len,fun k => ?_⟩
  have unit : ACFeasibility.LowRank.coeff (ForcedCoordinates.equation i j) k =
      ((if k = i then 1 else 0) - (if k = j then 1 else 0) : Int) := by
    simp only [ACFeasibility.LowRank.coeff,ForcedCoordinates.equation,Row.ofWeights,spike]
    split <;> split <;> decide
  rw [unit]
  exact eq k

def Correct (candidate : Kernel) : Prop :=
  (∀ w sides out, candidate w sides = some out → Packet w sides ∧ Labels w out ∧
    ∀ i j : Fin w.toNat, out[i.val]! = out[j.val]! → ∀ x : Vec w.toNat,
      (∀ r ∈ original w sides.toList, r.Holds x) → x i = x j) ∧
  (∀ w sides, Packet w sides → ForcedCoordinates.Within (original w sides.toList) →
    ∃ out, candidate w sides = some out ∧ ∀ i j : Fin w.toNat,
      InSpan (original w sides.toList) i j →
        out[i.val]! = out[j.val]!)

private theorem original_length (w : UInt64) (ss : List (Array UInt64)) :
    (original w ss).length = ss.length / 2 := by
  match ss with
  | [] | [_] => simp [original]
  | _::_::tail =>
    simp only [original,List.length_cons,original_length w tail]
    omega

private theorem histogram_at (w : UInt64) (a : Array UInt64) (ok : SideValid w a) (i : Fin w.toNat) :
    (GraphMatrix.histogram w a)[i.val]!.toNat = a.toList.count i.val.toUInt64 := by
  have lim : a.toList.count i.val.toUInt64 < 2^64 := Nat.lt_of_le_of_lt List.count_le_length ok.2.1
  rw [GraphMatrix.histogram_counts]
  have value : (GraphMatrix.counts w a.toList)[i.val]! = (a.toList.count i.val.toUInt64).toUInt64 := by
    simp [GraphMatrix.counts,getElem!_pos]
  exact value ▸ UInt64.toNat_ofNat_of_lt' lim

private theorem positive (w : UInt64) (a : Array UInt64) (ok : SideValid w a) :
    (GraphMatrix.histogram w a).any (· > 0) = true := by
  let k := a[0]'ok.1
  have mem : k ∈ a := Array.getElem_mem ok.1
  let i : Fin w.toNat := ⟨k.toNat,ok.2.2 _ mem⟩
  have pos : 0 < a.toList.count i.val.toUInt64 := List.count_pos_iff.mpr (by simpa [i] using mem)
  have h := histogram_at w a ok i
  have size : (GraphMatrix.histogram w a).size = w.toNat := by simp [GraphMatrix.histogram_counts,GraphMatrix.counts]
  apply Array.any_eq_true.mpr
  refine ⟨i.val,by simp [size],?_⟩
  simpa [UInt64.lt_iff_toNat_lt,getElem!_pos,show i.val < (GraphMatrix.histogram w a).size by simp [size]]
    using (show 0 < (GraphMatrix.histogram w a)[i.val]!.toNat from h ▸ pos)

private theorem read (w : UInt64) (ss : List (Array UInt64)) (even : ss.length % 2 = 0)
    (ok : ∀ a ∈ ss, SideValid w a) :
    Homogeneous.readRows w.toNat (ss.map (GraphMatrix.histogram w)) = some (original w ss) := by
  match ss with
  | [] => rfl
  | [_] => cases even
  | a::b::tail =>
    have l := ok a List.mem_cons_self
    have r := ok b (by simp)
    have rest := read w tail (by simp only [List.length_cons] at even; omega)
      (fun s hs => ok s (by simp [hs]))
    have size (s : Array UInt64) : (GraphMatrix.histogram w s).size = w.toNat := by
      simp [GraphMatrix.histogram_counts,GraphMatrix.counts]
    simp only [original,List.map_cons,Homogeneous.readRows,positive w a l,positive w b r]
    simp only [size,BEq.rfl,Bool.and_self,rest,histogram_at w a l,histogram_at w b r]
    rfl

private theorem guarded (w : UInt64) (ss : Array (Array UInt64)) :
    (SpanCertificate.dimensions w.toNat (ss.size/2) && ss.size % 2 == 0 &&
      ss.all (fun a => 0 < a.size && a.size < UInt64.size && a.all (· < w))) = true ↔
      SpanCertificate.dimensions w.toNat (ss.size/2) = true ∧ Packet w ss := by
  simp only [Bool.and_eq_true,beq_iff_eq,Array.all_eq_true_iff_forall_mem,decide_eq_true_eq,Packet,SideValid,and_assoc]

private theorem wire (w : UInt64) (ss : Array (Array UInt64)) (out : Array UInt64) :
    run w ss = some out ↔ SpanCertificate.dimensions w.toNat (ss.size/2) = true ∧ Packet w ss ∧
      ∃ v, ForcedCoordinates.run (original w ss.toList) = some v ∧ out = v.toArray.map Nat.toUInt64 := by
  unfold run
  cases h : (SpanCertificate.dimensions w.toNat (ss.size/2) && ss.size % 2 == 0 &&
      ss.all (fun a => 0 < a.size && a.size < UInt64.size && a.all (· < w))) with
  | false =>
    constructor
    · intro bad; cases bad
    · rintro ⟨dims,p,_⟩
      exact False.elim (Bool.noConfusion (h.symm.trans ((guarded ..).mpr ⟨dims,p⟩)))
  | true =>
    obtain ⟨dims,valid⟩ := (guarded ..).mp h
    have decode := read w ss.toList valid.1 (by simpa using valid.2)
    simp only [Array.toList_map,decode,guard,Option.bind_eq_bind,Option.bind_some,pure,
      dims,valid,true_and]
    cases ForcedCoordinates.run (original w ss.toList) <;> simp [eq_comm]

theorem run_correct : Correct run := by
  constructor
  · intro w sides out got
    obtain ⟨_,packet,v,returned,rfl⟩ := (wire ..).mp got
    have bound (i : Fin w.toNat) : v[i] < w.toNat := ForcedCoordinates.run_labels_lt returned i
    have get (i : Fin w.toNat) : (v.toArray.map Nat.toUInt64)[i.val]! = v[i].toUInt64 := by
      simp [getElem!_pos]
    refine ⟨packet,⟨by simp,?_⟩,?_⟩
    · intro k hk
      obtain ⟨a,ha,rfl⟩ := Array.mem_map.mp hk
      obtain ⟨i,hi,rfl⟩ := Array.getElem_of_mem ha
      have lt := bound ⟨i,by simpa using hi⟩
      change v.toArray[i].toUInt64.toNat < w.toNat
      have size : v.toArray[i] < UInt64.size := Nat.lt_trans lt w.toNat_lt_size
      calc
        _ = v.toArray[i] := UInt64.toNat_ofNat_of_lt' size
        _ < w.toNat := lt
    · intro i j eq
      rw [get,get] at eq
      have exactNat (k : Fin w.toNat) := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (bound k) w.toNat_lt_size)
      exact ForcedCoordinates.run_correct.sound _ v returned i j
        ((exactNat i).symm.trans ((congrArg UInt64.toNat eq).trans (exactNat j)))
  · intro w sides packet within
    have dims : SpanCertificate.dimensions w.toNat (sides.size/2) = true := by
      obtain ⟨n,m,work,_⟩ := within
      simpa [SpanCertificate.dimensions,original_length] using And.intro n (And.intro m work)
    obtain ⟨v,returned,all⟩ := ForcedCoordinates.run_correct.complete _ within
    refine ⟨_,(wire ..).mpr ⟨dims,packet,v,returned,rfl⟩,?_⟩
    intro i j certificate
    simpa [getElem!_pos] using congrArg Nat.toUInt64 (all i j (valid_of_span _ i j certificate))

private def asRow {n} (pair : OperandBatch.Row n) : ACRowElimination.Row (Fin n) :=
  ⟨pair.1.ids,pair.2.ids⟩

private theorem side_count {w : UInt64} (s : OperandBatch.Side w.toNat) (i : Fin w.toNat) :
    s.words.toList.count i.val.toUInt64 = s.ids.count i := by
  have inj (j : Fin w.toNat) : j.val.toUInt64 = i.val.toUInt64 ↔ j = i := by
    constructor
    · intro same
      apply Fin.ext
      have read (k : Fin w.toNat) : k.val.toUInt64.toNat = k.val :=
        UInt64.toNat_ofNat_of_lt' (Nat.lt_trans k.isLt w.toNat_lt_size)
      exact (read j).symm.trans ((congrArg UInt64.toNat same).trans (read i))
    · rintro rfl; rfl
  unfold OperandBatch.Side.words
  induction s.ids with
  | nil => rfl
  | cons x xs ih => simp [List.count_cons,beq_iff_eq,inj,ih]

private theorem rows_exact {w : UInt64} (batch : List (OperandBatch.Row w.toNat)) :
    original w (OperandBatch.sides batch).toList = (batch.map asRow).map ACLinearConsequence.incidence := by
  induction batch with
  | nil => rfl
  | cons pair tail ih =>
    rcases pair with ⟨l,r⟩
    change Row.ofWeights _ _ :: original w (OperandBatch.sides tail).toList = _ :: _
    rw [ih]
    exact congrArg (· :: _) (congr (congrArg Row.ofWeights (funext (side_count l))) (funext (side_count r)))

private theorem row_sources {sig : Signature} [DecidableEq sig.ACSym] {n : Nat}
    {f : sig.ACSym} {term : Fin n → Term sig} {batch selected}
    (layout : OperandBatch.Represents f term batch selected) :
    ∀ r ∈ batch.map asRow, ∃ e ∈ selected, ACRowElimination.Represents r f term e := by
  have side (s : OperandBatch.Side n) (t : Term sig) (h : s.Represents f term t) :
      ∃ u, ACRepresentation.decode f (s.ids.map term) = some u ∧ EquivB t u := by
    obtain ⟨v,hv,eq⟩ := ACRepresentation.flatten_correct f t
    exact ⟨_,rfl,((ACRepresentation.decode_perm f h _ _ rfl hv).trans eq).symm⟩
  induction layout with
  | nil => simp
  | @cons l r e rs es left right _ ih =>
    intro row mem
    rcases List.mem_cons.mp mem with rfl|rest
    · exact ⟨e,List.mem_cons_self,side l _ left,side r _ right⟩
    · obtain ⟨e,member,rep⟩ := ih row rest
      exact ⟨e,List.mem_cons_of_mem _ member,rep⟩

/-- Equal labels permit retaining an equality between the actual caller
operands. Both columns must be present in the encoded selection; unselected
equations and variables of the original problem remain in scope. -/
def Source (candidate : Kernel) : Prop :=
  ∀ {sig : Signature} [DecidableEq sig.ACSym] (f : sig.ACSym) {w : UInt64} (term : Fin w.toNat → Term sig)
    (batch : List (OperandBatch.Row w.toNat)) (selected p : Problem sig),
    OperandBatch.Represents f term batch selected → selected ⊆ p →
    ∀ out, candidate w (OperandBatch.sides batch) = some out → ∀ i j : Fin w.toNat,
    i ∈ OperandBatch.used batch → j ∈ OperandBatch.used batch → out[i.val]! = out[j.val]! →
    ACForcedEquations.Forced p [⟨term i,term j⟩]

theorem source_of_correct {candidate : Kernel} (correct : Correct candidate) : Source candidate := by
  intro sig _ f w term batch selected p represented part out returned i j usedI usedJ same
  apply ACForcedEquations.forced_pair_of_holds f term p (batch.map asRow)
    (fun r hr => by
      obtain ⟨e,he,rep⟩ := row_sources represented r hr
      exact ⟨e,part he,rep⟩) i j
  · intro k member
    have used : k ∈ OperandBatch.used batch := by
      rcases List.mem_cons.mp member with rfl|rest
      · exact usedI
      · obtain rfl := List.mem_singleton.mp rest; exact usedJ
    obtain ⟨pair,hp,hk⟩ := List.mem_flatMap.mp used
    exact ⟨asRow pair,List.mem_map_of_mem hp,hk⟩
  · simpa only [rows_exact] using (correct.1 w _ out returned).2.2 i j same

end Tamarin.ForcedOperandClasses
