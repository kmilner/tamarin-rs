import Tamarin.OpenMatchSelect
import Tamarin.AtomicACPair
import Tamarin.MatchingConjunction

/-! Directional matching of AC products with open factors under rigid heads.
A selector names subject occurrences, so equal subject terms at different
positions can discharge different pattern factors. -/
namespace Tamarin.OpenMatch
open ACRepresentation Cancellation Matching
variable {sig : Signature}

private noncomputable def images (f : sig.ACSym) (σ : Substitution sig) (xs : List (Term sig)) :=
  xs.flatMap fun x => Cancellation.flatten f (σ.apply x)

private theorem flat_fold (f : sig.ACSym) (σ : Substitution sig) (x : Term sig) (xs : List (Term sig)) :
    Cancellation.flatten f (σ.apply (ACRepresentation.fold f x xs)) = images f σ (x :: xs) := by
  induction xs generalizing x with
  | nil => simp [ACRepresentation.fold, images]
  | cons y ys ih =>
    change Cancellation.flatten f (.ac f (σ.apply x) (σ.apply (ACRepresentation.fold f y ys))) = _
    rw [Cancellation.flatten_ac, ih]
    rfl

theorem subject_flat (f : sig.ACSym) (x : Term sig) (xs : List (Term sig)) :
    Cancellation.flatten f (ACRepresentation.fold f x xs) = (x :: xs).flatMap (Cancellation.flatten f) := by
  simpa [images, Substitution.apply_identity] using flat_fold f (.identity) x xs

theorem factor_of_mem_flatten [DecidableEq sig.ACSym] (f : sig.ACSym) (t : Term sig) :
    ∀ u ∈ ACRepresentation.flatten f t, Cancellation.flatten f u = [Cancellation.classOf u] := by
  induction t with
  | var | atom | free | comm => simp [ACRepresentation.flatten,Cancellation.flatten]
  | ac g a b ia ib =>
    by_cases same : f = g
    · simpa [ACRepresentation.flatten,same] using fun u (h : u ∈ ACRepresentation.flatten f a ∨
          u ∈ ACRepresentation.flatten f b) => h.elim (ia u) (ib u)
    · simp [ACRepresentation.flatten,Cancellation.flatten,same]

private theorem flat_nonempty (f : sig.ACSym) (t : Term sig) : Cancellation.flatten f t ≠ [] := by
  intro he
  have eq := Cancellation.fold_flatten f t
  rw [he] at eq
  cases eq

/-- An empty remainder discharges an empty pattern. Exactly one empty side
rejects the branch: AC products have no unit. -/
def residual (f : sig.ACSym) (left right : List (Term sig)) : Option (Problem sig) :=
  match decode f left, decode f right with
  | none, none => some []
  | some p, some s => some [⟨p,s⟩]
  | _, _ => none

def Holds (f : sig.ACSym) (left right : List (Term sig)) (σ : Substitution sig) : Prop :=
  ∃ q, residual f left right = some q ∧ Matches q σ

theorem holds_iff (f : sig.ACSym) (l r : List (Term sig)) (σ : Substitution sig) :
    Holds f l r σ ↔ (l.flatMap fun t => Cancellation.flatten f (σ.apply t)).Perm
      (r.flatMap (Cancellation.flatten f)) := by
  cases l with
  | nil =>
    cases r with
    | nil => simp [Holds,residual,decode,Matches]
    | cons y ys =>
      simp only [Holds,residual,decode,reduceCtorEq,false_and,exists_false,List.flatMap_nil,
        false_iff]
      intro h
      have := List.flatMap_eq_nil_iff.mp h.symm.eq_nil y (by simp)
      exact flat_nonempty f y this
  | cons x xs =>
    cases r with
    | nil =>
      simp only [Holds,residual,decode,reduceCtorEq,false_and,exists_false,List.flatMap_nil,
        false_iff]
      intro h
      exact flat_nonempty f (σ.apply x) (List.flatMap_eq_nil_iff.mp h.eq_nil x (by simp))
    | cons y ys =>
      simp only [Holds,residual,decode,Option.some.injEq,exists_eq_left',Matches,
        List.mem_singleton, forall_eq]
      rw [← subject_flat]
      change EquivB _ _ ↔ (images ..).Perm _
      rw [← flat_fold]
      exact ⟨Cancellation.flatten_equiv f, Cancellation.equiv_of_flatten_perm f⟩

/-- Interpret one selector row. Its prefix of positions chooses an ordinary
pattern/subject equation for each distinguished factor. Its suffix supplies the
subject factors of one remaining AC matching problem. -/
def branch (f : sig.ACSym) (loose : List (Term sig)) (subject : Nat → Term sig) :
    List (Term sig) → List Nat → Option (Problem sig)
  | [], is => residual f loose (is.map subject)
  | _ :: _, [] => none
  | p :: ps, i :: is => (branch f loose subject ps is).map (⟨p, subject i⟩ :: ·)

private theorem subject_parts (f : sig.ACSym) (s : Nat → Term sig) (is : List Nat)
    (atomic : ∀ i ∈ is, Cancellation.flatten f (s i) = [classOf (s i)]) :
    (is.map s).flatMap (Cancellation.flatten f) = is.map (fun i => classOf (s i)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.flatMap_cons, atomic i (by simp), List.singleton_append,
      ih (fun j hj => atomic j (List.mem_cons_of_mem _ hj))]

private theorem branch_iff (f : sig.ACSym) (σ : Substitution sig) (s : Nat → Term sig)
    (ps loose : List (Term sig)) (pick rest : List Nat) (len : pick.length = ps.length)
    (atomic : ∀ i ∈ rest, Cancellation.flatten f (s i) = [classOf (s i)]) :
    (∃ q, branch f loose s ps (pick ++ rest) = some q ∧ Matches q σ) ↔
      ps.map (fun t => classOf (σ.apply t)) = pick.map (fun i => classOf (s i)) ∧
      (images f σ loose).Perm (rest.map (fun i => classOf (s i))) := by
  induction ps generalizing pick with
  | nil =>
    obtain rfl : pick = [] := List.length_eq_zero_iff.mp len
    simp only [List.nil_append, branch, List.map_nil, true_and]
    rw [← subject_parts f s rest atomic]
    exact holds_iff ..
  | cons t ps ih =>
    cases pick with
    | nil => simp at len
    | cons i pick =>
      simp only [List.length_cons, Nat.succ.injEq] at len
      simp only [List.cons_append, branch, Option.map_eq_some_iff, List.map_cons, List.cons.injEq]
      have hf : classOf (σ.apply t) = classOf (s i) ↔ EquivB (σ.apply t) (s i) :=
        ⟨Quotient.exact,fun h => Quotient.sound h⟩
      rw [hf, and_assoc, ← ih pick len]
      constructor
      · rintro ⟨_,⟨q, h, rfl⟩,hm⟩
        exact ⟨hm _ (List.mem_cons_self ..), q,h, fun e he => hm e (List.mem_cons_of_mem _ he)⟩
      · rintro ⟨he,q,h,hm⟩
        exact ⟨_, ⟨q,h,rfl⟩, fun e hh => (List.mem_cons.mp hh).elim (fun eq => eq ▸ he) (hm e)⟩

private theorem rigid_parts (f : sig.ACSym) (σ : Substitution sig) (ps : List (Term sig))
    (stable : ∀ p ∈ ps, AtomicACPair.Atomic f p) :
    images f σ ps = ps.map (fun p => classOf (σ.apply p)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Cancellation.flatten f (σ.apply p) ++ images f σ ps = _
    rw [stable p (by simp) σ, ih (fun p hp => stable p (List.mem_cons_of_mem _ hp))]
    rfl

/-- Lift each requested B-class to a separate original position, even when
the same B-class occurs several times. -/
private theorem select_prefix {α : Type} (code : Nat → α) (want leftover : List α)
    (is : List Nat) (perm : (want ++ leftover).Perm (is.map code)) :
    ∃ pick rest : List Nat, (pick ++ rest).Perm is ∧ pick.map code = want ∧ leftover.Perm (rest.map code) := by
  induction want generalizing is with
  | nil => exact ⟨[], is, .refl _, rfl, perm⟩
  | cons x xs ih =>
    have mem := perm.mem_iff.mp (List.mem_cons_self ..)
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp mem
    subst x
    have move := List.perm_cons_erase hi
    have tail := (perm.trans (move.map code)).cons_inv
    obtain ⟨pick,rest,hp,hw,hr⟩ := ih (is.erase i) tail
    exact ⟨i::pick,rest, (hp.cons i).trans move.symm, by simp [hw], hr⟩

private theorem flat_layout [DecidableEq sig.ACSym] (f : sig.ACSym) (σ : Substitution sig) (t : Term sig) :
    images f σ (ACRepresentation.flatten f t) = Cancellation.flatten f (σ.apply t) := by
  induction t with
  | var | atom | free | comm => simp [images, ACRepresentation.flatten]
  | ac g a b ha hb =>
    by_cases he : f = g
    · subst g
      simp only [ACRepresentation.flatten, ite_true, images, List.flatMap_append] at *
      rw [ha,hb]
      exact (Cancellation.flatten_ac ..).symm
    · simp [images,ACRepresentation.flatten, he]

/-- Matching depends only on the two represented factor inventories. -/
theorem layout_iff [DecidableEq sig.ACSym] (f : sig.ACSym) (σ : Substitution sig)
    (p t : Term sig) (ps ts : List (Term sig))
    (pl : ps.Perm (ACRepresentation.flatten f p))
    (sl : ts.Perm (ACRepresentation.flatten f t)) :
    EquivB (σ.apply p) t ↔ Holds f ps ts σ := by
  rw [holds_iff]
  have left := pl.flatMap_right (fun a => Cancellation.flatten f (σ.apply a))
  change (images f σ ps).Perm (images f σ (ACRepresentation.flatten f p)) at left
  rw [flat_layout] at left
  have right := sl.flatMap_right (Cancellation.flatten f)
  have identity := flat_layout f (.identity : Substitution sig) t
  simp only [images, Substitution.apply_identity] at identity
  rw [identity] at right
  exact ⟨fun e => left.trans ((Cancellation.flatten_equiv f e).trans right.symm),
    fun h => Cancellation.equiv_of_flatten_perm f (left.symm.trans (h.trans right))⟩

/-- When no pattern factor can expand at this head, every match consumes
exactly one subject occurrence per pattern occurrence. -/
theorem rigid_length (f : sig.ACSym) (σ : Substitution sig) (ps ts : List (Term sig))
    (rigid : ∀ a ∈ ps, AtomicACPair.Atomic f a)
    (subjects : ∀ a ∈ ts, AtomicACPair.Atomic f a)
    (h : Holds f ps ts σ) : ps.length = ts.length := by
  have left := rigid_parts f σ ps rigid
  have right := rigid_parts f (.identity : Substitution sig) ts subjects
  simp only [images, Substitution.apply_identity] at left right
  have perm := (holds_iff ..).mp h
  simpa only [left,right,List.length_map] using perm.length_eq

private theorem equation_iff [DecidableEq sig.ACSym] (f : sig.ACSym) (σ : Substitution sig)
    (p t : Term sig) (rigid loose : List (Term sig)) (subject : Nat → Term sig) (pool : List Nat)
    (pl : (rigid ++ loose).Perm (ACRepresentation.flatten f p))
    (sl : (pool.map subject).Perm (ACRepresentation.flatten f t))
    (stable : ∀ a ∈ rigid, AtomicACPair.Atomic f a)
    (factor : ∀ i ∈ pool, Cancellation.flatten f (subject i) = [classOf (subject i)]) :
    EquivB (σ.apply p) t ↔
      ((rigid.map (fun a => classOf (σ.apply a))) ++ images f σ loose).Perm
        (pool.map (fun i => classOf (subject i))) := by
  have hl := pl.flatMap_right (fun a => Cancellation.flatten f (σ.apply a))
  change (images f σ (rigid ++ loose)).Perm (images f σ (ACRepresentation.flatten f p)) at hl
  rw [flat_layout] at hl
  have app : images f σ (rigid ++ loose) = images f σ rigid ++ images f σ loose := List.flatMap_append
  rw [app, rigid_parts f σ rigid stable] at hl
  have hr := sl.flatMap_right (Cancellation.flatten f)
  have id := flat_layout f (.identity : Substitution sig) t
  simp only [images, Substitution.apply_identity] at id
  rw [subject_parts f subject pool factor, id] at hr
  exact ⟨fun e => hl.trans ((Cancellation.flatten_equiv f e).trans hr.symm),
    fun h => Cancellation.equiv_of_flatten_perm f (hl.symm.trans (h.trans hr))⟩

/-- Pointwise interpretation for an occurrence selector. A single substitution is
shared by all selected child constraints, loose factors, and any pending equations. -/
def Correct (run : OpenMatchSelect.Kernel) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (f : s.ACSym) (p t : Term s)
    (rigid loose : List (Term s)) (subject : Nat → Term s) (k n : UInt64),
    k.toNat = rigid.length → (rigid ++ loose).Perm (ACRepresentation.flatten f p) →
    ((List.range n.toNat).map subject).Perm (ACRepresentation.flatten f t) →
    (∀ a ∈ rigid, AtomicACPair.Atomic f a) →
    (∀ i < n.toNat, Cancellation.flatten f (subject i) = [classOf (subject i)]) →
    ∀ out, run k n = some out → ∀ (pending : Problem s) (σ : Substitution s),
      Matches (⟨p,t⟩ :: pending) σ ↔ ∃ row ∈ OpenMatchSelect.decoded out,
        ∃ q, branch f loose subject rigid row = some q ∧ Matches (q ++ pending) σ

theorem correct {run : OpenMatchSelect.Kernel} (hc : OpenMatchSelect.Correct run) : Correct run := by
  intro sig _ f p t rigid loose s k n len pl sl stable atom out ran pending σ
  let pool := List.range n.toNat
  have atomic (i : Nat) (h : i ∈ pool) := atom i (List.mem_range.mp h)
  have eq := equation_iff f σ p t rigid loose s pool pl sl stable atomic
  have branchMatch (q : Problem sig) : Matches (q ++ pending) σ ↔ Matches q σ ∧ Matches pending σ := by
    simp only [Matches,List.mem_append,or_imp,forall_and]
  constructor
  · intro hm
    have hp := eq.mp (hm _ (List.mem_cons_self ..))
    obtain ⟨pick,rest,all,chosen,remain⟩ := select_prefix _ _ _ _ hp
    have size : pick.length = rigid.length := by simpa using congrArg List.length chosen
    obtain ⟨rem, isChosen, moved⟩ := hc.covers ran (size.trans len.symm) all
    have keep (j) (hj : j ∈ rem) := atomic j (all.mem_iff.mp (List.mem_append_right _ (moved.mem_iff.mp hj)))
    obtain ⟨q,hq,hsol⟩ := (branch_iff f σ s rigid loose pick rem size keep).mpr
      ⟨chosen.symm, remain.trans (moved.map _).symm⟩
    exact ⟨_,isChosen,q,hq,(branchMatch q).mpr ⟨hsol,fun e he => hm e (List.mem_cons_of_mem _ he)⟩⟩
  · rintro ⟨row, mem, q, hq, hm⟩
    let pick := row.take k.toNat
    let rest := row.drop k.toNat
    have whole : pick ++ rest = row := List.take_append_drop ..
    have enough := (hc.sound ran mem).1
    have size : pick.length = rigid.length := by simpa [pick,Nat.min_eq_left enough] using len
    have valid := hc.perm ran mem
    rw [← whole] at valid hq
    have keep (j) (hj : j ∈ rest) := atomic j (valid.mem_iff.mp (List.mem_append_right _ hj))
    obtain ⟨sol,tail⟩ := (branchMatch q).mp hm
    obtain ⟨chosen,remain⟩ := (branch_iff f σ s rigid loose pick rest size keep).mp ⟨q,hq,sol⟩
    have all := valid.map (fun i => classOf (s i))
    rw [List.map_append] at all
    have e := eq.mpr (chosen ▸ (remain.append_left _).trans all)
    exact fun d hd => (List.mem_cons.mp hd).elim (fun he => he ▸ e) (tail d)

private theorem occurs_fold (f : sig.ACSym) (v : Variable) (a : Term sig) (xs : List (Term sig)) :
    (ACRepresentation.fold f a xs).Occurs v ↔ ∃ t ∈ a :: xs, t.Occurs v := by
  induction xs generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih =>
    change a.Occurs v ∨ (ACRepresentation.fold f b bs).Occurs v ↔ _
    simp only [ih, List.mem_cons, exists_eq_or_imp]

private theorem occurs_flatten [DecidableEq sig.ACSym] (f : sig.ACSym) (v : Variable) (p : Term sig) :
    (∃ t ∈ ACRepresentation.flatten f p, t.Occurs v) ↔ p.Occurs v := by
  induction p with
  | ac g a b ha hb =>
    by_cases eq : f = g
    · subst g
      simp only [ACRepresentation.flatten, ite_true, List.mem_append, or_and_right, exists_or, ha, hb]
      rfl
    · simp [ACRepresentation.flatten,eq]
  | _ => simp [ACRepresentation.flatten]

private theorem observed_residual {f : sig.ACSym} {left right : List (Term sig)} {q}
    (h : residual f left right = some q) (v : Variable) :
    Observed q v ↔ ∃ t ∈ left, t.Occurs v := by
  cases left with
  | nil => cases right <;> simp [residual,decode] at h <;> subst q <;> simp [Observed]
  | cons a as =>
    cases right with
    | nil => cases h
    | cons b bs =>
      cases Option.some.inj h
      simp [Observed, occurs_fold]

private theorem observed_branch {f : sig.ACSym} (loose : List (Term sig)) (subject : Nat → Term sig)
    (rigid : List (Term sig)) (indices : List Nat) {q}
    (h : branch f loose subject rigid indices = some q) (v : Variable) :
    Observed q v ↔ ∃ t ∈ rigid ++ loose, t.Occurs v := by
  induction rigid generalizing indices q with
  | nil => exact observed_residual h v
  | cons p ps ih =>
    cases indices with
    | nil => cases h
    | cons i is =>
      obtain ⟨q',hq,rfl⟩ := Option.map_eq_some_iff.mp h
      have eq : Observed (⟨p,subject i⟩ :: q') v ↔ p.Occurs v ∨ Observed q' v := by
        simp [Observed]
      rw [eq, ih is hq]
      simp

/-- Decode complete residual matching problems. Including pending equations in
each branch preserves variable sharing with constraints outside the AC node. -/
def queries (f : sig.ACSym) (rigid loose : List (Term sig)) (s : Nat → Term sig)
    (out : OpenMatchSelect.Packet) (pending : Problem sig) : List (Problem sig) :=
  ((OpenMatchSelect.decoded out).filterMap (branch f loose s rigid)).map (· ++ pending)

/-- A complete matcher for each surviving residual gives a complete match set
on the original conjunction, with the original bindable-variable scope. -/
theorem complete {run} (verified : Correct run) [DecidableEq sig.ACSym]
    (f : sig.ACSym) (p t : Term sig) (rigid loose : List (Term sig)) (s : Nat → Term sig)
    (k n : UInt64) (len : k.toNat = rigid.length)
    (pl : (rigid ++ loose).Perm (ACRepresentation.flatten f p))
    (sl : ((List.range n.toNat).map s).Perm (ACRepresentation.flatten f t))
    (stable : ∀ a ∈ rigid, AtomicACPair.Atomic f a)
    (atom : ∀ i < n.toNat, Cancellation.flatten f (s i) = [classOf (s i)])
    {out} (ran : run k n = some out) (pending : Problem sig)
    (bindable : Variable → Prop) (solve : Problem sig → List (Substitution sig))
    (closed : ∀ q ∈ queries f rigid loose s out pending, Matching.Complete q bindable (solve q)) :
    Matching.Complete (⟨p,t⟩ :: pending) bindable ((queries f rigid loose s out pending).flatMap solve) := by
  let branches := queries f rigid loose s out pending
  have part (q) : q ∈ branches ↔ ∃ row ∈ OpenMatchSelect.decoded out,
      ∃ residual, branch f loose s rigid row = some residual ∧ residual ++ pending = q := by
    simp only [branches,queries,List.mem_map,List.mem_filterMap]
    constructor
    · rintro ⟨r,⟨row,mem,e⟩,rfl⟩; exact ⟨row,mem,r,e,rfl⟩
    · rintro ⟨row,mem,r,e,rfl⟩; exact ⟨r,⟨row,mem,e⟩,rfl⟩
  have obs {q} (hq : q ∈ branches) : Observed q = Observed (⟨p,t⟩ :: pending) := by
    obtain ⟨_,_,r,hr,rfl⟩ := (part q).mp hq
    funext v; apply propext
    rw [observed_append, observed_branch loose s rigid _ hr]
    have left : (∃ t ∈ rigid ++ loose, t.Occurs v) ↔ p.Occurs v := by
      rw [← occurs_flatten f v p]
      simp only [pl.mem_iff]
    rw [left]
    simp [Observed]
  have interpret (σ : Substitution sig) : Matches (⟨p,t⟩ :: pending) σ ↔
      ∃ q ∈ branches, Matches q σ := by
    rw [verified f p t rigid loose s k n len pl sl stable atom out ran pending σ]
    constructor
    · rintro ⟨row,mem,r,hr,sol⟩; exact ⟨_, (part _).mpr ⟨row,mem,r,hr,rfl⟩,sol⟩
    · rintro ⟨q,hq,sol⟩
      obtain ⟨row,mem,r,hr,rfl⟩ := (part _).mp hq
      exact ⟨row,mem,r,hr,sol⟩
  constructor
  · intro σ member
    obtain ⟨q,hq,hs⟩ := List.mem_flatMap.mp member
    obtain ⟨sol,scope⟩ := (closed q hq).sound σ hs
    exact ⟨(interpret _).mpr ⟨q,hq,sol⟩, by simpa only [Scoped,obs hq] using scope⟩
  · intro ρ hρ scope
    obtain ⟨q,hq,sol⟩ := (interpret _).mp hρ
    obtain ⟨σ,hs,agreement⟩ := (closed q hq).covers ρ sol (by simpa only [Scoped,obs hq] using scope)
    exact ⟨σ,List.mem_flatMap.mpr ⟨q,hq,hs⟩, by simpa only [obs hq] using agreement⟩

end Tamarin.OpenMatch
