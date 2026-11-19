import Tamarin.OpenMatchAdapter
import Tamarin.VariantJoin

/-! Existence of a directional match for distinct unrestricted AC captures.
The subject stays rigid, including occurrences of a pattern variable. -/
namespace Tamarin.Matching.LinearAC
open Cancellation OpenMatch
open Rewriting.VariantJoin (choose)
variable {sig : Signature}

/-- Give one subject factor to each capture except the last, which takes
the entire remaining product. Images are simultaneous even when a subject
factor mentions a variable whose binding is being constructed. -/
private theorem distribute (f : sig.ACSym) (v : Variable) (vs : List Variable)
    (ts : List (Term sig)) (distinct : (v :: vs).Nodup)
    (sorts : ∀ w ∈ v :: vs, Subsort (sig.acSort f) w.sort)
    (typed : ∀ t ∈ ts, HasSort t (sig.acSort f)) (room : (v :: vs).length ≤ ts.length) :
    ∃ s : Substitution sig, ((v :: vs).flatMap fun w => flatten f (s.image w)) = ts.flatMap (flatten f) := by
  classical
  induction vs generalizing ts v with
  | nil =>
    cases ts with
    | nil => simp at room
    | cons t ts =>
      let term := ACRepresentation.fold f t ts
      have ht := ACRepresentation.fold_hasSort f t ts (typed t List.mem_cons_self)
        (fun u h => typed u (List.mem_cons_of_mem _ h))
      refine ⟨Substitution.binding v term (ht.widen (sorts _ List.mem_cons_self)),?_⟩
      simpa [term] using OpenMatch.subject_flat f t ts
  | cons w ws ih =>
    cases ts with
    | nil => simp at room
    | cons t ts =>
      obtain ⟨s,hit⟩ := ih w ts distinct.tail (fun u h => sorts u (List.mem_cons_of_mem _ h))
        (fun u h => typed u (List.mem_cons_of_mem _ h)) (by simpa using room)
      let first := Substitution.binding v t ((typed t List.mem_cons_self).widen (sorts v List.mem_cons_self))
      let joined := choose (· = v) first s
      have tail : ((w :: ws).flatMap fun u => flatten f (joined.image u)) =
          ((w :: ws).flatMap fun u => flatten f (s.image u)) := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro u hu
        have ne : u ≠ v := fun eq => (List.nodup_cons.mp distinct).1 (eq ▸ hu)
        simp [joined,choose,ne]
      refine ⟨joined,?_⟩
      change flatten f (joined.image v) ++ ((w :: ws).flatMap fun u => flatten f (joined.image u)) =
        flatten f t ++ ts.flatMap (flatten f)
      rw [tail,hit]
      simp [joined,choose,first]

/-- Exact cancellation records the fixed factors as the same multiset on
both sides. The remaining factors may be arbitrary open terms. -/
theorem remainder [DecidableEq sig.ACSym] (f : sig.ACSym) (p t : Term sig)
    (fixed extra ts : List (Term sig))
    (left : (fixed ++ extra).Perm (ACRepresentation.flatten f p))
    (right : (fixed ++ ts).Perm (ACRepresentation.flatten f t))
    (ground : ∀ u ∈ fixed, u.Ground) (s : Substitution sig) :
    EquivB (s.apply p) t ↔ OpenMatch.Holds f extra ts s := by
  rw [OpenMatch.layout_iff f s p t _ _ left right,OpenMatch.holds_iff,OpenMatch.holds_iff]
  have unchanged : (fixed.flatMap fun u => flatten f (s.apply u)) = fixed.flatMap (flatten f) := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro u hu
    rw [(ground u hu).apply_eq]
  simp only [List.flatMap_append,unchanged,List.perm_append_left_iff]

/-- Physical counts are exact occurrence counts for a nonempty set of
distinct captures after successful cancellation. Both Boolean outcomes
describe the original equation modulo B. -/
def Correct (excludes : UInt64 → UInt64 → Bool) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (f : s.ACSym) (p t : Term s)
    (fixed : List (Term s)) (vs : List Variable) (ts : List (Term s)) (k n : UInt64),
    (fixed ++ vs.map Term.var).Perm (ACRepresentation.flatten f p) →
    (fixed ++ ts).Perm (ACRepresentation.flatten f t) → (∀ u ∈ fixed, u.Ground) →
    vs ≠ [] → vs.Nodup → (∀ w ∈ vs, Subsort (s.acSort f) w.sort) →
    HasSort t (s.acSort f) →
    k.toNat = vs.length → n.toNat = ts.length →
    (excludes k n = false ↔ ∃ σ : Substitution s, EquivB (σ.apply p) t)

theorem correct : Correct (fun k n => decide (n < k)) := by
  intro sig _ f p t fixed vs ts k n pl sl ground nonempty distinct sorts subject keys count
  have member u (hu : u ∈ ts) := sl.subset (List.mem_append_right fixed hu)
  have typed u (hu : u ∈ ts) := ACRepresentation.flatten_hasSort f t subject u (member u hu)
  have atoms u (hu : u ∈ ts) := OpenMatch.factor_of_mem_flatten f t u (member u hu)
  have numeric : decide (n < k) = false ↔ vs.length ≤ ts.length := by
    simp [← keys,← count,UInt64.lt_iff_toNat_lt]
  rw [numeric]
  have remn := remainder f p t fixed (vs.map Term.var) ts pl sl ground
  constructor
  · intro room
    cases vs with
    | nil => contradiction
    | cons v vs =>
      obtain ⟨s,h⟩ := distribute f v vs ts distinct sorts typed room
      refine ⟨s,(remn s).2 ((OpenMatch.holds_iff ..).2 ?_)⟩
      simpa [List.flatMap_map,Substitution.apply,Term.subst] using List.Perm.of_eq h
  · rintro ⟨s,hit⟩
    simpa using OpenMatchAdapter.long_enough f s (vs.map Term.var) ts atoms ((remn s).1 hit)

/-- Canonicalizing either side modulo B before identifying fixed factors
preserves both verdicts. The same canonical term may represent several
different raw C/AC trees in the input. -/
theorem presented {excludes} (checked : Correct excludes) [DecidableEq sig.ACSym]
    (f : sig.ACSym) (p t cp ct : Term sig) (hp : EquivB p cp) (ht : EquivB t ct)
    (fixed : List (Term sig)) (vs : List Variable) (ts : List (Term sig)) (k n : UInt64)
    (pl : (fixed ++ vs.map Term.var).Perm (ACRepresentation.flatten f cp))
    (sl : (fixed ++ ts).Perm (ACRepresentation.flatten f ct)) (ground : ∀ u ∈ fixed, u.Ground)
    (nonempty : vs ≠ []) (distinct : vs.Nodup) (sorts : ∀ w ∈ vs, Subsort (sig.acSort f) w.sort)
    (subject : HasSort ct (sig.acSort f)) (keys : k.toNat = vs.length) (count : n.toNat = ts.length) :
    excludes k n = false ↔ ∃ σ : Substitution sig, EquivB (σ.apply p) t := by
  rw [checked f cp ct fixed vs ts k n pl sl ground nonempty distinct sorts subject keys count]
  exact exists_congr fun σ => ⟨fun h => (hp.subst σ.image).trans (h.trans ht.symm),
    fun h => (hp.subst σ.image).symm.trans (h.trans ht)⟩

/-- Connect the two physical results to the original pattern and rigid
subject. Multiplicities count separately even for equivalent ground terms.
A missing fixed occurrence rules out every assignment. -/
def PacketCorrect (cancel : Array UInt64 → Array UInt64 → Array (Array UInt64))
    (excludes : UInt64 → UInt64 → Bool) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (f : s.ACSym) (p t : Term s)
    (d : UInt64 → Term s) (fixed subject : Array UInt64) (vs : List Variable) (k : UInt64),
    (fixed.toList.map d ++ vs.map Term.var).Perm (ACRepresentation.flatten f p) →
    (subject.toList.map d).Perm (ACRepresentation.flatten f t) →
    (∀ i ∈ fixed.toList, (d i).Ground) →
    (∀ i ∈ fixed.toList, ∀ j ∈ subject.toList, EquivB (d i) (d j) → i = j) →
    vs ≠ [] → vs.Nodup → (∀ w ∈ vs, Subsort (s.acSort f) w.sort) →
    HasSort t (s.acSort f) → k.toNat = vs.length →
    ∃ missing rest : List UInt64, cancel fixed subject = #[missing.toArray,rest.toArray] ∧
      ∀ n : UInt64, n.toNat = rest.length →
        (missing = [] ∧ excludes k n = false ↔ ∃ σ : Substitution s, EquivB (σ.apply p) t)

theorem packet_correct {cancel excludes} (hc : CommonCancellation.Correct cancel)
    (hk : Correct excludes) : PacketCorrect cancel excludes := by
  intro sig _ f p t d fixed subject vs k pl sl ground reflects ne distinct sorts typed keys
  obtain ⟨common,missing,rest,out,left,right,apart⟩ := hc fixed subject
  refine ⟨missing,rest,out,?_⟩
  intro n count
  have inFix i (mem : i ∈ common ++ missing) := left.mem_iff.mpr mem
  have inSub j (mem : j ∈ rest) := right.mem_iff.mpr (List.mem_append_right common mem)
  have commonGround u (hu : u ∈ common.map d) : u.Ground := by
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hu
    exact ground i (inFix _ (List.mem_append_left _ hi))
  have lp : (common.map d ++ (missing.map d ++ vs.map Term.var)).Perm (ACRepresentation.flatten f p) := by
    apply List.Perm.trans _ pl
    simpa [List.append_assoc] using ((left.map d).symm.append_right (vs.map (Term.var (sig := sig))))
  have rp : (common.map d ++ rest.map d).Perm (ACRepresentation.flatten f t) := by
    exact (by simpa using (right.map d).symm : (common.map d ++ rest.map d).Perm (subject.toList.map d)) |>.trans sl
  cases missing with
  | nil =>
    simpa using hk f p t (common.map d) vs (rest.map d) k n (by simpa using lp) rp
      commonGround ne distinct sorts typed keys (by simpa using count)
  | cons i is =>
    simp only [List.cons_ne_nil,false_and,false_iff,not_exists]
    intro σ hit
    have h := (remainder f p t _ _ _ lp rp commonGround σ).1 hit
    have perm := (OpenMatch.holds_iff ..).1 h
    have input := inFix i (List.mem_append_right _ List.mem_cons_self)
    have pat := pl.subset (List.mem_append_left _ (List.mem_map_of_mem (f := d) input))
    have src : classOf (d i) ∈ (((i :: is).map d ++ vs.map Term.var).flatMap
        fun a => flatten f (σ.apply a)) := by
      apply List.mem_flatMap.mpr
      refine ⟨d i,by simp,?_⟩
      rw [(ground i input).apply_eq,OpenMatch.factor_of_mem_flatten f p _ pat]
      simp
    obtain ⟨a,ha,belongs⟩ := List.mem_flatMap.mp (perm.subset src)
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
    have factor := OpenMatch.factor_of_mem_flatten f t _ (sl.subset (List.mem_map_of_mem (f := d) (inSub _ hj)))
    rw [factor,List.mem_singleton] at belongs
    exact apart i List.mem_cons_self ((reflects i input j (inSub _ hj) (Quotient.exact belongs)).symm ▸ hj)

/-- Variables are shared through patterns. A name occurring in one pattern
and another row's rigid subject does not couple the assignments. -/
theorem independent_exists (parts : List (Problem sig))
    (apart : parts.Pairwise (fun p q => ∀ v, Observed p v → ¬Observed q v)) :
    (∃ s, Matches parts.flatten s) ↔ ∀ p ∈ parts, ∃ s, Matches p s := by
  constructor
  · rintro ⟨s,h⟩ p hp
    exact ⟨s,fun e he => h e (List.mem_flatten.mpr ⟨p,hp,he⟩)⟩
  · intro solved
    induction parts with
    | nil => exact ⟨.identity,fun _ h => False.elim (List.not_mem_nil h)⟩
    | cons p rest ih =>
      obtain ⟨all,tail⟩ := List.pairwise_cons.mp apart
      obtain ⟨s,hs⟩ := solved p List.mem_cons_self
      obtain ⟨r,hr⟩ := ih tail (fun q h => solved q (List.mem_cons_of_mem _ h))
      apply Exists.intro (merge p s r)
      apply merge_matches hs hr
      intro v hv ⟨e,he,hit⟩
      obtain ⟨q,hq,member⟩ := List.mem_flatten.mp he
      exact False.elim (all q hq v hv ⟨e,member,hit⟩)

end Tamarin.Matching.LinearAC
