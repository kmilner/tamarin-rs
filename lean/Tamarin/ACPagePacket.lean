import TamarinRuntime.ACPagePacket
import Tamarin.ACBagPages
import Tamarin.ACMatchSortedBags

namespace Tamarin.Matching.ACPagePacket
open ACMatchPacket
abbrev Arm := List (List UInt64)
abbrev Run := Packet → Array UInt64 → UInt64 → Option Answers

theorem cursor_limbs (n : Nat) : cursor (limbs n) = n := by
  unfold limbs
  split
  · subst n; rfl
  · rw [cursor,cursor_limbs (n / UInt64.size)]
    exact Nat.mod_add_div n UInt64.size
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- The arithmetic meaning is fixed independently of the runtime decoder.
Rust may compare the number of limbs before reading them individually. -/
theorem cursor_value (ws : List UInt64) :
    cursor ws = ws.foldr (fun word rest => word.toNat + 2^64 * rest) 0 := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [cursor,List.foldr_cons,ih]

theorem limbs_minimal (n : Nat) (w : UInt64) (h : (limbs n).getLast? = some w) : w ≠ 0 := by
  rw [limbs] at h
  split at h
  · simp at h
  · rename_i nz
    cases q : limbs (n / UInt64.size) with
    | nil =>
      have hi : n / UInt64.size = 0 := by simpa [q,cursor] using (cursor_limbs (n / UInt64.size)).symm
      have small := (Nat.div_eq_zero_iff_lt (by decide : 0 < UInt64.size)).mp hi
      simp only [q,List.getLast?_singleton,Option.some.injEq] at h
      intro zero
      have val := UInt64.toNat_ofNat_of_lt' small
      change n.toUInt64.toNat = n at val
      simp [h,zero] at val
      omega
    | cons v vs =>
      apply limbs_minimal (n / UInt64.size) w
      simpa [q] using h
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

/-- The shim reads the three header fields before reading the arm arrays.
Having one canonical encoding of the total lets a bounded collector compare
it to its budget before reading a second page. -/
def Wire (p : Answers) (page : ACBagPages.Page) : Prop :=
  unpack p = [limbs page.stop, [if page.done then 1 else 0], limbs page.total] :: page.answers

theorem wire_pack (p : ACBagPages.Page) : Wire (pack p.stop p.total p.done p.answers) p := by
  simp [Wire,pack,unpack,List.map_map,Function.comp_def]

theorem Wire.unique {p : Answers} {a b : ACBagPages.Page} (x : Wire p a) (y : Wire p b) : a = b := by
  obtain ⟨atot,ast,ad,aa⟩ := a
  obtain ⟨btot,bst,bd,ba⟩ := b
  have e := x.symm.trans y
  simp only [List.cons.injEq,and_true] at e
  obtain ⟨⟨hs,hd,ht⟩,ha⟩ := e
  have s : ast = bst := by simpa [cursor_limbs] using congrArg cursor hs
  have t : atot = btot := by simpa [cursor_limbs] using congrArg cursor ht
  cases ad <;> cases bd <;> simp_all

/-- A candidate chooses its own order, raw positions and page boundaries.
The complete family at the final cursor is specified directly by simultaneous
matching, independently of the factor-column enumeration. -/
structure Schedule (rows : List Row) where
  total : Nat
  emitted : Nat → List Arm
  initial : emitted 0 = []
  subset : ∀ i, emitted i ⊆ emitted total
  complete : ACBags.Complete rows ((emitted total).map (readArm rows))
  bounded : ∀ upper : UInt64 → List (List Nat),
    (∀ a ∈ (rows.flatMap Prod.snd).eraseDups, ∀ v, ACBags.Balanced rows a v → (answerKeys rows).map v ∈ upper a) →
    total ≤ ((rows.flatMap Prod.snd).eraseDups.map fun a => (upper a).length).prod

structure Advances {rs : List Row} (s : Schedule rs) (start requested : Nat) (page : ACBagPages.Page) : Prop where
  total : page.total = s.total
  interval : start ≤ page.stop ∧ page.stop ≤ s.total ∧ page.stop - start ≤ requested
  progress : start < s.total → start < page.stop
  done : page.done = true ↔ page.stop = s.total
  append : s.emitted start ++ page.answers = s.emitted page.stop
  count : page.answers.length ≤ page.stop - start
  shape : ∀ a ∈ page.answers, a.length = (answerKeys rs).length ∧ ∀ bag ∈ a, bag ≠ []

structure Correct (run : Run) : Prop where
  malformed : ∀ p c n, decode p.toList = none → run p c n = none
  schedule : ∀ rows, ∃ s : Schedule rows, ∀ p, decode p.toList = some rows →
    (∀ c n reply, run p c n = some reply → ∃ page, Wire reply page ∧ Advances s (cursor c.toList) n.toNat page) ∧
    (∀ c n, ACBagSearch.Within rows → cursor c.toList ≤ s.total → 0 < n.toNat → (run p c n).isSome)

/-- The boundary uses the actual returned cursor from the preceding page.
Only a page with its completion bit set can contribute a final answer. -/
inductive Chain (run : Run) (packet : Packet) : Nat → List Arm → Prop where
  | start : Chain run packet 0 []
  | next {i acc n reply page} : Chain run packet i acc →
      run packet (limbs i).toArray n = some reply → Wire reply page →
      Chain run packet page.stop (acc ++ page.answers)

theorem Correct.finished {run} (ok : Correct run) {packet rs} (read : decode packet.toList = some rs)
    {i acc requested reply page} (previous : Chain run packet i acc)
    (last : run packet (limbs i).toArray requested = some reply) (wire : Wire reply page)
    (done : page.done = true) : ACBags.Complete rs ((acc ++ page.answers).map (readArm rs)) := by
  obtain ⟨s,correct⟩ := ok.schedule rs
  have step {i n reply page} (h : run packet (limbs i).toArray n = some reply) (w : Wire reply page) :
      Advances s i n.toNat page := by
    obtain ⟨pg,encoded,adv⟩ := (correct _ read).1 _ _ _ h
    obtain rfl := encoded.unique w
    simpa [cursor_limbs] using adv
  have emitted {j xs} (h : Chain run packet j xs) : xs = s.emitted j := by
    induction h with
    | start => exact s.initial.symm
    | next _ ret w ih => exact ih ▸ (step ret w).append
  have endAt := (step last wire).done.mp done
  rw [emitted (previous.next last wire),endAt]
  exact s.complete

/-- Following positive-sized requests from zero always reaches a final packet
on the mandatory domain, even if a candidate produces empty intermediate pages. -/
theorem Correct.exhausts {run} (ok : Correct run) {packet rs} (read : decode packet.toList = some rs)
    (covered : ACBagSearch.Within rs) (n : UInt64) (positive : 0 < n.toNat) :
    ∃ i acc reply page, Chain run packet i acc ∧ run packet (limbs i).toArray n = some reply ∧
      Wire reply page ∧ page.done = true ∧ ACBags.Complete rs ((acc ++ page.answers).map (readArm rs)) := by
  obtain ⟨s,correct⟩ := ok.schedule rs
  obtain ⟨safe,required⟩ := correct _ read
  let rec finish (i : Nat) (acc : List Arm) (valid : i ≤ s.total) (chain : Chain run packet i acc) :
      ∃ j before reply page, Chain run packet j before ∧ run packet (limbs j).toArray n = some reply ∧
        Wire reply page ∧ page.done = true ∧ ACBags.Complete rs ((before ++ page.answers).map (readArm rs)) := by
    obtain ⟨reply,h⟩ := Option.isSome_iff_exists.mp
      (required (limbs i).toArray n covered (by simpa [cursor_limbs] using valid) positive)
    obtain ⟨page,wire,step⟩ := safe _ _ _ h
    simp only [cursor_limbs] at step
    cases done : page.done with
    | true => exact ⟨_,_,_,_,chain,h,wire,done,ok.finished read chain h wire done⟩
    | false =>
      have room : page.stop < s.total := Nat.lt_of_le_of_ne step.interval.2.1
        (fun eq => by simpa [done] using step.done.mpr eq)
      have up := step.progress (Nat.lt_of_le_of_lt step.interval.1 room)
      exact finish page.stop _ step.interval.2.1 (chain.next h wire)
    termination_by s.total - i
    decreasing_by omega
  exact finish 0 [] (Nat.zero_le _) .start

/-- Reassembling pages and filtering by the caller's sorts yields all and
only the sorted substitutions for the original simultaneous equations. -/
theorem Correct.finished_sorted {run} (ok : Correct run) {packet rs} (read : decode packet.toList = some rs)
    {i acc requested reply page} (previous : Chain run packet i acc)
    (last : run packet (limbs i).toArray requested = some reply) (wire : Wire reply page) (done : page.done = true)
    {sig : Signature} [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → Row} {name term fixed} (p : ACBags.Presentation f problem row name term fixed)
    (order : rs.Perm (problem.map row)) (accepted : List Arm) (out : Arm → Substitution sig)
    (retain : ∀ a, a ∈ accepted ↔ a ∈ acc ++ page.answers ∧ ACBags.Fits f (problem.map row) name term (readArm rs a))
    (scope : ∀ a ∈ accepted, Scoped problem (fun _ => True) (out a))
    (images : ∀ arm ∈ accepted, ∀ e ∈ problem, ∀ k ∈ (row e).1, ∀ a tail,
      readArm rs arm k = a :: tail →
      EquivB ((out arm).image (name k)) (ACRepresentation.fold f (term a) (tail.map term))) :
    Matching.Complete problem (fun _ => True) (accepted.map out) := by
  have complete := ACBags.complete_perm order (ok.finished read previous last wire done)
  exact p.sorted_complete _ _ _ _ complete retain (fun a ha => ⟨scope a ha,
    p.represents_fold (complete.sound _ (List.mem_map_of_mem ((retain a).1 ha).1)) (images a ha)⟩)

end Tamarin.Matching.ACPagePacket

namespace Tamarin.Matching.ACPagePacket
open ACMatchPacket ACBagPages ACBagAnswers

private def referenceSchedule (rs : List Row) : Schedule rs where
  total := (reference rs).length
  emitted i := render (keys rs) ((reference rs).take i)
  initial := by simp [render]
  subset i := by
    rw [List.take_of_length_le (Nat.le_refl _)]
    intro a ha
    obtain ⟨hm,positive⟩ := List.mem_filter.mp ha
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    exact List.mem_filter.mpr ⟨List.mem_map_of_mem (List.mem_of_mem_take hp),positive⟩
  complete := by
    rw [List.take_of_length_le (Nat.le_refl _)]
    exact exact_family rs
  bounded upper bound := by
    rw [reference,product_size]
    simpa [batch,List.map_map,Function.comp_def] using product_bound rs upper bound

theorem run_correct : Correct (runWith ACBagPages.run) where
  malformed p c n h := by simp [runWith,h]
  schedule rs := by
    refine ⟨referenceSchedule rs,?_⟩
    intro p read
    constructor
    · intro c n reply run
      cases e : ACBagPages.run rs (cursor c.toList) n.toNat with
      | none => simp [runWith,read,e] at run
      | some pg =>
        simp [runWith,read,e] at run
        subst reply
        have spec := run_page_spec e
        refine ⟨pg,wire_pack _,spec.total,⟨spec.ordered,by simpa only [referenceSchedule,spec.total] using spec.bounded,spec.requested_bound⟩,
          by simpa only [referenceSchedule,spec.total] using spec.progress,by simpa only [referenceSchedule,spec.total] using spec.finished,spec.prefix,?_,?_⟩
        · rw [spec.range_eq]
          exact Nat.le_trans (List.length_filter_le ..) (by simp [Nat.min_le_left])
        · intro a ha
          rw [spec.range_eq] at ha
          obtain ⟨mem,positive⟩ := List.mem_filter.mp ha
          obtain ⟨pick,_,rfl⟩ := List.mem_map.mp mem
          exact ⟨by simp [materialize,keys,answerKeys],fun b hb => by simpa using List.all_eq_true.mp positive b hb⟩
    · intro c n within start pos
      obtain ⟨pg,h⟩ := Option.isSome_iff_exists.mp (run_completes within start pos)
      simp [runWith,read,h]

end Tamarin.Matching.ACPagePacket
