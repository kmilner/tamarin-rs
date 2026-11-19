import TamarinRuntime.ACBagPages
import Tamarin.ACBagAnswers

namespace Tamarin.Matching.ACBagPages
open ACBags ACBagSearch ACBagAnswers

private theorem prepare_size (ls : Batch) : (prepare ls).1 = (product ls).length := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    rcases l with ⟨a,cs⟩
    simp only [prepare, product_size, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]

private theorem block_at {α β γ : Type} (cs : List α) (ts : List β) (f : α → β → γ)
    (j k : Nat) (hj : j < cs.length) (hk : k < ts.length) :
    (cs.flatMap fun c => ts.map (f c))[j * ts.length + k]? = some (f cs[j] ts[k]) := by
  induction cs generalizing j with
  | nil => contradiction
  | cons c cs ih =>
    cases j with
    | zero =>
      simp only [Nat.zero_mul,Nat.zero_add,List.flatMap_cons,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa using hk),List.getElem?_map,List.getElem?_eq_getElem hk]
      rfl
    | succ j =>
      simp only [List.flatMap_cons,List.getElem_cons_succ,Nat.succ_mul]
      rw [List.getElem?_append_right (by simp; omega), List.length_map]
      rw [show j * ts.length + ts.length + k - ts.length = j * ts.length + k by omega]
      exact ih j (by simpa using hj)

/-- Mixed-radix selection yields the reference product's pick at exactly the
given ordinal, regardless of the number of other picks. -/
theorem pick_at (ls : Batch) (i : Nat) (hi : i < (product ls).length) :
    (prepare ls).2.pick i = (product ls)[i] := by
  induction ls generalizing i with
  | nil => have : i = 0 := by simpa [product] using hi
           subst i; rfl
  | cons l ls ih =>
    rcases l with ⟨a,cs⟩
    let n := (product ls).length
    have len : (product ((a,cs) :: ls)).length = cs.length * n := by
      simp [n,product_size]
    have bound := len ▸ hi
    have pos : 0 < n := Nat.pos_of_ne_zero (fun zero => by simp [zero] at bound)
    have hj := (Nat.div_lt_iff_lt_mul pos).mpr bound
    have hk := Nat.mod_lt i pos
    have atIndex := block_at cs (product ls) (fun v p => (a,v)::p) (i/n) (i%n) hj hk
    have recombine : i / n * n + i % n = i := by rw [Nat.mul_comm, Nat.div_add_mod]
    change (product ((a,cs)::ls))[i / n * n + i % n]? = _ at atIndex
    rw [recombine,List.getElem?_eq_getElem hi] at atIndex
    simp only [prepare,Plan.pick,prepare_size,List.getElem?_toArray]
    rw [List.getElem?_eq_getElem hj, ih _ hk]
    exact (Option.some.inj atIndex).symm

private theorem picks_slice (ls : Batch) (start span : Nat) (room : span ≤ (product ls).length - start) :
    (List.range span).map (fun off => (prepare ls).2.pick (start + off)) =
      ((product ls).drop start).take span := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left room]
  · intro i hi _
    simp only [List.length_map,List.length_range] at hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_take,List.getElem_drop]
    exact pick_at _ _ (by omega)

/-- The reference list is mathematical. The linked candidate computes counts
and seeks directly to its cursor, without constructing this list. -/
abbrev reference (rs : Rows) := product (batch rs (atoms rs))

def charge (rs : Rows) : Nat :=
  1 + (keys rs).length * (1 + (atoms rs).length) + (rs.map fun r => r.2.length).sum

structure PageSpec (rs : Rows) (start requested : Nat) (p : Page) : Prop where
  total : p.total = (reference rs).length
  ordered : start ≤ p.stop
  bounded : p.stop ≤ p.total
  finished : p.done = true ↔ p.stop = p.total
  progress : start < p.total → start < p.stop
  requested_bound : p.stop - start ≤ requested
  work : p.stop - start ≤ 256
  construction : (p.stop - start) * charge rs ≤ 65536
  range_eq : p.answers = render (keys rs) (((reference rs).drop start).take (p.stop-start))

theorem run_page_spec {rs : Rows} {start requested : Nat} {p : Page}
    (returned : run rs start requested = some p) : PageSpec rs start requested p := by
  cases h : inventories rs with
  | none => simp [run,h] at returned
  | some pair =>
    rw [inventories_eq h] at h
    let ls := batch rs (atoms rs)
    have read : readPage (keys rs) ls (charge rs) start requested = some p := by
      simpa [run,h,ls,batch,charge,wordsPerPick,atoms,keys] using returned
    dsimp only [readPage] at read
    split at read
    · contradiction
    · rename_i ok
      simp only [not_or] at ok
      obtain ⟨positive,inRange,capacity⟩ := ok
      change ¬ (prepare ls).1 < start at inRange
      rw [prepare_size] at inRange
      cases read
      simp only [prepare_size] at *
      let span := min ((product ls).length - start) (min requested (min 256 (65536 / charge rs)))
      have room : span ≤ (product ls).length - start := Nat.min_le_left _ _
      have req : span ≤ requested := Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)
      have cap : span ≤ min 256 (65536 / charge rs) :=
        Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _)
      have budget := Nat.le_trans (Nat.mul_le_mul_right (charge rs) (Nat.le_trans cap (Nat.min_le_right _ _)))
        (Nat.div_mul_le_self 65536 (charge rs))
      change PageSpec rs start requested ⟨(product ls).length, start + span, _ , _⟩
      constructor
      · rfl
      · exact Nat.le_add_right _ _
      · dsimp; omega
      · simp [span]
      · intro left
        change start < (product ls).length at left
        change start < start + span
        have rem := Nat.sub_pos_of_lt left
        exact Nat.lt_add_of_pos_right (Nat.lt_min.mpr ⟨rem,Nat.lt_min.mpr ⟨Nat.pos_of_ne_zero positive, Nat.pos_of_ne_zero capacity⟩⟩)
      · simpa using req
      · simpa using Nat.le_trans cap (Nat.min_le_left _ _)
      · simpa using budget
      · simp only [Nat.add_sub_cancel_left]
        exact congrArg (render (keys rs)) (picks_slice ls start span room)

theorem total_le {rs : Rows} {start requested : Nat} {p : Page}
    (returned : run rs start requested = some p) (upper : UInt64 → List (List Nat))
    (bound : ∀ a ∈ atoms rs, ∀ v, Balanced rs a v → (keys rs).map v ∈ upper a) :
    p.total ≤ ((atoms rs).map fun a => (upper a).length).prod := by
  rw [(run_page_spec returned).total,reference,product_size]
  simpa [batch,List.map_map,Function.comp_def] using product_bound rs upper bound

private theorem target_mass (rs : Rows) :
    (rs.map (fun r => r.2.length)).sum ≤ (rs.map (fun r => r.1.length + r.2.length)).sum := by
  induction rs with
  | nil => exact Nat.le_refl _
  | cons r rs ih => simp only [List.map_cons,List.sum_cons]; omega

/-- Every admissible positive-sized request at a valid raw ordinal returns a
page, including the empty terminal page of an unsatisfiable factor system. -/
theorem run_completes {rs : Rows} (within : ACBagSearch.Within rs)
    {start requested : Nat} (valid : start ≤ (reference rs).length) (positive : 0 < requested) :
    (run rs start requested).isSome := by
  obtain ⟨ctx,h⟩ := Option.isSome_iff_exists.mp (inventories_complete within)
  rw [inventories_eq h] at h
  obtain ⟨_,size,kinds,atomsBound,_⟩ := within
  have size' := Nat.le_trans (target_mass rs) size
  have parts := Nat.mul_le_mul kinds (Nat.add_le_add_left atomsBound 1)
  have posWords : 0 < charge rs := by simp [charge]; omega
  have upper : charge rs ≤ 65536 := by
    change 1 + _ + _ ≤ 65536
    dsimp [keys,atoms] at *
    omega
  have cap := Nat.div_pos upper posWords
  have readable : ¬ (prepare (batch rs (atoms rs))).1 < start := by
    rw [prepare_size]
    exact Nat.not_lt_of_ge valid
  rw [run,h]
  change (readPage (keys rs) (batch rs (atoms rs)) (charge rs) start requested).isSome
  simp [readPage,show requested ≠ 0 by omega,readable,show min 256 (65536 / charge rs) ≠ 0 by omega]

private theorem render_append (ks : List UInt64) (xs ys : List Pick) :
    render ks (xs ++ ys) = render ks xs ++ render ks ys := by simp [render]

theorem PageSpec.prefix {rs : Rows} {start requested} {p : Page} (h : PageSpec rs start requested p) :
    render (keys rs) ((reference rs).take start) ++ p.answers =
      render (keys rs) ((reference rs).take p.stop) := by
  rw [h.range_eq,←render_append,←List.take_add]
  rw [Nat.add_sub_of_le h.ordered]

theorem PageSpec.answer_count {rs : Rows} {start requested} {p : Page} (h : PageSpec rs start requested p) :
    p.answers.length ≤ p.stop - start := by
  rw [h.range_eq]
  apply Nat.le_trans (List.length_filter_le ..)
  simp only [List.length_map,List.length_take]
  exact Nat.min_le_left _ _

theorem PageSpec.arm_shape {rs : Rows} {start requested} {p : Page} (h : PageSpec rs start requested p)
    {arm : Arm} (hit : arm ∈ p.answers) :
    arm.length = (keys rs).length ∧ (∀ bag ∈ arm, bag ≠ []) ∧
    (arm.map List.length).sum ≤ (rs.map fun r => r.2.length).sum := by
  rw [h.range_eq] at hit
  obtain ⟨generated,allNonempty⟩ := List.mem_filter.mp hit
  obtain ⟨pick,appears,rfl⟩ := List.mem_map.mp generated
  exact ⟨by simp [materialize],fun bag hb => by simpa using List.all_eq_true.mp allNonempty bag hb,
    pick_mass (List.mem_of_mem_drop (List.mem_of_mem_take appears))⟩

/-- Pages may request different sizes. The cursor of each successful page is
the start of the next, even when its answer list is empty. -/
inductive Chain (rows : Rows) : Nat → List Arm → Prop where
  | start : Chain rows 0 []
  | next {i answers requested page} : Chain rows i answers → run rows i requested = some page →
      Chain rows page.stop (answers ++ page.answers)

theorem Chain.prefix {rs : Rows} {i answers} (h : Chain rs i answers) :
    answers = render (keys rs) ((reference rs).take i) := by
  induction h with
  | start => simp [render]
  | next _ page ih => exact ih ▸ (run_page_spec page).prefix

/-- At the last page the entire emitted sequence, including multiplicity and
order, equals the unbounded exact answer family. -/
theorem chain_family {rs : Rows} {i answers requested page} (chain : Chain rs i answers)
    (last : run rs i requested = some page) (done : page.done = true) :
    answers ++ page.answers = family (keys rs) (batch rs (atoms rs)) := by
  have h := run_page_spec last
  have stop := (h.finished.mp done).trans h.total
  have eq := (chain.next last).prefix
  rw [stop,List.take_of_length_le (Nat.le_refl _)] at eq
  exact eq

theorem chain_complete {rs : Rows} {i answers requested page} (chain : Chain rs i answers)
    (last : run rs i requested = some page) (done : page.done = true) :
    Complete rs ((answers ++ page.answers).map (decode (keys rs))) := by
  rw [chain_family chain last done]
  exact exact_family rs

/-- A finite client traversal from the given start, at a fixed positive page
size. Every nonterminal cursor is followed, even if its page has no answers. -/
inductive Drains (rs : Rows) (requested : Nat) : Nat → List Arm → Prop where
  | last {i p} : run rs i requested = some p → p.done = true → Drains rs requested i p.answers
  | more {i p tail} : run rs i requested = some p → p.done = false →
      Drains rs requested p.stop tail → Drains rs requested i (p.answers ++ tail)

theorem drains {rs : Rows} (within : ACBagSearch.Within rs) (requested : Nat)
    (positive : 0 < requested) {i} (valid : i ≤ (reference rs).length) :
    ∃ answers, Drains rs requested i answers := by
  obtain ⟨p,returned⟩ := Option.isSome_iff_exists.mp (run_completes within valid positive)
  have h := run_page_spec returned
  cases terminal : p.done with
  | true => exact ⟨_,.last returned terminal⟩
  | false =>
    have endAfter : p.stop < (reference rs).length := by
      rw [←h.total]
      exact Nat.lt_of_le_of_ne h.bounded (fun eq => by simpa [terminal] using h.finished.mpr eq)
    have advance := h.progress (by rw [h.total]; have := h.ordered; omega)
    obtain ⟨tail,rest⟩ := drains within requested positive (Nat.le_of_lt endAfter)
    exact ⟨_,.more returned terminal rest⟩
termination_by (reference rs).length - i
decreasing_by omega

theorem Drains.reaches_last {rs : Rows} {requested i tail} (runAll : Drains rs requested i tail)
    {answers} (chain : Chain rs i answers) :
    ∃ j previous page, Chain rs j previous ∧ run rs j requested = some page ∧ page.done = true ∧
      answers ++ tail = previous ++ page.answers := by
  induction runAll generalizing answers with
  | last returned done => exact ⟨_,_,_,chain,returned,done,rfl⟩
  | more returned _ _ ih =>
    obtain ⟨_,_,_,prior,last,done,eq⟩ := ih (chain.next returned)
    exact ⟨_,_,_,prior,last,done,by simpa only [List.append_assoc] using eq⟩

theorem drains_complete {rs : Rows} {requested answers} (runAll : Drains rs requested 0 answers) :
    Complete rs (answers.map (decode (keys rs))) := by
  obtain ⟨_,_,_,chain,last,done,all⟩ := runAll.reaches_last .start
  simp only [List.nil_append] at all
  rw [all]
  exact chain_complete chain last done

end Tamarin.Matching.ACBagPages
