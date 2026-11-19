import Tamarin.MatchingFlatAC
import Tamarin.ACRepresentation
import Tamarin.FlatMatchSearch

/-! Completeness foundation for arbitrary-variable flat AC matching.
The subject is a nonempty product of rigid atoms. Variables may repeat; no
linearity assumption is made. Every matching image must be B-equivalent to a
nonempty submultiset of the subject, which makes finite search complete. -/
namespace Tamarin.FlatMatching
variable {sig : Signature}

abbrev Leaf (sig : Signature) := Sum Variable sig.Atom

def leaf (x : Leaf sig) : Term sig := match x with
  | .inl v => .var v
  | .inr a => .atom a

def pattern (f : sig.ACSym) : List (Leaf sig) → Term sig
  | [] => .var ⟨0, .msg⟩
  | x :: xs => ACRepresentation.fold f (leaf x) (xs.map leaf)

noncomputable def parts (f : sig.ACSym) (σ : Substitution sig) (x : Leaf sig) : List (Cancellation.Class sig) :=
  Cancellation.flatten f (σ.apply (leaf x))

private theorem flatten_fold (f : sig.ACSym) (a : Term sig) (as : List (Term sig)) :
    Cancellation.flatten f (ACRepresentation.fold f a as) =
      Cancellation.flatten f a ++ as.flatMap (Cancellation.flatten f) := by
  induction as generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih => simp [ACRepresentation.fold, Cancellation.flatten_ac, ih]

private theorem apply_fold (f : sig.ACSym) (σ : Substitution sig) (a : Term sig)
    (as : List (Term sig)) : σ.apply (ACRepresentation.fold f a as) =
      ACRepresentation.fold f (σ.apply a) (as.map σ.apply) := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    change Term.ac f (σ.apply a) (σ.apply (ACRepresentation.fold f b bs)) = _
    rw [ih]; rfl

theorem flatten_pattern (f : sig.ACSym) (σ : Substitution sig) (xs : List (Leaf sig))
    (hx : xs ≠ []) : Cancellation.flatten f (σ.apply (pattern f xs)) = xs.flatMap (parts f σ) := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons x xs => simp [pattern, apply_fold, flatten_fold, parts, List.flatMap_map]
                 rfl

theorem flatten_atoms (f : sig.ACSym) (xs : List sig.Atom) (hx : xs ≠ []) :
    Cancellation.flatten f (FlatAC.term f xs) = xs.map (fun a => Cancellation.classOf (.atom a)) := by
  induction xs with
  | nil => exact False.elim (hx rfl)
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      simp only [FlatAC.term, Cancellation.flatten_ac, Cancellation.flatten, List.map_cons]
      simpa using ih (by simp)

theorem part_sublist {α β : Type} (f : α → List β) {x : α} {xs : List α}
    (h : x ∈ xs) : List.Sublist (f x) (xs.flatMap f) := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (ih h).trans (List.sublist_append_right _ _)

/-- This ranges over arbitrary sorted substitutions, including images with
alien symbols and fresh variables. Matching itself rules those images out. -/
theorem image_submultiset (f : sig.ACSym) (xs : List (Leaf sig)) (rhs : List sig.Atom)
    (hx : xs ≠ []) (hr : rhs ≠ []) (σ : Substitution sig)
    (hm : EquivB (σ.apply (pattern f xs)) (FlatAC.term f rhs))
    (v : Variable) (hv : Sum.inl v ∈ xs) :
    ∃ rest : List sig.Atom, List.Sublist rest rhs ∧ rest ≠ [] ∧ EquivB (σ.image v) (FlatAC.term f rest) := by
  have hp := Cancellation.flatten_equiv f hm
  rw [flatten_pattern f σ xs hx, flatten_atoms f rhs hr] at hp
  have hs := part_sublist (parts f σ) hv
  obtain ⟨ys, hy, hsub⟩ := List.exists_perm_sublist hs hp
  obtain ⟨rest, hrest, he⟩ := List.sublist_map_iff.mp hsub
  subst ys
  have hn : rest ≠ [] := by
    intro he
    subst rest
    have hz := (List.Perm.nil_eq hy).symm
    have hf := Cancellation.fold_flatten f (σ.image v)
    change Cancellation.flatten f (σ.image v) = [] at hz
    rw [hz] at hf
    cases hf
  refine ⟨rest, hrest, hn, ?_⟩
  apply Cancellation.equiv_of_flatten_perm f
  rw [flatten_atoms f rest hn]
  exact hy.symm

/-- Fixed interpretation of a row vector; the runtime returns atoms for each
registered variable, with no auxiliary variables or implicit freshening. -/
noncomputable def rowSubst (f : sig.ACSym) {n : Nat} (vars : Fin n → Variable)
    (rows : Fin n → List sig.Atom) (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hr : ∀ i, rows i ≠ [])
    (hs : ∀ i a, a ∈ rows i → Subsort (sig.atomSort a) (sig.acSort f)) : Substitution sig where
  image := fun v => if h : ∃ i, vars i = v then FlatAC.term f (rows (Classical.choose h)) else .var v
  support := List.ofFn vars
  outside := by
    intro v h
    split
    · rename_i he
      exact False.elim (h (List.mem_ofFn.mpr he))
    · rfl
  sorted := by
    intro v
    split
    · rename_i he
      have hi := Classical.choose_spec he
      have hsort : v.sort = sig.acSort f := (congrArg Variable.sort hi).symm.trans (hv _)
      rw [hsort]
      exact FlatAC.term_hasSort f _ (hr _) (hs _)
    · exact .var _

theorem rowSubst_image (f : sig.ACSym) {n : Nat} (vars : Fin n → Variable)
    (rows : Fin n → List sig.Atom) (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hr : ∀ i, rows i ≠ []) (hs : ∀ i a, a ∈ rows i → Subsort (sig.atomSort a) (sig.acSort f))
    (hinj : Function.Injective vars) (i : Fin n) :
    (rowSubst f vars rows hv hr hs).image (vars i) = FlatAC.term f (rows i) := by
  simp only [rowSubst]
  split
  · rename_i h
    rw [hinj (Classical.choose_spec h)]
  · rename_i h; exact False.elim (h ⟨i, rfl⟩)

/-- A row query retains variable repetitions. Moving literals to the tail is
only an AC permutation, justified by the shared AC representation contract. -/
def queryLeaves {n : Nat} (vars : Fin n → Variable) (occ : List (Fin n))
    (tail : List sig.Atom) : List (Leaf sig) :=
  occ.map (fun i => Sum.inl (vars i)) ++ tail.map Sum.inr

def expanded {n : Nat} (rows : Fin n → List sig.Atom) (occ : List (Fin n))
    (tail : List sig.Atom) : List sig.Atom := occ.flatMap rows ++ tail

theorem pattern_expand (f : sig.ACSym) {n : Nat} (vars : Fin n → Variable)
    (occ : List (Fin n)) (tail : List sig.Atom) (rows : Fin n → List sig.Atom)
    (σ : Substitution sig) (hr : ∀ i, rows i ≠ [])
    (hi : ∀ i, EquivB (σ.image (vars i)) (FlatAC.term f (rows i)))
    (hq : queryLeaves vars occ tail ≠ []) (he : expanded rows occ tail ≠ []) :
    EquivB (σ.apply (pattern f (queryLeaves vars occ tail))) (FlatAC.term f (expanded rows occ tail)) := by
  apply Cancellation.equiv_of_flatten_perm f
  rw [flatten_pattern f σ _ hq, flatten_atoms f _ he]
  have hp : ∀ i, (parts f σ (Sum.inl (vars i))).Perm
      ((rows i).map (fun a => Cancellation.classOf (Term.atom a))) := by
    intro i
    have h := Cancellation.flatten_equiv f (hi i)
    rw [flatten_atoms f _ (hr i)] at h
    exact h
  have hocc : (occ.flatMap (fun i => parts f σ (Sum.inl (vars i)))).Perm
      (occ.flatMap (fun i => (rows i).map (fun a => Cancellation.classOf (Term.atom a)))) := by
    clear hq he
    induction occ with
    | nil => exact .refl _
    | cons i occ ih => exact (hp i).append ih
  simpa [queryLeaves, expanded, List.flatMap_append, List.flatMap_map,
    List.map_append, List.map_flatMap, ← List.map_eq_flatMap, parts, leaf, Substitution.apply, Term.subst,
    Cancellation.flatten] using hocc.append (List.Perm.refl (tail.map (fun a => Cancellation.classOf (Term.atom a))))

private theorem occurs_fold (f : sig.ACSym) (v : Variable) (a : Term sig)
    (as : List (Term sig)) : (ACRepresentation.fold f a as).Occurs v ↔
      a.Occurs v ∨ ∃ b ∈ as, b.Occurs v := by
  induction as generalizing a with
  | nil => simp [ACRepresentation.fold]
  | cons b bs ih => simp [ACRepresentation.fold, Term.Occurs, ih]

theorem occurs_pattern (f : sig.ACSym) {n : Nat} (vars : Fin n → Variable)
    (occ : List (Fin n)) (tail : List sig.Atom) (hq : queryLeaves vars occ tail ≠ []) (v : Variable) :
    (pattern f (queryLeaves vars occ tail)).Occurs v ↔ ∃ i ∈ occ, v = vars i := by
  have general : ∀ xs : List (Leaf sig), xs ≠ [] →
      ((pattern f xs).Occurs v ↔ ∃ x ∈ xs, (leaf x).Occurs v) := by
    intro xs hx
    cases xs with
    | nil => exact False.elim (hx rfl)
    | cons x xs => simp [pattern, occurs_fold]; grind
  rw [general _ hq]
  simp [queryLeaves, leaf]
  constructor
  · rintro ⟨x, (⟨i, hi, rfl⟩ | ⟨a, ha, rfl⟩), hx⟩
    · exact ⟨i, hi, hx⟩
    · exact False.elim hx
  · rintro ⟨i, hi, hv⟩
    exact ⟨Sum.inl (vars i), Or.inl ⟨i, hi, rfl⟩, hv⟩

def rowVector {α : Type} {n : Nat} (rows : List (List α)) (hl : rows.length = n)
    (i : Fin n) : List α := rows[i.val]'(by omega)

theorem expand_vector {n : Nat} (rows : List (List sig.Atom)) (hl : rows.length = n)
    (occ : List (Fin n)) (tail : List sig.Atom) :
    FlatMatchSearch.expand rows (occ.map Fin.val) ++ tail = expanded (rowVector rows hl) occ tail := by
  simp only [FlatMatchSearch.expand, expanded, List.flatMap_map]
  have he : (fun i : Fin n => rows[i.val]?.getD []) = rowVector rows hl := by
    funext i
    simp [List.getElem?_eq_getElem (show i.val < rows.length from by omega), rowVector]
  rw [he]

/-- Executable exhaustive search has complete coverage of arbitrary matching
substitutions, including repeated variables and multiple independent bindings. -/
theorem search_covers [DecidableEq sig.Atom] (f : sig.ACSym) {n : Nat}
    (vars : Fin n → Variable) (occ : List (Fin n)) (tail rhs : List sig.Atom)
    (hq : queryLeaves vars occ tail ≠ []) (hr : rhs ≠ []) (ho : ∀ i, i ∈ occ)
    (ρ : Substitution sig)
    (hm : EquivB (ρ.apply (pattern f (queryLeaves vars occ tail))) (FlatAC.term f rhs)) :
    ∃ rows, rows ∈ FlatMatchSearch.solve n (occ.map Fin.val) tail rhs ∧
      ∃ hl : rows.length = n, ∀ i, EquivB (ρ.image (vars i)) (FlatAC.term f (rowVector rows hl i)) := by
  classical
  have hi : ∀ i, ∃ rest : List sig.Atom, List.Sublist rest rhs ∧ rest ≠ [] ∧
      EquivB (ρ.image (vars i)) (FlatAC.term f rest) := by
    intro i
    apply image_submultiset f _ rhs hq hr ρ hm (vars i)
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, ho i, rfl⟩)
  let rs : Fin n → List sig.Atom := fun i => Classical.choose (hi i)
  have hrs : ∀ i, List.Sublist (rs i) rhs ∧ rs i ≠ [] ∧
      EquivB (ρ.image (vars i)) (FlatAC.term f (rs i)) := fun i => Classical.choose_spec (hi i)
  have hn : expanded rs occ tail ≠ [] := by
    intro he
    have hh : occ.flatMap rs = [] ∧ tail = [] := List.append_eq_nil_iff.mp he
    have hz : occ = [] := by
      cases occ with
      | nil => rfl
      | cons i is =>
        have hh := List.append_eq_nil_iff.mp hh.1
        exact False.elim ((hrs i).2.1 hh.1)
    exact hq (by simp [queryLeaves, hz, hh.2])
  have he := pattern_expand f vars occ tail rs ρ (fun i => (hrs i).2.1) (fun i => (hrs i).2.2) hq hn
  have hp := FlatAC.equiv_perm f (he.symm.trans hm)
  refine ⟨List.ofFn rs, ?_, List.length_ofFn, ?_⟩
  · apply (FlatMatchSearch.mem_solve _ _ _ _ _).mpr
    refine ⟨List.length_ofFn, ?_, ?_⟩
    · intro row hrow
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
      exact ⟨(hrs i).2.1, (hrs i).1⟩
    · simpa [FlatMatchSearch.expand, List.flatMap_map, expanded, List.getElem?_ofFn] using hp
  · intro i
    simpa [rowVector] using (hrs i).2.2

abbrev admissibleRows {n : Nat} (rhs : List sig.Atom) (rows : List (List sig.Atom)) : Prop :=
  rows.length = n ∧ ∀ row ∈ rows, row ≠ [] ∧ List.Sublist row rhs

noncomputable def answer (f : sig.ACSym) {n : Nat} (vars : Fin n → Variable)
    (rhs : List sig.Atom) (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (rows : List (List sig.Atom)) (h : admissibleRows (n := n) rhs rows) : Substitution sig :=
  rowSubst f vars (rowVector rows h.1) hv
    (fun i => (h.2 _ (List.getElem_mem (by omega))).1)
    (fun i a ha => hs a ((h.2 _ (List.getElem_mem (by omega))).2.subset ha))

noncomputable def answers [DecidableEq sig.Atom] (f : sig.ACSym) {n : Nat}
    (vars : Fin n → Variable) (occ : List (Fin n)) (tail rhs : List sig.Atom)
    (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f)) : List (Substitution sig) :=
  (FlatMatchSearch.solve n (occ.map Fin.val) tail rhs).attach.map fun r =>
    answer f vars rhs hv hs r.val (by
      have h := (FlatMatchSearch.mem_solve _ _ _ _ _).mp r.property
      exact ⟨h.1, h.2.1⟩)

theorem answer_image (f : sig.ACSym) {n : Nat} (vars : Fin n → Variable)
    (rhs : List sig.Atom) (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (rows : List (List sig.Atom)) (h : admissibleRows (n := n) rhs rows)
    (hinj : Function.Injective vars) (i : Fin n) :
    (answer f vars rhs hv hs rows h).image (vars i) = FlatAC.term f (rowVector rows h.1 i) :=
  rowSubst_image f vars _ hv _ _ hinj i

/-- Full semantic completeness of the reference matcher for arbitrary counts
and repetitions of variables. The returned substitutions are ground and scoped. -/
theorem complete [DecidableEq sig.Atom] (f : sig.ACSym) {n : Nat}
    (vars : Fin n → Variable) (occ : List (Fin n)) (tail rhs : List sig.Atom)
    (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (hinj : Function.Injective vars) (ho : ∀ i, i ∈ occ)
    (hq : queryLeaves vars occ tail ≠ []) (hr : rhs ≠ []) :
    Matching.Complete [⟨pattern f (queryLeaves vars occ tail), FlatAC.term f rhs⟩]
      (fun _ => True) (answers f vars occ tail rhs hv hs) := by
  constructor
  · intro σ hσ
    obtain ⟨⟨rows, hrows⟩, _, rfl⟩ := List.mem_map.mp hσ
    have hc := (FlatMatchSearch.mem_solve _ _ _ _ _).mp hrows
    have ha : admissibleRows (n := n) rhs rows := ⟨hc.1, hc.2.1⟩
    have hi := answer_image f vars rhs hv hs rows ha hinj
    have hp := hc.2.2
    rw [expand_vector rows hc.1 occ tail] at hp
    have hn : expanded (rowVector rows hc.1) occ tail ≠ [] := by
      intro he; exact hr (List.Perm.nil_eq (he ▸ hp)).symm
    constructor
    · intro e he
      have he := List.mem_singleton.mp he; subst e
      exact (pattern_expand f vars occ tail _ _
        (fun i => (hc.2.1 _ (List.getElem_mem (by omega))).1)
        (fun i => by rw [hi]; exact .refl _) hq hn).trans (FlatAC.perm_equiv f hp)
    · intro v hnot
      apply (answer f vars rhs hv hs rows ha).outside v
      intro hm
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
      apply hnot
      refine ⟨⟨⟨pattern f (queryLeaves vars occ tail), FlatAC.term f rhs⟩, by simp, ?_⟩, trivial⟩
      exact (occurs_pattern f vars occ tail hq _).mpr ⟨i, ho i, rfl⟩
  · intro ρ hm _
    have he := hm ⟨pattern f (queryLeaves vars occ tail), FlatAC.term f rhs⟩ (by simp)
    obtain ⟨rows, hrows, hl, hi⟩ := search_covers f vars occ tail rhs hq hr ho ρ he
    have hc := (FlatMatchSearch.mem_solve _ _ _ _ _).mp hrows
    let ha : admissibleRows (n := n) rhs rows := ⟨hc.1, hc.2.1⟩
    refine ⟨answer f vars rhs hv hs rows ha, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨⟨rows, hrows⟩, List.mem_attach _ _, rfl⟩
    · intro v ⟨e, he, hevar⟩
      have he := List.mem_singleton.mp he; subst e
      obtain ⟨i, _, rfl⟩ := (occurs_pattern f vars occ tail hq v).mp hevar
      rw [answer_image f vars rhs hv hs rows ha hinj]
      exact hi i

noncomputable def answersFrom (f : sig.ACSym) {n : Nat} (vars : Fin n → Variable)
    (rhs : List sig.Atom) (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (out : List (List (List sig.Atom)))
    (hout : ∀ rows ∈ out, admissibleRows (n := n) rhs rows) : List (Substitution sig) :=
  out.attach.map fun r => answer f vars rhs hv hs r.val (hout r.val r.property)

/-- The semantic theorem is independent of the search implementation.
Equivalent row sets suffice; enumeration order and duplicates do not matter. -/
theorem complete_of_rows [DecidableEq sig.Atom] (f : sig.ACSym) {n : Nat}
    (vars : Fin n → Variable) (occ : List (Fin n)) (tail rhs : List sig.Atom)
    (hv : ∀ i, (vars i).sort = sig.acSort f)
    (hs : ∀ a ∈ rhs, Subsort (sig.atomSort a) (sig.acSort f))
    (hinj : Function.Injective vars) (ho : ∀ i, i ∈ occ)
    (hq : queryLeaves vars occ tail ≠ []) (hr : rhs ≠ [])
    (out : List (List (List sig.Atom)))
    (hout : ∀ rows ∈ out, admissibleRows (n := n) rhs rows)
    (he : ∀ rows, rows ∈ out ↔ rows ∈ FlatMatchSearch.solve n (occ.map Fin.val) tail rhs) :
    Matching.Complete [⟨pattern f (queryLeaves vars occ tail), FlatAC.term f rhs⟩]
      (fun _ => True) (answersFrom f vars rhs hv hs out hout) := by
  have hc := complete f vars occ tail rhs hv hs hinj ho hq hr
  have hm : ∀ σ, σ ∈ answersFrom f vars rhs hv hs out hout ↔ σ ∈ answers f vars occ tail rhs hv hs := by
    intro σ
    constructor
    · intro h
      obtain ⟨⟨rows, hrows⟩, _, rfl⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨⟨rows, (he rows).mp hrows⟩, List.mem_attach _ _, rfl⟩
    · intro h
      obtain ⟨⟨rows, hrows⟩, _, rfl⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨⟨rows, (he rows).mpr hrows⟩, List.mem_attach _ _, rfl⟩
  constructor
  · intro σ hs; exact hc.sound σ ((hm σ).mp hs)
  · intro ρ hr hc'
    obtain ⟨σ, hs, ha⟩ := hc.covers ρ hr hc'
    exact ⟨σ, (hm σ).mpr hs, ha⟩

end Tamarin.FlatMatching
