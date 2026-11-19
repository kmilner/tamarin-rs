import Tamarin.NestedTreeMatch

/-! Ordered C pairs and nonempty sorted vectors at AC heads give structural
identities for complete ground trees. A vector flattens just its own symbol;
a nested AC application at a different symbol is one operand. -/
namespace Tamarin.CanonicalTree

variable {sig : Signature}
open ACRepresentation

/-- Rust stores the AC vector directly. Its binary interpretation uses a right fold. -/
inductive Canonical (le : Term sig → Term sig → Prop) : Term sig → Prop where
  | atom (a : sig.Atom) : Canonical le (.atom a)
  | free (f : sig.FreeSym) {xs} (children : ∀ i, Canonical le (xs i)) : Canonical le (.free f xs)
  | comm (f : sig.CSym) {a b} (left : Canonical le a) (right : Canonical le b)
      (ordered : le a b) : Canonical le (.comm f a b)
  | ac (f : sig.ACSym) {a b rest}
      (children : ∀ t ∈ a :: b :: rest, Canonical le t)
      (flat : ∀ t ∈ a :: b :: rest, CompoundOffset.Fixed f t)
      (ordered : (a :: b :: rest).Pairwise le) : Canonical le (.ac f a (fold f b rest))

theorem Canonical.ground {le} {t : Term sig} (h : Canonical le t) : t.Ground := by
  induction h with
  | atom a => intro v; exact id
  | free f _ ih => intro v ⟨i,hi⟩; exact ih i v hi
  | comm f _ _ _ ia ib => intro v hv; exact hv.elim (ia v) (ib v)
  | ac f ch flat sorted ih => exact CompoundMatching.fold_ground f _ (_ :: _) ih

theorem alien_factor (f : sig.ACSym) {t : Term sig} (h : CompoundOffset.Fixed f t) :
    Cancellation.flatten f t = [Cancellation.classOf t] := by
  simpa only [Substitution.apply_identity] using CompoundOffset.fixed_factor f t h (.identity)

private theorem flatten_fold (f : sig.ACSym) (a : Term sig) (xs : List (Term sig))
    (flat : ∀ t ∈ a :: xs, CompoundOffset.Fixed f t) :
    Cancellation.flatten f (fold f a xs) = (a :: xs).map Cancellation.classOf := by
  induction xs generalizing a with
  | nil => exact alien_factor f (flat _ List.mem_cons_self)
  | cons b bs ih =>
    simp only [fold,Cancellation.flatten_ac,alien_factor f (flat a List.mem_cons_self),
      ih b (fun t ht => flat t (List.mem_cons_of_mem _ ht)),List.singleton_append,List.map_cons]

private theorem perm_of_map {α β : Type} (key : α → β) {xs ys : List α}
    (faithful : ∀ a ∈ xs, ∀ b ∈ ys, key a = key b → a = b)
    (hp : (xs.map key).Perm (ys.map key)) : xs.Perm ys := by
  classical
  induction xs generalizing ys with
  | nil => simpa using hp.symm.eq_nil
  | cons a xs ih =>
    have mem := hp.mem_iff.mp (List.mem_cons_self ..)
    obtain ⟨b,hb,e⟩ := List.mem_map.mp mem
    obtain rfl := faithful a List.mem_cons_self b hb e.symm
    have rest := (hp.trans ((List.perm_cons_erase hb).map key)).cons_inv
    apply (List.Perm.cons a (ih _ rest)).trans (List.perm_cons_erase hb).symm
    exact fun u hu v hv => faithful u (List.mem_cons_of_mem _ hu) v (List.mem_of_mem_erase hv)

/-- Canonical ground trees in the same B-class are structurally identical.
The ordering of the caller may be any antisymmetric relation. -/
theorem Canonical.unique {le : Term sig → Term sig → Prop}
    (anti : ∀ a b, le a b → le b a → a = b) {a b} (ha : Canonical le a)
    (hb : Canonical le b) (same : EquivB a b) : a = b := by
  induction ha generalizing b with
  | atom x =>
    cases hb <;> cases same.head_eq
    rfl
  | free f _ ih =>
    cases hb <;> cases same.head_eq
    rename_i ys children
    congr
    funext i
    exact ih i (children i) ((Matching.free_equiv_iff _ _ _).mp same i)
  | comm f ca cb ord ia ib =>
    cases hb <;> cases same.head_eq
    rename_i l r lcanon rcanon rhsOrd
    rcases (Commutative.equiv_iff ..).mp same with ⟨x,y⟩ | ⟨x,y⟩
    · rw [ia lcanon x,ib rcanon y]
    · have x' := ia rcanon x
      have y' := ib lcanon y
      subst_vars
      rw [anti _ _ ord rhsOrd]
  | @ac f a b xs ch flat ordered ih =>
    cases hb <;> cases same.head_eq
    rename_i c d ys rhsCh rhsOrdered rhsFlat
    have hp := Cancellation.flatten_equiv f same
    change (Cancellation.flatten f (fold f a (b::xs))).Perm
      (Cancellation.flatten f (fold f c (d::ys))) at hp
    rw [flatten_fold f _ _ flat,flatten_fold f _ _ rhsFlat] at hp
    have perm := perm_of_map _ (fun u hu v hv e => ih u hu (rhsCh v hv) (Quotient.exact e)) hp
    have eq := List.Perm.eq_of_pairwise (fun u v _ _ => anti u v) ordered rhsOrdered perm
    cases eq
    rfl

/-- Equality of folded AC images is exactly permutation of their full
canonical factors, even with other AC operators nested inside those factors. -/
theorem product_iff {le : Term sig → Term sig → Prop}
    (anti : ∀ a b, le a b → le b a → a = b) (f : sig.ACSym)
    (a b : Term sig) (xs ys : List (Term sig))
    (left : ∀ t ∈ a :: xs, Canonical le t ∧ CompoundOffset.Fixed f t)
    (right : ∀ t ∈ b :: ys, Canonical le t ∧ CompoundOffset.Fixed f t) :
    EquivB (fold f a xs) (fold f b ys) ↔ (a :: xs).Perm (b :: ys) := by
  constructor
  · intro e
    have hp := Cancellation.flatten_equiv f e
    rw [flatten_fold f _ _ (fun u hu => (left u hu).2),
      flatten_fold f _ _ (fun u hu => (right u hu).2)] at hp
    exact perm_of_map _ (fun u hu v hv h =>
      (left u hu).1.unique anti (right v hv).1 (Quotient.exact h)) hp
  · intro h
    exact decode_perm f h _ _ rfl rfl

/-- The caller can use any sorting procedure producing an ordered permutation. -/
structure Ordering (le : Term sig → Term sig → Prop) where
  sort : List (Term sig) → List (Term sig)
  perm : ∀ xs, (sort xs).Perm xs
  ordered : ∀ xs, (sort xs).Pairwise le

private theorem flatten_fixed [DecidableEq sig.ACSym] (f : sig.ACSym) {t : Term sig}
    (h : CompoundOffset.Fixed f t) : flatten f t = [t] := by
  cases t with
  | var | atom | free | comm => rfl
  | ac g l r => simp only [flatten,ite_eq_right h]

private theorem flatten_vector [DecidableEq sig.ACSym] (f : sig.ACSym)
    (a : Term sig) (xs : List (Term sig)) (flat : ∀ t ∈ a :: xs, CompoundOffset.Fixed f t) :
    flatten f (fold f a xs) = a :: xs := by
  induction xs generalizing a with
  | nil => exact flatten_fixed f (flat _ List.mem_cons_self)
  | cons b bs ih =>
    simp only [fold,flatten,ite_true,flatten_fixed f (flat a List.mem_cons_self),
      ih b (fun t ht => flat t (List.mem_cons_of_mem _ ht)),List.singleton_append]

theorem Canonical.factors [DecidableEq sig.ACSym] {le} {t : Term sig} (h : Canonical le t)
    (f : sig.ACSym) : ∀ u ∈ flatten f t, Canonical le u ∧ CompoundOffset.Fixed f u := by
  cases h with
  | atom a => simp [flatten,Canonical.atom,CompoundOffset.Fixed]
  | free g ch => simpa [flatten,CompoundOffset.Fixed] using Canonical.free g ch
  | comm g l r ord => simpa [flatten,CompoundOffset.Fixed] using Canonical.comm g l r ord
  | @ac g a b xs ch flat ord =>
    by_cases e : f = g
    · subst g
      change ∀ u ∈ flatten f (fold f a (b::xs)), _
      rw [flatten_vector f _ _ flat]
      exact fun u hu => ⟨ch u hu, flat u hu⟩
    · simpa [flatten,e,CompoundOffset.Fixed] using Canonical.ac g ch flat ord

private def join [DecidableEq sig.ACSym] {le : Term sig → Term sig → Prop} (order : Ordering le) (f : sig.ACSym)
    (a b : Term sig) : Term sig :=
  (decode f (order.sort (flatten f a ++ flatten f b))).getD (.ac f a b)

private theorem join_spec [DecidableEq sig.ACSym] {le : Term sig → Term sig → Prop} (order : Ordering le) (f : sig.ACSym)
    (a b : Term sig) : ∃ x y xs,
    order.sort (flatten f a ++ flatten f b) = x :: y :: xs ∧
    join order f a b = fold f x (y::xs) := by
  have sizes := (order.perm (flatten f a ++ flatten f b)).length_eq
  rw [List.length_append] at sizes
  have ha := List.length_pos_iff.mpr (flatten_nonempty f a)
  have hb := List.length_pos_iff.mpr (flatten_nonempty f b)
  cases h : order.sort (flatten f a ++ flatten f b) with
  | nil => rw [h] at sizes; simp only [List.length_nil] at sizes; omega
  | cons x xs =>
    cases xs with
    | nil => rw [h] at sizes; simp at sizes; omega
    | cons y ys => exact ⟨x,y,ys,rfl,by simp [join,h,decode]⟩

private theorem join_equiv [DecidableEq sig.ACSym] {le : Term sig → Term sig → Prop} (order : Ordering le) (f : sig.ACSym)
    (a b : Term sig) : EquivB (join order f a b) (.ac f a b) := by
  obtain ⟨x,y,xs,h,hj⟩ := join_spec order f a b
  rw [hj]
  obtain ⟨t,ht,he⟩ := flatten_correct f (.ac f a b)
  simp only [flatten,ite_true] at ht
  have hp := order.perm (flatten f a ++ flatten f b)
  rw [h] at hp
  exact (decode_perm f hp _ t rfl ht).trans he

private theorem join_canonical [DecidableEq sig.ACSym] {le : Term sig → Term sig → Prop} (order : Ordering le) (f : sig.ACSym)
    {a b : Term sig} (ha : Canonical le a) (hb : Canonical le b) : Canonical le (join order f a b) := by
  obtain ⟨x,y,xs,h,hj⟩ := join_spec order f a b
  rw [hj]
  have hp := order.perm (flatten f a ++ flatten f b)
  have hs := order.ordered (flatten f a ++ flatten f b)
  rw [h] at hp hs
  have each (t) (ht : t ∈ x::y::xs) := (List.mem_append.mp (hp.mem_iff.mp ht)).elim
    (ha.factors f t) (hb.factors f t)
  exact Canonical.ac f (fun t ht => (each t ht).1) (fun t ht => (each t ht).2) hs

/-- Bottom-up smart construction suffices. Sorting of AC operands is described
by its result rather than by a specific comparison algorithm. -/
def normalize [DecidableEq sig.ACSym] (le : Term sig → Term sig → Prop) [DecidableRel le]
    (order : Ordering le) : Term sig → Term sig
  | .free f xs => .free f (fun i => normalize le order (xs i))
  | .comm f a b =>
    let l := normalize le order a
    let r := normalize le order b
    if le l r then .comm f l r else .comm f r l
  | .ac f a b => join order f (normalize le order a) (normalize le order b)
  | t => t

theorem normalize_equiv [DecidableEq sig.ACSym] {le : Term sig → Term sig → Prop} [DecidableRel le]
    (order : Ordering le) (t : Term sig) : EquivB (normalize le order t) t := by
  induction t with
  | free f xs ih => exact .free f _ _ ih
  | comm f a b ha hb =>
    simp only [normalize]
    split
    · exact .comm_congr f ha hb
    · exact (EquivB.comm_swap ..).trans (.comm_congr f ha hb)
  | ac f _ _ ha hb => exact (join_equiv order f _ _).trans (.ac_congr f ha hb)
  | _ => exact .refl _

theorem normalize_canonical [DecidableEq sig.ACSym] {le : Term sig → Term sig → Prop} [DecidableRel le]
    (order : Ordering le) (total : ∀ a b, le a b ∨ le b a) {t : Term sig} (h : t.Ground) :
    Canonical le (normalize le order t) := by
  induction t with
  | var v => exact False.elim (h v rfl)
  | atom a => exact .atom a
  | free f ch ih => exact .free f (fun i => ih i (fun v hv => h v ⟨i,hv⟩))
  | comm f a b ia ib =>
    have l := ia (fun v hv => h v (Or.inl hv))
    have r := ib (fun v hv => h v (Or.inr hv))
    simp only [normalize]
    split
    · next lr => exact .comm f l r lr
    · next lr => exact .comm f r l ((total _ _).resolve_left lr)
  | ac f a b ia ib =>
    exact join_canonical order f (ia (fun v hv => h v (Or.inl hv))) (ib (fun v hv => h v (Or.inr hv)))

/-- Query-local structural identities of normalized ground terms faithfully
represent the complete B-classes, independently of nesting depth. -/
theorem normalize_eq_iff [DecidableEq sig.ACSym] {le : Term sig → Term sig → Prop} [DecidableRel le]
    (order : Ordering le) (total : ∀ a b, le a b ∨ le b a)
    (anti : ∀ a b, le a b → le b a → a = b) {a b : Term sig} (ha : a.Ground) (hb : b.Ground) :
    normalize le order a = normalize le order b ↔ EquivB a b := by
  have ea := normalize_equiv order a
  have eb := normalize_equiv order b
  exact ⟨fun eq => ea.symm.trans (eq ▸ eb), fun e =>
    (normalize_canonical order total ha).unique anti (normalize_canonical order total hb)
      (ea.trans (e.trans eb.symm))⟩

theorem cancel {kernel} (ok : CommonCancellation.Correct kernel) (f : sig.ACSym)
    (le : Term sig → Term sig → Prop) (anti : ∀ a b, le a b → le b a → a = b)
    (d : UInt64 → Term sig) (fixed subject : Array UInt64)
    (closed : ∀ i ∈ fixed.toList ++ subject.toList, Canonical le (d i) ∧ CompoundOffset.Fixed f (d i))
    (ids : ∀ i ∈ fixed.toList, ∀ j ∈ subject.toList, d i = d j → i = j) :
    ∃ missing rest : List UInt64, kernel fixed subject = #[missing.toArray, rest.toArray] ∧
      ∀ (pattern extra : List (Term sig)), pattern.Perm (fixed.toList.map d ++ extra) →
      ∀ σ : Substitution sig, ACResidual.Holds f σ pattern (subject.toList.map d) ↔
        missing = [] ∧ ACResidual.Holds f σ extra (rest.map d) :=
  OpenMatchCancellation.cancel_factors ok f d fixed subject
    (fun i hi => ⟨(closed i hi).1.ground,alien_factor f (closed i hi).2⟩)
    (fun i hi j hj he => ids i hi j hj ((closed i (List.mem_append_left _ hi)).1.unique anti
      (closed j (List.mem_append_right _ hj)).1 he))

/-- Only the closed pattern occurrences receive cancellation IDs. Open children
remain intact for the recursive matcher. -/
structure CancelLayout [DecidableEq sig.ACSym] (f : sig.ACSym) (p t : Term sig) where
  le : Term sig → Term sig → Prop
  anti : ∀ a b, le a b → le b a → a = b
  d : UInt64 → Term sig
  fixed : Array UInt64
  subject : Array UInt64
  extra : List (Term sig)
  closed : ∀ i ∈ fixed.toList ++ subject.toList, Canonical le (d i) ∧ CompoundOffset.Fixed f (d i)
  ids : ∀ i ∈ fixed.toList, ∀ j ∈ subject.toList, d i = d j → i = j
  pattern : (flatten f p).Perm (fixed.toList.map d ++ extra)
  target : (flatten f t).Perm (subject.toList.map d)

private theorem ground_subject (f : sig.ACSym) (xs ys : List (Term sig))
    (h : ∀ y ∈ ys, y.Ground) (σ : Substitution sig) :
    OpenMatch.Holds f xs ys σ ↔ ACResidual.Holds f σ xs ys := by
  rw [OpenMatch.holds_iff, ACResidual.holds_iff]
  have e : ys.flatMap (fun t => Cancellation.flatten f (σ.apply t)) =
      ys.flatMap (Cancellation.flatten f) := by
    rw [List.flatMap_def, List.flatMap_def]
    exact congrArg List.flatten (List.map_congr_left fun y hy => congrArg _ ((h y hy).apply_eq σ))
  rw [e]

private theorem flatten_match [DecidableEq sig.ACSym] (f : sig.ACSym) (p t : Term sig) (σ : Substitution sig) :
    EquivB (σ.apply p) t ↔ OpenMatch.Holds f (flatten f p) (flatten f t) σ := by
  obtain ⟨p', hp, ep⟩ := flatten_correct f p
  obtain ⟨t', ht, et⟩ := flatten_correct f t
  simp only [OpenMatch.Holds, OpenMatch.residual, hp, ht, Option.some.injEq, exists_eq_left',
    Matching.Matches, List.mem_singleton, forall_eq]
  exact ⟨fun e => (ep.subst σ.image).trans (e.trans et.symm),
    fun e => (ep.subst σ.image).symm.trans (e.trans et)⟩

private theorem rows_eq {a b c d : List UInt64}
    (h : #[a.toArray,b.toArray] = #[c.toArray,d.toArray]) : a = c ∧ b = d := by
  have rows := congrArg (fun rows : Array (Array UInt64) => rows.toList.map Array.toList) h
  simpa using rows

/-- With the two rows actually returned by the checked cancellation kernel, a
missing closed factor rules out a match; otherwise exactly the residual
directional matching problem remains. -/
theorem CancelLayout.run_iff [DecidableEq sig.ACSym] {f : sig.ACSym} {p t : Term sig}
    (l : CancelLayout f p t) {kernel} (ok : CommonCancellation.Correct kernel)
    (missing rest : List UInt64) (ran : kernel l.fixed l.subject = #[missing.toArray,rest.toArray])
    (σ : Substitution sig) :
    EquivB (σ.apply p) t ↔ missing = [] ∧ OpenMatch.Holds f l.extra (rest.map l.d) σ := by
  obtain ⟨left, right, out, eq⟩ := cancel ok f l.le l.anti l.d l.fixed l.subject l.closed l.ids
  obtain ⟨rfl, rfl⟩ := rows_eq (ran.symm.trans out)
  obtain ⟨common, left', right', out', _, rhs, _⟩ := ok l.fixed l.subject
  obtain ⟨rfl, rfl⟩ := rows_eq (out.symm.trans out')
  have subGround (i) (hi : i ∈ l.subject.toList) := (l.closed i (List.mem_append_right _ hi)).1.ground
  have groundMap (is : List UInt64) (sub : is ⊆ l.subject.toList) : ∀ y ∈ is.map l.d, y.Ground := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
    exact subGround i (sub hi)
  rw [flatten_match f p t σ]
  have perm : OpenMatch.Holds f (flatten f p) (flatten f t) σ ↔
      OpenMatch.Holds f (flatten f p) (l.subject.toList.map l.d) σ := by
    rw [OpenMatch.holds_iff, OpenMatch.holds_iff]
    have h := l.target.flatMap_right (Cancellation.flatten f)
    exact ⟨fun e => e.trans h, fun e => e.trans h.symm⟩
  rw [perm, ground_subject _ _ _ (groundMap _ (fun _ h => h)) σ, eq _ _ l.pattern σ]
  rw [ground_subject _ _ _ (groundMap _ (fun _ hi => rhs.mem_iff.mpr (List.mem_append_right common hi))) σ]

end Tamarin.CanonicalTree
