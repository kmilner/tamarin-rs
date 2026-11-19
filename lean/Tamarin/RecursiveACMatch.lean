import Tamarin.CanonicalTree
import Tamarin.MatchingConjunction

/-! A completed directional search under arbitrarily nested free, C, and AC
heads. Each AC node chooses its own layout and word interner. Its selected
rigid children can themselves contain another partition search. -/
namespace Tamarin.RecursiveACMatch
open Matching NestedTreeMatch
variable {sig : Signature}

/-- The layout of one nonempty AC equation, after flattening at this symbol.
A child headed by a *different* AC symbol is a single rigid factor here.
Only distinct live equivalence classes need distinct word identities. -/
structure Layout [DecidableEq sig.ACSym] (f : sig.ACSym) (p t : Term sig) where
  rigid : List (Term sig)
  m : UInt64
  vars : Fin m.toNat → Variable
  occ : List (Fin m.toNat)
  subject : Nat → Term sig
  k : UInt64
  n : UInt64
  pack : (is : List Nat) → OpenMatchAdapter.Words (is.map subject)
  count : k.toNat = rigid.length
  used : ∀ i, i ∈ occ
  patternLayout : (rigid ++ occ.map (fun i => Term.var (vars i))).Perm (ACRepresentation.flatten f p)
  subjectLayout : ((List.range n.toNat).map subject).Perm (ACRepresentation.flatten f t)
  rigidHead : ∀ a ∈ rigid, CompoundOffset.Fixed f a
  subjectHead : ∀ i < n.toNat, CompoundOffset.Fixed f (subject i)
  le : Term sig → Term sig → Prop
  antisymmetric : ∀ a b, le a b → le b a → a = b
  canonical : ∀ i < n.toNat, CanonicalTree.Canonical le (subject i)

abbrev Cancellation := Array UInt64 → Array UInt64 → Array (Array UInt64)

abbrev Observation (sig : Signature) := Substitution sig → Prop

/-- Decoding a selection retains the same substitution in every recursive
child and in every row returned for the remaining variables. -/
def Layout.read [DecidableEq sig.ACSym] {f p t} (l : Layout (sig := sig) f p t)
    (flat : SortedMatch.Flat) (out : OpenMatchSelect.Packet)
    (child : Term sig → Term sig → Observation sig) (σ : Substitution sig) : Prop :=
  ∃ row ∈ OpenMatchSelect.decoded out,
    OpenMatchAdapter.ArmWith (fun r s => child r s σ) (fun is =>
      OpenMatchAdapter.Remainder flat f l.vars l.occ (is.map l.subject) (l.pack is) σ)
      l.subject l.rigid row

/-- A pair of empty residuals succeeds. Exactly one empty side fails.
Only two nonempty products are handed to the next matching step. -/
def residualRead (f : sig.ACSym) (left right : List (Term sig))
    (child : Term sig → Term sig → Observation sig) (σ : Substitution sig) : Prop :=
  match ACRepresentation.decode f left, ACRepresentation.decode f right with
  | none, none => True
  | some p, some t => child p t σ
  | _, _ => False

private theorem residual_iff (f : sig.ACSym) (left right : List (Term sig))
    (child : Term sig → Term sig → Observation sig) (σ : Substitution sig)
    (ih : ∀ p t, ACRepresentation.decode f left = some p →
      ACRepresentation.decode f right = some t → (child p t σ ↔ EquivB (σ.apply p) t)) :
    residualRead f left right child σ ↔ OpenMatch.Holds f left right σ := by
  cases hp : ACRepresentation.decode f left <;> cases ht : ACRepresentation.decode f right <;>
    simp [residualRead, OpenMatch.Holds, OpenMatch.residual, hp, ht, Matches, ih]

/-- The finite tree of completed kernel calls. Each constructor fixes its
own observable predicate. A declined AC selection has no completed node. -/
inductive Search [DecidableEq sig.ACSym] (select : OpenMatchSelect.Kernel)
    (flat : SortedMatch.Flat) (orient : Orient) (cancel : Cancellation) (enc : Encoding sig) :
    Term sig → Term sig → Observation sig → Prop where
  | var (v : Variable) (t : Term sig) : Search select flat orient cancel enc (.var v) t
      (fun σ => Subsort t.rootSort v.sort ∧ EquivB (σ.image v) t)
  | atom (a : sig.Atom) : Search select flat orient cancel enc (.atom a) (.atom a) (fun _ => True)
  | clash (p t : Term sig) (rigid : ∀ v, p ≠ .var v)
      (different : (headModel sig).eval Head.var p ≠ (headModel sig).eval Head.var t) :
      Search select flat orient cancel enc p t (fun _ => False)
  | free (f : sig.FreeSym) {ps ts} {read : Fin (sig.arity f) → Observation sig}
      (children : ∀ i, Search select flat orient cancel enc (ps i) (ts i) (read i)) :
      Search select flat orient cancel enc (.free f ps) (.free f ts) (fun σ => ∀ i, read i σ)
  | comm (f : sig.CSym) (a b c d : Term sig) (left : c.Ground) (right : d.Ground)
      {ac bd ad bc : Observation sig}
      (direct₁ : Commutative.Selected (mask orient enc ⟨f,a,b,c,d,[]⟩) false →
        Search select flat orient cancel enc a c ac)
      (direct₂ : Commutative.Selected (mask orient enc ⟨f,a,b,c,d,[]⟩) false →
        Search select flat orient cancel enc b d bd)
      (crossed₁ : Commutative.Selected (mask orient enc ⟨f,a,b,c,d,[]⟩) true →
        Search select flat orient cancel enc a d ad)
      (crossed₂ : Commutative.Selected (mask orient enc ⟨f,a,b,c,d,[]⟩) true →
        Search select flat orient cancel enc b c bc) :
      Search select flat orient cancel enc (.comm f a b) (.comm f c d) (fun σ =>
        let m := mask orient enc ⟨f,a,b,c,d,[]⟩
        (Commutative.Selected m false ∧ ac σ ∧ bd σ) ∨ (Commutative.Selected m true ∧ ad σ ∧ bc σ))
  | ac {f p t} (l : Layout (sig := sig) f p t) (out : OpenMatchSelect.Packet)
      (ran : select l.k l.n = some out) (child : Term sig → Term sig → Observation sig)
      (children : ∀ r ∈ l.rigid, ∀ i < l.n.toNat,
        Search select flat orient cancel enc r (l.subject i) (child r (l.subject i))) :
      Search select flat orient cancel enc p t (l.read flat out child)

  | collectors {f p t} (l : Layout (sig := sig) f p t) (noRigid : l.rigid = []) :
      Search select flat orient cancel enc p t (fun σ =>
        let indices := List.range l.n.toNat
        OpenMatchAdapter.Remainder flat f l.vars l.occ (indices.map l.subject) (l.pack indices) σ)

  | cardinality (f : sig.ACSym) (p t : Term sig) (ps ts : List (Term sig))
      (pl : ps.Perm (ACRepresentation.flatten f p)) (sl : ts.Perm (ACRepresentation.flatten f t))
      (target : ∀ a ∈ ts, CompoundOffset.Fixed f a)
      (clash : ts.length < ps.length ∨
        ((∀ a ∈ ps, CompoundOffset.Fixed f a) ∧ ps.length ≠ ts.length)) :
      Search select flat orient cancel enc p t (fun _ => False)
  | cancelFixed {f p t} (l : CanonicalTree.CancelLayout (sig := sig) f p t)
      (missing rest : List UInt64)
      (ran : cancel l.fixed l.subject = #[missing.toArray,rest.toArray])
      (child : Term sig → Term sig → Observation sig)
      (remaining : ∀ pp tt, missing = [] → ACRepresentation.decode f l.extra = some pp →
        ACRepresentation.decode f (rest.map l.d) = some tt →
        Search select flat orient cancel enc pp tt (child pp tt)) :
      Search select flat orient cancel enc p t (fun σ =>
        missing = [] ∧ residualRead f l.extra (rest.map l.d) child σ)

/-- The proof is by induction on the search tree, independent of the number
of nested AC nodes or the order of alternatives. -/
theorem search_iff {select flat orient cancel} (sel : OpenMatchSelect.Correct select)
    (part : CompoundPartitions.Correct flat) (comm : Commutative.Correct orient)
    (can : CommonCancellation.Correct cancel)
    [DecidableEq sig.ACSym] {enc : Encoding sig} {p t read}
    (tree : Search select flat orient cancel enc p t read) (σ : Substitution sig) :
    read σ ↔ EquivB (σ.apply p) t := by
  induction tree with
  | var v t => exact ⟨And.right, fun h => ⟨Term.rootSort_equiv h ▸ Term.rootSort_le (σ.sorted v),h⟩⟩
  | atom a => exact ⟨fun _ => .refl _,fun _ => trivial⟩
  | clash p t rigid different =>
    refine ⟨False.elim, fun h => different ?_⟩
    cases p with
    | var v => exact False.elim (rigid v rfl)
    | atom | free | comm | ac => exact h.head_eq
  | free f _ ih =>
    change (∀ i, _) ↔ EquivB (.free f _) (.free f _)
    rw [Matching.free_equiv_iff]
    exact forall_congr' ih
  | comm f a b c d left right _ _ _ _ ia ib ic id =>
    rw [NestedTreeMatch.select_iff orient comm enc f a b c d left right σ]
    exact or_congr (and_congr_right fun h => and_congr (ia h) (ib h))
      (and_congr_right fun h => and_congr (ic h) (id h))
  | ac l out ran child _ ih =>
    have complete := OpenMatchAdapter.compose sel part _ _ _ l.rigid l.m l.vars l.occ l.subject l.k l.n
      l.pack l.count l.used l.patternLayout l.subjectLayout (fun r hr => AtomicACPair.atomic_of_fixed _ _ (l.rigidHead r hr))
      (fun i hi => (l.canonical i hi).ground) (fun i hi => CanonicalTree.alien_factor _ (l.subjectHead i hi))
      (fun i hi j hj => (l.canonical i hi).unique l.antisymmetric (l.canonical j hj)) out ran [] σ (fun r s => child r s σ) ih
    simpa only [Layout.read, Matches,List.forall_mem_cons,List.not_mem_nil,false_implies,
      implies_true,and_true,true_and] using complete.symm

  | collectors l empty =>
    have pl := l.patternLayout
    rw [empty, List.nil_append] at pl
    rw [OpenMatch.layout_iff _ σ _ _ _ _ pl l.subjectLayout]
    apply Iff.symm
    apply OpenMatchAdapter.remainder_iff part _ _ _ l.used
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact (l.canonical i (List.mem_range.mp hi)).ground
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      exact CanonicalTree.alien_factor _ (l.subjectHead i (List.mem_range.mp hi))
    · intro t ht u hu
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hu
      exact (l.canonical i (List.mem_range.mp hi)).unique l.antisymmetric
        (l.canonical j (List.mem_range.mp hj))

  | cardinality f p t ps ts pl sl target clash =>
    refine ⟨False.elim, fun e => ?_⟩
    have h := (OpenMatch.layout_iff f σ p t ps ts pl sl).mp e
    rcases clash with tooMany | ⟨rigid,unequal⟩
    · exact (Nat.not_le_of_lt tooMany) (OpenMatchAdapter.long_enough f σ ps ts
        (fun a ha => CanonicalTree.alien_factor f (target a ha)) h)
    · exact unequal (OpenMatch.rigid_length f σ ps ts
        (fun a ha => AtomicACPair.atomic_of_fixed f a (rigid a ha))
        (fun a ha => AtomicACPair.atomic_of_fixed f a (target a ha)) h)
  | cancelFixed l missing rest ran child _ ih =>
    rw [l.run_iff can missing rest ran σ]
    exact and_congr_right fun h => residual_iff _ _ _ child σ (fun p t => ih p t h)

/-- Each completed recursive search preserves exactly the original equation
and its pending context, for any representatives chosen during preparation. -/
def Correct (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : Orient) (cancel : Cancellation) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] {enc : Encoding s} {p t read},
    Search select flat orient cancel enc p t read → ∀ (rawP rawT : Term s),
    EquivB p rawP → EquivB t rawT → ∀ (pending : Problem s) (σ : Substitution s),
      Matches (⟨rawP,rawT⟩ :: pending) σ ↔ read σ ∧ Matches pending σ

theorem correct {select flat orient cancel} (sel : OpenMatchSelect.Correct select)
    (part : CompoundPartitions.Correct flat) (comm : Commutative.Correct orient)
    (can : CommonCancellation.Correct cancel) :
    Correct select flat orient cancel := by
  intro sig _ enc p t read tree rawP rawT left right pending σ
  rw [NestedTreeMatch.prepare_iff left right, search_iff sel part comm can tree σ]
  simp only [Matches,List.forall_mem_cons]

/-- Classify the entire conjunction, including variables observed both by a
forced capture and by one or more recursive searches. Every accepted
continuation must agree with one initial seed on its entire observed domain. -/
def SeededCorrect (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : Orient) (cancel : Cancellation) : Prop :=
  ∀ {sig : Signature} [DecidableEq sig.ACSym] {enc : Encoding sig}
    (captures pending : Problem sig) (seeds : List (Substitution sig)),
    Complete captures (fun _ => True) seeds →
    ∀ (read : Equation sig → Substitution sig → Prop),
    (∀ e ∈ pending, ∃ p t, EquivB p e.lhs ∧ EquivB t e.rhs ∧
      Search select flat orient cancel enc p t (read e)) →
    ∀ σ : Substitution sig, Matches (captures ++ pending) σ ↔
      (∃ seed ∈ seeds, Substitution.AgreesOn (Observed captures) σ seed) ∧
      ∀ e ∈ pending, read e σ

private theorem seed_agreement {caps : Problem sig} {seeds} (hc : Complete caps (fun _ => True) seeds)
    (σ : Substitution sig) : Matches caps σ ↔ ∃ seed ∈ seeds, Substitution.AgreesOn (Observed caps) σ seed := by
  constructor
  · intro only
    -- Other pending observations may bind variables outside the capture domain.
    let restricted := merge caps σ Substitution.identity
    have agrees : Substitution.AgreesOn (Observed caps) σ restricted := by
      intro v h; simp [restricted,merge,h]; exact .refl _
    have scope : Scoped caps (fun _ => True) restricted := by
      intro v h
      have off : ¬Observed caps v := fun m => h ⟨m,trivial⟩
      simp [restricted,merge,off,Substitution.identity]
    obtain ⟨seed,hs,agree⟩ := hc.covers restricted
      (matches_of_agrees only (fun v h => (agrees v h).symm)) scope
    exact ⟨seed,hs,fun v h => (agrees v h).trans (agree v h)⟩
  · rintro ⟨seed,hs,agree⟩
    exact matches_of_agrees (hc.sound seed hs).1 agree

theorem seeded_correct {select flat orient cancel} (checked : Correct select flat orient cancel) :
    SeededCorrect select flat orient cancel := by
  intro sig _ enc caps pending seeds hc read searches σ
  have rest (e) (he : e ∈ pending) : EquivB (σ.apply e.lhs) e.rhs ↔ read e σ := by
    obtain ⟨p,t,hp,ht,tree⟩ := searches e he
    simpa [Matches] using checked tree e.lhs e.rhs hp ht [] σ
  constructor
  · intro all
    have only (e) (h : e ∈ caps) := all e (List.mem_append_left _ h)
    obtain ⟨seed,hs,agree⟩ := (seed_agreement hc σ).mp only
    exact ⟨⟨seed,hs,agree⟩,
      fun e h => (rest e h).mp (all e (List.mem_append_right _ h))⟩
  · rintro ⟨⟨seed,hs,agree⟩,found⟩ e he
    exact (List.mem_append.mp he).elim ((matches_of_agrees (hc.sound seed hs).1 agree) e)
      (fun h => (rest e h).mpr (found e h))

/-- Forced ground images may replace every occurrence in the remaining
patterns before the recursive search. The original subjects and substitution
domain are preserved even when specialization removes all uses of a capture. -/
def SpecializedSeedCorrect (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : Orient) (cancel : Cancellation) : Prop :=
  ∀ {sig : Signature} [DecidableEq sig.ACSym] {enc : Encoding sig}
    (captures pending : Problem sig) (seeds : List (Substitution sig)),
    (∀ e ∈ captures, e.rhs.Ground) → Complete captures (fun _ => True) seeds →
    ∀ (read : Substitution sig → Equation sig → Substitution sig → Prop),
    (∀ seed ∈ seeds, ∀ e ∈ pending, ∃ p t, EquivB p (seed.apply e.lhs) ∧ EquivB t e.rhs ∧
      Search select flat orient cancel enc p t (read seed e)) →
    ∀ σ : Substitution sig, Matches (captures ++ pending) σ ↔
      ∃ seed ∈ seeds, Substitution.AgreesOn (Observed captures) σ seed ∧ ∀ e ∈ pending, read seed e σ

theorem specialized_seed_correct {select flat orient cancel} (checked : Correct select flat orient cancel) :
    SpecializedSeedCorrect select flat orient cancel := by
  intro sig _ enc caps pending seeds ground hc read searches σ
  have rest {seed} (hs : seed ∈ seeds) (agrees : Substitution.AgreesOn (Observed caps) σ seed)
      (e) (he : e ∈ pending) : EquivB (σ.apply e.lhs) e.rhs ↔ read seed e σ := by
    obtain ⟨matched,within⟩ := hc.sound seed hs
    have images := ground_images_of_solves ground ((ground_subjects_iff caps ground seed).mp matched)
    have same : EquivB (σ.apply e.lhs) (σ.apply (seed.apply e.lhs)) := by
      rw [← Substitution.apply_compose]
      apply Term.subst_equiv
      intro v _
      change EquivB (σ.image v) (σ.apply (seed.image v))
      by_cases seen : Observed caps v
      · obtain ⟨c,hm,hv⟩ := seen
        rw [(images v ⟨c,hm,Or.inl hv⟩).apply_eq]
        exact agrees v ⟨c,hm,hv⟩
      · rw [within v (fun h => seen h.1)]
        exact .refl _
    obtain ⟨p,t,hp,ht,tree⟩ := searches seed hs e he
    have prepared : EquivB (σ.apply (seed.apply e.lhs)) e.rhs ↔ read seed e σ := by
      simpa [Matches] using checked tree (seed.apply e.lhs) e.rhs hp ht [] σ
    exact ⟨fun h => prepared.mp (same.symm.trans h),fun h => same.trans (prepared.mpr h)⟩
  constructor
  · intro all
    obtain ⟨seed,hs,agrees⟩ := (seed_agreement hc σ).mp (fun e h => all e (List.mem_append_left _ h))
    exact ⟨seed,hs,agrees,fun e h => (rest hs agrees e h).mp (all e (List.mem_append_right _ h))⟩
  · rintro ⟨seed,hs,agrees,found⟩ e he
    exact (List.mem_append.mp he).elim ((matches_of_agrees (hc.sound seed hs).1 agrees) e)
      (fun h => (rest hs agrees e h).mpr (found e h))

end Tamarin.RecursiveACMatch
