import Tamarin.ACMatchProfiles
import Tamarin.MatchPrefilter

/-! The incidence test uses equality of the caller's factor identifiers.
Relate those identifiers to the structural congruence classes of the actual
equations, including subject factors that contain pattern variable names. -/
namespace Tamarin.OpenMatch.Profiles

variable {α : Type} [DecidableEq α] {sig : Signature}

def Possible (keys : List Variable) (atoms : List α) (rows : List (List Variable × List α)) : Prop :=
  (∀ row ∈ rows, row.2 ⊆ atoms) ∧
  (∀ b ∈ atoms, ∃ a ∈ keys, profile (rows.map Prod.fst) a = profile (rows.map Prod.snd) b) ∧
  ∀ group, (keys.filter (fun a => profile (rows.map Prod.fst) a == group)).length ≤
    (atoms.filter (fun b => profile (rows.map Prod.snd) b == group)).length

private theorem factor_of_mem_flatten [DecidableEq sig.ACSym] (f : sig.ACSym) (t : Term sig) :
    ∀ u ∈ ACRepresentation.flatten f t, Cancellation.flatten f u = [Cancellation.classOf u] := by
  induction t with
  | var | atom | free | comm => simp [ACRepresentation.flatten,Cancellation.flatten]
  | ac g a b ia ib =>
    by_cases same : f = g
    · simpa [ACRepresentation.flatten,same] using fun u (h : u ∈ ACRepresentation.flatten f a ∨
          u ∈ ACRepresentation.flatten f b) => h.elim (ia u) (ib u)
    · simp [ACRepresentation.flatten,Cancellation.flatten,same]

/-- A failed profile or capacity check rules out every simultaneous match.
The caller may use any factor identifiers that distinguish B classes on the
observed subjects. Their order and all identifiers outside these equations
are irrelevant. -/
theorem possible_of_matches [DecidableEq sig.ACSym] (f : sig.ACSym) (problem : Problem sig)
    (layout : Equation sig → List Variable × List α) (term : α → Term sig)
    (pivot : Equation sig) (used : pivot ∈ problem) (distinct : (layout pivot).2.Nodup)
    (covered : ∀ e ∈ problem, (layout e).1 ⊆ (layout pivot).1)
    (left : ∀ e ∈ problem, ((layout e).1.map Term.var).Perm (ACRepresentation.flatten f e.lhs))
    (right : ∀ e ∈ problem, ((layout e).2.map term).Perm (ACRepresentation.flatten f e.rhs))
    (reflects : ∀ e ∈ problem, ∀ a ∈ (layout e).2, ∀ d ∈ problem, ∀ b ∈ (layout d).2,
      EquivB (term a) (term b) → a = b)
    (σ : Substitution sig) (matched : Matching.Matches problem σ) :
    Possible (layout pivot).1 (layout pivot).2 (problem.map layout) := by
  classical
  let cls (a : α) := Cancellation.classOf (term a)
  let source := fun k => Cancellation.flatten f (σ.image k)
  let Live (a : α) := ∃ e ∈ problem, a ∈ (layout e).2
  let identify (c : Cancellation.Class sig) : List α :=
    if h : ∃ a, Live a ∧ cls a = c then [h.choose] else []
  have back (a : α) (ha : Live a) : identify (cls a) = [a] := by
    have exists_key : ∃ b, Live b ∧ cls b = cls a := ⟨a,ha,rfl⟩
    obtain ⟨e,he,hm⟩ := exists_key.choose_spec.1
    obtain ⟨d,hd,hn⟩ := ha
    have eq := reflects e he exists_key.choose hm d hd a hn (Quotient.exact exists_key.choose_spec.2)
    simp [identify,exists_key,eq]
  have source_eq (e : Equation sig) (he : e ∈ problem) :
      ((layout e).1.flatMap source).Perm ((layout e).2.map cls) := by
    have run := (OpenMatch.layout_iff f σ e.lhs e.rhs _ _ (left e he) (right e he)).mp (matched e he)
    have perm := coordinate f (layout e).1 ((layout e).2.map term) (by
      rintro _ ht
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
      exact factor_of_mem_flatten f e.rhs _ ((right e he).subset (List.mem_map.mpr ⟨a,ha,rfl⟩))) σ run
    simpa [cls,source,List.map_map,Function.comp_def] using perm
  let im (k : Variable) := (source k).flatMap identify
  have transported (e : Equation sig) (he : e ∈ problem) : ((layout e).1.flatMap im).Perm (layout e).2 := by
    have perm := (source_eq e he).flatMap_right identify
    have ret (ids : List α) (present : ∀ a ∈ ids, Live a) : (ids.map cls).flatMap identify = ids := by
      induction ids with
      | nil => rfl
      | cons a tail ih =>
        simp [back a (present a List.mem_cons_self),ih (fun b hb => present b (List.mem_cons_of_mem _ hb))]
    rw [ret _ (fun a ha => ⟨e,he,ha⟩)] at perm
    simpa [List.flatMap_assoc,im] using perm
  apply necessary _ _ _ im _ distinct (transported pivot used)
  · intro row hr
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact covered e he
  · intro row hr
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hr
    exact transported e he
  · intro k hk
    obtain ⟨c,hc⟩ : ∃ c, c ∈ source k := by
      cases h : source k with
      | cons c cs => exact ⟨c,List.mem_cons_self⟩
      | nil =>
        have impossible := Cancellation.fold_flatten f (σ.image k)
        rw [show Cancellation.flatten f (σ.image k) = [] from h] at impossible
        cases impossible
    have mem := (source_eq pivot used).subset (List.mem_flatMap.mpr ⟨k,hk,hc⟩)
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp mem
    have belongs : a ∈ im k := List.mem_flatMap.mpr ⟨cls a,hc,by simp [back a ⟨pivot,used,ha⟩]⟩
    intro empty
    simp [empty] at belongs

/-- Rust can use the structural term itself as the factor key on canonical
C/AC representatives. Freezing the subject makes this criterion applicable
to open terms. Restricting substitutions by an existing seed can only
further restrict the set excluded by this refutation. -/
theorem refutes_canonical [DecidableEq sig.ACSym] [DecidableEq (Term sig)] (f : sig.ACSym)
    (problem : Problem sig) (keys : Equation sig → List Variable) (pivot : Equation sig)
    (used : pivot ∈ problem) (distinct : (ACRepresentation.flatten f pivot.rhs).Nodup)
    (covered : ∀ e ∈ problem, keys e ⊆ keys pivot)
    (left : ∀ e ∈ problem, ((keys e).map Term.var).Perm (ACRepresentation.flatten f e.lhs))
    {le : Term (Matching.RigidSubject.frozenSig sig) → Term (Matching.RigidSubject.frozenSig sig) → Prop}
    (anti : ∀ a b, le a b → le b a → a = b)
    (canonical : ∀ e ∈ problem, ∀ t ∈ ACRepresentation.flatten f e.rhs,
      CanonicalTree.Canonical le (Matching.RigidSubject.freeze sig t))
    (failed : ¬ Possible (keys pivot) (ACRepresentation.flatten f pivot.rhs)
      (problem.map (fun e => (keys e, ACRepresentation.flatten f e.rhs)))) :
    ¬ ∃ σ, Matching.Matches problem σ := by
  rintro ⟨σ,sol⟩
  apply failed
  apply possible_of_matches f problem (fun e => (keys e, ACRepresentation.flatten f e.rhs))
    id pivot used distinct covered left _ _ σ sol
  · intro e _
    simp
  · intro e he a ha d hd b hb eq
    exact (Matching.Prefilter.canonical_eq_iff anti (canonical e he a ha) (canonical d hd b hb)).mp eq

end Tamarin.OpenMatch.Profiles
