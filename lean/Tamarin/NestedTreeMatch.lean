import Tamarin.OpenMatchAdapter
import Tamarin.OpenMatchCancellation
import Tamarin.Commutative

/-! Directional matching under free and binary C heads. Each nested C invocation
may choose its own head interner. Sorting a ground C pair gives a representative
that can be interned by structural equality. -/
namespace Tamarin.NestedTreeMatch

variable {sig : Signature}

inductive Pattern : Term sig → Prop where
  | var (v : Variable) : Pattern (.var v)
  | atom (a : sig.Atom) : Pattern (.atom a)
  | free (f : sig.FreeSym) {xs} (children : ∀ i, Pattern (xs i)) : Pattern (.free f xs)
  | comm (f : sig.CSym) {a b} (left : Pattern a) (right : Pattern b) : Pattern (.comm f a b)

inductive Canonical (le : Term sig → Term sig → Prop) : Term sig → Prop where
  | atom (a : sig.Atom) : Canonical le (.atom a)
  | free (f : sig.FreeSym) {xs} (children : ∀ i, Canonical le (xs i)) : Canonical le (.free f xs)
  | comm (f : sig.CSym) {a b} (left : Canonical le a) (right : Canonical le b)
      (ordered : le a b) : Canonical le (.comm f a b)

theorem Canonical.ground {le} {t : Term sig} (h : Canonical le t) : t.Ground := by
  induction h with
  | atom => intro v; exact id
  | free _ _ ih => intro v ⟨i, hi⟩; exact ih i v hi
  | comm f _ _ _ hl hr => intro v hv; exact hv.elim (hl v) (hr v)

theorem Canonical.factor {le} {t : Term sig} (h : Canonical le t) (f : sig.ACSym) :
    Cancellation.flatten f t = [Cancellation.classOf t] := by cases h <;> rfl

/-- Rust may use its own total order on terms. Only antisymmetry enters the
identity proof since each admitted C pair is already ordered. -/
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
    rename_i left right first second rhsOrd
    rcases (Commutative.equiv_iff ..).mp same with ⟨l,r⟩ | ⟨l,r⟩
    · rw [ia first l,ib second r]
    · have e1 := ia second l
      have e2 := ib first r
      subst_vars
      rw [anti _ _ ord rhsOrd]

/-- Normalize just the C pairs when encoding ground factors. -/
def normalize (le : Term sig → Term sig → Prop) [DecidableRel le] : Term sig → Term sig
  | .free f xs => .free f (fun i => normalize le (xs i))
  | .comm f a b =>
    let l := normalize le a
    let r := normalize le b
    if le l r then .comm f l r else .comm f r l
  | .ac f a b => .ac f (normalize le a) (normalize le b)
  | t => t

theorem normalize_equiv (le : Term sig → Term sig → Prop) [DecidableRel le] (t : Term sig) :
    EquivB (normalize le t) t := by
  induction t with
  | free f xs ih => exact .free f _ _ ih
  | comm f a b ha hb =>
    simp only [normalize]
    split
    · exact .comm_congr f ha hb
    · exact (EquivB.comm_swap ..).trans (.comm_congr f ha hb)
  | ac f _ _ ha hb => exact .ac_congr f ha hb
  | _ => exact .refl _

theorem normalize_canonical (le : Term sig → Term sig → Prop) [DecidableRel le]
    (total : ∀ a b, le a b ∨ le b a) {t : Term sig} (p : Pattern t) (h : t.Ground) :
    Canonical le (normalize le t) := by
  induction p with
  | var v => exact False.elim (h v rfl)
  | atom a => exact .atom a
  | free f ch ih => exact .free f (fun i => ih i (fun v hv => h v ⟨i,hv⟩))
  | comm f _ _ ia ib =>
    have l := ia (fun v hv => h v (Or.inl hv))
    have r := ib (fun v hv => h v (Or.inr hv))
    simp only [normalize]
    split
    · next lr => exact .comm f l r lr
    · next lr => exact .comm f r l ((total _ _).resolve_left lr)

abbrev Orient := UInt64 → UInt64 → UInt64 → UInt64 → UInt8 → UInt8

/-- Each C node may intern its four rigid heads independently. The integer
priority can prune only under the checked orientation dominance hypotheses. -/
structure Encoding (sig : Signature) where
  key : Commutative.Query sig → Head sig → UInt64
  priority : (q : Commutative.Query sig) → UInt8
  valid : ∀ q, Commutative.Priority q (priority q)

def mask (run : Orient) (enc : Encoding sig) (q : Commutative.Query sig) : UInt8 :=
  let code := Commutative.headCode (enc.key q)
  run (code q.a) (code q.b) (code q.c) (code q.d) (enc.priority q)

/-- Interpret all variable occurrences with the same substitution. Selecting
an orientation constrains both children together. -/
def Reads (run : Orient) (enc : Encoding sig) (σ : Substitution sig) : Term sig → Term sig → Prop
  | .var v, t => Subsort t.rootSort v.sort ∧ EquivB (σ.image v) t
  | .atom a, .atom b => a = b
  | .free f xs, .free g ys => ∃ e : f = g, ∀ i, Reads run enc σ (xs i) (ys (e ▸ i))
  | .comm f a b, .comm g c d =>
    f = g ∧ let m := mask run enc ⟨f,a,b,c,d,[]⟩
            (Commutative.Selected m false ∧ Reads run enc σ a c ∧ Reads run enc σ b d) ∨
            (Commutative.Selected m true ∧ Reads run enc σ a d ∧ Reads run enc σ b c)
  | _,_ => False
termination_by structural p _ => p

theorem select_iff (run : Orient) (verified : Commutative.Correct run) (enc : Encoding sig)
    (f : sig.CSym) (a b c d : Term sig) (hc : c.Ground) (hd : d.Ground) (σ : Substitution sig) :
    EquivB (σ.apply (.comm f a b)) (.comm f c d) ↔
    let m := mask run enc ⟨f,a,b,c,d,[]⟩
    (Commutative.Selected m false ∧ EquivB (σ.apply a) c ∧ EquivB (σ.apply b) d) ∨
    (Commutative.Selected m true ∧ EquivB (σ.apply a) d ∧ EquivB (σ.apply b) c) := by
  let q : Commutative.Query sig := ⟨f,a,b,c,d,[]⟩
  have h := Commutative.run_solves verified q (enc.key q) _ (enc.valid q) σ
  have ground : (Term.comm f c d).Ground := fun v hv => hv.elim (hc v) (hd v)
  have prob : q.problem.Solves σ ↔ EquivB (σ.apply (.comm f a b)) (.comm f c d) := by
    simp [q,Commutative.Query.problem,Problem.Solves,ground.apply_eq]
  dsimp only at h
  rw [← prob,h]
  change (∃ i ∈ Commutative.orientations (mask run enc q), (q.branch i).Solves σ) ↔ _
  simp only [Commutative.mem_orientations, Bool.exists_bool]
  simp [q,Commutative.Query.branch,Problem.Solves,hc.apply_eq,hd.apply_eq]

theorem reads_iff {run : Orient} (verified : Commutative.Correct run) (enc : Encoding sig)
    {le} {p t : Term sig} (hp : Pattern p) (ht : Canonical le t) (σ : Substitution sig) :
    Reads run enc σ p t ↔ EquivB (σ.apply p) t := by
  induction hp generalizing t with
  | var v =>
    exact ⟨And.right, fun h => ⟨Term.rootSort_equiv h ▸ Term.rootSort_le (σ.sorted v),h⟩⟩
  | atom a =>
    cases ht with
    | atom b => exact ⟨fun e => e ▸ .refl _,fun h => Head.atom.inj h.head_eq⟩
    | free | comm => exact ⟨False.elim,fun h => by cases h.head_eq⟩
  | free f _ ih =>
    cases ht with
    | atom | comm => exact ⟨False.elim,fun h => by cases h.head_eq⟩
    | free g children =>
      constructor
      · rintro ⟨rfl,all⟩
        exact (Matching.free_equiv_iff ..).mpr (fun i => (ih i (children i)).mp (all i))
      · intro same
        obtain rfl := Head.free.inj same.head_eq
        exact ⟨rfl,fun i => (ih i (children i)).mpr ((Matching.free_equiv_iff ..).mp same i)⟩
  | comm f _ _ il ir =>
    cases ht with
    | atom | free => exact ⟨False.elim,fun h => by cases h.head_eq⟩
    | comm g left right order =>
      by_cases h : f = g
      · subst g
        simp only [Reads,true_and,il left,ir right,il right,ir left]
        exact (select_iff _ verified enc _ _ _ _ _ left.ground right.ground σ).symm
      · exact ⟨fun pair => False.elim (h pair.1),fun he => False.elim (h (Head.comm.inj he.head_eq))⟩

/-- Two AC images of a shared variable agree exactly when their complete
canonical factors agree as multisets. The factors may contain C symbols. -/
theorem product_iff (f : sig.ACSym) {le : Term sig → Term sig → Prop}
    (anti : ∀ a b, le a b → le b a → a = b) (a b : Term sig) (xs ys : List (Term sig))
    (left : ∀ t ∈ a :: xs, Canonical le t) (right : ∀ t ∈ b :: ys, Canonical le t) :
    EquivB (ACRepresentation.fold f a xs) (ACRepresentation.fold f b ys) ↔ (a :: xs).Perm (b :: ys) := by
  classical
  let repr (c : Cancellation.Class sig) : Term sig :=
    if h : ∃ t, Canonical le t ∧ Cancellation.classOf t = c then h.choose else a
  have recover {t : Term sig} (h : Canonical le t) : repr (Cancellation.classOf t) = t := by
    have live : ∃ u, Canonical le u ∧ Cancellation.classOf u = Cancellation.classOf t := ⟨t,h,rfl⟩
    exact (dite_eq_left live).trans (Canonical.unique anti live.choose_spec.1 h (Quotient.exact live.choose_spec.2))
  have parts (ls : List (Term sig)) (h : ∀ t ∈ ls, Canonical le t) :
      ls.flatMap (Cancellation.flatten f) = ls.map Cancellation.classOf := by
    induction ls with
    | nil => rfl
    | cons t ts ih =>
      simp only [List.flatMap_cons,List.map_cons,(h t List.mem_cons_self).factor f,
        List.singleton_append,ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]
  have invert (ls : List (Term sig)) (h : ∀ t ∈ ls, Canonical le t) :
      (ls.map Cancellation.classOf).map repr = ls := by
    rw [List.map_map]
    exact (List.map_congr_left (g := id) (fun t ht => recover (h t ht))).trans (List.map_id _)
  have base := ACResidual.holds_iff f (Substitution.identity (sig := sig)) (a :: xs) (b :: ys)
  simp only [ACResidual.Holds,ACRepresentation.decode,Substitution.apply_identity,parts _ left,parts _ right] at base
  apply base.trans
  exact ⟨fun hp => by simpa only [invert _ left,invert _ right] using hp.map repr,
    fun hp => hp.map Cancellation.classOf⟩

/-- Closed factors with C descendants can cancel before occurrence selection.
The interner can use ordinary structural equality on canonical trees. -/
theorem cancel {kernel} (ok : CommonCancellation.Correct kernel) (f : sig.ACSym)
    (le : Term sig → Term sig → Prop) (anti : ∀ a b, le a b → le b a → a = b)
    (d : UInt64 → Term sig) (fixed subject : Array UInt64)
    (closed : ∀ i ∈ fixed.toList ++ subject.toList, Canonical le (d i))
    (ids : ∀ i ∈ fixed.toList, ∀ j ∈ subject.toList, d i = d j → i = j) :
    ∃ missing rest : List UInt64, kernel fixed subject = #[missing.toArray, rest.toArray] ∧
      ∀ (pattern extra : List (Term sig)), pattern.Perm (fixed.toList.map d ++ extra) →
      ∀ σ : Substitution sig, ACResidual.Holds f σ pattern (subject.toList.map d) ↔
        missing = [] ∧ ACResidual.Holds f σ extra (rest.map d) :=
  OpenMatchCancellation.cancel_factors ok f d fixed subject
    (fun i hi => ⟨(closed i hi).ground,(closed i hi).factor f⟩)
    (fun i hi j hj he => ids i hi j hj (Canonical.unique anti (closed i (List.mem_append_left _ hi))
      (closed j (List.mem_append_right _ hj)) he))

/-- Replacing pattern or subject by any B-equivalent representative preserves
the original directional equation, including its shared pending equations. -/
theorem prepare_iff {p t rawP rawT : Term sig} (left : EquivB p rawP) (right : EquivB t rawT)
    (pending : Problem sig) (σ : Substitution sig) :
    Matching.Matches (⟨rawP,rawT⟩ :: pending) σ ↔ Matching.Matches (⟨p,t⟩ :: pending) σ := by
  have applied : EquivB (σ.apply p) (σ.apply rawP) := left.subst σ.image
  have equiv : EquivB (σ.apply rawP) rawT ↔ EquivB (σ.apply p) t :=
    ⟨fun e => applied.trans (e.trans right.symm),fun e => applied.symm.trans (e.trans right)⟩
  simp only [Matching.Matches,List.forall_mem_cons,equiv]

/-- Complete pointwise characterization of the three numeric exports used by
the open AC matcher, under one sorted substitution for every C orientation,
AC partition, repeated variable, and pending equation. -/
def Correct (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat) (orient : Orient) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] (le : Term s → Term s → Prop)
    (_anti : ∀ a b, le a b → le b a → a = b) (enc : Encoding s)
    (f : s.ACSym) (p t : Term s) (rigid : List (Term s)) (m : UInt64) (vars : Fin m.toNat → Variable)
    (occ : List (Fin m.toNat)) (subject : Nat → Term s) (k n : UInt64)
    (pack : (is : List Nat) → OpenMatchAdapter.Words (is.map subject)),
    k.toNat = rigid.length → (∀ i, i ∈ occ) →
    (rigid ++ occ.map (fun i => Term.var (vars i))).Perm (ACRepresentation.flatten f p) →
    ((List.range n.toNat).map subject).Perm (ACRepresentation.flatten f t) →
    (∀ a ∈ rigid, AtomicACPair.Atomic f a ∧ Pattern a) → (∀ i < n.toNat, Canonical le (subject i)) →
    ∀ out, select k n = some out → ∀ rawP rawT, EquivB p rawP → EquivB t rawT →
    ∀ (pending : Problem s) (σ : Substitution s),
      Matching.Matches (⟨rawP,rawT⟩ :: pending) σ ↔ Matching.Matches pending σ ∧
        ∃ row ∈ OpenMatchSelect.decoded out, OpenMatchAdapter.ArmWith (Reads orient enc σ)
          (fun is => OpenMatchAdapter.Remainder flat f vars occ (is.map subject) (pack is) σ) subject rigid row

theorem correct {select flat orient} (sel : OpenMatchSelect.Correct select)
    (part : CompoundPartitions.Correct flat) (comm : Commutative.Correct orient) : Correct select flat orient := by
  intro s _ le anti enc f p t rigid m vars occ subj k n pack len used pl sl pat closed out ran rawP rawT left right pending σ
  rw [prepare_iff left right]
  exact OpenMatchAdapter.compose sel part f p t rigid m vars occ subj k n pack len used pl sl
    (fun a ha => (pat a ha).1) (fun i hi => (closed i hi).ground) (fun i hi => (closed i hi).factor f)
    (fun i hi j hj => Canonical.unique anti (closed i hi) (closed j hj)) out ran pending σ _
    (fun r hr i hi => reads_iff comm enc (pat r hr).2 (closed i hi) σ)

end Tamarin.NestedTreeMatch
