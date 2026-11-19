import Tamarin.XorRules

/-! A packed query may observe either input or their XOR repeatedly, in any
order. One instantiation must cover the whole tuple and both variable images. -/
namespace Tamarin.Rewriting.FreshXor
variable {sig : Signature}

inductive Slot where | left | right | sum deriving DecidableEq
structure Query (sig : Signature) where
  table : Table sig
  x : Variable
  y : Variable
  witness : Variable
  sx : x.sort = .fresh
  sy : y.sort = .fresh
  sw : witness.sort = .fresh
  wx : witness ≠ x
  wy : witness ≠ y

/-- Arbitrarily many binary XORs in one tuple may share any Fresh
variables. Uniqueness of each normalized value holds independently of the
algorithm that enumerates their jointly correlated substitutions. -/
inductive Observation (f : sig.ACSym) : Term sig → Prop where
  | name (v : Variable) : Observation f (.var v)
  | pair (x y : Variable) (sx : x.sort = .fresh) (sy : y.sort = .fresh) :
      Observation f (.ac f (.var x) (.var y))

/-- Uniqueness for each observed component under an arbitrary common
normalized substitution. This supplies the uniqueness premise of the
generic family join, including when distinct edges share a fresh variable. -/
theorem Observation.unique {T : Table sig} {t : Term sig} (obs : Observation T.f t)
    (ρ : Substitution sig) (hn : Normalized T.R ρ) {u v : Term sig}
    (hu : NormalForm T.R (ρ.apply t) u) (hv : NormalForm T.R (ρ.apply t) v) : EquivB u v := by
  cases obs with
  | name w => exact (normal_reduces_equiv hu.1 (hn w)).symm.trans (normal_reduces_equiv hv.1 (hn w))
  | pair x y sx sy =>
    have hx : HasSort (ρ.image x) .fresh := sx ▸ ρ.sorted x
    have hy : HasSort (ρ.image y) .fresh := sy ▸ ρ.sorted y
    change NormalForm _ (.ac T.f (ρ.image x) (ρ.image y)) _ at hu hv
    by_cases eq : ρ.image x = ρ.image y
    · rw [← eq] at hu hv
      exact (T.duplicate_unique hx (hn x) hu).trans (T.duplicate_unique hx (hn x) hv).symm
    · have normal := T.distinct_normal hx hy (hn x) (hn y) eq
      exact (normal_reduces_equiv hu.1 normal).symm.trans (normal_reduces_equiv hv.1 normal)

theorem Table.reconstructible {T : Table sig} {terms : List (Term sig)}
    (admit : ∀ t ∈ terms, Observation T.f t) {arm : Variant sig} (sound : arm.Sound T.R terms) :
    arm.Reconstructible T.R terms :=
  Variant.reconstructible_of_unique sound fun t ht _ _ hu hv =>
    (admit t ht).unique arm.subst sound.1 hu hv

namespace Query
variable (q : Query sig)

def input : Slot → Term sig
  | .left => .var q.x
  | .right => .var q.y
  | .sum => .ac q.table.f (.var q.x) (.var q.y)

def rep : Variable := if q.x = q.y then q.x else q.witness

theorem rep_sort : q.rep.sort = .fresh := by unfold rep; split <;> simp [q.sx, q.sw]

/-- For identical inputs the adapter uses the identity substitution; for
distinct inputs the two bindings explicitly share one fresh range variable. -/
def diagonal : Substitution sig :=
  if q.x = q.y then .identity else {
    image := fun v => if v = q.x ∨ v = q.y then .var q.witness else .var v
    support := [q.x,q.y]
    outside := by intro v h; simp_all
    sorted := by
      intro v; split
      · next e => rcases e with rfl | rfl <;> first | rw [q.sx] | rw [q.sy]
                  all_goals exact q.sw ▸ HasSort.var q.witness
      · exact .var _ }

theorem diagonal_x : q.diagonal.image q.x = .var q.rep := by
  by_cases h : q.x = q.y <;> simp [diagonal,rep,h,Substitution.identity]
theorem diagonal_y : q.diagonal.image q.y = .var q.rep := by
  by_cases h : q.x = q.y <;> simp [diagonal,rep,h,Substitution.identity]

def value : Slot → Term sig
  | .sum => q.table.zero
  | .left | .right => .var q.rep

def unchanged (slots : List Slot) : Variant sig := ⟨.identity,slots.map q.input⟩
def merged (slots : List Slot) : Variant sig := ⟨q.diagonal,slots.map q.value⟩

theorem observed (slots : List Slot) (sum : .sum ∈ slots) (v : Variable) :
    Observed (slots.map q.input) v ↔ v = q.x ∨ v = q.y := by
  constructor
  · rintro ⟨_,hm,h⟩
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
    cases i with
    | left => exact Or.inl h
    | right => exact Or.inr h
    | sum => exact h
  · intro h; exact ⟨_,List.mem_map_of_mem (f := q.input) sum,h⟩

private theorem vars_normal : Normalized q.table.R Substitution.identity :=
  (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1

private theorem as_is {R : Root sig} {t : Term sig} (h : Normal R t) : NormalForm R t t :=
  ⟨.basis (.refl _),h,fun _ hs => hs⟩

private theorem unchanged_sound (slots) (ne : q.x ≠ q.y) :
    (q.unchanged slots).Sound q.table.R (slots.map q.input) := by
  refine ⟨q.vars_normal,aligned_maps slots q.input q.input ?_⟩
  intro i _
  change NormalForm _ (Substitution.identity.apply _) _
  rw [Substitution.apply_identity]
  apply as_is
  cases i with
  | left => exact q.vars_normal q.x
  | right => exact q.vars_normal q.y
  | sum =>
    exact q.table.distinct_normal (q.sx ▸ .var q.x) (q.sy ▸ .var q.y)
      (q.vars_normal q.x) (q.vars_normal q.y) (fun h => ne (Term.var.inj h))

private theorem normal_diagonal : Normalized q.table.R q.diagonal := by
  intro v; unfold diagonal
  split
  · exact q.vars_normal v
  · dsimp only; split <;> exact q.vars_normal _

private theorem merged_sound (slots) :
    (q.merged slots).Sound q.table.R (slots.map q.input) := by
  refine ⟨q.normal_diagonal,aligned_maps slots q.input q.value ?_⟩
  intro i _
  cases i with
  | left =>
    change NormalForm _ (q.diagonal.image q.x) (.var q.rep)
    rw [q.diagonal_x]; exact as_is (q.vars_normal _)
  | right =>
    change NormalForm _ (q.diagonal.image q.y) (.var q.rep)
    rw [q.diagonal_y]; exact as_is (q.vars_normal _)
  | sum =>
    change NormalForm _ (.ac _ (q.diagonal.image q.x) (q.diagonal.image q.y)) _
    rw [q.diagonal_x,q.diagonal_y]
    exact q.table.duplicate_nf (q.rep_sort ▸ HasSort.var q.rep)

private theorem separate_covers (slots) (ρ : Substitution sig) (hn : Normalized q.table.R ρ)
    (ne : ρ.image q.x ≠ ρ.image q.y) (values)
    (nfs : Aligned (fun t u => NormalForm q.table.R (ρ.apply t) u) (slots.map q.input) values) :
    (q.unchanged slots).Covers q.table.R (slots.map q.input) ρ values := by
  refine ⟨ρ,hn,fun _ _ => .refl _,aligned_values slots q.input q.input values nfs ?_⟩
  intro i _ u nf
  apply (normal_reduces_equiv nf.1 _).symm
  cases i with
  | left => exact hn q.x
  | right => exact hn q.y
  | sum => exact q.table.distinct_normal (q.sx ▸ ρ.sorted q.x) (q.sy ▸ ρ.sorted q.y) (hn _) (hn _) ne

private theorem merged_covers (slots) (sum : .sum ∈ slots) (ρ : Substitution sig)
    (hn : Normalized q.table.R ρ) (eq : ρ.image q.x = ρ.image q.y) (values)
    (nfs : Aligned (fun t u => NormalForm q.table.R (ρ.apply t) u) (slots.map q.input) values) :
    (q.merged slots).Covers q.table.R (slots.map q.input) ρ values := by
  let δ := Substitution.binding q.rep (ρ.image q.x) (q.rep_sort ▸ q.sx ▸ ρ.sorted q.x)
  have atRep : δ.image q.rep = ρ.image q.x := by simp [δ,Substitution.binding]
  refine ⟨δ,?_,?_,aligned_values slots q.input q.value values nfs ?_⟩
  · intro v
    by_cases h : v = q.rep
    · subst v; rw [atRep]; exact hn _
    · simpa [δ,Substitution.binding,h,Substitution.identity] using q.vars_normal v
  · intro v hv; change EquivB _ (δ.apply (q.diagonal.image v))
    rcases (q.observed slots sum v).mp hv with rfl | rfl
    · rw [q.diagonal_x]; exact atRep ▸ EquivB.refl _
    · rw [q.diagonal_y]; change EquivB _ (δ.image q.rep); rw [atRep,eq]; exact .refl _
  · intro i _ u nf
    cases i with
    | left => change EquivB u (δ.image q.rep); rw [atRep]; exact (normal_reduces_equiv nf.1 (hn q.x)).symm
    | right => change EquivB u (δ.image q.rep); rw [atRep,eq]; exact (normal_reduces_equiv nf.1 (hn q.y)).symm
    | sum =>
      change EquivB u (δ.apply q.table.zero); rw [q.table.fixes_zero]
      change NormalForm _ (.ac _ (ρ.image q.x) (ρ.image q.y)) u at nf
      rw [← eq] at nf; exact q.table.duplicate_unique (q.sx ▸ ρ.sorted q.x) (hn _) nf

private theorem merged_safe (slots) (sum : .sum ∈ slots) (avoid : List Variable) (fresh : q.witness ∉ avoid) :
    (q.merged slots).Safe (slots.map q.input) avoid := by
  have hr : Observed (slots.map q.input) q.rep ∨ q.rep ∉ avoid := by
    unfold rep; split
    · exact Or.inl ((q.observed slots sum _).mpr (Or.inl rfl))
    · exact Or.inr fresh
  constructor
  · intro v hv
    have h := mt (q.observed slots sum v).mpr hv
    change q.diagonal.image v = .var v
    by_cases he : q.x = q.y <;> simp [diagonal,he,h,Substitution.identity]
  · intro v hv w hw
    change (q.diagonal.image v).Occurs w at hw
    rcases (q.observed slots sum v).mp hv with rfl | rfl
    · rw [q.diagonal_x] at hw; exact hw ▸ hr
    · rw [q.diagonal_y] at hw; exact hw ▸ hr
  · intro t ht w hw
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    cases i with
    | left | right => exact hw ▸ hr
    | sum => exact False.elim (q.table.zeroGround w hw)

theorem diagonal_idempotent (v : Variable) : q.diagonal.apply (q.diagonal.image v) = q.diagonal.image v := by
  by_cases he : q.x = q.y
  · simp [diagonal,he]
  · simp only [diagonal,ite_eq_right he]
    split <;> simp_all [Substitution.apply,Term.subst,q.wx,q.wy]

def decode (slots : List Slot) (mask : UInt8) : List (Variant sig) :=
  (if mask = 3 then [q.unchanged slots] else []) ++ (if mask = 2 ∨ mask = 3 then [q.merged slots] else [])

def Admissible (slots : List Slot) (avoid : List Variable) (answers : List (Variant sig)) : Prop :=
  CompleteVariants q.table.R (slots.map q.input) answers ∧
  ∀ a ∈ answers, a.Safe (slots.map q.input) avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v

/-- The Rust adapter returns only substitutions. For every selected arm the
values obtained by any subsequent normalization agree with the proved tuple. -/
theorem reconstruct (slots : List Slot) (mask : UInt8)
    (openValid : mask = 3 → q.x ≠ q.y) (answer) (hm : answer ∈ q.decode slots mask) :
    answer.Reconstructible q.table.R (slots.map q.input) := by
  apply Table.reconstructible
  · rintro t ht
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    cases i with
    | left | right => exact .name _
    | sum => exact .pair _ _ q.sx q.sy
  · unfold decode at hm
    rcases List.mem_append.mp hm with hl | hr
    · split at hl
      · next h => obtain rfl := List.mem_singleton.mp hl; exact q.unchanged_sound slots (openValid h)
      · contradiction
    · split at hr
      · obtain rfl := List.mem_singleton.mp hr; exact q.merged_sound slots
      · contradiction

theorem correct (run : Bool → UInt8) (kernel : ∀ same, run same = if same then 2 else 3)
    (slots : List Slot) (sum : .sum ∈ slots) (avoid : List Variable) (fresh : q.witness ∉ avoid) :
    q.Admissible slots avoid (q.decode slots (run (decide (q.x = q.y)))) := by
  rw [kernel]
  have cover := q.merged_covers slots sum
  have safe := q.merged_safe slots sum avoid fresh
  by_cases eq : q.x = q.y
  · simp [eq,decode,Admissible,CompleteVariants] at *
    exact ⟨⟨q.merged_sound _, cover⟩, safe, q.diagonal_idempotent⟩
  · simp [eq,decode,Admissible,CompleteVariants]
    refine ⟨⟨⟨q.unchanged_sound _ eq, q.merged_sound _⟩, ?_⟩, ?_⟩
    · intro ρ hn vals nf
      by_cases he : ρ.image q.x = ρ.image q.y
      · exact Or.inr (cover ρ hn he vals nf)
      · exact Or.inl (q.separate_covers slots ρ hn he vals nf)
    · exact ⟨⟨Variant.safe_identity _ _, fun v => Substitution.apply_identity _⟩, safe, q.diagonal_idempotent⟩

end Query
end Tamarin.Rewriting.FreshXor
