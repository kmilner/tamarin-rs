import Tamarin.XorFlatNormal
import Tamarin.XorMatchingValuations

/-! Decode a partner row using one Fresh name for each pair, retaining the
other inputs. The factor through a row must reproduce its output by ordinary
substitution. In particular, it cannot cancel anything else in that output. -/
namespace Tamarin.Rewriting.FreshXor.Flat
variable {sig : Signature} {n : Nat}
open XorMatchings

structure Query (sig : Signature) (n : Nat) where
  table : Table sig
  x : Variable
  y : Variable
  tail : List Variable
  fresh : ∀ v ∈ x :: y :: tail, v.sort = .fresh
  key : Fin n → Variable
  distinct : ∀ i j, key i = key j → i = j
  present : ∀ i, key i ∈ x :: y :: tail
  parity : ∀ v, (x :: y :: tail).count v % 2 = ((List.finRange n).map key).count v % 2

abbrev Query.vars (q : Query sig n) := q.x :: q.y :: q.tail

def Query.term (q : Query sig n) := q.table.value (q.vars.map Term.var)

private theorem subst_fold (σ : Substitution sig) (f : sig.ACSym) (a : Term sig) (xs : List (Term sig)) :
    σ.apply (ACRepresentation.fold f a xs) = ACRepresentation.fold f (σ.apply a) (xs.map σ.apply) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => exact congrArg (Term.ac f (σ.apply a)) (ih b)

theorem Table.subst_value (T : Table sig) (σ : Substitution sig) (xs : List (Term sig)) :
    σ.apply (T.value xs) = T.value (xs.map σ.apply) := by
  cases xs with
  | nil => exact T.toTable.fixes_zero σ
  | cons a as => exact subst_fold σ _ a as

theorem Query.apply_term (q : Query sig n) (σ : Substitution sig) :
    σ.apply q.term = q.table.value (q.vars.map σ.image) := by
  rw [term,Table.subst_value,List.map_map]
  rfl

private theorem occurs_vars (v : Variable) (f : sig.ACSym) (a : Variable) (as : List Variable) :
    (ACRepresentation.fold f (.var a) (as.map Term.var)).Occurs v ↔ v ∈ a::as := by
  induction as generalizing a with
  | nil => simp [ACRepresentation.fold,Term.Occurs]
  | cons b bs ih =>
    change (v = a ∨ (ACRepresentation.fold f (.var b) (bs.map Term.var)).Occurs v) ↔ _
    rw [ih b]
    exact List.mem_cons.symm

theorem Query.observed (q : Query sig n) (v : Variable) : Observed [q.term] v ↔ v ∈ q.vars := by
  simp only [Observed,List.mem_singleton,exists_eq_left]
  exact occurs_vars v _ _ _

/-- The only identifications made by Rust are the edges of its decoded
matching. Non-odd variables remain independent even when they occur many times. -/
structure Naming (q : Query sig n) (p : Fin n → Fin n) where
  name : Variable → Variable
  sorted : ∀ v, (name v).sort = v.sort
  outside : ∀ v ∉ q.vars, name v = v
  kernel : ∀ a ∈ q.vars, ∀ b ∈ q.vars, name a = name b ↔
    a = b ∨ ∃ i, q.key i = a ∧ q.key (p i) = b

namespace Naming
variable {q : Query sig n} {p : Fin n → Fin n} (w : Naming q p)

def subst : Substitution sig where
  image v := .var (w.name v)
  support := q.vars
  sorted v := w.sorted v ▸ HasSort.var _
  outside v hv := congrArg Term.var (w.outside v hv)

def fixed (p : Fin n → Fin n) := (List.finRange n).filter (fun i => p i == i)

def leaves := (fixed p).map fun i => (Term.var (w.name (q.key i)) : Term sig)

def arm : Variant sig := ⟨w.subst,[q.table.value w.leaves]⟩

private theorem names_normal : Normalized q.table.R w.subst :=
  fun v => (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1 (w.name v)

theorem paired (i : Fin n) : w.name (q.key i) = w.name (q.key (p i)) :=
  (w.kernel _ (q.present _) _ (q.present _)).mpr (.inr ⟨i,rfl,rfl⟩)

theorem fixed_distinct : w.leaves.Nodup := by
  apply List.pairwise_map.mpr
  have nd := (List.nodup_finRange n).filter (fun i => p i == i)
  apply nd.imp_of_mem
  intro i j hi _ ne e
  have ei := (List.mem_filter.mp hi).2
  have eq := (w.kernel _ (q.present i) _ (q.present j)).mp (Term.var.inj e)
  rcases eq with k | ⟨k,ki,kj⟩
  · exact ne (q.distinct _ _ k)
  · obtain rfl := q.distinct _ _ ki
    exact ne (q.distinct _ _ ((beq_iff_eq.mp ei) ▸ kj))

private noncomputable def factor (ρ : Substitution sig) : Substitution sig := by
  classical
  let src (v : Variable) := ∃ k ∈ q.vars, w.name k = v
  exact {
    image := fun v => if h : src v then ρ.image h.choose else .var v
    support := q.vars.map w.name
    outside := by intro v hv; exact dite_eq_right (fun h => hv (List.mem_map.mpr h))
    sorted := by
      intro v; split
      · next h => exact ((w.sorted h.choose).symm.trans (congrArg Variable.sort h.choose_spec.2)) ▸ ρ.sorted _
      · exact .var _ }

private theorem factor_correct (ρ : Substitution sig) (hn : Normalized q.table.R ρ)
    (preserves : ∀ i, ρ.image (q.key (p i)) = ρ.image (q.key i)) :
    Normalized q.table.R (w.factor ρ) ∧ ∀ k ∈ q.vars, (w.factor ρ).image (w.name k) = ρ.image k := by
  classical
  constructor
  · intro v
    simp only [factor]; split
    · exact hn _
    · exact (ConstructorVariants.constructor_normal q.table.rules q.table.apps).1 _
  · intro k hk
    have ex : ∃ j ∈ q.vars, w.name j = w.name k := ⟨k,hk,rfl⟩
    simp only [factor,dite_eq_left ex]
    rcases (w.kernel _ ex.choose_spec.1 k hk).mp ex.choose_spec.2 with eq | ⟨i,ha,hb⟩
    · exact congrArg ρ.image eq
    · rw [← ha,← hb]; exact (preserves i).symm

private theorem selected {σ : Substitution sig} (hn : Normalized q.table.R σ)
    (inv : ∀ i, p (p i) = i) (keep : ∀ i, σ.image (q.key (p i)) = σ.image (q.key i))
    (nd : ((fixed p).map (fun i => σ.image (q.key i))).Nodup) (u : Term sig) :
    NormalForm q.table.R (σ.apply q.term) u ↔
      EquivB u (q.table.value ((fixed p).map (fun i => σ.image (q.key i)))) := by
  classical
  rw [q.apply_term]
  refine q.table.normalForm_iff ?_ ?_ nd ?_ u
  · intro t ht
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (show t ∈ q.vars.map σ.image from ht)
    exact q.fresh v hv ▸ σ.sorted v
  · intro t ht
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp (show t ∈ q.vars.map σ.image from ht)
    exact hn v
  · intro t
    have odd := map_parity σ.image q.parity t
    rw [List.map_map] at odd
    exact odd.trans (fixed_parity _ p inv keep t).symm

theorem sound_reconstruct (inv : ∀ i, p (p i) = i) :
    w.arm.Sound q.table.R [q.term] ∧ w.arm.Reconstructible q.table.R [q.term] := by
  have nf := selected w.names_normal inv (fun i => congrArg Term.var (w.paired i).symm) w.fixed_distinct
  refine ⟨⟨w.names_normal,(nf _).mpr (.refl _),trivial⟩,?_⟩
  rintro (_|⟨u,(_|⟨_,_⟩)⟩) forms
  · exact False.elim forms
  · exact ⟨(nf u).mp forms.1,trivial⟩
  · exact False.elim forms.2

theorem covers (ρ : Substitution sig) (hn : Normalized q.table.R ρ) (inv : ∀ i, p (p i) = i)
    (keep : ∀ i, ρ.image (q.key (p i)) = ρ.image (q.key i))
    (nd : ((fixed p).map fun i => ρ.image (q.key i)).Nodup)
    (u : Term sig) (form : NormalForm q.table.R (ρ.apply q.term) u) :
    w.arm.Covers q.table.R [q.term] ρ [u] := by
  obtain ⟨hnorm,hits⟩ := w.factor_correct ρ hn keep
  refine ⟨w.factor ρ,hnorm,?_,?_,trivial⟩
  · intro v hv
    exact (hits v ((q.observed v).mp hv)) ▸ EquivB.refl _
  · change EquivB u ((w.factor ρ).apply (q.table.value w.leaves))
    rw [Table.subst_value]
    have mapped : w.leaves.map (w.factor ρ).apply = (fixed p).map (fun i => ρ.image (q.key i)) := by
      rw [leaves,List.map_map]; apply List.map_congr_left; intro i _
      exact hits (q.key i) (q.present i)
    rw [mapped]
    exact (selected hn inv keep nd u).mp form

end Naming

def Family (q : Query sig n) (arms : List (Variant sig)) : Prop :=
  (∀ a ∈ arms, ∃ p, (∀ i, p (p i) = i) ∧ ∃ w : Naming q p, a = w.arm) ∧
  (∀ p : Fin n → Fin n, (∀ i, p (p i) = i) → ∃ w : Naming q p, w.arm ∈ arms)

theorem Query.complete (q : Query sig n) {arms : List (Variant sig)} (family : Family q arms) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term] := by
  have valid (a) (ha : a ∈ arms) : a.Sound q.table.R [q.term] ∧ a.Reconstructible q.table.R [q.term] := by
    obtain ⟨_,inv,w,rfl⟩ := family.1 a ha
    exact w.sound_reconstruct inv
  refine ⟨⟨fun a ha => (valid a ha).1,?_⟩,fun a ha => (valid a ha).2⟩
  intro ρ hn values forms
  obtain ⟨p,inv,keep,nd⟩ := exists_fitting fun i => ρ.image (q.key i)
  obtain ⟨w,mem⟩ := family.2 p inv
  cases values with
  | nil => exact False.elim forms
  | cons u us => cases us with
    | nil => exact ⟨_,mem,w.covers ρ hn inv keep nd u forms.1⟩
    | cons => exact False.elim forms.2

/-- When all run counts are even, specialization cannot expose any odd
leaf. Rust returns the identity arm and skips the matching call entirely. -/
def evenNaming (q : Query sig 0) (p : Fin 0 → Fin 0) : Naming q p where
  name := id
  sorted := fun _ => rfl
  outside := fun _ _ => rfl
  kernel := by
    intro a _ b _
    exact ⟨Or.inl,fun h => h.elim id (fun ⟨i,_⟩ => Fin.elim0 i)⟩

theorem Query.even_complete (q : Query sig 0) :
    let a := (evenNaming q id).arm
    CompleteVariants q.table.R [q.term] [a] ∧ a.Reconstructible q.table.R [q.term] := by
  let a := (evenNaming q id).arm
  have fam : Family q [a] := by
    constructor
    · intro b hb
      exact ⟨id,fun _ => rfl,evenNaming q id,List.mem_singleton.mp hb⟩
    · intro p _
      have eq : p = id := funext (fun i => Fin.elim0 i)
      cases eq; exact ⟨evenNaming q id,List.mem_singleton_self _⟩
  exact ⟨(q.complete fam).1,(q.complete fam).2 _ (List.mem_singleton_self _)⟩

/-- The wire contains indices only. The Rust boundary decodes each packet
row once, using sorted orbit names. Both directions of membership permit
reordering and duplicate removal while forbidding lost or invented arms. -/
def Decodes (q : Query sig n) (row : Array UInt64) (a : Variant sig) : Prop :=
  ∃ p, Encodes p row ∧ ∃ w : Naming q p, a = w.arm

theorem exported_complete {width : UInt64} (q : Query sig width.toNat) {run}
    (verified : Correct run) {rows} (success : run width = some rows)
    (arms : List (Variant sig))
    (all : ∀ row ∈ rows, ∃ a ∈ arms, Decodes q row a)
    (only : ∀ a ∈ arms, ∃ row ∈ rows, Decodes q row a) :
    CompleteVariants q.table.R [q.term] arms ∧ ∀ a ∈ arms, a.Reconstructible q.table.R [q.term] := by
  have inject {p g : Fin width.toNat → Fin width.toNat} {row}
      (hp : Encodes p row) (hg : Encodes g row) : p = g := by
    have eq := hp.symm.trans hg
    funext i; apply Fin.ext
    have h := congrArg (fun xs : Array UInt64 => xs[i.val]!) eq
    simp only [Array.getElem!_eq_getD, Array.getD, Array.size_ofFn, i.isLt, dite_true] at h
    have bound (j : Fin width.toNat) : j.val < 2^64 := Nat.lt_trans j.isLt width.toNat_lt
    simpa [UInt64.toNat_ofNat,Nat.mod_eq_of_lt (bound _)] using congrArg UInt64.toNat h
  apply q.complete
  constructor
  · intro a ha
    obtain ⟨row,mem,p,enc,w,rfl⟩ := only a ha
    obtain ⟨g,inv,hg⟩ := ((verified width).2 rows success row).mp mem
    obtain rfl := inject enc hg
    exact ⟨_,inv,w,rfl⟩
  · intro p inv
    let row := Array.ofFn fun i => (p i).val.toUInt64
    have hp : Encodes p row := rfl
    obtain ⟨a,mem,g,hg,w,rfl⟩ := all row (((verified width).2 rows success row).mpr ⟨p,inv,hp⟩)
    obtain rfl := inject hp hg
    exact ⟨w,mem⟩

end Tamarin.Rewriting.FreshXor.Flat
