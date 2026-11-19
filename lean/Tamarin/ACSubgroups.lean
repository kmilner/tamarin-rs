import TamarinRuntime.ACSubgroups
import Tamarin.FlatMatchSearch
import Tamarin.DHProduct
import Tamarin.RecursiveACMatch
import Tamarin.SpecializedFresh

namespace Tamarin.ACSubgroups
open Rewriting
variable {s : Signature}
abbrev Kernel := UInt64 → Option (Array (Array UInt64))

/-- Every submultiset of at least two positions occurs. Both row order and
operand order within a row are immaterial, as are duplicate rows. -/
def Correct (select : Kernel) : Prop :=
  ∀ n, (n.toNat ≤ 10 → (select n).isSome) ∧
    ∀ rows, select n = some rows → ∀ group : List UInt64,
      (∃ row : List UInt64, row.toArray ∈ rows ∧ row.Perm group) ↔
      ∃ row : List UInt64, row.Sublist ((List.range n.toNat).map Nat.toUInt64) ∧
        2 ≤ row.length ∧ row.Perm group

theorem correct : Correct run := by
  intro n
  constructor
  · intro h; simp [run,h]
  · intro rows ran group
    unfold run at ran
    split at ran
    · obtain rfl := Option.some.inj ran
      simp [FlatMatchSearch.mem_sublists, and_assoc]
    · cases ran

/-- The caller interprets a row as the indicated factors in the original
term. Every binary AC subproduct exposed by B-equivalence is represented. -/
theorem covers {select : Kernel} (ok : Correct select) {n : UInt64} {rows}
    (ran : select n = some rows) {α : Type} (d : UInt64 → α) {part rest : List α}
    (occ : (part ++ rest).Perm (((List.range n.toNat).map Nat.toUInt64).map d))
    (two : 2 ≤ part.length) :
    ∃ row : List UInt64, row.toArray ∈ rows ∧ (row.map d).Perm part := by
  have sub : part.Sublist (part ++ rest) := List.sublist_append_left ..
  obtain ⟨g,perm,hg⟩ := List.exists_perm_sublist sub occ
  have mem := (FlatMatchSearch.mem_sublists ..).mpr hg
  rw [FlatMatchSearch.sublists_map] at mem
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp mem
  have size : 2 ≤ row.length := by
    simpa using (perm.length_eq.symm ▸ two : 2 ≤ (row.map d).length)
  obtain ⟨out,hm,order⟩ := ((ok n).2 rows ran row).mpr
    ⟨row,(FlatMatchSearch.mem_sublists ..).mp hr,size,.refl _⟩
  exact ⟨out,hm,(order.map d).trans perm⟩

private theorem nonempty (f : s.ACSym) (t : Term s) : 0 < (Cancellation.flatten f t).length := by
  have hf := Cancellation.fold_flatten f t
  cases h : Cancellation.flatten f t with
  | nil => rw [h] at hf; contradiction
  | cons => simp

private theorem binary {f : s.ACSym} {t : Term s} (h : ConstructorVariants.head t = .ac f) :
    2 ≤ (Cancellation.flatten f t).length := by
  cases t with
  | ac g a b =>
    cases h
    rw [Cancellation.flatten_ac, List.length_append]
    have := nonempty f a
    have := nonempty f b
    omega
  | _ => cases h

/-- The adapter decodes positional rows into canonical AC products and performs a
complete directional match on each active rule for that head. A finished search
with no answer for every row means that the whole product is irreducible modulo B. -/
def Normality (subgroups : Kernel) (select : OpenMatchSelect.Kernel) (flat : SortedMatch.Flat)
    (orient : NestedTreeMatch.Orient) (cancel : RecursiveACMatch.Cancellation) : Prop :=
  ∀ {s : Signature} [DecidableEq s.ACSym] {f : s.ACSym} (whole : Term s)
    (rules : List (Equation s)) (_ : ∀ r ∈ rules, ConstructorVariants.Application r.lhs)
    (_ : ∀ t ∈ ACRepresentation.flatten f whole, Normal (ruleRoot rules) t)
    {n : UInt64} {rows} (_ : subgroups n = some rows)
    (d : UInt64 → Cancellation.Class s) (piece : List UInt64 → Term s)
    (_ : (Cancellation.flatten f whole).Perm (((List.range n.toNat).map Nat.toUInt64).map d))
    (_ : ∀ row : List UInt64, row.toArray ∈ rows →
      (Cancellation.flatten f (piece row)).Perm (row.map d))
    (_ : ∀ row : List UInt64, row.toArray ∈ rows → ∀ r ∈ rules,
      ConstructorVariants.head r.lhs = .ac f →
      ∃ enc read, RecursiveACMatch.Search select flat orient cancel enc r.lhs (piece row) read ∧
        ∀ σ, ¬read σ), Normal (ruleRoot rules) whole

theorem normal {subgroups select flat orient cancel} (sub : Correct subgroups)
    (matchOk : RecursiveACMatch.Correct select flat orient cancel) :
    Normality subgroups select flat orient cancel := by
  intro s inst f whole rules apps children n rows ran d piece layout dec misses
  apply DHProduct.subgroup_normal f whole children
  rintro p q hp ⟨rest,occ⟩ ⟨r,hr,σ,rfl,rfl⟩
  obtain ⟨row,hm,perm⟩ := covers sub ran d (occ.symm.trans layout) (binary hp)
  have eq := Cancellation.equiv_of_flatten_perm f ((dec _ hm).trans perm).symm
  obtain ⟨_,read,search,empty⟩ := misses row hm r hr
    ((ConstructorVariants.instance_head r (apps r hr) σ).symm.trans hp)
  apply empty σ
  apply ((matchOk search _ _ (.refl _) (.refl _) [] σ).mp _).1
  simpa [Matching.Matches] using eq

/-- Ordinary reduction may freeze query variables to distinct rigid names.
Checking a normal frozen image suffices once the returned term round-trips. -/
theorem normal_before_freezing (rules : List (Equation s)) (freeze : Substitution s)
    {answer observed : Term s} (roundTrip : EquivB (freeze.apply answer) observed)
    (hn : Normal (ruleRoot rules) observed) : Normal (ruleRoot rules) answer := by
  have hx := (normal_equiv _ roundTrip).mpr hn
  exact fun u hu => hx (freeze.apply u) (SpecializedFresh.stepModulo_subst rules freeze hu)

/-- The concrete reducer replays a successful rule with its thawed substitution.
This justifies each local step before lifting it through the term context. -/
theorem replay (rules : List (Equation s)) {r : Equation s} (mem : r ∈ rules)
    (σ : Substitution s) {p q} (lhs : EquivB p (σ.apply r.lhs))
    (rhs : EquivB (σ.apply r.rhs) q) : StepModulo (ruleRoot rules) p q :=
  ⟨_,_,lhs,.root ⟨r,mem,σ,rfl,rfl⟩,rhs⟩

end Tamarin.ACSubgroups
