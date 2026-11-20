import Tamarin.ActiveAC
import Tamarin.ConstructorPresentation
import Tamarin.TablePresentation

/-! Compose presentations by their declared heads. Every component sees the entire
combined rewrite relation. Rows outside these heads use the ordinary constructor
criterion. Exact inventories prevent one component from hiding a competing rule. -/
namespace Tamarin.PresentationComponents
open Rewriting ConstructorVariants MaudeOperations ShortVariantPaths
variable {s : Signature}

structure Part (s : Signature) where
  owns : Head s → Bool
  rows : Problem s

def claimed (ps : List (Part s)) (h : Head s) := ps.any fun p => p.owns h

def extras (ps : List (Part s)) (rs : Problem s) := rs.filter fun r => !claimed ps (head r.lhs)

def table (ps : List (Part s)) (rs : Problem s) := ps.flatMap Part.rows ++ extras ps rs

structure Inventory (p : Part s) (rs : Problem s) : Prop where
  present : ∀ r ∈ p.rows, r ∈ rs
  only : ∀ r ∈ rs, p.owns (head r.lhs) → r ∈ p.rows

def FreeBound (rs : Problem s) (f : s.FreeSym) := ∃ k, ∀ xs, (∀ i, Normal (ruleRoot rs) (xs i)) →
  ∃ u, Path (ruleRoot rs) k (.free f xs) u ∧ Normal (ruleRoot rs) u

def CommBound (rs : Problem s) (f : s.CSym) := ∃ k, ∀ a b, Normal (ruleRoot rs) a → Normal (ruleRoot rs) b →
  ∃ u, Path (ruleRoot rs) k (.comm f a b) u ∧ Normal (ruleRoot rs) u

def Local (rs : Problem s) (h : Head s) : Prop :=
  match h with
  | .free f => (∀ r ∈ rs, head r.lhs = .free f → NormalAlgebra.UniqueRow rs r) ∧ FreeBound rs f
  | .comm f => (∀ r ∈ rs, head r.lhs = .comm f → NormalAlgebra.UniqueRow rs r) ∧ CommBound rs f
  | .ac f => Nonempty (ActiveAC.Operator rs f)
  | _ => False

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def exactRows (p : Part s) (rs : Problem s) : Bool := rs.all fun r =>
  !p.owns (head r.lhs) || p.rows.any fun q => r.lhs == q.lhs && r.rhs == q.rhs

def accepts (ps : List (Part s)) (weights : Problem s → Head s → Nat) (fuel : Nat) (rs : Problem s) : Bool :=
  let whole := table ps rs
  whole.all (fun r => match r.lhs with
      | .free .. | .comm .. => true | .ac f .. => claimed ps (.ac f) | _ => false) &&
    TablePresentation.Agrees rs whole && ps.all (fun p => exactRows p whole) &&
    TableDecrease.sorted whole && SymbolWeight.decreasing (weights whole) whole &&
    whole.all (fun r => claimed ps (head r.lhs) || ConstructorRows.checkedRow whole fuel r)

structure Evidence (ps : List (Part s)) (rs : Problem s) : Prop where
  agrees : TablePresentation.Agrees rs (table ps rs)
  pres : NormalAlgebra.Presentation (table ps rs)
  scope : ReferenceReduction.Bound (table ps rs)
  inventory : ∀ p ∈ ps, Inventory p (table ps rs)
  other : ∀ r ∈ table ps rs, claimed ps (head r.lhs) = false →
    SubtermVariants.Row r ∧ NormalAlgebra.UniqueRow (table ps rs) r

theorem evidence {ps : List (Part s)} {rs w fuel} (ok : accepts ps w fuel rs) : Evidence ps rs := by
  obtain ⟨⟨⟨⟨⟨apps,agree⟩,parts⟩,sorts⟩,dec⟩,rows⟩ := by simpa only [accepts,Bool.and_eq_true] using ok
  have bound := SymbolWeight.bound dec
  have app r (mem : r ∈ table ps rs) : Application r.lhs := by
    have hit := List.all_eq_true.mp apps r mem
    cases h : r.lhs <;> simp_all [Application]
  refine ⟨agree,⟨app,SymbolWeight.terminating dec,TableDecrease.sortPreserving sorts⟩,bound,?_,?_⟩
  · intro p hp
    refine ⟨fun r hr => List.mem_append_left _ (List.mem_flatMap.mpr ⟨p,hp,hr⟩),?_⟩
    intro r hr owned
    have hit := List.all_eq_true.mp (List.all_eq_true.mp parts p hp) r hr
    simp only [owned,Bool.not_true,Bool.false_or,List.any_eq_true,Bool.and_eq_true,beq_iff_eq] at hit
    obtain ⟨q,mem,l,k⟩ := hit
    obtain rfl : r = q := by cases r; cases q; congr
    exact mem
  · intro r hr outside
    have hit := List.all_eq_true.mp rows r hr
    exact ConstructorRows.checkedRow_sound hr bound app (by simpa [outside] using hit)

theorem Evidence.complete {ps : List (Part s)} {rs} (e : Evidence ps rs)
    (heads : ∀ p ∈ ps, ∀ h ∈ ruleHeads (table ps rs), p.owns h → Local (table ps rs) h) :
    ReferenceReduction.Bound rs ∧ CanonicalPresentation (ruleRoot rs) ∧ FiniteVariantProperty (ruleRoot rs) := by
  classical
  let whole := table ps rs
  have supplied {h} (active : h ∈ ruleHeads whole) (yes : claimed ps h) : Local whole h := by
    obtain ⟨p,hp,hh⟩ := List.any_eq_true.mp yes
    exact heads _ hp _ active hh
  have atRow (r) (hr : r ∈ whole) : head r.lhs ∈ ruleHeads whole := List.mem_map_of_mem hr
  have ctor {r} (hr : r ∈ whole) {h} (same : head r.lhs = h) (no : claimed ps h = false) :=
    e.other r hr (same ▸ no)
  obtain ⟨can,fvp⟩ := ActiveAC.complete_of_bounds e.pres e.scope (by
    intro f active
    cases yes : claimed ps (.ac f) with
    | true => exact Classical.choice (supplied active yes)
    | false =>
      exfalso
      obtain ⟨r,hr,hd⟩ := List.mem_map.mp active
      have bad := (ctor hr hd yes).1
      cases lhs : r.lhs <;> simp [SubtermVariants.Row,lhs,head,headModel,Model.eval] at bad hd) (by
    intro r hr notAC
    cases yes : claimed ps (head r.lhs) with
    | false => exact (e.other r hr yes).2
    | true =>
      have localHead := supplied (atRow r hr) yes
      cases h : head r.lhs with
      | var | atom => simp [h,Local] at localHead
      | ac f => exact (notAC f h).elim
      | free f | comm f => rw [h] at localHead; exact localHead.1 r hr h) (by
    intro can f
    by_cases h : Head.free f ∈ ruleHeads whole ∧ claimed ps (.free f)
    · exact (supplied h.1 h.2).2
    · exact SubtermVariants.free_bound e.scope can e.pres.apps f (fun r hr hd =>
        (ctor hr hd (Bool.eq_false_iff.mpr (fun yes => h ⟨hd ▸ atRow r hr,yes⟩))).1)) (by
    intro can f
    by_cases h : Head.comm f ∈ ruleHeads whole ∧ claimed ps (.comm f)
    · exact (supplied h.1 h.2).2
    · exact SubtermVariants.comm_bound e.scope can e.pres.apps f (fun r hr hd =>
        (ctor hr hd (Bool.eq_false_iff.mpr (fun yes => h ⟨hd ▸ atRow r hr,yes⟩))).1))
  exact ⟨TablePresentation.bound_of_agrees e.agrees e.scope,
    (TablePresentation.canonical_iff e.agrees).mpr can,(TablePresentation.finite_iff e.agrees).mpr fvp⟩

end Tamarin.PresentationComponents
