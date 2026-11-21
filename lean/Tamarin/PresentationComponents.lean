import Tamarin.ActiveAC
import Tamarin.ConstructorPresentation
import Tamarin.TablePresentation
import Tamarin.DefinedPatterns

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

/-- A component whose local obligations use only its inventory and the complete table. -/
structure Independent (s : Signature) extends Part s where
  localProof : ∀ {rs}, Inventory toPart rs → (∀ r ∈ rs, Application r.lhs) →
    ∀ h ∈ ruleHeads rs, owns h → Local rs h

variable [DecidableEq s.FreeSym] [DecidableEq s.CSym] [DecidableEq s.ACSym] [DecidableEq s.Atom]

private def exactRows (p : Part s) (rs : Problem s) : Bool := rs.all fun r =>
  !p.owns (head r.lhs) || p.rows.any fun q => r.lhs == q.lhs && r.rhs == q.rhs

private def checkOther (rs : Problem s) (fuel : Nat) (r : Equation s) :=
  ConstructorRows.checkedRow rs fuel r || (DefinedPatterns.frontier rs fuel r).isSome

private theorem checkOther_sound {rs : Problem s} {fuel r} (mem : r ∈ rs)
    (scope : ReferenceReduction.Bound rs) (apps : ∀ q ∈ rs, Application q.lhs)
    (ok : checkOther rs fuel r) :
    (SubtermVariants.ResultRow rs r ∨ SubtermVariants.RowPaths rs r) ∧ NormalAlgebra.UniqueRow rs r := by
  rcases Bool.or_eq_true_iff.mp ok with structural | frontier
  · obtain ⟨shape,uniq⟩ := ConstructorRows.checkedRow_sound mem scope apps structural
    exact ⟨.inl shape,uniq⟩
  · obtain ⟨⟨rows,reply⟩, _⟩ := Option.isSome_iff_exists.mp frontier
    exact ⟨.inr (bounded_paths_of_complete_variants reply.complete),DefinedPatterns.unique_of_reply reply⟩

def accepts (ps : List (Part s)) (weights : Problem s → Head s → Nat) (fuel : Nat) (rs : Problem s) : Bool :=
  let whole := table ps rs
  whole.all (fun r => match r.lhs with
      | .free .. | .comm .. => true | .ac f .. => claimed ps (.ac f) | _ => false) &&
    (ps.isEmpty || TablePresentation.Agrees rs whole) && ps.all (fun p => exactRows p whole) &&
    TableDecrease.sorted whole && SymbolWeight.decreasing (weights whole) whole &&
    whole.all (fun r => claimed ps (head r.lhs) || checkOther whole fuel r)

structure Evidence (ps : List (Part s)) (rs : Problem s) : Prop where
  agrees : TablePresentation.Agrees rs (table ps rs)
  pres : NormalAlgebra.Presentation (table ps rs)
  scope : ReferenceReduction.Bound (table ps rs)
  inventory : ∀ p ∈ ps, Inventory p (table ps rs)
  activeAC : ∀ f, Head.ac f ∈ ruleHeads (table ps rs) → claimed ps (.ac f)
  other : ∀ r ∈ table ps rs, claimed ps (head r.lhs) = false →
    (SubtermVariants.ResultRow (table ps rs) r ∨ SubtermVariants.RowPaths (table ps rs) r) ∧ NormalAlgebra.UniqueRow (table ps rs) r

theorem evidence {ps : List (Part s)} {rs w fuel} (ok : accepts ps w fuel rs) : Evidence ps rs := by
  obtain ⟨⟨⟨⟨⟨apps,agree⟩,parts⟩,sorts⟩,dec⟩,rows⟩ := by simpa only [accepts,Bool.and_eq_true] using ok
  have bound := SymbolWeight.bound dec
  have app r (mem : r ∈ table ps rs) : Application r.lhs := by
    have hit := List.all_eq_true.mp apps r mem
    cases h : r.lhs <;> simp_all [Application]
  have same : TablePresentation.Agrees rs (table ps rs) := by
    rcases Bool.or_eq_true_iff.mp agree with empty | yes
    · obtain rfl := List.isEmpty_iff.mp empty
      have all : rs.filter (fun _ => true) = rs := List.filter_eq_self.mpr (by simp)
      simpa [table,extras,claimed,all] using TablePresentation.agrees_self rs
    · exact yes
  refine ⟨same,⟨app,SymbolWeight.terminating dec,TableDecrease.sortPreserving sorts⟩,bound,?_,?_,?_⟩
  · intro p hp
    refine ⟨fun r hr => List.mem_append_left _ (List.mem_flatMap.mpr ⟨p,hp,hr⟩),?_⟩
    intro r hr owned
    have hit := List.all_eq_true.mp (List.all_eq_true.mp parts p hp) r hr
    simp only [owned,Bool.not_true,Bool.false_or,List.any_eq_true,Bool.and_eq_true,beq_iff_eq] at hit
    obtain ⟨q,mem,l,k⟩ := hit
    obtain rfl : r = q := by cases r; cases q; congr
    exact mem
  · intro f used
    obtain ⟨r,hr,eq⟩ := List.mem_map.mp used
    have hit := List.all_eq_true.mp apps r hr
    cases src : r.lhs <;> simp [src,head,headModel,Model.eval] at eq hit
    exact eq ▸ hit
  · intro r hr outside
    have hit := List.all_eq_true.mp rows r hr
    exact checkOther_sound hr bound app (by simpa [outside] using hit)

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
    exact Classical.choice (supplied active (e.activeAC f active))) (by
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
    · exact SubtermVariants.free_paths_bound e.scope can e.pres.apps f (fun r hr hd =>
        (ctor hr hd (Bool.eq_false_iff.mpr (fun yes => h ⟨hd ▸ atRow r hr,yes⟩))).1)) (by
    intro can f
    by_cases h : Head.comm f ∈ ruleHeads whole ∧ claimed ps (.comm f)
    · exact (supplied h.1 h.2).2
    · exact SubtermVariants.comm_paths_bound e.scope can e.pres.apps f (fun r hr hd =>
        (ctor hr hd (Bool.eq_false_iff.mpr (fun yes => h ⟨hd ▸ atRow r hr,yes⟩))).1))
  exact ⟨TablePresentation.bound_of_agrees e.agrees e.scope,
    (TablePresentation.canonical_iff e.agrees).mpr can,(TablePresentation.finite_iff e.agrees).mpr fvp⟩

theorem independent_complete {parts : List (Independent s)} {rs weights fuel}
    (ok : accepts (parts.map Independent.toPart) weights fuel rs) :
    ReferenceReduction.Bound rs ∧ CanonicalPresentation (ruleRoot rs) ∧ FiniteVariantProperty (ruleRoot rs) := by
  let facts := evidence ok
  apply facts.complete
  intro p hp
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
  exact c.localProof (facts.inventory _ (List.mem_map_of_mem hc)) facts.pres.apps

end Tamarin.PresentationComponents
