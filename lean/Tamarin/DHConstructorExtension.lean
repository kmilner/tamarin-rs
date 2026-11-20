import Tamarin.DHMixedVariants
import Tamarin.DHMixedCanonical
import Tamarin.ConstructorPresentation
import Tamarin.TablePresentation

/-! Extend any exact DH presentation with equations at additional free or commutative heads.
The syntactic checks refer to the complete combined table. -/
namespace Tamarin.Rewriting.DHPeer
open ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

def Table.append (T : Table s) (rows : Problem sig) : Table s where
  rules := T.rules ++ rows
  actual := T.actual
  actualSort := T.actualSort
  distinct := T.distinct
  present r := List.mem_append_left _ (T.present r)

def ExtraTable.append (E : ExtraTable T) (rows : Problem sig) : ExtraTable (T.append rows) where
  actual := E.actual
  sorted := E.sorted
  distinct := E.distinct
  present r := List.mem_append_left _ (E.present r)

namespace ConstructorExtension
variable [DecidableEq sig.FreeSym]

def extraHead (s : Symbols sig) : Head sig → Bool
  | .free f => decide (f ≠ s.pow ∧ f ≠ s.inv ∧ f ≠ s.one ∧ f ≠ s.neutral)
  | .comm _ => true
  | _ => false

variable {rows : Problem sig}

theorem protectedHeads (base : ExactTable E) (outside : ∀ r ∈ rows, extraHead s (head r.lhs)) :
    ProtectedTable (E.append rows) := by
  constructor
  · intro r hr
    rcases List.mem_append.mp hr with hb | he
    · exact base.apps r hb
    · have ok := outside r he
      cases eq : r.lhs <;> simp_all [extraHead,head,headModel,Model.eval,Application]
  · intro r hr atDH
    rcases List.mem_append.mp hr with hb | he
    · exact base r hb
    · have ok := outside r he
      rcases atDH with e|e|e|e <;> simp [e,extraHead] at ok

theorem otherRows (base : ExactTable E) (outside : ∀ r ∈ rows, extraHead s (head r.lhs))
    (subterms : SubtermVariants.Presentation rows) : OtherRows (T.append rows) := by
  constructor
  · intro f hp hi r hr h
    rcases List.mem_append.mp hr with hb | he
    · rcases base.heads hb with dh|dh|dh <;> rw [h] at dh
      · cases dh
      · exact (hi (Head.free.inj dh)).elim
      · exact (hp (Head.free.inj dh)).elim
    · exact subterms r he
  · intro f r hr h
    rcases List.mem_append.mp hr with hb | he
    · rcases base.heads hb with dh|dh|dh <;> rw [h] at dh <;> cases dh
    · exact subterms r he
  · intro f hm member
    obtain ⟨r,hr,h⟩ := List.mem_map.mp member
    rcases List.mem_append.mp hr with hb | he
    · rcases base.heads hb with dh|dh|dh <;> rw [h] at dh
      · exact hm (Head.ac.inj dh)
      · cases dh
      · cases dh
    · have ok := outside r he; simp [h,extraHead] at ok

theorem inert {h : Head sig} (base : ExactTable E) (outside : ∀ r ∈ rows, extraHead s (head r.lhs))
    (mul : h ≠ .ac s.mul) (inv : h ≠ .free s.inv) (pow : h ≠ .free s.pow)
    (foreign : extraHead s h = false) : h ∉ ruleHeads (T.append rows).rules := by
  rintro hh
  obtain ⟨r,hr,eq⟩ := List.mem_map.mp hh
  rcases List.mem_append.mp hr with hb | he
  · exact base.absent mul inv pow (List.mem_map.mpr ⟨r,hb,eq⟩)
  · have good := outside r he; simp_all

/-- Each extra head can be discharged independently in the same combined table. -/
theorem canonical (base : ExactTable E) (outside : ∀ r ∈ rows, extraHead s (head r.lhs))
    (w : Head sig → Nat) (decreasing : SymbolWeight.decreasing w (T.append rows).rules)
    (sorted : TableDecrease.sorted (T.append rows).rules)
    (unique : ∀ r ∈ rows, ChurchRosser.UniqueRow (T.append rows).rules r) :
    MaudeOperations.CanonicalPresentation (ruleRoot (T.append rows).rules) := by
  have neutral : Head.free s.neutral ∉ ruleHeads (T.append rows).rules := by
    apply inert base outside (by intro e; cases e)
    · intro e
      have ar := congrArg sig.arity (Head.free.inj e)
      simp [s.neutralArity,s.invArity] at ar
    · intro e
      have ar := congrArg sig.arity (Head.free.inj e)
      simp [s.neutralArity,s.powArity] at ar
    · simp [extraHead]
  have ac (f : sig.ACSym) (h : f ≠ s.mul) : Head.ac f ∉ ruleHeads (T.append rows).rules :=
    inert base outside (fun e => h (Head.ac.inj e)) (by intro e; cases e) (by intro e; cases e) rfl
  apply (ChurchRosser.Extension.of_checks (protectedHeads base outside) w decreasing sorted neutral ac).canonical
  intro r hr notDH
  rcases List.mem_append.mp hr with hb | he
  · rcases base.heads hb with h|h|h
    · exact (notDH (.inr (.inr (.inr h)))).elim
    · exact (notDH (.inr (.inl h))).elim
    · exact (notDH (.inl h)).elim
  · exact unique r he

variable [DecidableEq sig.CSym] [DecidableEq sig.ACSym] [DecidableEq sig.Atom]

/-- Reconstruct the DH schemas independently and keep all additional rows.
Agreement in both directions checks the original orientation and all variables.
Fuel bounds only the check on fixed ground results. -/
def accepts (s : Symbols sig) (keys : Fin 3 → Variable) (weight : Head sig → Nat)
    (fuel : Nat) (rules : Problem sig) : Bool :=
  let more := rules.filter fun r => extraHead s (head r.lhs)
  let combined := Schemas.rules s keys ++ more
  TablePresentation.Agrees rules combined && SymbolWeight.decreasing weight combined &&
    TableDecrease.sorted combined && more.all (ConstructorRows.checkedRow combined fuel)

/-- Admission certifies the entire relation used by reduction and variants
for every open or kind-level observation tuple. -/
theorem accepts_sound (s : Symbols sig) (keys : Fin 3 → Variable)
    (typed : ∀ i, (keys i).sort = .msg) (distinct : ∀ i j, keys i = keys j → i = j)
    {weight fuel rules} (ok : accepts s keys weight fuel rules) :
    ReferenceReduction.Bound rules ∧ MaudeOperations.CanonicalPresentation (ruleRoot rules) ∧
      MaudeOperations.FiniteVariantProperty (ruleRoot rules) := by
  let more := rules.filter fun r => extraHead s (head r.lhs)
  let base := Schemas.exactTable s keys typed distinct
  let extended := (Schemas.T s keys typed distinct).append more
  have outside : ∀ r ∈ more, extraHead s (head r.lhs) := fun _ h => (List.mem_filter.mp h).2
  have dh := protectedHeads base outside
  obtain ⟨⟨⟨agrees,weightOK⟩,sorts⟩,rowsOK⟩ := by
    simpa only [accepts,Bool.and_eq_true] using ok
  have scope : ReferenceReduction.Bound extended.rules := SymbolWeight.bound weightOK
  have good (r) (mem : r ∈ more) := ConstructorRows.checkedRow_sound (List.mem_append_right _ mem) scope dh.apps
    (List.all_eq_true.mp rowsOK r mem)
  have can := canonical base outside weight weightOK sorts (fun r h => (good r h).2)
  have others := otherRows base outside (fun r h => (good r h).1)
  exact ⟨TablePresentation.bound_of_agrees agrees scope,(TablePresentation.canonical_iff agrees).mpr can,
    (TablePresentation.finite_iff agrees).mpr (mixedFiniteVariants can dh others)⟩

end ConstructorExtension
end Tamarin.Rewriting.DHPeer
