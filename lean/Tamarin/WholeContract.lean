import Tamarin.WholeProblem
import Tamarin.WholeLayout
import Tamarin.SpecializedRule

namespace Tamarin.WholeProblem
open Whole
variable {sig : Signature}

def encodeRows (c : Codec sig) (p : Problem sig) :=
  p.map fun e => (encode c e.lhs, encode c e.rhs)

def Faithful (c : Codec sig) (p : Problem sig) : Prop :=
  ∀ e ∈ p, Live c e.lhs ∧ Live c e.rhs

def AllEqual (p : Problem sig) := ∀ e ∈ p, EquivB e.lhs e.rhs

def Closed (t : Term sig) := ∀ v, ¬ t.Occurs v

def Clash (e : Equation sig) := Closed e.lhs ∧ Closed e.rhs ∧ ¬ EquivB e.lhs e.rhs

def HasClash (p : Problem sig) := ∃ e ∈ p, Clash e

/-- The wire result distinguishes a deferred query, a complete empty set
and the singleton identity substitution. Malformed replies have no meaning. -/
def reply (packet : Array (Array UInt64)) : Option (Outcome sig) :=
  if packet == #[#[0]] then some (.stopped .unsupported [])
  else if packet == #[#[1]] then some (.complete [])
  else if packet == #[#[2]] then some (.complete [.identity])
  else none

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array (Array UInt64)

/-- Each wire root denotes its original term, with any same-symbol AC
children spliced into their parent. Equation order and shared IDs are fixed. -/
inductive RowLayout : List (Tree × Tree) → List (Tree × Tree) → Prop where
  | nil : RowLayout [] []
  | cons {a b x y : Tree} {es rs : List (Tree × Tree)} : Layout a x → Layout b y → RowLayout es rs →
      RowLayout ((a, b) :: es) ((x, y) :: rs)

/-- Every graph accepted by the original binary interface has this layout. -/
theorem RowLayout.refl (rows : List (Tree × Tree)) : RowLayout rows rows := by
  induction rows with
  | nil => exact .nil
  | cons p _ ih => exact .cons (.refl p.1) (.refl p.2) ih

private theorem RowLayout.classify_eq {es rs : List (Tree × Tree)} (h : RowLayout es rs) :
    classify es = classify rs := by
  induction h with
  | nil => rfl
  | cons hl hr _ ih =>
    obtain ⟨cl, gl⟩ := hl.observations
    obtain ⟨cr, gr⟩ := hr.observations
    simp only [classify, cl, cr, gl, gr, ih]

/-- The active ABI admits every term graph representing the original conjunction.
Every completed answer must satisfy its mathematical contract. Equivalent
conjunctions and contradictions between closed sides must always complete.
The caller may reserve any variables independently of the computation. -/
structure Correct (run : Kernel) : Prop where
  malformed : ∀ ds ns es, Wire.decodeProblem ds ns es = none → run ds ns es = #[#[0]]
  valid : ∀ {s : Signature} (c : Codec s) (p : Problem s) (avoid : List Variable) ds ns es rows,
    Wire.decodeProblem ds ns es = some rows → RowLayout (encodeRows c p) rows → Faithful c p →
    ∃ out, reply (run ds ns es) = some out ∧ out.CorrectIn p avoid ∧
      (AllEqual p ∨ HasClash p → ∃ answers, out = .complete answers)

private theorem ground_args (xs : List Tree) : groundArgs xs = true ↔ ∀ t ∈ xs, ground t = true := by
  induction xs with
  | nil => simp [groundArgs]
  | cons t ts ih => simp [groundArgs, ih]

private theorem ground_encode (c : Codec sig) (t : Term sig) : ground (encode c t) = true ↔ Closed t := by
  induction t with
  | var v => simp [Closed, encode, ground, Term.Occurs]
  | atom a => simp [Closed, encode, ground, Term.Occurs]
  | free f args ih =>
    simp [Closed, encode, ground, ground_args, ih, Term.Occurs]
    exact forall_comm
  | comm f a b ha hb | ac f a b ha hb =>
    simp [Closed, encode, ground, groundArgs, ha, hb, Term.Occurs, forall_and]

private theorem classify_spec (c : Codec sig) (p : Problem sig) (hf : Faithful c p) :
    let s := classify (encodeRows c p)
    (s = 2 ↔ AllEqual p) ∧ (s = 1 ↔ HasClash p) ∧ (s = 0 ∨ s = 1 ∨ s = 2) := by
  induction p with
  | nil => simp [encodeRows, classify, AllEqual, HasClash]
  | cons e p ih =>
    obtain ⟨hl, hr⟩ := hf e (by simp)
    obtain ⟨two, one, valid⟩ := ih (fun eq he => hf eq (List.mem_cons_of_mem _ he))
    have key := canonical_iff c hl hr
    have equal_cons : AllEqual (e :: p) ↔ EquivB e.lhs e.rhs ∧ AllEqual p := by simp [AllEqual]
    have clash_cons : HasClash (e :: p) ↔ Clash e ∨ HasClash p := by simp [HasClash]
    dsimp only
    simp only [equal_cons, clash_cons, encodeRows, List.map_cons, classify, beq_iff_eq, key,
      Bool.and_eq_true, ground_encode]
    simp only [encodeRows] at two one valid
    by_cases he : EquivB e.lhs e.rhs
    · simp_all [Clash]
    · by_cases hg : Closed e.lhs ∧ Closed e.rhs
      · simp_all [Clash, ground_encode]
      · rcases valid with h | h | h <;> simp_all [Clash, ground_encode] <;> split <;> decide

private theorem correct_equal (p : Problem sig) (avoid : List Variable) (hp : AllEqual p) :
    (Outcome.complete [Substitution.identity]).CorrectIn p avoid := by
  constructor
  · constructor
    · intro σ _ e he
      exact (hp e he).subst σ.image
    · intro ρ _; exact ⟨_, List.mem_singleton_self _, ρ, fun _ _ => .refl _⟩
  · intro σ hs v _
    obtain rfl := List.mem_singleton.mp hs
    rfl
  · intro σ hs v hv w hw hn
    obtain rfl := List.mem_singleton.mp hs
    exact False.elim (hn (hw ▸ hv))

private theorem correct_clash (p : Problem sig) (avoid : List Variable) (hc : HasClash p) :
    (Outcome.complete []).CorrectIn p avoid := by
  refine ⟨(complete_empty_iff p).mpr ?_, by simp [Outcome.answers], by simp [Outcome.answers]⟩
  rintro ⟨σ, sol⟩
  obtain ⟨e, he, hl, hr, ne⟩ := hc
  exact ne (by simpa only [Rewriting.SpecializedRule.apply_ground hl,
    Rewriting.SpecializedRule.apply_ground hr] using sol e he)

theorem run_correct : Correct run where
  malformed := fun _ _ _ h => by simp [run, decodeProblem, h]
  valid := by
    intro s c p avoid ds ns es rows decoded layout faithful
    obtain ⟨two, one, valid⟩ := classify_spec c p faithful
    simp only [run, decodeProblem, decoded, ← layout.classify_eq]
    rcases valid with z | o | t
    · refine ⟨.stopped .unsupported [], by rw [z]; rfl, ?_, ?_⟩
      · exact ⟨by simp [Outcome.Correct, Sound], by simp [Outcome.answers], by simp [Outcome.answers]⟩
      · rintro (eq | clash)
        · simp [z] at two; exact False.elim (two eq)
        · simp [z] at one; exact False.elim (one clash)
    · exact ⟨.complete [], by rw [o]; rfl, correct_clash p avoid (one.mp o), fun _ => ⟨_, rfl⟩⟩
    · exact ⟨.complete [.identity], by rw [t]; rfl, correct_equal p avoid (two.mp t), fun _ => ⟨_, rfl⟩⟩

end Tamarin.WholeProblem
