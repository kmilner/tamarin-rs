import Tamarin.ACMatchPacket

namespace Tamarin.Matching.ACMatchPacket

/-- Positions in each returned substitution follow the first occurrence
of a pattern identifier while reading the packet from beginning to end. -/
def answerKeys (rows : List Row) := (rows.flatMap Prod.fst).eraseDups

def readArm (rows : List Row) (arm : List (List UInt64)) (k : UInt64) : List UInt64 :=
  arm[(answerKeys rows).idxOf k]?.getD []

def unpack (p : Answers) : List (List (List UInt64)) :=
  p.toList.map fun arm => arm.toList.map Array.toList

/-- A successful packet contains a complete family, with a nonempty image
in every slot. An empty family and a deferred call have distinct encodings. -/
structure FamilyCorrect (floor : List Row → Prop) (run : Packet → Option Answers) : Prop where
  malformed : ∀ p, decode p.toList = none → run p = none
  exact : ∀ p rows answer, decode p.toList = some rows → run p = some answer →
    ACBags.Complete rows ((unpack answer).map (readArm rows)) ∧
    ∀ arm ∈ unpack answer, arm.length = (answerKeys rows).length ∧ ∀ bag ∈ arm, bag ≠ []
  required : ∀ p rows, decode p.toList = some rows → floor rows → (run p).isSome

theorem runAnswersWith_correct (floor : List Row → Prop) (solve : List Row → Option (List (List (List UInt64))))
    (valid : ∀ rows arms, solve rows = some arms → ACBags.Complete rows (arms.map (readArm rows)))
    (shape : ∀ rows arms, solve rows = some arms → ∀ arm ∈ arms,
      arm.length = (answerKeys rows).length ∧ ∀ bag ∈ arm, bag ≠ [])
    (required : ∀ rows, floor rows → (solve rows).isSome) : FamilyCorrect floor (runAnswersWith solve) where
  malformed p h := by simp [runAnswersWith,h]
  exact p rows answer h done := by
    obtain ⟨arms,ha⟩ := Option.isSome_iff_exists.mp
      (show (solve rows).isSome from by cases e : solve rows <;> simp_all [runAnswersWith])
    simp [runAnswersWith,h,ha] at done
    subst answer
    simpa [unpack,List.map_map,Function.comp_def] using And.intro (valid _ _ ha) (shape _ _ ha)
  required p rows h ok := by
    obtain ⟨arms,ha⟩ := Option.isSome_iff_exists.mp (required rows ok)
    simp [runAnswersWith,h,ha]

/-- Transport the actual decoded packet to all original typed equations.
The caller supplies the layout of its packet, the returned variable images,
and identity outside the patterns. -/
theorem FamilyCorrect.term {floor run} (ok : FamilyCorrect floor run)
    {sig : Signature} [DecidableEq sig.ACSym] {f : sig.ACSym} {problem : Problem sig}
    {row : Equation sig → Row} {name term fixed} (layout : ACBags.Layout f problem row name term fixed)
    {packet rows arms} (read : decode packet.toList = some rows) (order : rows.Perm (problem.map row))
    (done : run packet = some arms) (out : List (List UInt64) → Substitution sig)
    (scope : ∀ a ∈ unpack arms, Scoped problem (fun _ => True) (out a))
    (images : ∀ arm ∈ unpack arms, ∀ e ∈ problem, ∀ k ∈ (row e).1, ∀ a tail,
      readArm rows arm k = a :: tail →
      EquivB ((out arm).image (name k)) (ACRepresentation.fold f (term a) (tail.map term))) :
    Matching.Complete problem (fun _ => True) ((unpack arms).map out) := by
  have complete := ACBags.complete_perm order (ok.exact _ _ _ read done).1
  exact layout.complete _ _ _ complete (fun a ha => ⟨scope a ha,
    layout.represents_fold (complete.sound _ (List.mem_map_of_mem ha)) (images a ha)⟩)

end Tamarin.Matching.ACMatchPacket
