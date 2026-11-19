import Tamarin.VariantJoin
import Tamarin.FreshSubstitution

/-! Complete unifiers for independent equation groups. A local answer has
one witness scope. Combining two answers requires distinct range variables
where the two local instantiations may disagree. -/
namespace Tamarin.IndependentUnification
open Rewriting.VariantJoin (choose choose_apply)
variable {sig : Signature} {p q : Problem sig}

/-- Variables in the images that callers observe, including unbound inputs. -/
def ImageVars (p : Problem sig) (a : Substitution sig) (w : Variable) : Prop :=
  ∃ v, p.Occurs v ∧ (a.image v).Occurs w

def Apart (p q : Problem sig) : Prop := ∀ v, p.Occurs v → ¬ q.Occurs v

def SeparateRanges (p q : Problem sig) (as bs : List (Substitution sig)) : Prop :=
  ∀ a ∈ as, ∀ b ∈ bs, ∀ w, ImageVars p a w → ¬ ImageVars q b w

private theorem solves_append (s : Substitution sig) :
    (p ++ q).Solves s ↔ p.Solves s ∧ q.Solves s := by
  simp [Problem.Solves, or_imp, forall_and]

private theorem occurs_append (v : Variable) : (p ++ q).Occurs v ↔ p.Occurs v ∨ q.Occurs v := by
  simp [Problem.Occurs, or_and_right, exists_or]

private theorem merge_solves (apart : Apart p q) {a b : Substitution sig}
    (left : p.Solves a) (right : q.Solves b) : (p ++ q).Solves (choose p.Occurs a b) := by
  apply (solves_append _).2
  constructor <;> intro e he
  · rw [(choose_apply _ _ _ _).1 (fun _ hv => ⟨e,he,Or.inl hv⟩),
        (choose_apply _ _ _ _).1 (fun _ hv => ⟨e,he,Or.inr hv⟩)]
    exact left e he
  · rw [(choose_apply _ _ _ _).2 (fun v hv hp => apart v hp ⟨e,he,Or.inl hv⟩),
        (choose_apply _ _ _ _).2 (fun v hv hp => apart v hp ⟨e,he,Or.inr hv⟩)]
    exact right e he

theorem satisfiable (apart : Apart p q) :
    (p ++ q).Satisfiable ↔ p.Satisfiable ∧ q.Satisfiable := by
  constructor
  · rintro ⟨s,hs⟩
    obtain ⟨l,r⟩ := (solves_append s).1 hs
    exact ⟨⟨s,l⟩,⟨s,r⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨_,merge_solves apart ha hb⟩

noncomputable def product (p : Problem sig) (as bs : List (Substitution sig)) :=
  as.flatMap fun a => bs.map (choose p.Occurs a)

private theorem mem_product {as bs : List (Substitution sig)} {s} :
    s ∈ product p as bs ↔ ∃ a ∈ as, ∃ b ∈ bs, choose p.Occurs a b = s := by
  simp [product]

/-- Factorization uses one simultaneous specialization over the entire
original input. Each selected pair of arms may use its own renaming. -/
theorem complete {as bs : List (Substitution sig)}
    (apart : Apart p q) (ranges : SeparateRanges p q as bs)
    (left : CompleteSet p as) (right : CompleteSet q bs) :
    CompleteSet (p ++ q) (product p as bs) := by
  classical
  constructor
  · intro s hs
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_product.mp hs
    exact merge_solves apart (left.sound a ha) (right.sound b hb)
  · intro s hs
    obtain ⟨l,r⟩ := (solves_append s).1 hs
    obtain ⟨a,ha,d,hd⟩ := left.covers s l
    obtain ⟨b,hb,f,hf⟩ := right.covers s r
    refine ⟨_,mem_product.mpr ⟨a,ha,b,hb,rfl⟩,choose (ImageVars p a) d f,?_⟩
    intro v hv
    change EquivB _ ((choose (ImageVars p a) d f).apply ((choose p.Occurs a b).image v))
    rcases (occurs_append v).1 hv with hp | hq
    · simp only [choose,ite_eq_left hp]
      change EquivB _ ((choose (ImageVars p a) d f).apply (a.image v))
      rw [(choose_apply _ _ _ _).1 (fun _ hw => ⟨v,hp,hw⟩)]
      exact hd v hp
    · have hp : ¬p.Occurs v := fun h => apart v h hq
      simp only [choose,ite_eq_right hp]
      change EquivB _ ((choose (ImageVars p a) d f).apply (b.image v))
      rw [(choose_apply _ _ _ _).2 (fun w hw h => ranges a ha b hb w h ⟨v,hq,hw⟩)]
      exact hf v hq

/-- Components may be collected in any equation order. Auxiliary names in
the combined output still respect the caller's original context. -/
theorem correctIn {original : Problem sig} (order : original.Perm (p ++ q))
    {as bs : List (Substitution sig)} {avoid : List Variable}
    (apart : Apart p q) (ranges : SeparateRanges p q as bs)
    (left : (Outcome.complete as).CorrectIn p avoid) (right : (Outcome.complete bs).CorrectIn q avoid) :
    (Outcome.complete (product p as bs)).CorrectIn original avoid := by
  classical
  have obs (v) : original.Occurs v ↔ p.Occurs v ∨ q.Occurs v := by
    rw [← occurs_append]; simp only [Problem.Occurs,order.mem_iff]
  have sol (s) : original.Solves s ↔ (p ++ q).Solves s := by simp only [Problem.Solves,order.mem_iff]
  have full := complete apart ranges left.mathematical right.mathematical
  refine ⟨⟨fun s hs => (sol s).2 (full.sound s hs),?_⟩,?_,?_⟩
  · intro s hs
    obtain ⟨a,ha,d,hd⟩ := full.covers s ((sol s).1 hs)
    exact ⟨a,ha,d,fun v hv => hd v ((occurs_append v).2 ((obs v).1 hv))⟩
  · intro s hs v hv
    obtain ⟨a,_,b,hb,rfl⟩ := mem_product.mp hs
    have hp : ¬p.Occurs v := fun h => hv ((obs v).2 (.inl h))
    simpa only [choose,ite_eq_right hp] using right.domain b hb v (fun h => hv ((obs v).2 (.inr h)))
  · intro s hs v hv w hw outside
    obtain ⟨a,ha,b,hb,rfl⟩ := mem_product.mp hs
    rcases (obs v).1 hv with hp | hq
    · exact left.fresh a ha v hp w (by simpa [choose,hp] using hw)
        (fun h => outside ((obs w).2 (.inl h)))
    · have hp : ¬p.Occurs v := fun h => apart v h hq
      exact right.fresh b hb v hq w (by simpa [choose,hp] using hw)
        (fun h => outside ((obs w).2 (.inr h)))

private def reserved (p : Problem sig) (answers : List (Substitution sig)) :=
  answers.flatMap (FreshAnswer.rangeVariables p.variables)

/-- Reference allocation. An implementation can allocate per pair instead by
discharging the disjointness premise of `correctIn` on its actual images. -/
noncomputable def freshProduct (p q : Problem sig) (avoid : List Variable)
    (as bs : List (Substitution sig)) :=
  let left := as.map (FreshAnswer.freshen p avoid)
  product p left (bs.map (FreshAnswer.freshen q (reserved p left ++ avoid)))

/-- Every finite pair of complete answer sets can be combined. In particular
local solvers may start numbering witnesses at zero on every invocation. -/
theorem freshProduct_correct {original : Problem sig} (order : original.Perm (p ++ q))
    (apart : Apart p q) (avoid : List Variable) {as bs : List (Substitution sig)}
    (left : CompleteSet p as) (right : CompleteSet q bs) :
    (Outcome.complete (freshProduct p q avoid as bs)).CorrectIn original avoid := by
  let ls := as.map (FreshAnswer.freshen p avoid)
  let extra := reserved p ls
  have l := FreshAnswer.freshen_correct ⟨p,avoid⟩ as left
  have r := FreshAnswer.freshen_correct ⟨q,extra ++ avoid⟩ bs right
  apply correctIn order apart _ l
  · refine ⟨r.mathematical,r.domain,?_⟩
    intro s hs v hv w hw out h
    exact r.fresh s hs v hv w hw out (List.mem_append_right extra h)
  · intro a ha opened hb w ha' hb'
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
    obtain ⟨v,hv,hw⟩ := ha'
    obtain ⟨z,hz,hit⟩ := hb'
    apply FreshAnswer.freshen_range_avoids q (extra ++ avoid) b z hz w hit
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr
      ⟨v,(p.mem_variables v).2 hv,((a.image v).mem_variables w).2 hw⟩⟩

/-- The unit of the product is the singleton identity answer to the empty
conjunction. An empty answer list in any nonempty component makes the full
product empty. -/
noncomputable def freshProducts (avoid : List Variable) :
    List (Problem sig × List (Substitution sig)) → List (Substitution sig)
  | [] => [.identity]
  | (p,as) :: rest => freshProduct p (rest.flatMap Prod.fst) avoid as (freshProducts avoid rest)

/-- The number and order of components are unrestricted. They may use
different AC symbols or sorts. Each component need only supply a complete
set for its own problem under the common signature. -/
theorem freshProducts_correct (parts : List (Problem sig × List (Substitution sig)))
    (apart : parts.Pairwise (fun a b => Apart a.1 b.1))
    (localSets : ∀ part ∈ parts, CompleteSet part.1 part.2)
    (avoid : List Variable) {original : Problem sig} (order : original.Perm (parts.flatMap Prod.fst)) :
    (Outcome.complete (freshProducts avoid parts)).CorrectIn original avoid := by
  induction parts generalizing original with
  | nil =>
    obtain rfl : original = [] := List.perm_nil.mp order
    exact ⟨empty_problem_complete,fun _ hs => (List.mem_singleton.mp hs) ▸ fun _ _ => rfl,
      fun _ _ _ ⟨_,he,_⟩ => False.elim (List.not_mem_nil he)⟩
  | cons part rest ih =>
    obtain ⟨p,as⟩ := part
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp apart
    have restComplete := ih tail (fun pair member => localSets pair (List.mem_cons_of_mem _ member))
      (List.Perm.refl _)
    apply freshProduct_correct order _ avoid (localSets _ List.mem_cons_self) restComplete.mathematical
    intro w hw ⟨e,he,occ⟩
    obtain ⟨pair,mem,member⟩ := List.mem_flatMap.mp he
    exact head pair mem w hw ⟨e,member,occ⟩

end Tamarin.IndependentUnification
