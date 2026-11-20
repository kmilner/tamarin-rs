import Tamarin.ContextualReduction
import Tamarin.RootNormalForms
import Tamarin.SortClash
import Tamarin.ShortVariantPaths

/-! With normal operands at a free or commutative head, an ill-sorted
application is stuck whenever every root redex requires the declared sort. -/
namespace Tamarin.Rewriting
open ConstructorVariants ContextualReduction
variable {s : Signature} {R : Root s} {k : SortId}

theorem unsorted_free {f : s.FreeSym} {xs : Fin (s.arity f) → Term s}
    (typed : ∀ {ys : Fin (s.arity f) → Term s} {b}, R (.free f ys) b → HasSort (.free f ys) k)
    (normal : ∀ i, Normal R (xs i)) (ill : ¬ HasSort (.free f xs) k) :
    Normal R (.free f xs) := by
  apply normal_free_no_root normal
  intro ys agree b step
  exact ill (Term.checkSort_sound _ _ ((SortClash.check_equiv (EquivB.free f xs ys agree) k).symm ▸
    Term.checkSort_complete (typed step)))

theorem unsorted_comm {f : s.CSym} {a b : Term s}
    (typed : ∀ {p q}, head p = .comm f → R p q → HasSort p k)
    (na : Normal R a) (nb : Normal R b) (ill : ¬ HasSort (.comm f a b) k) :
    Normal R (.comm f a b) := by
  intro u st
  rcases (comm_iff ..).mp st with ⟨p,_,eq,root,_⟩ | ⟨v,one,_⟩ | ⟨v,one,_⟩
  · exact ill (Term.checkSort_sound _ _ ((SortClash.check_equiv eq k).symm ▸
      Term.checkSort_complete (typed eq.head_eq.symm root)))
  · exact na v one
  · exact nb v one

/-- Lift a sorted path bound through a binary free declaration. Arity and
input sorts come from the signature, and each root step must require the
source sort. This applies equally to position-sensitive group operations. -/
theorem binary_free_paths {f : s.FreeSym} (ar : s.arity f = 2) {input : SortId}
    (inputs : ∀ i, s.inputSort f i = input)
    (typed : ∀ {ys : Fin (s.arity f) → Term s} {b}, R (.free f ys) b → HasSort (.free f ys) k)
    {n : Nat} (run : ∀ a b : Term s, HasSort a input → HasSort b input → Normal R a → Normal R b →
      ∃ u, ShortVariantPaths.Path R n (.free f (fun i => if i.val = 0 then a else b)) u ∧ Normal R u)
    (xs : Fin (s.arity f) → Term s) (normal : ∀ i, Normal R (xs i)) :
    ∃ u, ShortVariantPaths.Path R n (.free f xs) u ∧ Normal R u := by
  by_cases good : HasSort (.free f xs) k
  · let l : Fin (s.arity f) := ⟨0,by omega⟩
    let r : Fin (s.arity f) := ⟨1,by omega⟩
    have checks := Term.checkSort_complete good
    simp only [Term.checkSort,Bool.and_eq_true,List.all_eq_true] at checks
    have child i : HasSort (xs i) input := inputs i ▸ Term.checkSort_sound _ _ (checks.2 i (List.mem_finRange i))
    have args : (fun i : Fin (s.arity f) => if i.val = 0 then xs l else xs r) = xs := by
      funext i
      split <;> apply congrArg xs <;> apply Fin.ext <;> simp [l,r] <;> have := i.isLt <;> omega
    simpa only [args] using run (xs l) (xs r) (child l) (child r) (normal l) (normal r)
  · exact ⟨_,.basis (.refl _),unsorted_free typed normal good⟩

end Tamarin.Rewriting
