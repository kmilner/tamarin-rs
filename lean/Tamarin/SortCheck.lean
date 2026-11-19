import Tamarin.Algebra

namespace Tamarin

/-- Executable subsort test, including the incomparable Node sort. -/
def Subsort.check : SortId → SortId → Bool
  | a, b => a == b || (b == .msg && (a == .pub || a == .fresh || a == .nat))

theorem Subsort.check_iff (a b : SortId) : check a b = true ↔ Subsort a b := by
  cases a <;> cases b <;> simp [check] <;>
    first | constructor | (intro h; cases h)

namespace Term
variable {sig : Signature}

/-- The declared result sort alone does not establish well-sortedness:
children must also be checked. -/
def rootSort : Term sig → SortId
  | .var v => v.sort
  | .atom a => sig.atomSort a
  | .free f _ => sig.outputSort f
  | .comm f _ _ => sig.cSort f
  | .ac f _ _ => sig.acSort f

theorem rootSort_le {t : Term sig} {s : SortId} (h : HasSort t s) : Subsort t.rootSort s := by
  induction h with
  | widen _ hab ih => exact ih.trans hab
  | _ => exact .refl _

theorem rootSort_equiv {t u : Term sig} (h : EquivB t u) : t.rootSort = u.rootSort := by
  induction h with
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | _ => rfl

def checkSort : Term sig → SortId → Bool
  | .var v, s => Subsort.check v.sort s
  | .atom a, s => Subsort.check (sig.atomSort a) s
  | .free f args, s => Subsort.check (sig.outputSort f) s &&
      (List.finRange (sig.arity f)).all (fun i => checkSort (args i) (sig.inputSort f i))
  | .comm f a b, s => Subsort.check (sig.cSort f) s &&
      checkSort a (sig.cSort f) && checkSort b (sig.cSort f)
  | .ac f a b, s => Subsort.check (sig.acSort f) s &&
      checkSort a (sig.acSort f) && checkSort b (sig.acSort f)

theorem checkSort_widen (t : Term sig) {a b : SortId}
    (h : t.checkSort a = true) (hab : Subsort a b) : t.checkSort b = true := by
  have step (s : SortId) (h : Subsort.check s a = true) :
      Subsort.check s b = true :=
    (Subsort.check_iff s b).mpr (((Subsort.check_iff s a).mp h).trans hab)
  cases t <;> simp only [checkSort, Bool.and_eq_true] at *
  · exact step _ h
  · exact step _ h
  · exact ⟨step _ h.1, h.2⟩
  · exact ⟨⟨step _ h.1.1, h.1.2⟩, h.2⟩
  · exact ⟨⟨step _ h.1.1, h.1.2⟩, h.2⟩

theorem checkSort_complete {t : Term sig} {s : SortId} (h : HasSort t s) :
    t.checkSort s = true := by
  induction h with
  | var v => exact (Subsort.check_iff _ _).mpr (.refl _)
  | atom a => exact (Subsort.check_iff _ _).mpr (.refl _)
  | free f args h ih =>
    simp only [checkSort, Bool.and_eq_true, List.all_eq_true]
    exact ⟨(Subsort.check_iff _ _).mpr (.refl _), fun i _ => ih i⟩
  | comm f a b ha hb ia ib =>
    simp only [checkSort, Bool.and_eq_true]
    exact ⟨⟨(Subsort.check_iff _ _).mpr (.refl _), ia⟩, ib⟩
  | ac f a b ha hb ia ib =>
    simp only [checkSort, Bool.and_eq_true]
    exact ⟨⟨(Subsort.check_iff _ _).mpr (.refl _), ia⟩, ib⟩
  | widen h hab ih => exact checkSort_widen _ ih hab

theorem checkSort_sound (t : Term sig) (s : SortId) (h : t.checkSort s = true) :
    HasSort t s := by
  induction t generalizing s with
  | var v => exact .widen (.var v) ((Subsort.check_iff _ _).mp h)
  | atom a => exact .widen (.atom a) ((Subsort.check_iff _ _).mp h)
  | free f args ih =>
    simp only [checkSort, Bool.and_eq_true, List.all_eq_true] at h
    exact .widen (.free f args (fun i => ih i _ (h.2 i (List.mem_finRange i))))
      ((Subsort.check_iff _ _).mp h.1)
  | comm f a b ia ib =>
    simp only [checkSort, Bool.and_eq_true] at h
    exact .widen (.comm f a b (ia _ h.1.2) (ib _ h.2))
      ((Subsort.check_iff _ _).mp h.1.1)
  | ac f a b ia ib =>
    simp only [checkSort, Bool.and_eq_true] at h
    exact .widen (.ac f a b (ia _ h.1.2) (ib _ h.2))
      ((Subsort.check_iff _ _).mp h.1.1)

theorem checkSort_iff (t : Term sig) (s : SortId) :
    t.checkSort s = true ↔ HasSort t s :=
  ⟨checkSort_sound t s, checkSort_complete⟩

end Term
end Tamarin
