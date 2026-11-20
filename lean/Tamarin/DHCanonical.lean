import Tamarin.DHPresentation
import Tamarin.SymbolWeight

/-! Termination and sort preservation of the exact DH rule table at all
positions, including proper subproducts and ill-sorted caller contexts. -/
namespace Tamarin.Rewriting.DHPeer.ExactTable
open ConstructorVariants
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}

/-- A binary free application costs two. The tower equation replaces one
exponentiation by a product of cost one; each other row also decreases. -/
def weight : Head sig → Nat
  | .free f => if sig.arity f = 2 then 2 else 1
  | _ => 1

private def cost : Expr (Fin 3) → Nat
  | .var _ => 0
  | .pow a b => cost a + cost b + 2
  | .mul a b => cost a + cost b + 1
  | .inv a => cost a + 1
  | .one | .neutral => 1

private def leaves (keys : Fin 3 → Variable) : Expr (Fin 3) → List Variable
  | .var i => [keys i]
  | .pow a b | .mul a b => leaves keys a ++ leaves keys b
  | .inv a => leaves keys a
  | .one | .neutral => []

private theorem ofTwo {α : Type} {n : Nat} (h : n = 2) (a b : α) :
    (List.ofFn (fun (i : Fin n) => if i.val = 0 then a else b)) = [a,b] := by
  subst n; simp [List.ofFn_succ]

private theorem ofOne {α : Type} {n : Nat} (h : n = 1) (a : α) :
    (List.ofFn fun (_ : Fin n) => a) = [a] := by
  subst n; simp [List.ofFn_succ]

private theorem ofZero {α : Type} {n : Nat} (h : n = 0) (f : Fin n → α) :
    List.ofFn f = [] := by subst n; rfl

private theorem rank_eval (keys : Fin 3 → Variable) (e : Expr (Fin 3)) :
    SymbolWeight.rank weight (e.eval s (fun i => .var (keys i))) = cost e := by
  let env := fun i => Term.var (sig := sig) (keys i)
  induction e with
  | var => rfl
  | one => change (List.ofFn _).sum + weight (.free s.one) = 1
           simp [ofZero s.oneArity,weight,s.oneArity]
  | neutral => change (List.ofFn _).sum + weight (.free s.neutral) = 1
               simp [ofZero s.neutralArity,weight,s.neutralArity]
  | inv a ia =>
    change (List.ofFn fun _ : Fin (sig.arity s.inv) => SymbolWeight.rank weight (a.eval s env)).sum + weight (.free s.inv) = cost a + 1
    simp [ofOne s.invArity,weight,s.invArity,env,ia]
  | mul a b ia ib =>
    change SymbolWeight.rank weight (a.eval s env) + SymbolWeight.rank weight (b.eval s env) + 1 = _
    simp [env,ia,ib,cost]
  | pow a b ia ib =>
    change (List.ofFn fun i : Fin (sig.arity s.pow) =>
      SymbolWeight.rank weight (if i.val = 0 then a.eval s env else b.eval s env)).sum + weight (.free s.pow) = _
    simp only [apply_ite,ofTwo s.powArity,List.sum_cons,List.sum_nil,Nat.add_zero,weight,s.powArity]
    simp [env,ia,ib,cost]

private theorem vars_eval (keys : Fin 3 → Variable) (e : Expr (Fin 3)) :
    (e.eval s (fun i => .var (keys i))).variables = leaves keys e := by
  induction e with
  | var => rfl
  | one => exact congrArg List.flatten (ofZero s.oneArity _)
  | neutral => exact congrArg List.flatten (ofZero s.neutralArity _)
  | mul a b ia ib => change _ ++ _ = _ ++ _; rw [ia,ib]
  | inv a ia =>
    change (List.ofFn (fun _ : Fin (sig.arity s.inv) => _)).flatten = _
    simpa [ofOne s.invArity,leaves] using ia
  | pow a b ia ib =>
    change (List.ofFn (fun i : Fin (sig.arity s.pow) => (if i.val = 0 then _ else _ : Term sig).variables)).flatten = _
    simp only [apply_ite,ofTwo s.powArity,List.flatten_cons,List.flatten_nil,List.append_nil,ia,ib,leaves]

private theorem check {keys : Fin 3 → Variable} {lhs rhs : Expr (Fin 3)}
    (less : cost rhs < cost lhs) (counts : ∀ v,
      (leaves keys rhs).count v ≤ (leaves keys lhs).count v) :
    let r : Equation sig := ⟨lhs.eval s (fun i => .var (keys i)),rhs.eval s (fun i => .var (keys i))⟩
    decide (SymbolWeight.rank weight r.rhs < SymbolWeight.rank weight r.lhs) && TableDecrease.nonduplicating r := by
  dsimp only
  apply Bool.and_eq_true_iff.mpr
  refine ⟨by simpa [rank_eval] using less, List.all_eq_true.mpr fun v _ => ?_⟩
  simpa [vars_eval] using counts v

private theorem rule_check (s : Symbols sig) (keys : Fin 3 → Variable) (r : Rule) :
    let eq := r.instantiate s (fun i => .var (keys i))
    decide (SymbolWeight.rank weight eq.rhs < SymbolWeight.rank weight eq.lhs) && TableDecrease.nonduplicating eq := by
  apply check
  · cases r <;> decide
  · intro v; cases r <;> simp [Rule.equation,leaves,List.count_cons] <;> omega

private theorem extra_check (s : Symbols sig) (keys : Fin 3 → Variable) (r : ExtraRule) :
    let eq := r.instantiate s (fun i => .var (keys i))
    decide (SymbolWeight.rank weight eq.rhs < SymbolWeight.rank weight eq.lhs) && TableDecrease.nonduplicating eq := by
  apply check
  · cases r <;> decide
  · intro v; cases r <;> simp [ExtraRule.equation,leaves,List.count_cons] <;> omega

private theorem scope {r : Equation sig} (h : TableDecrease.nonduplicating r) {v : Variable}
    (hv : r.rhs.Occurs v) : r.lhs.Occurs v := by
  have bound := TableDecrease.bound_of_nonduplicating (rules := [r]) (by simpa using h)
  exact bound r List.mem_cons_self v hv

theorem rule_scope (s : Symbols sig) (keys : Fin 3 → Variable) (r : Rule) (v : Variable) :
    let eq := r.instantiate s (fun i => .var (keys i))
    eq.rhs.Occurs v → eq.lhs.Occurs v := scope (Bool.and_eq_true_iff.mp (rule_check s keys r)).2

theorem extra_scope (s : Symbols sig) (keys : Fin 3 → Variable) (r : ExtraRule) (v : Variable) :
    let eq := r.instantiate s (fun i => .var (keys i))
    eq.rhs.Occurs v → eq.lhs.Occurs v := scope (Bool.and_eq_true_iff.mp (extra_check s keys r)).2

theorem decreasing (tab : ExactTable E) : SymbolWeight.decreasing weight T.rules := by
  apply List.all_eq_true.mpr
  intro row mem
  rcases tab row mem with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · exact rule_check s _ r
  · exact extra_check s _ r

theorem terminating (tab : ExactTable E) : WellFounded fun b a => StepModulo (ruleRoot T.rules) a b :=
  SymbolWeight.terminating tab.decreasing

private theorem sortRule {env : Fin 3 → Term sig} (ty : ∀ i, HasSort (env i) .msg)
    {lhs rhs : Expr (Fin 3)} (app : Application (lhs.eval s env))
    (output : (lhs.eval s env).rootSort = .msg) :
    TableDecrease.sortRule ⟨lhs.eval s env,rhs.eval s env⟩ := by
  have typed := Term.checkSort_complete (rhs.sorted s env ty)
  generalize h : lhs.eval s env = l at app output ⊢
  cases l <;> simp_all [Application,TableDecrease.sortRule]

theorem sorted (tab : ExactTable E) : TableDecrease.sorted T.rules := by
  apply List.all_eq_true.mpr
  intro row hr
  rcases tab row hr with ⟨r,rfl⟩ | ⟨r,rfl⟩
  all_goals
    apply sortRule
    · intro i
      first
      | exact T.actualSort r i ▸ HasSort.var _
      | exact E.sorted r i ▸ HasSort.var _
    · exact tab.apps _ hr
    · cases r <;> first | exact s.mulSort | exact s.powSort | exact s.invSort

theorem sortPreserving (tab : ExactTable E) {a b : Term sig}
    (step : StepModulo (ruleRoot T.rules) a b) (k : SortId) (typed : HasSort a k) : HasSort b k :=
  TableDecrease.sortPreserving tab.sorted step k typed

end Tamarin.Rewriting.DHPeer.ExactTable
