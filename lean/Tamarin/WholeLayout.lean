import Tamarin.WholeOrdering

namespace Tamarin.Whole

/-- Remove a nested application of the same AC symbol, at any depth. The
ordered child lists retain every occurrence. A binary source tree can be
represented by any mixture of binary and flat rows obtained this way. -/
inductive Layout : Tree → Tree → Prop where
  | refl (t) : Layout t t
  | trans {a b d : Tree} : Layout a b → Layout b d → Layout a d
  | child {a b : Tree} (k i) (pre post : List Tree) : Layout a b →
      Layout (.app k i (pre ++ a :: post)) (.app k i (pre ++ b :: post))
  | flatten (i) (pre inner post : List Tree) :
      Layout (.app 4 i (pre ++ .app 4 i inner :: post)) (.app 4 i (pre ++ inner ++ post))

/-- A single row represents a binary fold of arbitrarily many children,
including repeated references. The caller may already have flattened a prefix. -/
theorem Layout.fold_children (i : UInt64) (pre tail : List Tree) {t : Tree}
    (h : Layout t (.app 4 i pre)) :
    Layout (tail.foldl (fun acc x => .app 4 i [acc, x]) t) (.app 4 i (pre ++ tail)) := by
  induction tail generalizing pre t with
  | nil => simpa using h
  | cons x xs ih =>
    have nested := Layout.child 4 i [] [x] h
    have step := nested.trans (Layout.flatten i [] pre [x])
    simpa using ih (pre ++ [x]) step

private theorem canon_args (ts : List Tree) : canonicalArgs ts = ts.map canonical := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [canonicalArgs, ih]

private theorem ground_list (ts : List Tree) : groundArgs ts = ts.all ground := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [groundArgs, ih]

/-- Flattening preserves the equality decision and the closed-clash test. -/
theorem Layout.observations {a b : Tree} (h : Layout a b) :
    canonical a = canonical b ∧ ground a = ground b := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | trans _ _ ih hj => exact ⟨ih.1.trans hj.1, ih.2.trans hj.2⟩
  | child k i pre post _ ih =>
    constructor
    · simp only [canonical, canon_args, List.map_append, List.map_cons, ih.1]
    · simp only [ground, ground_list, List.all_append, List.all_cons, ih.2]
  | flatten i pre inner post =>
    constructor
    · simp only [canonical, canon_args, make, ite_true, List.map_append, List.map_cons,
        List.flatMap_append, List.flatMap_cons]
      simp only [parts, ↓reduceIte]
      apply congrArg (Tree.app 4 i)
      apply order_eq_of_perm
      rw [List.append_assoc]
      exact ((order_perm _).append_right _).append_left _
    · simp [ground, ground_list, List.all_append]

/-- A flat row with valid references decodes to precisely those children, in
order and with multiplicity, including child rows shared by other roots. -/
theorem decode_flat_row (ds : List Decl) (prior : Array (Tree × UInt64)) (id : UInt64)
    (refs : List UInt64) (d : Decl) (children : List (Tree × UInt64))
    (declared : ds.find? (fun d => d.kind == 4 && d.id == id) = some d)
    (resolve : refs.mapM (fun i => prior[i.toNat]?) = some children)
    (arity : 2 ≤ children.length)
    (sorted : children.all (fun c => subsort c.2 d.output) = true) :
    decodeNode ds prior ((4 :: id :: refs).toArray) =
      some (.app 4 id (children.map Prod.fst), d.output) := by
  simp [decodeNode, declared, resolve, arity, sorted, guard]

end Tamarin.Whole
