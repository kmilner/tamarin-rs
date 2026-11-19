import Tamarin.DHPeerComplete
import Tamarin.DHTowerCallerSound
import Tamarin.DHTowerGroupedTuple

/-! Interpret the exported base-image packets as complete templates on the
caller's actual variables and a single shared valuation for arm-local names. -/
namespace Tamarin.Rewriting.DHTower.Caller
open DHPeer Packet VariantJoin
variable {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
private def masks : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (masks n).flatMap fun m => [false::m,true::m]

private theorem mem_masks {m : List Bool} : m ∈ masks m.length := by
  induction m with
  | nil => simp [masks]
  | cons b m ih => cases b <;> exact List.mem_flatMap.mpr ⟨m,ih,by simp⟩

private def recipes (n : Nat) : List Recipe :=
  [.unchanged,.neutral,.tower] ++ (masks n).flatMap fun m =>
    [.cancel m false false,.cancel m false true,.cancel m true false,.cancel m true true]

private theorem mem_recipes {r : Recipe} {n : Nat} (ok : r.Valid n) : r ∈ recipes n := by
  cases r with
  | unchanged | tower | neutral => simp [recipes]
  | cancel m p neg =>
    apply List.mem_append_right _ (List.mem_flatMap.mpr ⟨m,ok.1 ▸ mem_masks,?_⟩)
    cases p <;> cases neg <;> simp

/-- The interpretation uses only decoded rows from the actual export.
Several rows may describe the same template. -/
noncomputable def emitted (n : Nat) (rows : Array (Array UInt64)) : List {r : Recipe // r.Valid n} := by
  classical
  exact (recipes n).filterMap fun r =>
    if h : r.Valid n ∧ ∃ row ∈ rows, ∃ t, decode row = some t ∧ Reads n r t then some ⟨r,h.1⟩ else none

theorem mem_emitted {n : Nat} {rows} (r : Recipe) (h : r.Valid n)
    (live : ∃ row ∈ rows, ∃ t, decode row = some t ∧ Reads n r t) : ⟨r,h⟩ ∈ emitted n rows := by
  classical
  exact List.mem_filterMap.mpr ⟨r,mem_recipes h,by simp [h,live]⟩

private def witnessSub (q : Query sig) (b p n : Term sig)
    (sb : HasSort b .msg) (sp : HasSort p .msg) (sn : HasSort n .msg) : Substitution sig where
  image v := if v = q.var .base then b else if v = q.var .pos then p else if v = q.var .neg then n else .var v
  support := [q.var .base,q.var .pos,q.var .neg]
  outside := by intro v hv; simp_all
  sorted := by
    intro v; split
    · next eq => simpa [eq,q.sorted,Slot.sort] using sb
    · split
      · next eq => simpa [eq,q.sorted,Slot.sort] using sp
      · split
        · next eq => simpa [eq,q.sorted,Slot.sort] using sn
        · exact .var v

private theorem witness_normal {R : Root sig} (q : Query sig) {b p n : Term sig}
    {sb sp sn} (nb : Normal R b) (np : Normal R p) (nn : Normal R n) :
    ∀ v, q.witness v → Normal R ((witnessSub q b p n sb sp sn).image v) := by
  intro v hv; unfold witnessSub
  dsimp only; split <;> first | assumption | split <;> first | assumption | split <;> first | assumption | simp_all [Names.witness]

private noncomputable def chosen (q : Query sig) (ρ : Substitution sig) (b p n : Term sig) (sb sp sn) :=
  choose q.witness (witnessSub q b p n sb sp sn) ρ

private theorem chosen_slots (q : Query sig) (ρ : Substitution sig) (b p n : Term sig) (sb sp sn) :
    let δ := chosen q ρ b p n sb sp sn
    δ.apply (q.symbolic .peer) = ρ.image (q.var .peer) ∧
    δ.apply (q.symbolic .base) = b ∧ δ.apply (q.symbolic .pos) = p ∧ δ.apply (q.symbolic .neg) = n := by
  classical
  have eq (i j) : q.var i = q.var j ↔ i = j := ⟨q.distinct i j,congrArg q.var⟩
  simp [Names.symbolic,chosen,choose,Names.witness,witnessSub,Substitution.apply,Term.subst,eq]

private theorem chosen_factors (q : Query sig) (ρ : Substitution sig) (b p n : Term sig) (sb sp sn) :
    q.fs.map (chosen q ρ b p n sb sp sn).apply = q.fs.map ρ.apply := by
  classical
  apply List.map_congr_left
  intro t h
  exact Term.subst_eq_of_agree _ _ _ (fun v hv => by simp [chosen,choose,q.disjoint t h v hv])

private theorem sub_pow (δ : Substitution sig) (b e : Term sig) :
    δ.apply (s.power b e) = s.power (δ.apply b) (δ.apply e) := by
  apply congrArg (Term.free s.pow); funext i
  change δ.apply (if _ then _ else _) = (if _ then _ else _)
  split <;> rfl

private theorem sub_mul (δ : Substitution sig) (a b : Term sig) :
    δ.apply (s.product.mul a b) = s.product.mul (δ.apply a) (δ.apply b) := rfl

private theorem sub_neutral (δ : Substitution sig) : δ.apply s.neutralTerm = s.neutralTerm := by
  apply congrArg (Term.free s.neutral); funext i; exact Fin.elim0 (s.neutralArity ▸ i)

private theorem sub_one (δ : Substitution sig) : δ.apply s.product.one = s.product.one := by
  apply congrArg (Term.free s.one); funext i; exact Fin.elim0 (s.oneArity ▸ i)

private theorem sub_signed (δ : Substitution sig) (p n : Option (Term sig)) :
    δ.apply (Balance.assemble s p n) = Balance.assemble s (p.map δ.apply) (n.map δ.apply) := by
  cases p <;> cases n <;> first | rfl | exact sub_one δ

private theorem map_append (δ : Substitution sig) (p n : Option (Term sig)) :
    (DHTower.append s p n).map δ.apply = DHTower.append s (p.map δ.apply) (n.map δ.apply) := by cases p <;> cases n <;> rfl

private theorem sub_result (δ : Substitution sig) (b : Term sig) (p n : Option (Term sig)) :
    δ.apply (powerResult s b p n) = powerResult s (δ.apply b) (p.map δ.apply) (n.map δ.apply) := by
  cases p <;> cases n <;> first | rfl | exact sub_pow δ _ _

private theorem sub_fold (δ : Substitution sig) (a : Term sig) (xs : List (Term sig)) :
    δ.apply (ACRepresentation.fold s.mul a xs) = ACRepresentation.fold s.mul (δ.apply a) (xs.map δ.apply) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => exact congrArg (Term.ac s.mul (δ.apply a)) (ih b)

private theorem map_packed (δ : Substitution sig) (xs : List (Term sig)) :
    (packed s xs).map δ.apply = packed s (xs.map δ.apply) := by
  cases xs with
  | nil => rfl
  | cons x xs => exact congrArg some (sub_fold δ x xs)

private theorem parameter_map (δ : Substitution sig) (v : Variable) (a : Option (Term sig)) (default : Term sig)
    (value : δ.apply (.var v) = a.getD default) : (parameter sig a.isSome v).map δ.apply = a := by
  cases a <;> simp_all [parameter]

noncomputable def templates (q : Query sig) (s : Symbols sig) (rows : Array (Array UInt64)) :=
  (emitted q.fs.length rows).map fun r => template q s r.val r.property

private theorem predicted {R : Root sig} (q : Query sig) (ρ : Substitution sig)
    (hn : Normalized R ρ) (unit : Normal R s.product.one) {rows : Array (Array UInt64)}
    {row t out} (hm : row ∈ rows) (dec : decode row = some t)
    (prediction : Predicts s R q.fs.length (fun i => ρ.apply (q.factor i)) (ρ.image (q.var .peer))
       (ρ.apply (q.added s)) t out) :
    ∃ a ∈ templates q s rows, ∃ w : Substitution sig, (∀ v, q.witness v → Normal R (w.image v)) ∧
      let δ := choose q.witness w ρ
      EquivB (ρ.image (q.var .peer)) (δ.apply a.base) ∧ EquivB out (δ.apply a.value) := by
  classical
  let Y := ρ.image (q.var .peer)
  have sy : HasSort Y .msg := by simpa [Y,q.sorted,Slot.sort] using ρ.sorted (q.var .peer)
  have ny : Normal R Y := hn _
  have replay (r : Recipe) (h : r.Valid q.fs.length) (reads : Reads q.fs.length r t)
      (b p n : Term sig) (sb : HasSort b .msg) (sp : HasSort p .msg) (sn : HasSort n .msg)
      (nb : Normal R b) (np : Normal R p) (nn : Normal R n) :
      let δ := chosen q ρ b p n sb sp sn
      EquivB Y (δ.apply (r.base q s)) → EquivB out (δ.apply (r.value q s)) →
      ∃ a ∈ templates q s rows, ∃ w : Substitution sig, (∀ v, q.witness v → Normal R (w.image v)) ∧
        let δ := choose q.witness w ρ
        EquivB (ρ.image (q.var .peer)) (δ.apply a.base) ∧ EquivB out (δ.apply a.value) := by
    intro δ fits value
    have mem := mem_emitted r h ⟨_,hm,t,dec,reads⟩
    exact ⟨_,List.mem_map_of_mem (f := fun k : {r : Recipe // r.Valid q.fs.length} => template q s k.val k.property) mem,
      witnessSub q b p n sb sp sn,witness_normal q nb np nn,fits,value⟩
  have added (b p n : Term sig) (sb sp sn) : (chosen q ρ b p n sb sp sn).apply (q.added s) = ρ.apply (q.added s) := by
    have eq := chosen_factors q ρ b p n sb sp sn
    obtain ⟨one,tail⟩ := List.cons.inj eq
    simp only [Query.added,sub_fold,one,tail]
  cases prediction with
  | unchanged hv =>
    have slots := chosen_slots q ρ Y Y Y sy sy sy
    apply replay .unchanged trivial .unchanged Y Y Y sy sy sy ny ny ny
    · rw [Recipe.base,slots.1]; exact .refl _
    · simpa only [Recipe.value,sub_pow,slots.1,added] using hv
  | neutral hb hv =>
    apply replay .neutral trivial .neutral Y Y Y sy sy sy ny ny ny <;> simpa only [Recipe.base,Recipe.value,sub_neutral]
  | tower hb hv sb nb sp np =>
    rename_i b p
    have slots := chosen_slots q ρ b p Y sb sp sy
    apply replay .tower trivial .tower b p Y sb sp sy nb np ny
    · simpa only [Recipe.base,sub_pow,slots.2.1,slots.2.2.1] using hb
    · simpa only [Recipe.value,sub_pow,sub_mul,slots.2.1,slots.2.2.1,added] using hv
  | @cancelled t out m b p n i js sz sel image sb nb wp wn hb hv =>
    subst t
    have sortedOne : HasSort s.product.one .msg := by
      rw [← s.oneSort]; apply HasSort.free; intro j; exact Fin.elim0 (s.oneArity ▸ j)
    have defaultW {a} (h : Witness s R a) : HasSort (a.getD s.product.one) .msg ∧ Normal R (a.getD s.product.one) := by
      cases a with
      | none => exact ⟨sortedOne,unit⟩
      | some v => exact ⟨(h v rfl).1,(h v rfl).2.1⟩
    obtain ⟨sp,np⟩ := defaultW wp
    obtain ⟨sn,nn⟩ := defaultW wn
    let δ := chosen q ρ b (p.getD s.product.one) (n.getD s.product.one) sb sp sn
    let F := fun j => ρ.apply (q.factor j)
    have slots := chosen_slots q ρ b (p.getD s.product.one) (n.getD s.product.one) sb sp sn
    have pmap := parameter_map δ (q.var .pos) p s.product.one slots.2.2.1
    have nmap := parameter_map δ (q.var .neg) n s.product.one slots.2.2.2
    have fs : q.fs.map δ.apply = (List.range q.fs.length).map F := by
      rw [chosen_factors]
      change _ = (List.range q.fs.length).map (ρ.apply ∘ q.factor)
      simp only [← List.map_map,q.factorList]
    have selected : (packed s (select m q.fs)).map δ.apply = packed s ((i::js).map F) := by
      rw [map_packed,← select_map,fs,select_map,sel]
    have rest : (packed s (remaining m q.fs)).map δ.apply = packed s (remaining m ((List.range q.fs.length).map F)) := by
      rw [map_packed,remaining,← select_map,fs]; rfl
    have real : (Recipe.cancel m p.isSome n.isSome).Valid q.fs.length := ⟨sz,fun h => by rw [h] at sel; contradiction⟩
    apply replay _ real (.cancel sz sel) b (p.getD s.product.one) (n.getD s.product.one) sb sp sn nb np nn
    · change EquivB Y (δ.apply (s.power _ (Balance.assemble _ _ _)))
      rw [sub_pow,sub_signed,map_append,pmap,nmap,selected,slots.2.1]
      exact hb.trans (cancel_eval (s := s) F Y b p n i js).symm
    · change EquivB out (δ.apply (powerResult _ _ _ _))
      rw [sub_result,map_append,pmap,nmap,rest,slots.2.1]
      exact hv

/-- The live kernel's packet set discharges the local factorization
obligation for every normalized substitution, including substitutions
identifying two exponent occurrences. -/
theorem factors {run : Kernel} (ok : Correct run)
    {width : UInt64}
    {rows : Array (Array UInt64)} (ran : run width = some rows)
    (inventory : Balance.Inventory E) (pow : PowerBucket T) (mul : MulBucket E) (inv : InverseBucket E)
    (unit : Normal (ruleRoot T.rules) s.product.one) (q : Query sig)
    (size : width.toNat = q.fs.length)
    (stable : ∀ t ∈ q.fs, StableFactor s (ruleRoot T.rules) t) :
    Tuple.Factors (R := ruleRoot T.rules) (templates q s rows) q.witness (q.op s) := by
  intro ρ hn out form
  let F := fun i => ρ.apply (q.factor i)
  have fs : (List.range width.toNat).map F = q.fs.map ρ.apply := by
    rw [size]
    change (List.range _).map (ρ.apply ∘ q.factor) = _
    simp only [← List.map_map,q.factorList]
  have each (x) (hx : x ∈ q.fs.map ρ.apply) : HasSort x .msg ∧ Normal (ruleRoot T.rules) x ∧ Factor s x := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact ⟨(q.sortedFactors a ha).subst _ ρ.sorted,stable a ha ρ hn⟩
  have component (i) (h : i < width.toNat) := each (F i) (fs ▸ List.mem_map_of_mem (f := F) (List.mem_range.mpr h))
  have sy : HasSort (ρ.image (q.var .peer)) .msg := by simpa [q.sorted,Slot.sort] using ρ.sorted (q.var .peer)
  have flat := positive_tower_iff inventory pow mul inv unit (ρ.image (q.var .peer)) (ρ.apply q.first)
    (q.rest.map ρ.apply) sy (hn _) (fun t h => each t h) out
  rw [Tuple.apply_tower] at form
  have added : packed s ((List.range width.toNat).map F) = some (ρ.apply (q.added s)) := by
    rw [fs,← map_packed]
    rfl
  obtain ⟨row,hm,t,dec,prediction⟩ := classify_linked ok ran inventory pow mul unit F added
    (fun i h => (component i h).2.2) (fun i h => (component i h).2.1) (fun i h => (component i h).1) sy (hn _)
    (by simpa only [Query.added,sub_fold] using flat.mp form)
  exact predicted q ρ hn unit hm dec (size ▸ prediction)

private theorem choose_positions {α : Type} {xs ys : List α} (sub : xs.Sublist ys) :
    ∃ m, m.length = ys.length ∧ select m ys = xs := by
  induction sub with
  | slnil => exact ⟨[],rfl,rfl⟩
  | cons _ _ ih =>
    obtain ⟨m,h,eq⟩ := ih
    exact ⟨false::m,congrArg Nat.succ h,eq⟩
  | cons_cons x _ ih =>
    obtain ⟨m,h,eq⟩ := ih
    exact ⟨true::m,congrArg Nat.succ h,congrArg (List.cons x) eq⟩

/-- Every row physically returned by the export contributes an interpreted
template, including repeated occurrences and arbitrary implementation order. -/
theorem reads_all {run : Kernel} (ok : Correct run) {width : UInt64}
    {rows} (ran : run width = some rows)
    {row} (hr : row ∈ rows) : ∃ t, decode row = some t ∧ ∃ r ∈ emitted width.toNat rows, Reads width.toNat r.val t := by
  obtain ⟨read,exactSet⟩ := ok.describes width rows ran
  obtain ⟨t,decoded⟩ := Option.isSome_iff_exists.mp (read row hr)
  refine ⟨t,decoded,?_⟩
  have enters (r : Recipe) (h : r.Valid width.toNat) (meaning : Reads width.toNat r t) :
      ∃ a ∈ emitted width.toNat rows, Reads width.toNat a.val t :=
    ⟨⟨r,h⟩,mem_emitted r h ⟨row,hr,t,decoded,meaning⟩,meaning⟩
  rcases (exactSet t).mp ⟨row,hr,decoded⟩ with rfl|rfl|rfl|⟨i,js,sub,p,n,rfl⟩
  · exact enters .unchanged trivial .unchanged
  · exact enters .neutral trivial .neutral
  · exact enters .tower trivial .tower
  · obtain ⟨m,sz,sel⟩ := choose_positions sub
    simp only [List.length_range] at sz
    exact enters (.cancel m p n) ⟨sz,fun h => by rw [h] at sel; contradiction⟩ (.cancel sz sel)

def symbolicEnv (q : Query sig) : Arg → Term sig :=
  env (q.symbolic .peer) (q.symbolic .base) (q.symbolic .pos) (q.symbolic .neg) q.factor

private theorem product_eval (s : Symbols sig) (F : Nat → Term sig) (Y b p n : Term sig) (i js) :
    (product i js).eval s (env Y b p n F) = js.foldl (fun a j => s.product.mul a (F j)) (F i) := by
  suffices ∀ (t : Image), (js.foldl (fun a j => .mul a (.var (.factor j))) t).eval s (env Y b p n F) =
      js.foldl (fun a j => s.product.mul a (F j)) (t.eval s (env Y b p n F)) from this (.var (.factor i))
  induction js with
  | nil => intro t; rfl
  | cons j js ih => intro t; exact ih _

/-- Relate the base term Rust obtains by evaluating the returned row to the
canonical representative used to certify its normal output. Noncommutative
arguments retain their positions. AC factors may use a different association. -/
theorem Reads.base_equiv (q : Query sig) {r : Recipe} {t : Image} (read : Reads q.fs.length r t) :
    EquivB (r.base q s) (t.eval s (symbolicEnv q)) := by
  cases read with
  | unchanged | neutral | tower => exact .refl _
  | @cancel m p n i js _ take =>
    let b := q.symbolic (sig := sig) .base
    let Y := q.symbolic (sig := sig) .peer
    let pos := parameter sig p (q.var .pos)
    let neg := parameter sig n (q.var .neg)
    have eq := cancel_eval (s := s) q.factor Y b pos neg i js
    dsimp only at eq
    rw [←take,←select_map,q.factorList] at eq
    change EquivB _ ((Packet.cancel _ p n).eval s (env _ _ _ _ q.factor))
    cases p <;> cases n <;>
      simpa only [Recipe.base,b,Y,Names.symbolic,pos,neg,parameter,ite_true,Bool.false_eq_true,ite_false,Option.isSome_some,
        Option.isSome_none,Option.getD_some,Option.getD_none,Packet.cancel,Expr.eval,env,product_eval] using eq

/-- Caller-level semantics of the linked kernel. The bridge supplies the
original observation layout and its witnessed range allocation. All algebraic
premises concern the live theory and query, independently of the returned
programs or their particular witness values. -/
def Semantic (run : Kernel) : Prop :=
  ∀ {sig : Signature} {s : Symbols sig} {T : Table s} {E : ExtraTable T}
    {width : UInt64}
    {packet : Array (Array UInt64)} (_ : run width = some packet)
    (_ : PowerBucket T) (_ : MulBucket E) (_ : InverseBucket E)
    (_ : ∀ eq ∈ T.rules, ConstructorVariants.head eq.lhs ≠ .free s.one)
    (_ : ∀ eq ∈ T.rules, ConstructorVariants.head eq.lhs ≠ .free s.neutral)
    (q : Query sig) (_ : width.toNat = q.fs.length)
    (_ : ∀ t ∈ q.fs, StableFactor s (ruleRoot T.rules) t)
    (firstGroup : Term sig) (groups : List (Term sig))
    (_ : ∀ g ∈ firstGroup :: groups, ∃ part, packed s part = some g ∧ ∀ r ∈ part, r ∈ q.fs)
    (_ : EquivB (ACRepresentation.fold s.mul firstGroup groups) (q.added s))
    {keys : List Variable} (_ : ∀ v ∈ keys, ¬q.witness v)
    (rows : List (Row sig (Key keys) Unit))
    (_ : ∀ t ∈ templates q s packet, ∃ r ∈ rows, (t.row keys).Relabels r)
    (_ : ∀ r ∈ rows, ∃ t ∈ templates q s packet, (t.row keys).Relabels r)
    (slots : List (Sum Unit (Term sig))) (_ : Sum.inl () ∈ slots)
    (repr : Term sig → Term sig)
    (_ : ∀ t, .inr t ∈ slots → StableVariants.Representative (ruleRoot T.rules) t (repr t))
    (_ : ∀ v, v ∈ keys ↔ Observed (slots.map (packedInput (fun _ : Unit => Spine.tower s (q.symbolic .peer) firstGroup groups))) v)
    (avoid : List Variable) (_ : ∀ r ∈ rows, ∀ v, r.Uses v → v ∉ keys ++ avoid),
    (∀ row ∈ packet, ∃ t, decode row = some t ∧ ∃ r ∈ emitted q.fs.length packet,
      Reads q.fs.length r.val t ∧ EquivB (r.val.base q s) (t.eval s (symbolicEnv q))) ∧
    ∃ typedRows : ∀ r ∈ rows, r.Sorted,
      let query := slots.map (packedInput (fun _ : Unit => Spine.tower s (q.symbolic .peer) firstGroup groups))
      let answers := packRows rows typedRows slots repr
      CompleteVariants (ruleRoot T.rules) query answers ∧ ∀ a ∈ answers,
        a.Reconstructible (ruleRoot T.rules) query ∧ a.Safe query avoid ∧ ∀ v, a.subst.apply (a.subst.image v) = a.subst.image v

theorem certified {run : Kernel} (ok : Correct run) : Semantic run := by
  intro sig s T E width packet ran pow mul inv one neutral q size stable firstGroup groups grouping layout keys apart rows allRows onlyRows slots used repr uniform scope avoid fresh
  constructor
  · intro row hm
    have dec := reads_all ok ran hm
    rw [size] at dec
    obtain ⟨t,hd,r,hr,meaning⟩ := dec
    exact ⟨t,hd,r,hr,meaning,meaning.base_equiv q⟩
  have vars := (ConstructorVariants.constructor_normal _ pow.1).1
  have unit := normalConstant _ pow.1 _ s.oneArity one
  have neut := normalConstant _ pow.1 _ s.neutralArity neutral
  have inventory := Balance.Inventory.of_buckets mul inv one
  have obs := grouped_observation inventory pow mul inv unit q firstGroup groups stable grouping
    (Cancellation.flatten_equiv s.mul layout)
  have refScope (v) : v ∈ keys ↔ Observed (slots.map (packedInput (fun _ : Unit => q.op s))) v := by
    rw [scope]
    constructor <;> rintro ⟨_,mem,occ⟩ <;> obtain ⟨k,hk,rfl⟩ := List.mem_map.mp mem <;>
      refine ⟨_,List.mem_map_of_mem (f := packedInput _) hk,?_⟩ <;> cases k <;>
      first | exact occ | exact (obs.observes v).mp occ | exact (obs.observes v).mpr occ
  have types := Spine.tower_typed s q.rest (q.typed .peer) (q.sortedFactors q.first List.mem_cons_self)
    (fun t h => q.sortedFactors t (List.mem_cons_of_mem _ h))
  have typed : HasSort (q.op s) (q.op s).rootSort := types.2 ▸ types.1
  have rowsSound (t) (ht : t ∈ templates q s packet) :
      Normal (ruleRoot T.rules) t.base ∧ NormalForm (ruleRoot T.rules) (t.subst.apply (q.op s)) t.value := by
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ht
    have initial (x) (h : x ∈ q.fs) : Normal (ruleRoot T.rules) x ∧ Factor s x := by simpa using stable x h .identity vars
    exact symbolic pow mul inv unit neut q (fun x h => (initial x h).1) (fun x h => (initial x h).2) r.val r.property
  obtain ⟨typedRows,hc,hr⟩ := Tuple.complete (templates q s packet) q.witness apart (q.op s) typed vars rowsSound
    (factors ok ran inventory pow mul inv unit q size stable)
    (Tuple.unique_instances pow inventory unit (q.var .peer) (q.sorted .peer) q.first q.rest q.sortedFactors
      (fun t h σ hσ => (stable t h σ hσ).1))
    rows allRows onlyRows slots used repr uniform refScope avoid fresh
  exact ⟨typedRows,grouped_tuple obs slots _ avoid hc hr⟩

end Tamarin.Rewriting.DHTower.Caller
