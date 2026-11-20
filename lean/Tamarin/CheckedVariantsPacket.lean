import Tamarin.CheckedVariantsWire
import Tamarin.DefinitionCertificate
import Tamarin.TotalInputBounds

namespace Tamarin.ConstantDefinitions
open SignatureExtension
variable {s : Signature} {rs : Problem s} (extra : Signature)

private theorem ground_embed {t : Term s} (ctor : GroundConstructor rs t) :
    GroundConstructor (query extra rs) (embed extra t) := by
  induction t with
  | var _ => exact ctor.elim
  | atom _ => trivial
  | free f xs ih =>
    refine ⟨?_,fun i => ih i (ctor.2 i)⟩
    intro eq mem args same
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
    exact ctor.1 r hr (fun i => restrictTerm (args i)) (by
      simpa only [restrict_embed,restrictTerm] using congrArg (restrictTerm (s := s) (x := extra)) same)
  | comm _ _ _ l r | ac _ _ _ l r => exact ⟨l ctor.1,r ctor.2⟩

/-- Adding ambient constructors or names preserves the class, even when the
caller later instantiates variables with terms outside the packet dictionary. -/
theorem Presentation.embed (cls : Presentation rs) : Presentation (query extra rs) where
  shapes := by
    intro eq mem
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
    obtain ⟨f,xs,shape,arity,clean⟩ := cls.shapes r hr
    exact ⟨.inl f,fun i => SignatureExtension.embed extra (xs i),congrArg _ shape,arity,ground_embed extra clean⟩
  coherent := by
    intro l hl r hr equal
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
    exact embed_eq (cls.coherent a ha b hb (by
      simpa only [restrict_embed] using congrArg (restrictTerm (s := s) (x := extra)) equal))

theorem Presentation.sorted_embed (cls : Presentation rs) (sorted : TableDecrease.sorted rs) :
    TableDecrease.sorted (query extra rs) := by
  apply List.all_eq_true.mpr
  intro eq mem
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp mem
  obtain ⟨f,xs,h,_,_⟩ := cls.shapes r hr
  have base := List.all_eq_true.mp sorted r hr
  simp only [TableDecrease.sortRule,h] at base
  simp only [TableDecrease.sortRule,h]
  exact Term.checkSort_complete (embed_sort (Term.checkSort_sound _ _ base))

end Tamarin.ConstantDefinitions

namespace Tamarin.CheckedVariantsWire
open TotalUnifyWire Rewriting MaudeOperations

abbrev Kernel := Array UInt64 → Array (Array UInt64) → Array UInt64 → Array UInt64 → UInt64 → Array (Array UInt64)

def Required {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig)) (fuel : UInt64) : Prop :=
  ∃ rows, search rs q fuel = some rows ∧ ∃ wire, TableAmbient.emit q rows.val = some wire

def Decodes {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig)) (wire : Array (Array UInt64)) :=
  ∃ rows, TableAmbient.Decodes q wire rows ∧
    CheckedVariants.Reply (ruleRoot (TableAmbient.liftRules rs)) (q.map TableAmbient.liftTerm) rows

private def DefinitionAnswer {d : Dictionary} (rs : Problem d.sig) (q : List (Term d.sig))
    (wire : Array (Array UInt64)) : Prop :=
  let table := TableAmbient.liftRules rs
  let query := q.map TableAmbient.liftTerm
  let rows := [⟨.identity,query.map (ConstantDefinitions.expand table)⟩]
  TableAmbient.Decodes q wire rows ∧ CheckedVariants.Reply (ruleRoot table) query rows

private theorem identityPacket {ds ns es roots d rs q}
    (decoded : TableWire.input ds ns es roots = some ⟨d,rs,q⟩) :
    ∃ wire, pack (TableAmbient.observations q) [.identity] = some wire := by
  apply Packet.pack_exists
  intro σ hσ v hv
  obtain rfl := List.mem_singleton.mp hσ
  obtain ⟨t,ht,occ⟩ := (TableAmbient.inventory q v).mp hv
  have fits := Packet.var_fits t v occ ((TableWire.input_fits decoded).2 t ht)
  exact ⟨fits,fits⟩

private theorem definitionAnswer {ds ns es roots d rs q} (fuel : UInt64)
    (decoded : TableWire.input ds ns es roots = some ⟨d,rs,q⟩) (ok : definitions rs) :
    DefinitionAnswer rs q (run ds ns es roots fuel) := by
  let table := TableAmbient.liftRules rs
  let query := q.map TableAmbient.liftTerm
  let values := query.map (ConstantDefinitions.expand table)
  obtain ⟨packet,hp⟩ := identityPacket decoded
  have wire : TableAmbient.emit q [⟨.identity,values⟩] = some packet :=
    (TableAmbient.emit_identity q values).trans hp
  simp only [run,decoded,ok,ite_true,hp,Option.getD_some]
  obtain ⟨accepted,sorted⟩ := Bool.and_eq_true_iff.mp ok
  have cls := (ConstantDefinitions.accepts_iff rs).mp accepted
  exact ⟨TableAmbient.emit_correct wire,DefinitionCertificate.reply
    ((ConstantDefinitions.accepts_iff table).mpr (cls.embed TableAmbient.atoms))
    (cls.sorted_embed TableAmbient.atoms sorted) query⟩

structure Correct (kernel : Kernel) : Prop where
  definitions_complete : ∀ ds ns pairs roots n d rs q,
    TableWire.input ds ns pairs roots = some ⟨d,rs,q⟩ →
      ConstantDefinitions.Presentation rs → (∀ r ∈ rs, HasSort r.rhs r.lhs.rootSort) →
      Decodes rs q (kernel ds ns pairs roots n)
  malformed : ∀ ds ns rs qs n, TableWire.input ds ns rs qs = none → kernel ds ns rs qs n = #[#[0]]
  valid : ∀ ds ns pairs roots n d rs q, TableWire.input ds ns pairs roots = some ⟨d,rs,q⟩ →
    Decodes rs q (kernel ds ns pairs roots n) ∨
      (kernel ds ns pairs roots n = #[#[2]] ∧ ¬ Required rs q n)

theorem correct : Correct run where
  definitions_complete := fun _ _ _ _ n _ rs _ h cls typed =>
    ⟨_,definitionAnswer n h (Bool.and_eq_true_iff.mpr
      ⟨(ConstantDefinitions.accepts_iff rs).mpr cls,(DefinitionCertificate.sorted_iff cls).mpr typed⟩)⟩
  malformed := by intros; simp_all [run]
  valid := by
    intro ds ns pairs roots n d rs q decoded
    by_cases cls : definitions rs
    · exact .inl ⟨_,definitionAnswer n decoded cls⟩
    simp only [run,decoded,ite_eq_right cls]
    cases h : search rs q n with
    | none => exact .inr ⟨rfl,by simp [Required,h]⟩
    | some rows =>
      cases g : TableAmbient.emit q rows.val with
      | some packet =>
        exact .inl ⟨rows.val,by simpa [g] using TableAmbient.emit_correct g,rows.property⟩
      | none => exact .inr ⟨by simp [g],by simp [Required,h,g]⟩

end Tamarin.CheckedVariantsWire
