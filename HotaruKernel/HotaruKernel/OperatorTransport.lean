import HotaruKernel.ModelAgreement
import HotaruKernel.TheoryExtension

namespace HotaruKernel

variable {s : Signature}

theorem Signature.WellFormed.constant_type {name : QName} (h : s.WellFormed)
    (hd : s.constants.lookup name = some a) : s.validType a = true := by
  obtain ⟨l, r, hl, _⟩ := List.lookup_eq_some_iff.mp hd
  apply h.2.2 (name, a)
  rw [hl]
  exact List.mem_append_right _ (List.mem_cons_self ..)

namespace PolymorphicModel

def oldTypes (p : PolymorphicModel s) (m : TypeModel) : TypeModel where
  typeVar := m.typeVar
  typeOp := p.typeOp
  var_nonempty := m.var_nonempty
  op_nonempty := p.op_nonempty

structure OperatorExtension (p : PolymorphicModel s) where
  typeOp : QName → List Type → Type
  op_nonempty : ∀ name args, (∀ A ∈ args, Nonempty A) → Nonempty (typeOp name args)
  agrees : ∀ name arity, s.typeOps.lookup name = some arity →
    ∀ args, args.length = arity → p.typeOp name args = typeOp name args

namespace OperatorExtension

variable {s u : Signature} {p : PolymorphicModel s}

theorem types_agree (o : OperatorExtension p) (m : TypeModel) (hm : m.typeOp = o.typeOp) :
    TypeModel.Agrees s (p.oldTypes m) m := by
  refine ⟨fun _ => rfl, ?_⟩
  intro name arity hd args ha
  change p.typeOp name args = m.typeOp name args
  rw [hm]
  exact o.agrees name arity hd args ha

noncomputable def interpretation (o : OperatorExtension p) (hw : s.WellFormed)
    (hc : u.constants = s.constants) : PolymorphicModel u where
  typeOp := o.typeOp
  op_nonempty := o.op_nonempty
  constant name a hd m hm :=
    cast ((o.types_agree m hm).interp a (hw.constant_type (hc ▸ hd)))
      (p.constant name a (hc ▸ hd) (p.oldTypes m) rfl)
  constant_support name a hd m₁ m₂ h₁ h₂ hv := by
    apply (cast_heq _ _).trans
    apply HEq.trans _ (cast_heq _ _).symm
    exact p.constant_support name a (hc ▸ hd) (p.oldTypes m₁) (p.oldTypes m₂) rfl rfl hv

theorem instance_agrees (o : OperatorExtension p) (hw : s.WellFormed)
    (hc : u.constants = s.constants) (m : TypeModel) (hm : m.typeOp = o.typeOp)
    (name : QName) (scheme : HolType) (hd : s.constants.lookup name = some scheme)
    (i : TypeSubst) (hv : s.validType (scheme.inst i) = true) :
    HEq (p.instanceValue (p.oldTypes m) rfl name scheme hd i)
      ((o.interpretation hw hc).instanceValue m hm name scheme (hc ▸ hd) i) := by
  apply (p.instanceValue_heq _ _ name scheme hd i).trans
  apply HEq.trans _ ((o.interpretation hw hc).instanceValue_heq m hm name scheme (hc ▸ hd) i).symm
  change HEq (p.constant name scheme hd ((p.oldTypes m).instantiate i) rfl)
    (cast _ (p.constant name scheme hd (p.oldTypes (m.instantiate i)) rfl))
  apply HEq.trans _ (cast_heq _ _).symm
  apply p.constant_support
  intro k hk
  exact (o.types_agree m hm).interp _ (scheme.valid_inst_variable i s hv k hk)

theorem models_agree (o : OperatorExtension p) (hw : s.WellFormed)
    (hc : u.constants = s.constants) (m : TypeModel) (hm : m.typeOp = o.typeOp) :
    Model.Agrees s (p.atTypes (p.oldTypes m) rfl) ((o.interpretation hw hc).atTypes m hm) := by
  refine ⟨o.types_agree m hm, ?_⟩
  intro name a hv hs hu
  obtain ⟨scheme, i, hd, rfl⟩ := hs
  rw [p.atTypes_constant, (o.interpretation hw hc).atTypes_constant m hm name scheme (hc ▸ hd) i]
  exact o.instance_agrees hw hc m hm name scheme hd i hv

end OperatorExtension
end PolymorphicModel

theorem Theory.models_changeOperators (t : Theory) (p : PolymorphicModel t.signature)
    (hp : Models t p) (o : p.OperatorExtension) (hw : t.signature.WellFormed)
    (h : t.signature.Extends u) (hc : u.constants = t.signature.constants) :
    Models (t.withSignature u h) (o.interpretation hw hc) := by
  intro m hm f r hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  have agree := o.models_agree hw hc m hm
  have he := q.eval_agrees h (p.atTypes (p.oldTypes m) rfl)
    ((o.interpretation hw hc).atTypes m hm) agree (agree.pullFree f) f BoundEnv.nil BoundEnv.nil
    (fun _ h => by cases h)
    (fun name a ha => agree.pullFree_heq f a name (q.freeVar_valid name a ha))
    (fun _ v => by cases v)
  exact (eq_of_heq he).symm.trans (hp (p.oldTypes m) rfl (agree.pullFree f) q hq)

end HotaruKernel
