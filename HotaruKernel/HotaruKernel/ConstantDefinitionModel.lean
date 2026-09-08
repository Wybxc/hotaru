import HotaruKernel.ConstantDefinition

namespace HotaruKernel.ConstantDefinition

variable {t : Theory}

theorem declared_type (d : ConstantDefinition t) (a : HolType)
    (h : d.signature.constants.lookup d.name = some a) : a = d.type := by
  have ha : d.type = a := by simpa [signature, Signature.addConstant] using h
  exact ha.symm

noncomputable def family (d : ConstantDefinition t) (p : PolymorphicModel t.signature)
    (n : QName) (a : HolType) (hd : d.signature.constants.lookup n = some a)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) : m.interp a :=
  if hn : n = d.name then
    cast (congrArg m.interp (d.declared_type a (hn ▸ hd)).symm) (d.rhs.closedValue p m hm)
  else p.constant n a (by
    simpa [signature, Signature.addConstant, List.lookup_cons,
      beq_eq_false_iff_ne.mpr hn] using hd) m hm

noncomputable def interpretation (d : ConstantDefinition t) (p : PolymorphicModel t.signature) :
    PolymorphicModel d.signature where
  typeOp := p.typeOp
  op_nonempty := p.op_nonempty
  constant := d.family p
  constant_support n a hd m₁ m₂ h₁ h₂ hv := by
    by_cases hn : n = d.name
    · have ha := d.declared_type a (hn ▸ hd)
      subst a
      simp only [family, hn, ↓reduceDIte, cast_eq]
      exact d.rhs.closedValue_support d.closed p m₁ m₂ h₁ h₂
        (fun k hk => hv k (d.supported k hk))
    · simp only [family, hn, ↓reduceDIte]
      exact p.constant_support n a _ m₁ m₂ h₁ h₂ hv

theorem interpretation_restrict (d : ConstantDefinition t) (p : PolymorphicModel t.signature) :
    (d.interpretation p).restrict d.extendsSignature = p := by
  cases p with
  | mk typeOp op_nonempty constant constant_support =>
    unfold PolymorphicModel.restrict interpretation
    congr 1
    funext n a hd m hm
    have hn : n ≠ d.name := by intro hn; subst n; rw [d.fresh] at hd; cases hd
    simp only [family, hn, ↓reduceDIte]

theorem constant_value (d : ConstantDefinition t) (p : PolymorphicModel t.signature)
    (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv ((d.interpretation p).atTypes m hm)) :
    d.constant.eval ((d.interpretation p).atTypes m hm) f BoundEnv.nil =
      d.rhs.closedValue p m hm := by
  apply eq_of_heq
  apply (Term.eval_cast (HolType.inst_nil d.type) _ _ _ _).trans
  change HEq (((d.interpretation p).atTypes m hm).constant d.name (d.type.inst []) _)
    (d.rhs.closedValue p m hm)
  rw [(d.interpretation p).atTypes_constant m hm d.name d.type
    (by simp [signature, Signature.addConstant]) []]
  apply ((d.interpretation p).instanceValue_heq m hm d.name d.type
    (by simp [signature, Signature.addConstant]) []).trans
  simp only [interpretation, family, ↓reduceDIte, cast_eq]
  rfl

theorem equation_valid (d : ConstantDefinition t) (p : PolymorphicModel t.signature)
    (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv ((d.interpretation p).atTypes m hm)) :
    d.equation.eval ((d.interpretation p).atTypes m hm) f BoundEnv.nil = true := by
  apply (eval_equal_true _ _ _ _ _).mpr
  apply (d.constant_value p m hm f).trans
  have hr := Term.eval_rebase_polymorphic d.rhs d.extendsSignature (d.interpretation p)
    m hm f BoundEnv.nil
  have hc := d.rhs.closedValue_eq_eval d.closed ((d.interpretation p).restrict d.extendsSignature)
    m hm f
  have hp := d.rhs.closedValue_congr _ p (d.interpretation_restrict p) m hm hm
  exact hp.symm.trans (hc.trans hr.symm)

theorem interpretation_models (d : ConstantDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) : Models d.target (d.interpretation p) := by
  have old : Models (t.withSignature d.signature d.extendsSignature) (d.interpretation p) := by
    apply (t.models_withSignature_iff _ _ _).mpr
    rw [d.interpretation_restrict p]
    exact hp
  intro m hm f q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact d.equation_valid p m hm f
  · exact old m hm f q hq

theorem model_extension (d : ConstantDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) :
    ∃ q : PolymorphicModel d.target.signature,
      Models d.target q ∧ q.restrict d.extension.extension.signature = p :=
  ⟨d.interpretation p, d.interpretation_models p hp, d.interpretation_restrict p⟩

end HotaruKernel.ConstantDefinition
