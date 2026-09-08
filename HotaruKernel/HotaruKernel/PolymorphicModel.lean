import HotaruKernel.TypeVariables

namespace HotaruKernel

/-! A constant is a family over the type parameters in its declared scheme.
The support condition concerns interpretation data, not inference soundness. -/
structure PolymorphicModel (s : Signature) where
  typeOp : QName → List Type → Type
  op_nonempty : ∀ n args, (∀ a ∈ args, Nonempty a) → Nonempty (typeOp n args)
  constant : (n : QName) → (scheme : HolType) → s.constants.lookup n = some scheme →
    (m : TypeModel) → m.typeOp = typeOp → m.interp scheme
  constant_support : ∀ n scheme hd (m₁ m₂ : TypeModel)
    (h₁ : m₁.typeOp = typeOp) (h₂ : m₂.typeOp = typeOp),
    (∀ k ∈ scheme.vars, m₁.typeVar k = m₂.typeVar k) →
    HEq (constant n scheme hd m₁ h₁) (constant n scheme hd m₂ h₂)

noncomputable def PolymorphicModel.instanceValue (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) (n : QName) (scheme : HolType)
    (hd : s.constants.lookup n = some scheme) (i : TypeSubst) : m.interp (scheme.inst i) :=
  cast (m.interp_instantiate i scheme) (p.constant n scheme hd (m.instantiate i) hm)

theorem PolymorphicModel.instanceValue_heq (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) (n : QName) (scheme : HolType)
    (hd : s.constants.lookup n = some scheme) (i : TypeSubst) :
    HEq (p.instanceValue m hm n scheme hd i)
      (p.constant n scheme hd (m.instantiate i) hm) := cast_heq _ _

theorem PolymorphicModel.instanceValue_coherent (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) (n : QName) (scheme : HolType)
    (hd : s.constants.lookup n = some scheme) (i j : TypeSubst)
    (h : scheme.inst i = scheme.inst j) :
    HEq (p.instanceValue m hm n scheme hd i) (p.instanceValue m hm n scheme hd j) := by
  apply (p.instanceValue_heq m hm n scheme hd i).trans
  apply HEq.trans _ (p.instanceValue_heq m hm n scheme hd j).symm
  apply p.constant_support
  intro k hk
  exact congrArg m.interp (scheme.inst_injective_on_vars i j h k hk)

noncomputable def PolymorphicModel.atTypes (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) : Model s where
  toTypeModel := m
  constant n _ h :=
    let scheme := h.choose
    let i := h.choose_spec.choose
    let hi := h.choose_spec.choose_spec
    cast (congrArg m.interp hi.2) (p.instanceValue m hm n scheme hi.1 i)

theorem PolymorphicModel.atTypes_constant (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) (n : QName) (scheme : HolType)
    (hd : s.constants.lookup n = some scheme) (i : TypeSubst)
    (h : ∃ a j, s.constants.lookup n = some a ∧ a.inst j = scheme.inst i) :
    (p.atTypes m hm).constant n (scheme.inst i) h = p.instanceValue m hm n scheme hd i := by
  apply eq_of_heq
  change HEq (cast _ _) _
  apply (cast_heq _ _).trans
  have coherent : ∀ a (ha : s.constants.lookup n = some a) j,
      a.inst j = scheme.inst i →
      HEq (p.instanceValue m hm n a ha j) (p.instanceValue m hm n scheme hd i) := by
    intro a ha j hj
    have hs : a = scheme := Option.some.inj (ha.symm.trans hd)
    subst a
    exact p.instanceValue_coherent m hm n scheme hd j i hj
  exact coherent _ _ _ h.choose_spec.choose_spec.2

theorem PolymorphicModel.instanceValue_instantiate (p : PolymorphicModel s)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) (n : QName) (scheme : HolType)
    (hd : s.constants.lookup n = some scheme) (i j : TypeSubst) :
    HEq (p.instanceValue m hm n scheme hd (i.compose j))
      (p.instanceValue (m.instantiate j) hm n scheme hd i) := by
  apply (p.instanceValue_heq m hm n scheme hd _).trans
  apply HEq.trans _ (p.instanceValue_heq (m.instantiate j) hm n scheme hd i).symm
  apply p.constant_support
  intro k _
  change m.interp ((HolType.var k).inst (i.compose j)) =
    (m.instantiate j).interp ((HolType.var k).inst i)
  rw [m.interp_instantiate, HolType.inst_compose]

end HotaruKernel
