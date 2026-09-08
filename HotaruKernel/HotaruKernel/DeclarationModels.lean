import HotaruKernel.TheoryExtension

namespace HotaruKernel

variable {s : Signature}

def PolymorphicModel.addType (p : PolymorphicModel s) (n : QName) (arity : Nat) :
    PolymorphicModel (s.addType n arity) where
  typeOp := p.typeOp
  op_nonempty := p.op_nonempty
  constant := p.constant
  constant_support := p.constant_support

theorem PolymorphicModel.addType_restrict (p : PolymorphicModel s) (n : QName) (arity : Nat)
    (fresh : s.typeOps.lookup n = none) :
    (p.addType n arity).restrict (s.extends_addType n arity fresh) = p := rfl

private theorem choice_heq {A B : Type} (ha : Nonempty A) (hb : Nonempty B) (h : A = B) :
    HEq (Classical.choice ha) (Classical.choice hb) := by
  cases h
  rfl

noncomputable def PolymorphicModel.addConstantFamily (p : PolymorphicModel s)
    (n : QName) (scheme : HolType) (k : QName) (a : HolType)
    (hd : (s.addConstant n scheme).constants.lookup k = some a)
    (m : TypeModel) (hm : m.typeOp = p.typeOp) : m.interp a :=
  if hn : k = n then Classical.choice (m.interp_nonempty a)
  else p.constant k a (by
    simpa [Signature.addConstant, List.lookup_cons, beq_eq_false_iff_ne.mpr hn] using hd) m hm

noncomputable def PolymorphicModel.addConstant (p : PolymorphicModel s)
    (n : QName) (scheme : HolType) : PolymorphicModel (s.addConstant n scheme) where
  typeOp := p.typeOp
  op_nonempty := p.op_nonempty
  constant := p.addConstantFamily n scheme
  constant_support k a hd m₁ m₂ h₁ h₂ hv := by
    by_cases hn : k = n
    · simp only [addConstantFamily, hn, ↓reduceDIte]
      exact choice_heq _ _ (m₁.interp_congr_vars m₂ (h₁.trans h₂.symm) a hv)
    · simp only [addConstantFamily, hn, ↓reduceDIte]
      exact p.constant_support k a _ m₁ m₂ h₁ h₂ hv

theorem PolymorphicModel.addConstant_restrict (p : PolymorphicModel s)
    (n : QName) (scheme : HolType) (fresh : s.constants.lookup n = none) :
    (p.addConstant n scheme).restrict (s.extends_addConstant n scheme fresh) = p := by
  cases p with
  | mk typeOp op_nonempty constant constant_support =>
    unfold restrict addConstant
    congr 1
    funext k a hd m hm
    have hn : k ≠ n := by intro hk; subst k; rw [fresh] at hd; cases hd
    simp only [addConstantFamily, hn, ↓reduceDIte]

theorem Theory.addType_model {t : Theory} (p : PolymorphicModel t.signature)
    (hp : Models t p) (n : QName) (arity : Nat) (fresh : t.signature.typeOps.lookup n = none) :
    Models (t.withSignature _ (t.signature.extends_addType n arity fresh)) (p.addType n arity) := by
  apply (t.models_withSignature_iff _ _ _).mpr
  rw [p.addType_restrict n arity fresh]
  exact hp

theorem Theory.addConstant_model {t : Theory} (p : PolymorphicModel t.signature)
    (hp : Models t p) (n : QName) (scheme : HolType)
    (fresh : t.signature.constants.lookup n = none) :
    Models (t.withSignature _ (t.signature.extends_addConstant n scheme fresh))
      (p.addConstant n scheme) := by
  apply (t.models_withSignature_iff _ _ _).mpr
  rw [p.addConstant_restrict n scheme fresh]
  exact hp

theorem Kernel.declareType_model {t : Theory} (n : QName) (arity : Nat)
    (e : TheoryExtension t) (he : Kernel.DECLARE_TYPE t n arity = .ok e)
    (p : PolymorphicModel t.signature) (hp : Models t p) :
    ∃ q : PolymorphicModel e.target.signature,
      Models e.target q ∧ q.restrict e.extension.signature = p := by
  unfold DECLARE_TYPE at he
  split at he
  · split at he
    · rename_i fresh
      cases he
      exact ⟨p.addType n arity, t.addType_model p hp n arity fresh,
        p.addType_restrict n arity fresh⟩
    · cases he
  · cases he

theorem Kernel.declareConstant_model {t : Theory} (n : QName) (scheme : HolType)
    (e : TheoryExtension t) (he : Kernel.DECLARE_CONSTANT t n scheme = .ok e)
    (p : PolymorphicModel t.signature) (hp : Models t p) :
    ∃ q : PolymorphicModel e.target.signature,
      Models e.target q ∧ q.restrict e.extension.signature = p := by
  unfold DECLARE_CONSTANT at he
  split at he
  · split at he
    · rename_i fresh
      split at he
      · cases he
        exact ⟨p.addConstant n scheme, t.addConstant_model p hp n scheme fresh,
          p.addConstant_restrict n scheme fresh⟩
      · cases he
    · cases he
  · cases he

end HotaruKernel
