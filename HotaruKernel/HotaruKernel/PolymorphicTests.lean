import HotaruKernel.TypeInstantiationTests

namespace HotaruKernel.PolymorphicTests

open Examples TypeInstantiationTests

def signature : Signature := ⟨[], [(Tests.constName, .fn alpha alpha)]⟩

theorem declared_scheme (n : QName) (a : HolType)
    (h : signature.constants.lookup n = some a) : a = .fn alpha alpha := by
  simp only [signature, List.lookup_cons, List.lookup_nil] at h
  split at h
  · exact (Option.some.inj h).symm
  · contradiction

noncomputable def identityFamily (n : QName) (a : HolType)
    (h : signature.constants.lookup n = some a) (m : TypeModel) : m.interp a :=
  cast (congrArg m.interp (declared_scheme n a h).symm)
    (fun x : m.interp alpha => x)

theorem identityFamily_support (n : QName) (a : HolType)
    (h : signature.constants.lookup n = some a) (m₁ m₂ : TypeModel)
    (hv : ∀ k ∈ a.vars, m₁.typeVar k = m₂.typeVar k) :
    HEq (identityFamily n a h m₁) (identityFamily n a h m₂) := by
  have hs := declared_scheme n a h
  subst a
  have ha := hv "a" (by simp [HolType.vars, alpha])
  simp only [identityFamily, cast_eq]
  change HEq (fun x : m₁.typeVar "a" => x) (fun x : m₂.typeVar "a" => x)
  generalize m₁.typeVar "a" = A at ha ⊢
  generalize m₂.typeVar "a" = B at ha ⊢
  cases ha
  rfl

noncomputable def poly : PolymorphicModel signature where
  typeOp := types.typeOp
  op_nonempty := types.op_nonempty
  constant n a h m _ := identityFamily n a h m
  constant_support n a h m₁ m₂ _ _ hv := identityFamily_support n a h m₁ m₂ hv

def axiomTerm : Formula signature :=
  .equal (.const Tests.constName (.fn alpha alpha) [] (by decide +kernel) (by decide +kernel))
    (.lam (by decide +kernel) (.bvar .zero))

def theory : Theory := ⟨signature, [axiomTerm]⟩

theorem models : Models theory poly := by
  intro m hm f q hq
  have hq' : q = axiomTerm := List.mem_singleton.mp hq
  subst q
  apply (eval_equal_true _ _ _ _ _).mpr
  change (poly.atTypes m hm).constant Tests.constName _ _ = _
  rw [poly.atTypes_constant m hm Tests.constName (.fn alpha alpha) (by decide +kernel) []]
  apply eq_of_heq
  apply (poly.instanceValue_heq m hm Tests.constName (.fn alpha alpha)
    (by decide +kernel) []).trans
  rfl

def instantiatedAxiom : Except KernelError (Thm theory) :=
  Kernel.INST_TYPE theory [("a", .bool)]
    ⟨[], axiomTerm, Derivable.axiom (t := theory) axiomTerm (List.mem_cons_self ..)⟩

example : observe instantiatedAxiom = .ok ([], .equal
    (.const Tests.constName [("a", .bool)]) identity) := by decide +kernel

theorem instantiatedAxiom_sound (th : Thm theory) (h : instantiatedAxiom = .ok th) :
    theory.Entails th.assumptions th.conclusion := Kernel.success_sound _ th h

end HotaruKernel.PolymorphicTests
