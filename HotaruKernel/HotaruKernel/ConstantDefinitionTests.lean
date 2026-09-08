import HotaruKernel.ConstantDefinitionModel
import HotaruKernel.ExtensionTests

namespace HotaruKernel.ConstantDefinitionTests

open Examples

def name : QName := ⟨"defined", "id"⟩
def alpha : HolType := .var "a"
def polymorphicIdentity : RawTerm := .lam alpha (.bvar 0)

def observe (r : Except KernelError (ConstantDefinition t)) : Except KernelError RawTerm :=
  r.map (fun d => d.definitionThm.conclusion.raw)

example : observe (Kernel.DEFINE_CONSTANT theory name identity) =
    .ok (.equal (.const name []) identity) := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT theory name polymorphicIdentity) =
    .ok (.equal (.const name []) polymorphicIdentity) := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT theory name x) =
    .error .freeVariablesInDefinition := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT theory name (.lam .bool x)) =
    .error .freeVariablesInDefinition := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT theory name (.bvar 0)) =
    .error .unboundVariable := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT theory name (.const name [])) =
    .error .unknownConstant := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT theory name
    (.equal polymorphicIdentity polymorphicIdentity)) =
    .error .hiddenTypeVariables := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT theory name (.equal identity identity)) =
    .ok (.equal (.const name []) (.equal identity identity)) := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT ExtensionTests.declaredTheory Tests.constName identity) =
    .error .duplicateConstant := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT ExtensionTests.malformed name identity) =
    .error .invalidSignature := by decide +kernel
example : observe (Kernel.DEFINE_CONSTANT ExtensionTests.declaredTheory name
    (.const Tests.constName [("a", .bool)])) =
    .ok (.equal (.const name []) (.const Tests.constName [("a", .bool)])) := by decide +kernel

def monomorphic : Theory := ⟨⟨[], [(Tests.constName, .bool)]⟩, []⟩
-- Unused entries in an instance witness are not dependencies of the constant.
example : observe (Kernel.DEFINE_CONSTANT monomorphic name
    (.const Tests.constName [("unused", alpha)])) =
    .ok (.equal (.const name []) (.const Tests.constName [("unused", alpha)])) := by decide +kernel

def composedDefinition : Except KernelError (List RawTerm × RawTerm) := do
  let d ← Kernel.DEFINE_CONSTANT theory name polymorphicIdentity
  let th ← Kernel.INST_TYPE d.target [("a", .bool)] d.definitionThm
  let th ← Kernel.MK_COMB d.target th (← Kernel.REFL d.target x)
  let beta ← Kernel.BETA_CONV d.target (.app identity x)
  Examples.observe (Kernel.TRANS d.target th beta)

example : composedDefinition =
    .ok ([], .equal (.app (.const name [("a", .bool)]) x) x) := by decide +kernel

theorem definition_has_model (d : ConstantDefinition theory) :
    ∃ p : PolymorphicModel d.target.signature, Models d.target p := by
  obtain ⟨p, hp, _⟩ := d.model_extension polymorphicModel models
  exact ⟨p, hp⟩

end HotaruKernel.ConstantDefinitionTests
