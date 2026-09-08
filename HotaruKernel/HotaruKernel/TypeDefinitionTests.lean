import HotaruKernel.TypeDefinition
import HotaruKernel.ConstantDefinitionTests

namespace HotaruKernel.TypeDefinitionTests

open Examples

def name : QName := ⟨"defined", "inhabited"⟩
def trueRaw : RawTerm := (Term.trueT (s := theory.signature) (ctx := [])).raw
def falseRaw : RawTerm := (Term.falseT (s := theory.signature) (ctx := [])).raw
def predicate : RawTerm := .lam .bool trueRaw
def emptyPredicate : RawTerm := .lam .bool falseRaw
def existsRaw : RawTerm := .imp (.equal predicate emptyPredicate) falseRaw

def nonemptyProof : Except KernelError (Thm theory) := do
  let eq ← Kernel.ASSUME theory (.equal predicate emptyPredicate)
  let arg ← Kernel.REFL theory trueRaw
  let app ← Kernel.MK_COMB theory eq arg
  let left ← Kernel.BETA_CONV theory (.app predicate trueRaw)
  let right ← Kernel.BETA_CONV theory (.app emptyPredicate trueRaw)
  let eq ← Kernel.TRANS theory (← Kernel.SYM theory left) app
  let eq ← Kernel.TRANS theory eq right
  let truth ← Kernel.REFL theory identity
  let contradiction ← Kernel.EQ_MP theory eq truth
  Kernel.DISCH theory (.equal predicate emptyPredicate) contradiction

example : observe nonemptyProof = .ok ([], existsRaw) := by decide +kernel

def define : Except KernelError (TypeDefinition theory) := do
  let th ← nonemptyProof
  Kernel.DEFINE_TYPE theory name [] predicate (some th)

def observeDefinition (r : Except KernelError (TypeDefinition t)) : Except KernelError HolType :=
  r.map TypeDefinition.type

example : observeDefinition define = .ok (.op name []) := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE theory name [] predicate none) =
    .error .missingNonemptyProof := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE theory name ["a", "a"] predicate none) =
    .error .duplicateTypeParameter := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE theory name [] trueRaw none) =
    .error .notPredicate := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE theory name [] (.lam .bool x) none) =
    .error .freeVariablesInDefinition := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE theory name []
    (.lam (.var "a") trueRaw) none) = .error .hiddenTypeVariables := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE theory name [] (.bvar 0) none) =
    .error .unboundVariable := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE theory name [] (.const name []) none) =
    .error .unknownConstant := by decide +kernel
example : observeDefinition (Kernel.DEFINE_TYPE ExtensionTests.malformed name [] predicate none) =
    .error .invalidSignature := by decide +kernel

def assumedProof : Except KernelError (TypeDefinition theory) := do
  let th ← Kernel.ASSUME theory existsRaw
  Kernel.DEFINE_TYPE theory name [] predicate (some th)
example : observeDefinition assumedProof = .error .nonemptyProofHasAssumptions := by decide +kernel

def mismatchedProof : Except KernelError (TypeDefinition theory) := do
  let th ← Kernel.REFL theory identity
  Kernel.DEFINE_TYPE theory name [] predicate (some th)
example : observeDefinition mismatchedProof = .error .termMismatch := by decide +kernel

def repeatedDefinition : Except KernelError Unit := do
  let d ← define
  let _ ← Kernel.DEFINE_TYPE d.target name [] predicate none
  pure ()
example : repeatedDefinition = .error .duplicateType := by decide +kernel

example (d : TypeDefinition theory) (_foreignProof : Thm d.target) : True := by
  fail_if_success have _bad := Kernel.DEFINE_TYPE theory name [] predicate (some _foreignProof)
  trivial

theorem definition_valid (d : TypeDefinition theory) : d.target.Entails [] d.formula :=
  d.definition_sound

end HotaruKernel.TypeDefinitionTests
