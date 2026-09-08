import HotaruKernel.DeclarationModels
import HotaruKernelTests.DerivedInstantiation
import HotaruKernel.TheoryMigration

namespace HotaruKernel.ExtensionTests

open Examples

def observe (r : Except KernelError (TheoryExtension t)) :
    Except KernelError (Signature × List RawTerm) :=
  r.map (fun e => (e.target.signature, e.target.axioms.map Term.raw))

example : observe (Kernel.DECLARE_TYPE theory Tests.boxName 1) =
    .ok (⟨[(Tests.boxName, 1)], []⟩, []) := by decide +kernel
example : observe (Kernel.DECLARE_TYPE theory Tests.boxName 0) =
    .ok (⟨[(Tests.boxName, 0)], []⟩, []) := by decide +kernel
example : observe (Kernel.DECLARE_CONSTANT theory Tests.constName (.var "a")) =
    .ok (⟨[], [(Tests.constName, .var "a")]⟩, []) := by decide +kernel
example : observe (Kernel.DECLARE_CONSTANT theory Tests.constName (.op Tests.boxName [])) =
    .error .invalidType := by decide +kernel

def boxTheory : Theory := ⟨⟨[(Tests.boxName, 1)], []⟩, []⟩
example : observe (Kernel.DECLARE_TYPE boxTheory Tests.boxName 1) =
    .error .duplicateType := by decide +kernel
example : observe (Kernel.DECLARE_TYPE boxTheory Tests.boxName 2) =
    .error .duplicateType := by decide +kernel
example : observe (Kernel.DECLARE_CONSTANT boxTheory Tests.constName (.op Tests.boxName [.bool])) =
    .ok (⟨[(Tests.boxName, 1)], [(Tests.constName, .op Tests.boxName [.bool])]⟩, []) :=
  by decide +kernel
example : observe (Kernel.DECLARE_CONSTANT boxTheory Tests.constName (.op Tests.boxName [])) =
    .error .invalidType := by decide +kernel

def declaredTheory : Theory := ⟨Tests.signature, []⟩
example : observe (Kernel.DECLARE_CONSTANT declaredTheory Tests.constName .bool) =
    .error .duplicateConstant := by decide +kernel

def malformed : Theory := ⟨⟨[(Tests.boxName, 1), (Tests.boxName, 2)], []⟩, []⟩
example : observe (Kernel.DECLARE_CONSTANT malformed Tests.constName .bool) =
    .error .invalidSignature := by decide +kernel
example : observe (Kernel.DECLARE_TYPE malformed ⟨"other", "box"⟩ 0) =
    .error .invalidSignature := by decide +kernel

def malformedConstant : Theory :=
  ⟨⟨[], [(Tests.constName, .op Tests.boxName [])]⟩, []⟩
example : observe (Kernel.DECLARE_TYPE malformedConstant Tests.boxName 0) =
    .error .invalidSignature := by decide +kernel

example : observe (Kernel.DECLARE_TYPE DerivedInstantiationTests.axiomTheory Tests.boxName 1) =
    .ok (⟨[(Tests.boxName, 1)], []⟩, [x]) := by decide +kernel

theorem declaration_extends_model (e : TheoryExtension theory)
    (h : Kernel.DECLARE_CONSTANT theory Tests.constName (.var "a") = .ok e) :
    ∃ p : PolymorphicModel e.target.signature, Models e.target p := by
  obtain ⟨p, hp, _⟩ := Kernel.declareConstant_model _ _ e h polymorphicModel models
  exact ⟨p, hp⟩

def migratedExample : Except KernelError (List RawTerm × RawTerm) := do
  let th ← composed
  let e ← Kernel.DECLARE_TYPE theory Tests.boxName 1
  let th ← Kernel.MIGRATE e th
  let e' ← Kernel.DECLARE_CONSTANT e.target Tests.constName .bool
  let th ← Kernel.MIGRATE e' th
  Examples.observe (.ok th)

example : migratedExample = .ok ([.equal y z], expected) := by decide +kernel

example : (do
    let th ← Kernel.REFL theory (.fvar "x" (.var "a"))
    let th ← Kernel.INST_TYPE theory [("a", .bool)] th
    let th ← Kernel.INST theory [(x, y)] th
    let e ← Kernel.DECLARE_TYPE theory Tests.boxName 1
    let th ← Kernel.MIGRATE e th
    Examples.observe (.ok th)) = .ok ([], .equal y y) := by decide +kernel

example : (do
    let e ← Kernel.DECLARE_TYPE DerivedInstantiationTests.axiomTheory Tests.boxName 1
    let th ← Kernel.MIGRATE e DerivedInstantiationTests.axiomTheorem
    Examples.observe (.ok th)) = .ok ([], x) := by decide +kernel

example (_old : Thm theory) (_new : Thm boxTheory) : True := by
  fail_if_success have bad := Kernel.TRANS theory _old _new
  trivial

example (_e : TheoryExtension theory) (_alien : Thm boxTheory) : True := by
  fail_if_success have bad := Kernel.MIGRATE _e _alien
  trivial

end HotaruKernel.ExtensionTests
