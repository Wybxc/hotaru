import HotaruKernel.FoundationModel
import HotaruKernel.TypeDefinitionTests

namespace HotaruKernel.FoundationTests

open Foundation

def identity : RawTerm := .lam .bool (.bvar 0)
def trueRaw : RawTerm := .equal identity identity

def specialize (th : Thm theory) (x : RawTerm) : Except KernelError (Thm theory) := do
  let v ← equationView th.conclusion
  let app ← Kernel.MK_COMB theory th (← Kernel.REFL theory x)
  let right ← Kernel.BETA_CONV theory (.app v.right.raw x)
  let eq ← Kernel.TRANS theory app right
  let value ← Kernel.EQ_MP theory (← Kernel.SYM theory eq) (← Kernel.REFL theory identity)
  Kernel.EQ_MP theory (← Kernel.BETA_CONV theory (.app v.left.raw x)) value

def booleanSelection : Except KernelError (Thm theory) := do
  let th ← Kernel.INST_TYPE theory [("a", .bool)] selection
  let th ← specialize th identity
  let th ← specialize th trueRaw
  let beta ← Kernel.BETA_CONV theory (.app identity trueRaw)
  let antecedent ← Kernel.EQ_MP theory (← Kernel.SYM theory beta) (← Kernel.REFL theory identity)
  let result ← Kernel.MP theory th antecedent
  let selected := RawTerm.app (.const selectName [("a", .bool)]) identity
  Kernel.EQ_MP theory (← Kernel.BETA_CONV theory (.app identity selected)) result

example : Examples.observe booleanSelection =
    .ok ([], .app (.const selectName [("a", .bool)]) identity) := by decide +kernel

theorem booleanSelection_sound (th : Thm theory) (h : booleanSelection = .ok th) :
    theory.Entails th.assumptions th.conclusion := Kernel.success_sound booleanSelection th h

example : Examples.observe (Kernel.REFL theory (.const selectName [("a", ind)])) =
    .ok ([], .equal (.const selectName [("a", ind)])
      (.const selectName [("a", ind)])) := by decide +kernel
example : Examples.observe (Kernel.REFL theory
    (.const selectName [("a", .op indName [.bool])])) = .error .invalidType := by decide +kernel
example : Examples.observe (Kernel.REFL theory
    (.const selectName [("a", .op ⟨"missing", "type"⟩ [])])) =
    .error .invalidType := by decide +kernel
example : (Kernel.DECLARE_TYPE theory indName 0).map (fun _ => ()) =
    .error .duplicateType := by decide +kernel
example : (Kernel.DECLARE_CONSTANT theory selectName .bool).map (fun _ => ()) =
    .error .duplicateConstant := by decide +kernel
example : (Kernel.INST_TYPE theory [("a", .bool), ("b", ind)] eta).map
    (fun th => th.assumptions) = .ok [] := by decide +kernel

theorem base_has_model : ∃ p : PolymorphicModel theory.signature, Models theory p :=
  ⟨model, models⟩

end HotaruKernel.FoundationTests
