import HotaruKernelTests.LogicalEquality

namespace HotaruKernel.DerivedInstantiationTests

open Examples

def openAxiom : Formula ({} : Signature) := .fvar "x" .bool (by decide +kernel)
def axiomTheory : Theory := ⟨{}, [openAxiom]⟩
def axiomTheorem : Thm axiomTheory :=
  ⟨[], openAxiom, Derivable.axiom (t := axiomTheory) openAxiom (List.mem_cons_self ..)⟩

example : observe (Kernel.INST axiomTheory [(x, y)] axiomTheorem) =
    .ok ([], y) := by decide +kernel
example : observe (Kernel.INST axiomTheory [(x, identity)] axiomTheorem) =
    .error .typeMismatch := by decide +kernel

def duplicateHypotheses : Except KernelError (Thm theory) := do
  let th ← Kernel.ASSUME theory (.equal x y)
  Kernel.TRANS theory th (← Kernel.SYM theory th)

example : observe (do
    let th ← duplicateHypotheses
    Kernel.INST theory [(x, y), (y, x)] th) =
    .ok ([.equal y x, .equal y x], .equal y y) := by decide +kernel

example : observe (do
    let th ← Kernel.ASSUME theory (.equal (.lam .bool x) (.lam .bool y))
    Kernel.INST theory [(x, y), (y, z)] th) =
    .ok ([.equal (.lam .bool y) (.lam .bool z)],
      .equal (.lam .bool y) (.lam .bool z)) := by decide +kernel

-- Discharging logically equal hypotheses must preserve their original encodings
-- when INST restores the instantiated hypothesis list.
example : observe (do
    let th ← Kernel.ASSUME LogicalEqualityTests.theory
      (.equal LogicalEqualityTests.p LogicalEqualityTests.p')
    let th ← Kernel.TRANS LogicalEqualityTests.theory th (← Kernel.SYM _ th)
    Kernel.INST LogicalEqualityTests.theory [] th) =
    .ok ([.equal LogicalEqualityTests.p LogicalEqualityTests.p',
      .equal LogicalEqualityTests.p LogicalEqualityTests.p'],
      .equal LogicalEqualityTests.p LogicalEqualityTests.p) := by decide +kernel

theorem derived_inst_sound {t : Theory} (rs : Substitution t.signature)
    {hs : List (Formula t.signature)} {p : Formula t.signature} (d : Derivable t hs p) :
    t.Entails (hs.map rs.apply) (rs.apply p) := (d.inst rs).sound

end HotaruKernel.DerivedInstantiationTests
