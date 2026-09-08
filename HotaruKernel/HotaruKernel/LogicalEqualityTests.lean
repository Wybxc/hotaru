import HotaruKernel.PolymorphicTests

namespace HotaruKernel.LogicalEqualityTests

open Examples

def otherName : QName := ⟨"test", "otherId"⟩
def theory : Theory := ⟨⟨[],
  [(Tests.constName, .fn (.var "a") (.var "a")),
   (otherName, .fn (.var "a") (.var "a"))]⟩, []⟩

def c : RawTerm := .const Tests.constName [("a", .bool)]
def c' : RawTerm := .const Tests.constName [("unused", .var "b"), ("a", .bool)]
def p : RawTerm := .equal c c
def p' : RawTerm := .equal c' c'
def other : RawTerm := .const otherName [("a", .bool)]
def generic : RawTerm := .const Tests.constName []

def mp (p q : RawTerm) := do
  let ti ← Kernel.ASSUME theory (.imp p x)
  let tp ← Kernel.ASSUME theory q
  Kernel.MP theory ti tp

example : observe (mp p p') = .ok ([.imp p x, p'], x) := by decide +kernel
example : observe (mp p (.equal other other)) = .error .termMismatch := by decide +kernel
example : observe (mp p (.equal generic generic)) = .error .termMismatch := by decide +kernel

example : observe (do
    let th ← Kernel.ASSUME theory p'
    Kernel.DISCH theory p th) = .ok ([], .imp p p') := by decide +kernel

example : observe (do
    let th ← Kernel.ASSUME theory (.equal other other)
    Kernel.DISCH theory p th) =
    .ok ([.equal other other], .imp p (.equal other other)) := by decide +kernel

def trans (c d : RawTerm) := do
  let tl ← Kernel.REFL theory c
  let tr ← Kernel.REFL theory d
  Kernel.TRANS theory tl tr

example : observe (trans c c') = .ok ([], .equal c c') := by decide +kernel
example : observe (trans c other) = .error .termMismatch := by decide +kernel
example : observe (trans c generic) = .error .typeMismatch := by decide +kernel

example : observe (do
    let te ← Kernel.ASSUME theory (.equal p x)
    let tp ← Kernel.ASSUME theory p'
    Kernel.EQ_MP theory te tp) = .ok ([.equal p x, p'], x) := by decide +kernel

example : observe (do
    let th ← Kernel.ASSUME theory p'
    Kernel.SUBST theory [] p th) = .ok ([p'], p) := by decide +kernel

-- Logical comparison descends beneath applications and binders.
def applied : RawTerm := .equal (.app c x) x
def applied' : RawTerm := .equal (.app c' x) x
example : observe (mp applied applied') =
    .ok ([.imp applied x, applied'], x) := by decide +kernel

def abstracted : RawTerm := .equal (.lam .bool (.app c (.bvar 0))) identity
def abstracted' : RawTerm := .equal (.lam .bool (.app c' (.bvar 0))) identity
example : observe (mp abstracted abstracted') =
    .ok ([.imp abstracted x, abstracted'], x) := by decide +kernel

theorem matched_constant_sound (th : Thm theory) (h : trans c c' = .ok th) :
    theory.Entails th.assumptions th.conclusion := Kernel.success_sound _ th h

end HotaruKernel.LogicalEqualityTests
