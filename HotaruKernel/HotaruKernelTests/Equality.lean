import HotaruKernel.Equality

namespace HotaruKernel.EqualityTests

def constantName : QName := ⟨"test", "id"⟩
def signature : Signature :=
  ⟨[], [(constantName, .fn (.var "a") (.var "a"))]⟩

def p : Closed signature .bool := .fvar "p" .bool (by decide +kernel)
def q : Closed signature .bool := .fvar "q" .bool (by decide +kernel)
def bound0 : Term signature [.bool, .bool] .bool := .bvar .zero
def bound1 : Term signature [.bool, .bool] .bool := .bvar (.succ .zero)
def identity : Closed signature (.fn .bool .bool) :=
  .lam (by decide +kernel) (.bvar .zero)
def polymorphicIdentity : Closed signature (.fn (.var "a") (.var "a")) :=
  .lam (by decide +kernel) (.bvar .zero)
def constA : Closed signature (.fn .bool .bool) :=
  .const constantName (.fn (.var "a") (.var "a")) [("a", .bool)]
    (by decide +kernel) (by decide +kernel)
def constB : Closed signature (.fn .bool .bool) :=
  .const constantName (.fn (.var "a") (.var "a"))
    [("unused", .var "b"), ("a", .bool)]
    (by decide +kernel) (by decide +kernel)

example : p.rawEq p = true := by decide +kernel
example : p.rawEq q = false := by decide +kernel
example : decide (p = q) = false := by decide +kernel
example : bound0.rawEq bound1 = false := by decide +kernel
example : constA.rawEq constA = true := by decide +kernel
example : constA.rawEq constB = false := by decide +kernel
example : decide (constA = constB) = false := by decide +kernel
example : identity.rawEq polymorphicIdentity = false := by decide +kernel
example : (Term.app identity p).rawEq (.app identity q) = false := by decide +kernel
example : (Term.equal p q).rawEq (.equal p p) = false := by decide +kernel
example : (Term.imp p q).rawEq (.imp p p) = false := by decide +kernel
example : p.rawEq (.equal p p) = false := by decide +kernel

end HotaruKernel.EqualityTests
