import HotaruKernel.Tests

namespace HotaruKernel.PropositionalTests

open Examples

def discharge (p q : RawTerm) := do
  let h ← Kernel.ASSUME theory q
  Kernel.DISCH theory p h

example : observe (discharge x x) = .ok ([], .imp x x) := by decide +kernel
example : observe (discharge y x) = .ok ([x], .imp y x) := by decide +kernel
example : observe (discharge identity x) = .error .notBoolean := by decide +kernel
example : observe (discharge (.bvar 0) x) = .error .unboundVariable := by decide +kernel
example : Tests.checked {} (.imp identity x) = .error .notBoolean := by decide +kernel
example : Tests.checked {} (.imp x identity) = .error .notBoolean := by decide +kernel

def modusPonens (p q : RawTerm) := do
  let hi ← Kernel.ASSUME theory p
  let hp ← Kernel.ASSUME theory q
  Kernel.MP theory hi hp

example : observe (modusPonens (.imp x y) x) =
    .ok ([.imp x y, x], y) := by decide +kernel
example : observe (modusPonens (.imp x y) z) = .error .termMismatch := by decide +kernel
example : observe (modusPonens x y) = .error .notImplication := by decide +kernel

def symmetry (p : RawTerm) := do
  let h ← Kernel.ASSUME theory p
  Kernel.SYM theory h

example : observe (symmetry (.equal x y)) =
    .ok ([.equal x y], .equal y x) := by decide +kernel
example : observe (symmetry x) = .error .notEquation := by decide +kernel

def transitivity (p q : RawTerm) := do
  let hl ← Kernel.ASSUME theory p
  let hr ← Kernel.ASSUME theory q
  Kernel.TRANS theory hl hr

example : observe (transitivity (.equal x y) (.equal y z)) =
    .ok ([.equal x y, .equal y z], .equal x z) := by decide +kernel
example : observe (transitivity (.equal x y) (.equal z x)) =
    .error .termMismatch := by decide +kernel
example : observe (transitivity (.equal x y) (.equal identity identity)) =
    .error .typeMismatch := by decide +kernel
example : observe (transitivity x (.equal y z)) = .error .notEquation := by decide +kernel

def equalityMP (p q : RawTerm) := do
  let he ← Kernel.ASSUME theory p
  let hp ← Kernel.ASSUME theory q
  Kernel.EQ_MP theory he hp

example : observe (equalityMP (.equal x y) x) =
    .ok ([.equal x y, x], y) := by decide +kernel
example : observe (equalityMP (.equal x y) z) = .error .termMismatch := by decide +kernel
example : observe (equalityMP (.equal identity identity) x) =
    .error .notBoolean := by decide +kernel
example : observe (equalityMP x y) = .error .notEquation := by decide +kernel

def instantiate (rs : List (RawTerm × RawTerm)) (p : RawTerm) := do
  let h ← Kernel.ASSUME theory p
  Kernel.INST theory rs h

example : observe (instantiate [(x, y), (y, z)] (.equal x y)) =
    .ok ([.equal y z], .equal y z) := by decide +kernel
example : observe (instantiate [(x, y), (x, z)] x) = .ok ([y], y) := by decide +kernel
example : observe (instantiate [] x) = .ok ([x], x) := by decide +kernel
example : observe (instantiate [(x, identity)] x) = .error .typeMismatch := by decide +kernel
example : observe (instantiate [(identity, x)] x) = .error .notVariable := by decide +kernel
example : observe (instantiate [(x, .bvar 0)] x) = .error .unboundVariable := by decide +kernel
example : observe (instantiate [(x, y)] (.equal (.lam .bool x) identity)) =
    .ok ([.equal (.lam .bool y) identity], .equal (.lam .bool y) identity) := by decide +kernel
example : observe (instantiate [(x, y)] (.imp x (.equal x z))) =
    .ok ([.imp y (.equal y z)], .imp y (.equal y z)) := by decide +kernel
example : observe (instantiate [(x, y)] (.equal Tests.mixed x)) =
    .ok ([.equal (.app (.fvar "x" (.fn .bool .bool)) y) y],
      .equal (.app (.fvar "x" (.fn .bool .bool)) y) y) := by decide +kernel

def substitute (rs : List (RawTerm × RawTerm)) (body input : RawTerm) :
    Except KernelError (Thm theory) := do
  let rules ← rs.mapM fun (pair : RawTerm × RawTerm) => do
    let h ← Kernel.ASSUME theory pair.2
    return (pair.1, h)
  let h ← Kernel.ASSUME theory input
  Kernel.SUBST theory rules body h

example : observe (substitute [(x, .equal y z)] x y) =
    .ok ([.equal y z, y], z) := by decide +kernel
example : observe (substitute [(x, .equal y z)] x x) =
    .error .termMismatch := by decide +kernel
example : observe (substitute [(identity, .equal y z)] x y) =
    .error .notVariable := by decide +kernel
example : observe (substitute [(x, y)] x y) = .error .notEquation := by decide +kernel
example : observe (substitute [(x, .equal identity identity)] x y) =
    .error .typeMismatch := by decide +kernel
example : observe (substitute [] identity x) = .error .notBoolean := by decide +kernel
example : observe (substitute [] x x) = .ok ([x], x) := by decide +kernel

-- The two rewrites act simultaneously, not by cascading into their replacements.
example : observe (substitute [(x, .equal x y), (y, .equal y z)] (.equal x y) (.equal x y)) =
    .ok ([.equal x y, .equal y z, .equal x y], .equal y z) := by decide +kernel

example : observe (substitute [(x, .equal y z)] (.equal (.lam .bool x) identity)
    (.equal (.lam .bool y) identity)) =
    .ok ([.equal y z, .equal (.lam .bool y) identity],
      .equal (.lam .bool z) identity) := by decide +kernel

def duplicateDischarge := do
  let h ← Kernel.ASSUME theory (.equal x x)
  let h' ← Kernel.TRANS theory h h
  Kernel.DISCH theory (.equal x x) h'

example : observe duplicateDischarge =
    .ok ([], .imp (.equal x x) (.equal x x)) := by decide +kernel

end HotaruKernel.PropositionalTests
