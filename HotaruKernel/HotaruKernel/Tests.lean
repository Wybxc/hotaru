import HotaruKernel.Examples

namespace HotaruKernel.Tests

open Examples

def checked (s : Signature) (r : RawTerm) : Except KernelError (HolType × RawTerm) :=
  (check s [] r).map (fun c => (c.type, c.term.raw))

example : checked {} identity = .ok (.fn .bool .bool, identity) := by decide +kernel
example : checked {} (.bvar 0) = .error .unboundVariable := by decide +kernel
example : checked {} (.lam .bool (.bvar 1)) = .error .unboundVariable := by decide +kernel
example : checked {} (.app x y) = .error .notFunction := by decide +kernel
example : checked {} (.app identity identity) = .error .typeMismatch := by decide +kernel
example : checked {} (.equal x identity) = .error .typeMismatch := by decide +kernel
example : checked {} (.const ⟨"missing", "c"⟩ []) = .error .unknownConstant := by decide +kernel
example : checked {} (.fvar "x" (.op ⟨"missing", "ty"⟩ [])) =
    .error .invalidType := by decide +kernel

def boxName : QName := ⟨"test", "box"⟩
def constName : QName := ⟨"test", "id"⟩
def signature : Signature :=
  ⟨[(boxName, 1)], [(constName, .fn (.var "a") (.var "a"))]⟩

example : signature.validType (.op boxName [.bool]) = true := by decide +kernel
example : signature.validType (.op boxName []) = false := by decide +kernel
example : signature.validType (.op boxName [.op boxName []]) = false := by decide +kernel
example : checked signature (.const constName [("a", .bool)]) =
    .ok (.fn .bool .bool, .const constName [("a", .bool)]) := by decide +kernel
example : checked signature (.const constName [("a", .op boxName [])]) =
    .error .invalidType := by decide +kernel
example : checked signature (.const constName [("a", .op boxName [.bool])]) =
    .ok (.fn (.op boxName [.bool]) (.op boxName [.bool]),
      .const constName [("a", .op boxName [.bool])]) := by decide +kernel

example : observe (Kernel.ASSUME theory x) = .ok ([x], x) := by decide +kernel
example : observe (Kernel.ASSUME theory identity) = .error .notBoolean := by decide +kernel
example : observe (Kernel.REFL theory (.bvar 0)) = .error .unboundVariable := by decide +kernel
example : observe (Kernel.REFL theory identity) =
    .ok ([], .equal identity identity) := by decide +kernel
example : observe (Kernel.BETA_CONV theory x) = .error .notBetaRedex := by decide +kernel
example : observe (Kernel.BETA_CONV theory (.app identity identity)) =
    .error .typeMismatch := by decide +kernel
example : observe (Kernel.BETA_CONV theory (.app identity x)) =
    .ok ([], .equal (.app identity x) x) := by decide +kernel

-- Free x remains free beneath the inner lambda; bound index 1 opens to the argument.
def nested : RawTerm := .lam .bool (.lam .bool (.bvar 1))
example : observe (Kernel.BETA_CONV theory (.app nested x)) =
    .ok ([], .equal (.app nested x) (.lam .bool x)) := by decide +kernel

-- Opening beneath two binders also preserves the inner bound variable.
def nestedApplication : RawTerm :=
  .lam (.fn .bool .bool) (.lam .bool (.app (.bvar 1) (.bvar 0)))
example : observe (Kernel.BETA_CONV theory (.app nestedApplication identity)) =
    .ok ([], .equal (.app nestedApplication identity)
      (.lam .bool (.app identity (.bvar 0)))) := by decide +kernel

def abstractAssumption (n : String) (a : HolType) (p : RawTerm) := do
  let th ← Kernel.ASSUME theory p
  Kernel.ABS theory n a th

example : observe (abstractAssumption "x" .bool (.equal x y)) =
    .error .freeInAssumptions := by decide +kernel
example : observe (abstractAssumption "unused" .bool x) = .error .notEquation := by decide +kernel
example : observe (abstractAssumption "x" (.var "a") (.equal x y)) =
    .ok ([.equal x y], .equal (.lam (.var "a") x) (.lam (.var "a") y)) := by decide +kernel

def abstractReflexivity (n : String) (a : HolType) (r : RawTerm) := do
  let th ← Kernel.REFL theory r
  Kernel.ABS theory n a th

example : observe (abstractReflexivity "x" .bool x) =
    .ok ([], .equal identity identity) := by decide +kernel
example : observe (abstractReflexivity "y" .bool y) =
    .ok ([], .equal identity identity) := by decide +kernel
example : observe (abstractReflexivity "x" (.op boxName []) x) =
    .error .invalidType := by decide +kernel
example : observe (abstractReflexivity "x" .bool (.lam .bool x)) =
    .ok ([], .equal nested nested) := by decide +kernel

def combineReflexivity (f x : RawTerm) := do
  let tf ← Kernel.REFL theory f
  let tx ← Kernel.REFL theory x
  Kernel.MK_COMB theory tf tx

example : observe (combineReflexivity identity x) =
    .ok ([], .equal (.app identity x) (.app identity x)) := by decide +kernel
example : observe (combineReflexivity x y) = .error .notFunction := by decide +kernel
example : observe (combineReflexivity identity identity) = .error .typeMismatch := by decide +kernel

def combineNonEquation := do
  let tf ← Kernel.ASSUME theory x
  let tx ← Kernel.REFL theory y
  Kernel.MK_COMB theory tf tx

example : observe combineNonEquation = .error .notEquation := by decide +kernel

def combineNonEquationRight := do
  let tf ← Kernel.REFL theory identity
  let tx ← Kernel.ASSUME theory x
  Kernel.MK_COMB theory tf tx

example : observe combineNonEquationRight = .error .notEquation := by decide +kernel

-- The same spelling at distinct types denotes distinct free variables.
def mixed : RawTerm := .app (.fvar "x" (.fn .bool .bool)) x
example : observe (abstractReflexivity "x" .bool mixed) =
    .ok ([], .equal
      (.lam .bool (.app (.fvar "x" (.fn .bool .bool)) (.bvar 0)))
      (.lam .bool (.app (.fvar "x" (.fn .bool .bool)) (.bvar 0)))) := by decide +kernel

def typedX : Closed theory.signature .bool := .fvar "x" .bool (by decide +kernel)
def typedY : Closed theory.signature .bool := .fvar "y" .bool (by decide +kernel)
def typedNested : Closed theory.signature (.fn .bool .bool) :=
  .lam (by decide +kernel) (.fvar "x" .bool (by decide +kernel))

example : (typedNested.replace "x" .bool typedY).raw = .lam .bool y := by decide +kernel
example : (typedX.replace "x" .bool typedX).raw = x := by decide +kernel
example : (typedNested.replace "unused" .bool typedY).raw = typedNested.raw := by decide +kernel
example : (typedNested.replace "x" .bool typedY).freeVars = [("y", .bool)] := by decide +kernel

def typedFunction : Closed theory.signature (.fn .bool .bool) :=
  .fvar "x" (.fn .bool .bool) (by decide +kernel)
example : (typedFunction.replace "x" .bool typedY).raw = typedFunction.raw := by decide +kernel

-- A replacement referring to the outer binder must be shifted under a new lambda.
def openReplacement : Term theory.signature [.bool] .bool := .bvar .zero
def openBody : Term theory.signature [.bool] (.fn .bool .bool) :=
  .lam (by decide +kernel) (.fvar "x" .bool (by decide +kernel))
example : (openBody.replace "x" .bool openReplacement).raw =
    .lam .bool (.bvar 1) := by decide +kernel

-- Type substitutions are simultaneous, and do not recursively substitute their ranges.
example : (HolType.var "a").inst [("a", .var "b"), ("b", .bool)] =
    .var "b" := by decide +kernel

end HotaruKernel.Tests
