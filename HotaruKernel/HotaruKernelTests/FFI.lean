import HotaruKernelFFI

namespace HotaruKernel.FFITests
open Lean (toJson fromJson?)
open Execution
set_option linter.hashCommand false

def p : RawTerm := .fvar "p" .bool
def commands : List Command := [.infer (.refl p), .infer (.symm 4)]

def allCommands : List Command := [
  .infer (.assume p), .infer (.refl p), .infer (.beta p), .infer (.abs "p" .bool 0),
  .infer (.mkComb 0 1), .infer (.disch p 0), .infer (.mp 0 1), .infer (.symm 0),
  .infer (.trans 0 1), .infer (.eqMp 0 1), .infer (.inst [(p, p)] 0),
  .infer (.instType [("a", .bool)] 0), .infer (.subst [(p, 0)] p 0),
  .declareType ⟨"test", "t"⟩ 1, .declareConstant ⟨"test", "c"⟩ (.var "a"),
  .defineConstant ⟨"test", "id"⟩ (.lam .bool (.bvar 0)),
  .defineType ⟨"test", "t"⟩ ["a"] p (some 0),
  .defineType ⟨"test", "u"⟩ [] p none, .addAxiom p]

def terms : List RawTerm := [
  .fvar "x" (.op ⟨"test", "t"⟩ [.fn (.var "a") .bool]), .bvar 2,
  .const ⟨"test", "c"⟩ [("a", .bool)], .app p p, .lam .bool p, .equal p p, .imp p p]

-- JSON parsing uses partial runtime code: these are behavior checks, not proofs.
def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

#eval do
  check "commands roundtrip"
    (decide ((fromJson? (toJson allCommands) : Except String (List Command)) =
      Except.ok allCommands))
  check "terms roundtrip"
    (decide ((fromJson? (toJson terms) : Except String (List RawTerm)) = Except.ok terms))
  check "composition" (FFI.apply initial (toJson commands).compress).success
  check "invalid JSON" (!(FFI.apply initial "[").success)
  check "invalid command" (!(FFI.apply initial "[{}]").success)
  check "invalid reference" (!(FFI.apply initial
    (toJson ([.infer (.symm 999)] : List Command)).compress).success)


end HotaruKernel.FFITests
