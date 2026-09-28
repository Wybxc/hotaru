import HotaruKernel.Kernel

namespace KernelNativeBench

open HotaruKernel

private def theory : Theory := ⟨{}, [], .local⟩
private def p : RawTerm := .fvar "p" .bool
private def f : RawTerm := .fvar "f" (.fn .bool .bool)
private def checkedP : CheckedTerm theory :=
  ⟨.bool, .fvar "p" .bool (by decide +kernel)⟩

private def termAt (i : Nat) : RawTerm := .fvar s!"x{i}" .bool

private def requireTheorem (result : Except KernelError (Thm theory)) : IO (Thm theory) :=
  match result with
  | .ok thm => pure thm
  | .error error => throw <| IO.userError s!"kernel rule failed: {repr error}"

@[noinline] private def reflChecked (checked : CheckedTerm theory) : Thm theory :=
  Kernel.REFL_CHECKED theory checked

@[noinline] private def eqMp (equality premise : Thm theory) :
    Except KernelError (Thm theory) :=
  Kernel.EQ_MP theory equality premise

@[noinline] private def trans (left right : Thm theory) :
    Except KernelError (Thm theory) :=
  Kernel.TRANS theory left right

@[noinline] private def trace (function argument application : RawTerm) :
    Except KernelError (Thm theory) := do
  let functionRefl ← Kernel.REFL theory function
  let argumentRefl ← Kernel.REFL theory argument
  let combined ← Kernel.MK_COMB theory functionRefl argumentRefl
  let chain ← Kernel.TRANS theory combined combined
  let premise ← Kernel.ASSUME theory application
  Kernel.EQ_MP theory chain premise

private def equalityChain (start stop : Nat) : IO (Thm theory) := do
  if start == stop then
    return ← requireTheorem (Kernel.REFL theory (termAt start))
  let mut chain ← requireTheorem <| Kernel.ASSUME theory
    (.equal (termAt start) (termAt (start + 1)))
  for i in [start + 1:stop] do
    let step ← requireTheorem <| Kernel.ASSUME theory
      (.equal (termAt i) (termAt (i + 1)))
    chain ← requireTheorem (Kernel.TRANS theory chain step)
  return chain

private structure Case where
  name : String
  iterations : Nat
  expected : RawTerm
  assumptions : Nat
  make : Unit → IO (Thm theory)

private def sample (iterations : Nat) (make : Unit → IO (Thm theory)) :
    IO (Nat × Thm theory) := do
  let mut last : Option (Thm theory) := none
  let start ← IO.monoNanosNow
  for _ in [0:iterations / 256] do
    let mut block : Array (Thm theory) := Array.emptyWithCapacity 256
    for _ in [0:256] do
      block := block.push (← make ())
    last := block.back?
  let elapsed := (← IO.monoNanosNow) - start
  match last with
  | some thm => return (elapsed, thm)
  | none => throw <| IO.userError "empty benchmark sample"

private def validate (test : Case) (thm : Thm theory) : IO Unit := do
  unless thm.conclusion.raw == test.expected do
    throw <| IO.userError s!"{test.name}: conclusion mismatch"
  unless thm.assumptions.length == test.assumptions do
    throw <| IO.userError s!"{test.name}: assumption count mismatch"

private def runCase (test : Case) (warmup trials : Nat) : IO Unit := do
  let (_, warmed) ← sample warmup test.make
  validate test warmed
  for trial in [0:trials] do
    let (elapsed, thm) ← sample test.iterations test.make
    validate test thm
    IO.println s!"HOTARU_NATIVE_BENCH\t{test.name}\t{trial}\t{test.iterations}\t{elapsed}"

private def run (profile : String) : IO Unit := do
  let smoke := profile == "smoke"
  unless smoke || profile == "standard" do
    throw <| IO.userError "usage: kernelNativeBench smoke|standard"
  let warmup := if smoke then 256 else 2048
  let trials := if smoke then 1 else 7
  let count (standard : Nat) := if smoke then 256 else standard

  let equality ← requireTheorem (Kernel.REFL theory p)
  let premise ← requireTheorem (Kernel.ASSUME theory p)
  let trans0Left ← equalityChain 0 0
  let trans0Right ← equalityChain 0 0
  let trans64Left ← equalityChain 0 64
  let trans64Right ← equalityChain 64 128
  let checked := checkedP
  let application := RawTerm.app f p
  let cases : Array Case := #[
    ⟨"refl_checked/0", count 131072, .equal p p, 0,
      fun _ => pure (reflChecked checked)⟩,
    ⟨"eq_mp/0", count 524288, p, 1,
      fun _ => requireTheorem (eqMp equality premise)⟩,
    ⟨"trans_hyps/0", count 65536, .equal (termAt 0) (termAt 0), 0,
      fun _ => requireTheorem (trans trans0Left trans0Right)⟩,
    ⟨"trans_hyps/64", count 65536, .equal (termAt 0) (termAt 128), 128,
      fun _ => requireTheorem (trans trans64Left trans64Right)⟩,
    ⟨"trace/0", count 131072, application, 1,
      fun _ => requireTheorem (trace f p application)⟩
  ]
  for test in cases do
    runCase test warmup trials

end KernelNativeBench

def main (args : List String) : IO Unit :=
  match args with
  | [profile] => KernelNativeBench.run profile
  | _ => throw <| IO.userError "usage: kernelNativeBench smoke|standard"
