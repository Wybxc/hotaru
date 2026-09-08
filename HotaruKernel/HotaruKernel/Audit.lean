import HotaruKernel.PropositionalTests
import Lean.Util.CollectAxioms

/-! Fail the build if any project declaration acquires an unapproved axiom. -/
open Lean Elab Command in
elab "audit_hotaru" : command => do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  let mut count := 0
  for (name, _) in env.constants.toList do
    if (`HotaruKernel).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on forbidden axiom {axiomName}"
      count := count + 1
  logInfo m!"Axiom audit passed for {count} HotaruKernel declarations."

audit_hotaru

#print axioms HotaruKernel.check_sound
#print axioms HotaruKernel.Term.eval_substBound
#print axioms HotaruKernel.Term.eval_substFree
#print axioms HotaruKernel.Term.raw_heq
#print axioms HotaruKernel.Substitution.eval_apply
#print axioms HotaruKernel.rewrite_eval
#print axioms HotaruKernel.Derivable.sound
#print axioms HotaruKernel.Kernel.success_sound
#print axioms HotaruKernel.Examples.composed_output
#print axioms HotaruKernel.Examples.falsehood_not_derivable
