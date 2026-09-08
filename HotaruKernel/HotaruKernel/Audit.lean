import HotaruKernel.ExecutionTests
import HotaruKernel.OperatorTransport
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
#print axioms HotaruKernel.Term.eval_logical
#print axioms HotaruKernel.Derivable.eqMp
#print axioms HotaruKernel.Derivable.symm
#print axioms HotaruKernel.Derivable.trans
#print axioms HotaruKernel.Derivable.mkComb
#print axioms HotaruKernel.BooleanAxiom.sound
#print axioms HotaruKernel.Term.bind_comp
#print axioms HotaruKernel.Substitution.apply_cons_close
#print axioms HotaruKernel.Derivable.inst
#print axioms HotaruKernel.DerivedInstantiationTests.derived_inst_sound
#print axioms HotaruKernel.Term.eval_rebase
#print axioms HotaruKernel.Theory.Extends.entails
#print axioms HotaruKernel.Kernel.declareType_model
#print axioms HotaruKernel.Kernel.declareConstant_model
#print axioms HotaruKernel.Derivable.rebase
#print axioms HotaruKernel.Thm.rebase_sound
#print axioms HotaruKernel.Term.eval_typeVars
#print axioms HotaruKernel.Kernel.defineConstant_spec
#print axioms HotaruKernel.ConstantDefinition.model_extension
#print axioms HotaruKernel.Term.eval_existsT
#print axioms HotaruKernel.Term.eval_typeDefinitionT
#print axioms HotaruKernel.TypeDefinition.predicate_nonempty
#print axioms HotaruKernel.TypeDefinition.definition_sound
#print axioms HotaruKernel.Kernel.defineType_spec
#print axioms HotaruKernel.TypeModel.Agrees.interp
#print axioms HotaruKernel.Term.eval_agrees
#print axioms HotaruKernel.PolymorphicModel.OperatorExtension.models_agree
#print axioms HotaruKernel.Theory.models_changeOperators
#print axioms HotaruKernel.TypeDefinition.interpreted_subtype
#print axioms HotaruKernel.TypeDefinition.model_extension
#print axioms HotaruKernel.TypeDefinitionTests.definition_has_model
#print axioms HotaruKernel.Foundation.choiceFamily_support
#print axioms HotaruKernel.Foundation.models
#print axioms HotaruKernel.Foundation.falsehood_not_derivable
#print axioms HotaruKernel.FoundationTests.booleanSelection_sound
#print axioms HotaruKernel.Execution.execution_sound
#print axioms HotaruKernel.Execution.execution_consistent
#print axioms HotaruKernel.Execution.execution_sequents_wellFormed
#print axioms HotaruKernel.Execution.successful_run_wellFormed
#print axioms HotaruKernel.Execution.successful_run_extends
#print axioms HotaruKernel.ExecutionTests.completeTrace_output
#print axioms HotaruKernel.ExecutionTests.completeTrace_consistent
#print axioms HotaruKernel.Substitution.eval_apply
#print axioms HotaruKernel.rewrite_eval
#print axioms HotaruKernel.HolType.inst_compose
#print axioms HotaruKernel.TypeModel.interp_instantiate
#print axioms HotaruKernel.instType_preserves_type
#print axioms HotaruKernel.PolymorphicModel.atTypes_constant
#print axioms HotaruKernel.Term.eval_instType
#print axioms HotaruKernel.TypeInstantiationTests.abstractBeforeMerge_sound
#print axioms HotaruKernel.PolymorphicTests.models
#print axioms HotaruKernel.Derivable.sound
#print axioms HotaruKernel.Kernel.success_sound
#print axioms HotaruKernel.Examples.composed_output
#print axioms HotaruKernel.Examples.falsehood_not_derivable
