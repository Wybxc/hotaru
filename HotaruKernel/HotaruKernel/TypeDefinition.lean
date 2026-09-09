import HotaruKernel.ConstantDefinition
import HotaruKernel.TypeDefinitionFormula

namespace HotaruKernel

structure TypeDefinition (t : Theory) where
  name : QName
  parameters : List String
  representation : HolType
  predicate : Closed t.signature (.fn representation .bool)
  representationValid : t.signature.validType representation = true
  wellFormed : t.signature.WellFormed
  fresh : t.signature.typeOps.lookup name = none
  distinct : parameters.Nodup
  closed : predicate.freeVars = []
  supported : ∀ n ∈ predicate.typeVars, n ∈ parameters
  nonemptyProof : Derivable t [] (predicate.existsT representationValid)
  proofOrigin : Provenance.Origin

namespace TypeDefinition

variable {t : Theory}

def signature (d : TypeDefinition t) : Signature :=
  t.signature.addType d.name d.parameters.length

def type (d : TypeDefinition t) : HolType := .op d.name (d.parameters.map HolType.var)

theorem extendsSignature (d : TypeDefinition t) : t.signature.Extends d.signature :=
  t.signature.extends_addType d.name d.parameters.length d.fresh

theorem typeValid (d : TypeDefinition t) : d.signature.validType d.type = true := by
  rw [type, Signature.validType_op_iff]
  constructor
  · simp [signature, Signature.addType]
  · intro a ha
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp ha
    simp [Signature.validType]

def formula (d : TypeDefinition t) : Formula d.signature :=
  (d.predicate.rebase d.extendsSignature).typeDefinitionT d.type d.typeValid
    (d.extendsSignature.validType _ d.representationValid)

def target (d : TypeDefinition t) : Theory :=
  ⟨d.signature, d.formula :: t.axioms.map (Term.rebase d.extendsSignature),
    t.origin.join d.proofOrigin⟩

def extension (d : TypeDefinition t) : TheoryExtension t where
  target := d.target
  extension := ⟨d.extendsSignature,
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩
  wellFormed := d.wellFormed.addType d.name d.parameters.length d.fresh

def definitionThm (d : TypeDefinition t) : Thm d.target :=
  ⟨[], d.formula, Derivable.axiom (t := d.target) d.formula (List.mem_cons_self ..),
    d.target.origin⟩

theorem definition_sound (d : TypeDefinition t) : d.target.Entails [] d.formula :=
  d.definitionThm.sound

theorem predicate_nonempty (d : TypeDefinition t) (p : PolymorphicModel t.signature)
    (hp : Models t p) (m : TypeModel) (hm : m.typeOp = p.typeOp)
    (f : FreeEnv (p.atTypes m hm)) :
    ∃ x, d.predicate.eval (p.atTypes m hm) f BoundEnv.nil x = true :=
  (Term.eval_existsT _ _ _ _ _).mp
    (d.nonemptyProof.sound p hp m hm f (fun _ h => by cases h))

end TypeDefinition

def Kernel.DEFINE_TYPE (t : Theory) (n : QName) (parameters : List String)
    (predicate : RawTerm) (proof : Option (Thm t)) : Except KernelError (TypeDefinition t) := do
  if hw : t.signature.WellFormed then
    if hn : t.signature.typeOps.lookup n = none then
      if hd : parameters.Nodup then
        let ⟨ty, p, _⟩ ← check t.signature [] predicate
        match ty with
        | .fn a .bool =>
          have hv : t.signature.validType a = true := by
            have h := p.validType (fun _ h => by cases h)
            simpa only [Signature.validType, Bool.and_eq_true, and_true] using h
          if hc : p.freeVars = [] then
            if ht : ∀ k ∈ p.typeVars, k ∈ parameters then
              match proof with
              | none => .error .missingNonemptyProof
              | some th =>
                if hh : th.assumptions = [] then
                  if he : th.conclusion.Equivalent (p.existsT hv) then
                    return ⟨n, parameters, a, p, hv, hw, hn, hd, hc, ht,
                      Derivable.conversion he (hh ▸ th.derivation), th.origin⟩
                  else .error .termMismatch
                else .error .nonemptyProofHasAssumptions
            else .error .hiddenTypeVariables
          else .error .freeVariablesInDefinition
        | _ => .error .notPredicate
      else .error .duplicateTypeParameter
    else .error .duplicateType
  else .error .invalidSignature

theorem Kernel.defineType_spec (t : Theory) (n : QName) (parameters : List String)
    (predicate : RawTerm) (proof : Option (Thm t)) (d : TypeDefinition t)
    (hd : Kernel.DEFINE_TYPE t n parameters predicate proof = .ok d) :
    d.name = n ∧ d.parameters = parameters ∧ d.predicate.raw = predicate := by
  unfold DEFINE_TYPE at hd
  split at hd
  · split at hd
    · split at hd
      · cases hc : check t.signature [] predicate with
        | error e => simp [hc, bind, Except.bind] at hd
        | ok r =>
          rcases r with ⟨ty, p, erases⟩
          simp only [hc, bind, Except.bind] at hd
          split at hd
          · split at hd
            · split at hd
              · split at hd
                · cases hd
                · split at hd
                  · split at hd
                    · cases hd
                      exact ⟨rfl, rfl, by assumption⟩
                    · cases hd
                  · cases hd
              · cases hd
            · cases hd
          · cases hd
      · cases hd
    · cases hd
  · cases hd

end HotaruKernel
