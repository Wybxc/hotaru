import HotaruKernel.TheoryMigration
import HotaruKernel.TypeSupport

namespace HotaruKernel

structure ConstantDefinition (t : Theory) where
  name : QName
  type : HolType
  rhs : Closed t.signature type
  wellFormed : t.signature.WellFormed
  fresh : t.signature.constants.lookup name = none
  closed : rhs.freeVars = []
  supported : ∀ n ∈ rhs.typeVars, n ∈ type.vars

namespace ConstantDefinition

variable {t : Theory}

def signature (d : ConstantDefinition t) : Signature := t.signature.addConstant d.name d.type

theorem extendsSignature (d : ConstantDefinition t) : t.signature.Extends d.signature :=
  t.signature.extends_addConstant d.name d.type d.fresh

theorem signatureWellFormed (d : ConstantDefinition t) : d.signature.WellFormed :=
  d.wellFormed.addConstant d.name d.type d.fresh (d.rhs.validType (fun _ h => by cases h))

def constant (d : ConstantDefinition t) : Closed d.signature d.type :=
  cast (congrArg (Closed d.signature) (HolType.inst_nil d.type))
    (.const d.name d.type [] (by simp [signature, Signature.addConstant]) (by
      rw [HolType.inst_nil]
      exact d.extendsSignature.validType _ (d.rhs.validType (fun _ h => by cases h))))

def equation (d : ConstantDefinition t) : Formula d.signature :=
  .equal d.constant (d.rhs.rebase d.extendsSignature)

def target (d : ConstantDefinition t) : Theory :=
  ⟨d.signature, d.equation :: t.axioms.map (Term.rebase d.extendsSignature), t.origin⟩

def extension (d : ConstantDefinition t) : TheoryExtension t where
  target := d.target
  extension := ⟨d.extendsSignature,
    fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩
  wellFormed := d.signatureWellFormed

def definitionThm (d : ConstantDefinition t) : Thm d.target :=
  ⟨[], d.equation, Derivable.axiom (t := d.target) d.equation (List.mem_cons_self ..),
    d.target.origin⟩

theorem definition_sound (d : ConstantDefinition t) : d.target.Entails [] d.equation :=
  d.definitionThm.sound

end ConstantDefinition

def Kernel.DEFINE_CONSTANT (t : Theory) (n : QName) (rhs : RawTerm) :
    Except KernelError (ConstantDefinition t) := do
  if hw : t.signature.WellFormed then
    if hn : t.signature.constants.lookup n = none then
      let r ← check t.signature [] rhs
      if hc : r.term.freeVars = [] then
        if ht : ∀ k ∈ r.term.typeVars, k ∈ r.type.vars then
          return ⟨n, r.type, r.term, hw, hn, hc, ht⟩
        else .error .hiddenTypeVariables
      else .error .freeVariablesInDefinition
    else .error .duplicateConstant
  else .error .invalidSignature

theorem Kernel.defineConstant_spec (t : Theory) (n : QName) (rhs : RawTerm)
    (d : ConstantDefinition t) (hd : Kernel.DEFINE_CONSTANT t n rhs = .ok d) :
    d.name = n ∧ d.rhs.raw = rhs := by
  unfold DEFINE_CONSTANT at hd
  split at hd
  · split at hd
    · cases hc : check t.signature [] rhs with
      | error e => simp [hc, bind, Except.bind] at hd
      | ok r =>
        simp only [hc, bind, Except.bind, pure, Except.pure] at hd
        split at hd
        · split at hd
          · cases hd
            exact ⟨rfl, r.erases⟩
          · cases hd
        · cases hd
    · cases hd
  · cases hd

end HotaruKernel
