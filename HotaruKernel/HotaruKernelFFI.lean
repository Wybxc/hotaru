import HotaruKernel

/-! Internal native exports for hotaru-sys. Rust checks handle ownership; all
logical operations call the verified kernel. No serialized theorem import. -/
namespace HotaruKernel.FFI

abbrev Result (α : Type) := Except UInt32 α

def errorCode : KernelError → UInt32
  | .invalidType => 100 | .unboundVariable => 101 | .unknownConstant => 102
  | .notFunction => 103 | .typeMismatch => 104 | .notBoolean => 105
  | .notEquation => 106 | .notBetaRedex => 107 | .freeInAssumptions => 108
  | .notImplication => 109 | .notVariable => 110 | .termMismatch => 111
  | .invalidSignature => 112 | .duplicateType => 113 | .duplicateConstant => 114
  | .freeVariablesInDefinition => 115 | .hiddenTypeVariables => 116
  | .duplicateTypeParameter => 117 | .missingNonemptyProof => 118
  | .nonemptyProofHasAssumptions => 119 | .notPredicate => 120
  | .invalidTheoremReference => 121

def result (r : Except KernelError α) : Result α := r.mapError errorCode

@[export hotaru_lean_new]
def newState (_ : Unit) : Tracking.State := Tracking.initial

@[export hotaru_lean_type_bool]
def typeBool (_ : Unit) : HolType := .bool
@[export hotaru_lean_type_var]
def typeVar (name : String) : HolType := .var name
@[export hotaru_lean_type_fn]
def typeFn (a b : HolType) : HolType := .fn a b
@[export hotaru_lean_type_op]
def typeOp (scope name : String) (args : Array HolType) : HolType :=
  .op ⟨scope, name⟩ args.toList
@[export hotaru_lean_binding]
def binding (name : String) (a : HolType) : String × HolType := (name, a)
@[export hotaru_lean_term_pair]
def termPair (a b : RawTerm) : RawTerm × RawTerm := (a, b)
@[export hotaru_lean_equation_pair]
def equationPair (s : Tracking.State) (a : RawTerm) (th : Tracking.Theorem s) :
    RawTerm × Tracking.Theorem s := (a, th)

@[export hotaru_lean_some_thm]
def someThm (s : Tracking.State) (th : Tracking.Theorem s) : Option (Tracking.Theorem s) := some th

@[export hotaru_lean_term_free]
def termFree (name : String) (a : HolType) : RawTerm := .fvar name a
@[export hotaru_lean_term_bound]
def termBound (index : UInt64) : RawTerm := .bvar index.toNat
@[export hotaru_lean_term_const]
def termConst (scope name : String) (inst : Array (String × HolType)) : RawTerm :=
  .const ⟨scope, name⟩ inst.toList
@[export hotaru_lean_term_app]
def termApp (f x : RawTerm) : RawTerm := .app f x
@[export hotaru_lean_term_lam]
def termLam (a : HolType) (body : RawTerm) : RawTerm := .lam a body
@[export hotaru_lean_term_equal]
def termEqual (a b : RawTerm) : RawTerm := .equal a b
@[export hotaru_lean_term_imp]
def termImp (a b : RawTerm) : RawTerm := .imp a b

@[export hotaru_lean_check]
def checkTerm (s : Tracking.State) (p : RawTerm) : Result HolType :=
  result ((check s.value.theory.signature [] p).map Checked.type)
@[export hotaru_lean_foundation]
def foundation (s : Tracking.State) (index : UInt64) : Result (Tracking.Theorem s) :=
  if index < 4 then result (Tracking.foundation s index.toNat) else .error 8

@[export hotaru_lean_assume]
def assume (s : Tracking.State) (p : RawTerm) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.assume p))
@[export hotaru_lean_refl]
def refl (s : Tracking.State) (p : RawTerm) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.refl p))
@[export hotaru_lean_beta]
def beta (s : Tracking.State) (p : RawTerm) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.beta p))
@[export hotaru_lean_abs]
def abs (s : Tracking.State) (name : String) (a : HolType) (th : Tracking.Theorem s) :
    Result (Tracking.Theorem s) := result (Tracking.Inference.run s (.abs name a th))
@[export hotaru_lean_mk_comb]
def mkComb (s : Tracking.State) (a b : Tracking.Theorem s) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.mkComb a b))
@[export hotaru_lean_disch]
def disch (s : Tracking.State) (p : RawTerm) (th : Tracking.Theorem s) :
    Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.disch p th))
@[export hotaru_lean_mp]
def mp (s : Tracking.State) (a b : Tracking.Theorem s) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.mp a b))
@[export hotaru_lean_symm]
def symm (s : Tracking.State) (th : Tracking.Theorem s) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.symm th))
@[export hotaru_lean_trans]
def trans (s : Tracking.State) (a b : Tracking.Theorem s) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.trans a b))
@[export hotaru_lean_eq_mp]
def eqMp (s : Tracking.State) (a b : Tracking.Theorem s) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.eqMp a b))
@[export hotaru_lean_inst]
def inst (s : Tracking.State) (rs : Array (RawTerm × RawTerm)) (th : Tracking.Theorem s) :
    Result (Tracking.Theorem s) := result (Tracking.Inference.run s (.inst rs.toList th))
@[export hotaru_lean_inst_type]
def instType (s : Tracking.State) (rs : Array (String × HolType)) (th : Tracking.Theorem s) :
    Result (Tracking.Theorem s) := result (Tracking.Inference.run s (.instType rs.toList th))
@[export hotaru_lean_subst]
def subst (s : Tracking.State) (rs : Array (RawTerm × Tracking.Theorem s)) (p : RawTerm)
    (th : Tracking.Theorem s) : Result (Tracking.Theorem s) :=
  result (Tracking.Inference.run s (.subst rs.toList p th))

abbrev Extension (s : Tracking.State) := Tracking.Extension s

@[export hotaru_lean_extension_state]
def Extension.state (s : Tracking.State) (e : Extension s) : Tracking.State :=
  Tracking.Extension.state e

@[export hotaru_lean_extension_thm]
def Extension.theorem (s : Tracking.State) (e : Extension s) :
    Result (Tracking.Theorem e.state) :=
  match Tracking.Extension.theorem e with | none => .error 8 | some th => .ok th

@[export hotaru_lean_rebase]
def rebase (s : Tracking.State) (e : Extension s) (th : Tracking.Theorem s) :
    Tracking.Theorem e.state := e.rebase th

@[export hotaru_lean_declare_type]
def declareType (s : Tracking.State) (scope name : String) (arity : UInt64) :
    Result (Extension s) :=
  result (Tracking.Change.run s (.declareType ⟨scope, name⟩ arity.toNat))

@[export hotaru_lean_declare_const]
def declareConst (s : Tracking.State) (scope name : String) (a : HolType) :
    Result (Extension s) :=
  result (Tracking.Change.run s (.declareConstant ⟨scope, name⟩ a))

@[export hotaru_lean_define_const]
def defineConst (s : Tracking.State) (scope name : String) (p : RawTerm) :
    Result (Extension s) :=
  result (Tracking.Change.run s (.defineConstant ⟨scope, name⟩ p))

@[export hotaru_lean_define_type]
def defineType (s : Tracking.State) (scope name : String) (parameters : Array String)
    (predicate : RawTerm) (proof : Option (Tracking.Theorem s)) : Result (Extension s) :=
  result (Tracking.Change.run s (.defineType ⟨scope, name⟩ parameters.toList predicate proof))

@[export hotaru_lean_add_axiom]
def addAxiom (s : Tracking.State) (p : RawTerm) : Result (Extension s) :=
  result (Tracking.Change.run s (.addAxiom p))

@[export hotaru_lean_source]
def source (kind : UInt32) (artifact : String) : Result Provenance.Source :=
  match kind with
  | 0 => .ok ⟨.theoryFile, artifact⟩
  | 1 => .ok ⟨.checkpoint, artifact⟩
  | _ => .error 6

@[export hotaru_lean_mark_theorem]
def markTheorem (s : Tracking.State) (th : Tracking.Theorem s) (src : Provenance.Source) :
    Tracking.Theorem s := th.mark src

@[export hotaru_lean_mark_theory]
def markTheory (s : Tracking.State) (src : Provenance.Source) : Result (Extension s) :=
  result (Tracking.Change.run s (.mark src))

@[export hotaru_lean_theorem_sources]
def theoremSources (s : Tracking.State) (th : Tracking.Theorem s) : Array Provenance.Source :=
  th.origin.sources.toArray

@[export hotaru_lean_theory_sources]
def theorySources (s : Tracking.State) : Array Provenance.Source := s.origin.sources.toArray

@[export hotaru_lean_sources_count]
def sourcesCount (xs : Array Provenance.Source) : UInt64 := xs.size.toUInt64

@[export hotaru_lean_sources_get]
def sourcesGet (xs : Array Provenance.Source) (i : UInt64) : Result Provenance.Source :=
  match xs[i.toNat]? with | some src => .ok src | none => .error 8

@[export hotaru_lean_source_kind]
def sourceKind (src : Provenance.Source) : UInt32 :=
  match src.kind with | .theoryFile => 0 | .checkpoint => 1

@[export hotaru_lean_source_artifact]
def sourceArtifact (src : Provenance.Source) : String := src.artifact

@[export hotaru_lean_conclusion]
def conclusion (s : Tracking.State) (th : Tracking.Theorem s) : RawTerm := th.value.conclusion.raw
@[export hotaru_lean_assumption_count]
def assumptionCount (s : Tracking.State) (th : Tracking.Theorem s) : UInt64 :=
  th.value.assumptions.length.toUInt64
@[export hotaru_lean_assumption]
def assumption (s : Tracking.State) (th : Tracking.Theorem s) (i : UInt64) : Result RawTerm :=
  match th.value.assumptions[i.toNat]? with | none => .error 8 | some p => .ok p.raw

@[export hotaru_lean_type_eq]
def typeEq (a b : HolType) : Bool := a == b
@[export hotaru_lean_term_eq]
def termEq (a b : RawTerm) : Bool := a == b
@[export hotaru_lean_type_kind]
def typeKind : HolType → UInt32
  | .bool => 0 | .var _ => 1 | .fn .. => 2 | .op .. => 3
@[export hotaru_lean_term_kind]
def termKind : RawTerm → UInt32
  | .fvar .. => 0 | .bvar _ => 1 | .const .. => 2 | .app .. => 3
  | .lam .. => 4 | .equal .. => 5 | .imp .. => 6
@[export hotaru_lean_type_name]
def typeName : HolType → Result String
  | .var n | .op ⟨_, n⟩ _ => .ok n | _ => .error 6
@[export hotaru_lean_type_scope]
def typeScope : HolType → Result String
  | .op ⟨n, _⟩ _ => .ok n | _ => .error 6
@[export hotaru_lean_term_name]
def termName : RawTerm → Result String
  | .fvar n _ | .const ⟨_, n⟩ _ => .ok n | _ => .error 6
@[export hotaru_lean_term_scope]
def termScope : RawTerm → Result String
  | .const ⟨n, _⟩ _ => .ok n | _ => .error 6
@[export hotaru_lean_type_arity]
def typeArity : HolType → UInt64
  | .fn .. => 2 | .op _ args => args.length.toUInt64 | _ => 0
@[export hotaru_lean_type_child]
def typeChild (a : HolType) (i : UInt64) : Result HolType :=
  let children := match a with | .fn a b => [a, b] | .op _ xs => xs | _ => []
  match children[i.toNat]? with | none => .error 8 | some b => .ok b
@[export hotaru_lean_term_child]
def termChild (p : RawTerm) (i : UInt64) : Result RawTerm :=
  let children := match p with
    | .app a b | .equal a b | .imp a b => [a, b] | .lam _ b => [b] | _ => []
  match children[i.toNat]? with | none => .error 8 | some b => .ok b
@[export hotaru_lean_term_annotation]
def termAnnotation : RawTerm → Result HolType
  | .fvar _ a | .lam a _ => .ok a | _ => .error 6
@[export hotaru_lean_bound_index]
def boundIndex : RawTerm → Result UInt64
  | .bvar n => if n < 2^64 then .ok n.toUInt64 else .error 8 | _ => .error 6
@[export hotaru_lean_inst_count]
def instCount : RawTerm → Result UInt64
  | .const _ i => .ok i.length.toUInt64 | _ => .error 6
@[export hotaru_lean_inst_name]
def instName (p : RawTerm) (i : UInt64) : Result String :=
  match p with
  | .const _ xs => match xs[i.toNat]? with | some x => .ok x.1 | none => .error 8
  | _ => .error 6
@[export hotaru_lean_inst_value]
def instValue (p : RawTerm) (i : UInt64) : Result HolType :=
  match p with
  | .const _ xs => match xs[i.toNat]? with | some x => .ok x.2 | none => .error 8
  | _ => .error 6

theorem success_sound (s : Tracking.State) (r : Result (Tracking.Theorem s))
    (th : Tracking.Theorem s) (_h : r = .ok th) :
    s.value.theory.Entails th.value.assumptions th.value.conclusion := th.value.sound

theorem extension_valid (s : Tracking.State) (e : Extension s) :
    s.value.theory.Extends e.state.value.theory ∧ e.state.value.theory.signature.WellFormed :=
  ⟨e.core.data.extension, e.core.data.wellFormed⟩

theorem rebase_sound (s : Tracking.State) (e : Extension s) (th : Tracking.Theorem s) :
    e.state.value.theory.Entails (rebase s e th).value.assumptions
      (rebase s e th).value.conclusion := (rebase s e th).value.sound

theorem theorem_sources_complete (s : Tracking.State) (th : Tracking.Theorem s)
    (src : Provenance.Source) (h : Provenance.Depends th.origin.history src) :
    src ∈ theoremSources s th := by
  simpa [theoremSources] using th.complete h

theorem theory_sources_complete (s : Tracking.State) (src : Provenance.Source)
    (h : Provenance.Depends s.origin.history src) : src ∈ theorySources s := by
  simpa [theorySources] using s.complete h

theorem theorem_sources_kind_absent (s : Tracking.State) (th : Tracking.Theorem s)
    (kind : Provenance.Kind)
    (h : ∀ src ∈ theoremSources s th, src.kind ≠ kind) :
    ∀ src, src.kind = kind → ¬ Provenance.Depends th.origin.history src := by
  apply th.kind_absent kind
  intro src hs
  exact h src (by simpa [theoremSources] using hs)

theorem theory_sources_kind_absent (s : Tracking.State) (kind : Provenance.Kind)
    (h : ∀ src ∈ theorySources s, src.kind ≠ kind) :
    ∀ src, src.kind = kind → ¬ Provenance.Depends s.origin.history src := by
  apply s.origin.kind_absent kind
  intro src hs
  exact h src (by simpa [theorySources] using hs)

end HotaruKernel.FFI
