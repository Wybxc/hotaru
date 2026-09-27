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
def newState (_ : Unit) : Execution.State := Execution.initial

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
def equationPair (s : Execution.State) (a : RawTerm) (th : Thm s.theory) :
    RawTerm × Thm s.theory := (a, th)

@[export hotaru_lean_some_thm]
def someThm (s : Execution.State) (th : Thm s.theory) : Option (Thm s.theory) := some th

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
def checkTerm (s : Execution.State) (p : RawTerm) : Result HolType :=
  result ((check s.theory.signature [] p).map Checked.type)
@[export hotaru_lean_check_term]
def checkTermHandle (s : Execution.State) (p : RawTerm) : Result (CheckedTerm s.theory) :=
  result (checkClosed s.theory p)
@[export hotaru_lean_checked_type]
def checkedType (s : Execution.State) (p : CheckedTerm s.theory) : HolType := p.type
@[export hotaru_lean_foundation]
def foundation (s : Execution.State) (index : UInt64) : Result (Thm s.theory) :=
  if index < 4 then result (s.get index.toNat) else .error 8

@[export hotaru_lean_assume]
def assume (s : Execution.State) (p : RawTerm) : Result (Thm s.theory) :=
  result (Kernel.ASSUME s.theory p)
@[export hotaru_lean_assume_checked]
def assumeChecked (s : Execution.State) (p : CheckedTerm s.theory) : Result (Thm s.theory) :=
  result (Kernel.ASSUME_CHECKED s.theory p)
@[export hotaru_lean_refl]
def refl (s : Execution.State) (p : RawTerm) : Result (Thm s.theory) :=
  result (Kernel.REFL s.theory p)
@[export hotaru_lean_refl_checked]
def reflChecked (s : Execution.State) (p : CheckedTerm s.theory) : Thm s.theory :=
  Kernel.REFL_CHECKED s.theory p
@[export hotaru_lean_beta]
def beta (s : Execution.State) (p : RawTerm) : Result (Thm s.theory) :=
  result (Kernel.BETA_CONV s.theory p)
@[export hotaru_lean_beta_checked]
def betaCheckedTerm (s : Execution.State) (p : CheckedTerm s.theory) : Result (Thm s.theory) :=
  result (Kernel.BETA_CONV_CHECKED s.theory p)
@[export hotaru_lean_abs]
def abs (s : Execution.State) (name : String) (a : HolType) (th : Thm s.theory) :
    Result (Thm s.theory) := result (Kernel.ABS s.theory name a th)
@[export hotaru_lean_mk_comb]
def mkComb (s : Execution.State) (a b : Thm s.theory) : Result (Thm s.theory) :=
  result (Kernel.MK_COMB s.theory a b)
@[export hotaru_lean_disch]
def disch (s : Execution.State) (p : RawTerm) (th : Thm s.theory) :
    Result (Thm s.theory) :=
  result (Kernel.DISCH s.theory p th)
@[export hotaru_lean_disch_checked]
def dischChecked (s : Execution.State) (p : CheckedTerm s.theory) (th : Thm s.theory) :
    Result (Thm s.theory) :=
  result (Kernel.DISCH_CHECKED s.theory p th)
@[export hotaru_lean_mp]
def mp (s : Execution.State) (a b : Thm s.theory) : Result (Thm s.theory) :=
  result (Kernel.MP s.theory a b)
@[export hotaru_lean_symm]
def symm (s : Execution.State) (th : Thm s.theory) : Result (Thm s.theory) :=
  result (Kernel.SYM s.theory th)
@[export hotaru_lean_trans]
def trans (s : Execution.State) (a b : Thm s.theory) : Result (Thm s.theory) :=
  result (Kernel.TRANS s.theory a b)
@[export hotaru_lean_eq_mp]
def eqMp (s : Execution.State) (a b : Thm s.theory) : Result (Thm s.theory) :=
  result (Kernel.EQ_MP s.theory a b)
@[export hotaru_lean_inst]
def inst (s : Execution.State) (rs : Array (RawTerm × RawTerm)) (th : Thm s.theory) :
    Result (Thm s.theory) := result (Kernel.INST s.theory rs.toList th)
@[export hotaru_lean_inst_type]
def instType (s : Execution.State) (rs : Array (String × HolType)) (th : Thm s.theory) :
    Result (Thm s.theory) := result (Kernel.INST_TYPE s.theory rs.toList th)
@[export hotaru_lean_subst]
def subst (s : Execution.State) (rs : Array (RawTerm × Thm s.theory)) (p : RawTerm)
    (th : Thm s.theory) : Result (Thm s.theory) :=
  result (Kernel.SUBST s.theory rs.toList p th)

/-- Packages a native extension result; provenance lives in its core theory and theorem. -/
structure Extension (s : Execution.State) where
  data : TheoryExtension s.theory
  produced : Option (Thm data.target)

@[export hotaru_lean_extension_state]
def Extension.state (s : Execution.State) (e : Extension s) : Execution.State :=
  ⟨e.data.target, e.data.wellFormed, s.theorems.map (Thm.rebase e.data.extension)⟩

@[export hotaru_lean_extension_thm]
def Extension.theorem (s : Execution.State) (e : Extension s) :
    Result (Thm e.state.theory) :=
  match e.produced with | none => .error 8 | some th => .ok th

@[export hotaru_lean_rebase]
def rebase (s : Execution.State) (e : Extension s) (th : Thm s.theory) :
    Thm e.state.theory := th.rebase e.data.extension

@[export hotaru_lean_declare_type]
def declareType (s : Execution.State) (scope name : String) (arity : UInt64) :
    Result (Extension s) :=
  result (do return ⟨← Kernel.DECLARE_TYPE_VALID s.theory s.wellFormed
    ⟨scope, name⟩ arity.toNat, none⟩)

@[export hotaru_lean_declare_const]
def declareConst (s : Execution.State) (scope name : String) (a : HolType) :
    Result (Extension s) :=
  result (do return ⟨← Kernel.DECLARE_CONSTANT_VALID s.theory s.wellFormed
    ⟨scope, name⟩ a, none⟩)

@[export hotaru_lean_define_const]
def defineConst (s : Execution.State) (scope name : String) (p : RawTerm) :
    Result (Extension s) :=
  result (do
    let d ← Kernel.DEFINE_CONSTANT s.theory ⟨scope, name⟩ p
    return ⟨d.extension, some d.definitionThm⟩)

@[export hotaru_lean_define_type]
def defineType (s : Execution.State) (scope name : String) (parameters : Array String)
    (predicate : RawTerm) (proof : Option (Thm s.theory)) : Result (Extension s) :=
  result (do
    let d ← Kernel.DEFINE_TYPE s.theory ⟨scope, name⟩ parameters.toList predicate proof
    return ⟨d.extension, some d.definitionThm⟩)

@[export hotaru_lean_add_axiom]
def addAxiom (s : Execution.State) (p : RawTerm) : Result (Extension s) :=
  result (do
    let step ← Execution.checkStep s (.addAxiom p)
    return ⟨step.extension, step.produced.head?⟩)

@[export hotaru_lean_source]
def source (kind : UInt32) (artifact : String) : Result Provenance.Source :=
  match kind with
  | 0 => .ok ⟨.theoryFile, artifact⟩
  | 1 => .ok ⟨.checkpoint, artifact⟩
  | _ => .error 6

@[export hotaru_lean_mark_theorem]
def markTheorem (s : Execution.State) (th : Thm s.theory) (src : Provenance.Source) :
    Thm s.theory := th.mark src

@[export hotaru_lean_mark_theory]
def markTheory (s : Execution.State) (src : Provenance.Source) : Result (Extension s) :=
  result (do return ⟨← Kernel.MARK_THEORY s.theory src, none⟩)

@[export hotaru_lean_theorem_sources]
def theoremSources (s : Execution.State) (th : Thm s.theory) : Array Provenance.Source :=
  th.origin.sources.toArray

@[export hotaru_lean_theory_sources]
def theorySources (s : Execution.State) : Array Provenance.Source := s.theory.origin.sources.toArray

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
def conclusion (s : Execution.State) (th : Thm s.theory) : RawTerm := th.conclusion.raw
@[export hotaru_lean_assumption_count]
def assumptionCount (s : Execution.State) (th : Thm s.theory) : UInt64 :=
  th.assumptions.length.toUInt64
@[export hotaru_lean_assumption]
def assumption (s : Execution.State) (th : Thm s.theory) (i : UInt64) : Result RawTerm :=
  match th.assumptions[i.toNat]? with | none => .error 8 | some p => .ok p.raw

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

theorem success_sound (s : Execution.State) (r : Result (Thm s.theory))
    (th : Thm s.theory) (_h : r = .ok th) :
    s.theory.Entails th.assumptions th.conclusion := th.sound

theorem extension_valid (s : Execution.State) (e : Extension s) :
    s.theory.Extends e.state.theory ∧ e.state.theory.signature.WellFormed :=
  ⟨e.data.extension, e.data.wellFormed⟩

theorem rebase_sound (s : Execution.State) (e : Extension s) (th : Thm s.theory) :
    e.state.theory.Entails (rebase s e th).assumptions
      (rebase s e th).conclusion := (rebase s e th).sound

theorem theorem_sources_complete (s : Execution.State) (th : Thm s.theory)
    (src : Provenance.Source) (h : Provenance.Depends th.origin.history src) :
    src ∈ theoremSources s th := by
  simpa [theoremSources] using th.complete h

theorem theory_sources_complete (s : Execution.State) (src : Provenance.Source)
    (h : Provenance.Depends s.theory.origin.history src) : src ∈ theorySources s := by
  simpa [theorySources] using s.theory.origin.complete h

theorem theorem_sources_kind_absent (s : Execution.State) (th : Thm s.theory)
    (kind : Provenance.Kind)
    (h : ∀ src ∈ theoremSources s th, src.kind ≠ kind) :
    ∀ src, src.kind = kind → ¬ Provenance.Depends th.origin.history src := by
  apply th.kind_absent kind
  intro src hs
  exact h src (by simpa [theoremSources] using hs)

theorem theory_sources_kind_absent (s : Execution.State) (kind : Provenance.Kind)
    (h : ∀ src ∈ theorySources s, src.kind ≠ kind) :
    ∀ src, src.kind = kind → ¬ Provenance.Depends s.theory.origin.history src := by
  apply s.theory.origin.kind_absent kind
  intro src hs
  exact h src (by simpa [theorySources] using hs)

end HotaruKernel.FFI
