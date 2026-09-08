# HotaruKernel

A Lean reimplementation of a HOL4-style logical kernel. **M1 and M2 are
complete:** all eight basic inference interfaces, simultaneous term and
equational substitution, polymorphic instantiation, and semantic soundness.
This is not a verification of HOL4's SML source or a complete HOL4 kernel.

## Build and check

From this directory, with the pinned Lean 4.29.0 toolchain:

```sh
lake build
lake env lean HotaruKernel/Audit.lean
LEAN_NUM_THREADS=2 lake env leanchecker HotaruKernel
```

The default build includes all library modules, 168 regression examples, a proof
composed using the five original M1 operations, and the axiom audit. Tests use
`decide +kernel`, not native proof evaluation. The root repository's
`.github/workflows/lean.yml` runs the build and checks the compiled declarations.
The template workflows nested inside this package are not active root workflows.

## Proof architecture

| Layer | Definitions and results |
| --- | --- |
| Syntax | `HolType`, `Signature`, `RawTerm`, and indexed `Term` |
| Checking | `check`, `HasType`, `check_sound`, `Term.validType` |
| Substitution | `rename`, `substBound`, `open`, `substFree`, `replace`, `close` |
| Type substitution | `HolType.inst_compose`, `Term.instType`, `instType_preserves_type` |
| Semantics | `TypeModel`, `PolymorphicModel`, `Model`, `Term.eval`, `Models`, `Theory.Entails` |
| Inference | Independent `Derivable` judgment and `Derivable.sound` |
| Executable kernel | `Thm`, thirteen operations, `Thm.sound`, `Kernel.success_sound` |
| Theory extensions | `Signature.Extends`, `Theory.Extends`, checked declarations, `Thm.rebase` |

`RawTerm` uses names and types for free variables and de Bruijn indices for bound
variables. `check` returns an internal term indexed by its type and binding
context, together with a proof that it erases to exactly the input. Every public
kernel entry point checks raw terms in the empty binding context. Standalone
checking in a nonempty context assumes that context's types are valid.

Types include variables, built-in booleans and functions, and named type operators
with checked arities. Constants have theory-qualified names and polymorphic type
schemes. An occurrence supplies an explicit simultaneous type substitution;
lookup uses the first matching entry, leaves unmapped variables unchanged, and
does not recursively substitute replacements. Constant interpretations depend on
the qualified name and instantiated type, not the substitution witness.

Equality is a built-in binary syntax form, interpreted as equality of semantic
values. M1 does not expose HOL4's curried equality constant or its raw term format.
Implication is another binary syntax form, with the usual Boolean interpretation.
Function types denote full Lean function spaces. All type interpretations are
proved nonempty. Equality of functions therefore uses Lean's function
extensionality, rather than an assumed soundness field on the model.

Bound substitution and free substitution have separate semantic preservation
theorems. Free replacements are weakened under binders to prevent capture.
`ABS` closes exactly the free variable identified by both name and type, and
rejects it when it occurs in any hypothesis.

## Kernel API and guarantee

All operations are in `HotaruKernel.Kernel` and return
`Except KernelError (Thm theory)`:

| Operation | Inputs after `theory` | Result |
| --- | --- | --- |
| `ASSUME` | Boolean raw term `p` | `[p] |- p` |
| `REFL` | Checked raw term `t` | `[] |- t = t` |
| `BETA_CONV` | Raw root beta redex `(lambda x. b) a` | Equality with its capture-avoiding reduct |
| `ABS` | Variable name, type, equational theorem | Equality of abstractions, subject to freshness |
| `MK_COMB` | Function equality and argument equality | Equality of applications, combining hypotheses |
| `DISCH` | Boolean term and theorem | Implication, removing all occurrences of the discharged hypothesis |
| `MP` | Implication theorem and antecedent theorem | Consequent, after checking the antecedents agree |
| `SYM` | Equality theorem | Reversed equality |
| `TRANS` | Two equality theorems | Transitive equality, after checking the middle terms agree |
| `EQ_MP` | Boolean equality and antecedent theorem | Right-hand proposition |
| `INST` | List of `(variable, replacement)` pairs and theorem | Simultaneous substitution in hypotheses and conclusion |
| `SUBST` | List of `(variable, equality theorem)` pairs, Boolean template, input theorem | Simultaneous equational substitution |
| `INST_TYPE` | List of `(type-variable name, type)` pairs and theorem | Simultaneous type instantiation in hypotheses and conclusion |

`SUBST` checks that substituting all left sides into the template gives the
input conclusion. Its result substitutes all right sides simultaneously and
includes hypotheses of the equality theorems. `INST` and `SUBST` use the first
matching entry for repeated variables. Replacements are not substituted again.
`SYM`, `TRANS`, `EQ_MP`, and `MK_COMB` are proved from the basic rules using
`SUBST` and `REFL`. They have no independent inference constructors or soundness
cases. `freshName_not_mem` and `Substitution.apply_fresh` justify the fresh
template variables used in these derivations.
`INST` is also a derived rule. `InstDerivation.lean` discharges hypotheses,
uses abstraction and beta conversion to construct simultaneous substitution,
then restores the instantiated hypotheses. `Substitution.apply_cons_close`
is the syntactic identity ensuring that inserted replacements are not
substituted again. No derived interface has its own inference constructor.

The eight basic interfaces correspond to the official `ASSUME`, `REFL`,
`BETA_CONV`, `SUBST`, `ABS`, `INST_TYPE`, `DISCH`, and `MP` rules. Type-substitution
keys are strings, so the interface enforces the type-variable domain by its
input type. It checks validity of every replacement type.

The logical foundation includes the explicit `BooleanAxiom.impAntisym` schema,
`(p ==> q) ==> (q ==> p) ==> (p = q)`, the role of HOL4's `IMP_ANTISYM_AX`.
`BooleanAxiom.sound` proves it in the fixed Bool interpretation for every model;
it is not a Lean axiom or an assumed model field. The `INST` derivation uses this
Boolean foundation to turn a closed proof of `p` into an equality with truth.
`truth` itself is defined by reflexivity of the Boolean identity function.

`Equality.lean` proves that equal raw encodings of typed terms have equal types
and equal internal terms. The executable term comparison uses this theorem;
it never supplies a proof merely because an unverified Boolean comparison passed.
Rule matching uses the separate `LogicalTerm` representation, which identifies
constants by qualified name and instantiated type. `Term.eval_logical` proves
that equal logical representations have equal interpretations, independently
of the substitution witnesses. `MP`, `TRANS`, `EQ_MP`, `SUBST`, and `DISCH` use
this executable comparison. Distinct constant names or instance types still
fail to match. The raw representation and its exact erasure proof are preserved.

`Thm` stores its assumptions, Boolean conclusion, and a proof of `Derivable`.
Constructing a `Thm` directly also requires that proof; there is no oracle or
unchecked constructor. Hypotheses are lists, with order and duplicates preserved.
Their semantics is conjunction, so those representation choices do not affect
soundness. A theorem is indexed by its immutable theory; there is no implicit
cross-theory conversion.
The structural `Derivable.context` rule changes a hypothesis list only when its
membership set is equal, and `Derivable.conversion` changes a conclusion only
when its logical representation is equal. Their semantic preservation is
proved in `Derivable.sound`; neither accepts semantic validity as a premise.

`Derivable.sound` and `Kernel.success_sound` establish that every successful
output holds under every free-variable valuation satisfying its hypotheses,
in every polymorphic model satisfying all theory axioms at every type assignment.
`PolymorphicModel.constant_support` requires a constant's interpretation to depend
only on type variables in its declared scheme. This is a condition on semantic
data, not an assumed inference theorem. `atTypes_constant` proves independence
from the witness used to express a constant instance. `Term.eval_instType`
transports arbitrary terms, free valuations, and bound valuations between type
assignments; `Derivable.sound` uses it in its `instType` case.
Theory axioms are object-logic
assumptions, not new Lean axioms. No consistency claim is made for an arbitrary
user-supplied axiom list.

`Examples.composed_output` checks the exact assumptions and conclusion of an
actual computation using the five M1 operations. `Examples.composed_succeeds`
proves it returns a theorem, and `Examples.composed_sound` supplies its semantic
guarantee. `Examples.model` supplies a model of the empty theory;
`Examples.falsehood_not_derivable` proves that `id = (lambda b. b = b)`, a false
Boolean-function equality, cannot be derived there. This establishes that the M1
soundness result is not vacuous; it is not the M3 foundation theorem.
`PolymorphicTests.models` constructs a model of a theory with a polymorphic
identity constant and its defining equation as an axiom. Its checked
`instantiatedAxiom` computation specializes that axiom to booleans.

## Theory operations

The theory context remains explicit and immutable. The additional operations are:

| Operation | Inputs | Result |
| --- | --- | --- |
| `DECLARE_TYPE` | Theory, qualified name, arity | `Except KernelError (TheoryExtension theory)` |
| `DECLARE_CONSTANT` | Theory, qualified name, type scheme | `Except KernelError (TheoryExtension theory)` |
| `DEFINE_CONSTANT` | Theory, fresh qualified name, closed right-hand side | `Except KernelError (ConstantDefinition theory)` |
| `DEFINE_TYPE` | Theory, fresh name, distinct type parameters, closed predicate, optional nonempty theorem | `Except KernelError (TypeDefinition theory)` |
| `MIGRATE` | A checked extension and a theorem of its source theory | The theorem in the target theory |

Declarations reject malformed source signatures, duplicate names, and invalid
constant schemes. `Signature.WellFormed` checks unique type and constant names
and validity of every constant scheme. `TheoryExtension` carries the target
theory, its signature invariant, and a syntactic extension proof preserving all
old declarations and axioms. Old terms keep their raw and logical encodings.

`Kernel.declareType_model` and `Kernel.declareConstant_model` prove that every
source model extends to a target model whose restriction equals the source
model. `Term.eval_rebase` proves preservation of old-term interpretations.
The constant declaration model uses a default nonempty-type inhabitant in the
semantic proof only; declaration checking and theorem migration are executable.

`Derivable.rebase` reconstructs a derivation across a theory extension, using
proved commutation laws for substitution, abstraction, and type instantiation.
`Kernel.MIGRATE` uses this theorem. Its input type prevents migration of a
theorem from an unrelated source theory. Regression checks cover this rejection,
direct cross-theory inference rejection, and successive checked migrations.
An arbitrary `Theory.Extends` witness can permit additional axioms; preservation
of model existence is claimed only for the operations with model-extension proofs.

`DEFINE_CONSTANT` checks the right-hand side in the old signature, rejects free
term variables, and requires every type variable appearing in the term to occur
in its result type. `Term.typeVars` counts actual constant-instance types, not
unused substitution-witness entries. The returned definition provides `target`,
`extension`, and `definitionThm`; its equation is added to the target theory.
`Kernel.defineConstant_spec` proves that a successful result uses the requested
name and exact right-hand side.

`Term.eval_typeVars` proves that interpretations depend only on the type
variables that occur in a term. `ConstantDefinition.model_extension` uses this
result to construct a coherent polymorphic interpretation of the new constant
from the right-hand side. Every source model extends to a model satisfying the
defining equation, and restriction recovers the source model. The computation
in `ConstantDefinitionTests.composedDefinition` defines polymorphic identity,
instantiates its defining theorem to Bool, and applies it using kernel rules.

`DEFINE_TYPE` checks a closed predicate, its type-variable support, and an
assumption-free theorem of its existential closure in the source theory.
Missing proofs, mismatched conclusions, duplicate parameters, and proofs with
assumptions are rejected. The result introduces a type operator and the formula
asserting an injective representation whose image is exactly the predicate.
`Kernel.defineType_spec` verifies the returned name, parameters, and predicate.
`TypeDefinition.predicate_nonempty` derives semantic nonemptiness from the
supplied derivation. `TypeDefinitionTests.nonemptyProof` constructs the premise
through executable kernel calls.

`Quantifiers.lean` encodes quantifiers using equality and Boolean implication;
`Term.eval_typeDefinitionT` proves the representation formula's intended
full-function-space semantics. `subtype_representation` supplies the native
subtype inclusion and `subtype_nonempty_iff` its nonemptiness condition.
`TypeDefinition.model_extension` constructs a model of the extended theory from
every source model. The new operator denotes the nonempty subtype selected by
the predicate at each assignment of its type parameters. The inclusion map is
injective and has exactly the required image. The theorem also establishes
agreement on all old declarations; `Term.eval_agrees` transports old formulas.
Thus checked type definitions preserve model existence, as do checked constant
definitions. Regression examples construct both monomorphic and polymorphic
nonemptiness proofs through kernel calls.

`ModelAgreement.lean` proves that agreement on declared type operators preserves
the interpretation of valid old types and terms, including under binders.
`OperatorTransport.lean` transports polymorphic constant families when previously
undeclared operators acquire a new interpretation. `Theory.models_changeOperators`
proves that this transport preserves the old theory's axioms. Constant instances
may contain unused substitution entries; only variables present in the scheme
are used in the preservation proof. `TypeParameters.lean` constructs the parameter
assignment, and `TypeDefinitionModel.lean` verifies the parameterized subtype and
its defining representation formula.

## Validation and trust boundary

Regression cases cover successful and rejected kernel operations, malformed
applications, dangling indices, unknown constants, invalid and nested type
operator arities, polymorphic constant instances, same-name variables at distinct
types, nested beta reductions, free substitution, and shifting replacements
under binders.

`audit_hotaru` in `Audit.lean` traverses dependencies of all declarations under
the `HotaruKernel` namespace. It fails on any axiom outside this allowlist:

- `propext`
- `Classical.choice`
- `Quot.sound`

The key theorems currently depend on these three standard Lean axioms. The audit
rejects `sorryAx`, custom axioms, and native-evaluation proof axioms. Semantic
evaluation and the example valuation use classical reasoning; kernel operations
and substitutions remain executable. There are no admitted future theorems.

Lean's kernel and foundations remain trusted. These proofs concern the Lean
definitions; they do not verify Lean's code generator, runtime, HOL4's SML
implementation, parsing, printing, or theorem serialization.

## Remaining milestones

| Milestone | Status and next obligations |
| --- | --- |
| M1 | Complete: fixed-signature semantic soundness and five executable operations |
| M2 | Complete: eight basic interfaces, all five derived interfaces, polymorphic soundness, and logical constant-instance matching |
| M3 | In progress: declarations, conservative constant and type definitions, and theorem migration; the full foundation remains |
| M4 | Not implemented: execution traces containing theory extensions and their global correctness theorem |

`TypeInstantiation.lean` now proves composition of type substitutions, type
validity preservation, and native type-interpretation transport. Its executable
`Term.instType` and `instantiateTermChecked` preserve types, binding indices, and
the raw syntax specification. Regression cases cover free-variable type merging,
nested binders, composed polymorphic constant instances, and invalid substitutions.
`TypeInstantiationSemantics.lean` and `PolymorphicModel.lean` complete the semantic
transport needed by `Kernel.INST_TYPE`. Tests also cover abstraction before and
after variable-type merging: bound indices prevent newly merged free variables
from becoming captured.

`MixedSubstitution.lean` proves renaming and mixed-substitution composition under
arbitrary binders and connects them to the executable substitutions. These
syntactic lemmas justify the complete basic-rule derivation of `INST`, including
open theory axioms and hypotheses with duplicate or logically equal encodings.

The remaining M3 work is the foundation supporting extensionality, choice,
and infinity with individuals interpreted by Nat. Direct construction of a
`Theory` does not certify that it came from conservative extensions; the checked
operation results and their model-extension theorems provide that evidence.

## References

- [HOL4 Trindemossen-2: The HOL Logic in ML](https://hol-theorem-prover.org/docs/trindemossen-2/Description/)
  is the versioned logical-interface reference. M1 corresponds to `ASSUME`,
  `REFL`, `BETA_CONV`, `ABS`, and the derivable `MK_COMB` interface.
- [Candle standard development](https://github.com/CakeML/cakeml/tree/master/candle/standard)
  motivates the separation of syntax, semantic soundness, and executable
  refinement. This project does not port its set-theoretic proofs line by line.
- [HOL4 derived inference rules](https://hol-theorem-prover.org/docs/trindemossen-2/Description/drules)
  supplies the basic-rule derivations and explains their dependence on the
  axioms and definitions of `bool`.
- [Candle project](https://cakeml.org/candle/) verifies a HOL Light implementation
  through CakeML. Its end-to-end guarantee is outside HotaruKernel M1's scope.
