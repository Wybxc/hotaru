# HotaruKernel

A Lean reimplementation of a HOL4-style logical kernel. **M1 is complete; M2 is
in progress:** equality and propositional reasoning, simultaneous term and
equational substitution, executable checking, and semantic soundness.
This is not a verification of HOL4's SML source or a complete HOL4 kernel.

## Build and check

From this directory, with the pinned Lean 4.29.0 toolchain:

```sh
lake build
lake env lean HotaruKernel/Audit.lean
LEAN_NUM_THREADS=2 lake env leanchecker HotaruKernel
```

The default build includes all library modules, 81 regression examples, a proof
composed using all five public operations, and the axiom audit. Tests use
`decide +kernel`, not native proof evaluation. The root repository's
`.github/workflows/lean.yml` runs the build and checks the compiled declarations.
The template workflows nested inside this package are not active root workflows.

## Proof architecture

| Layer | Definitions and results |
| --- | --- |
| Syntax | `HolType`, `Signature`, `RawTerm`, and indexed `Term` |
| Checking | `check`, `HasType`, `check_sound`, `Term.validType` |
| Substitution | `rename`, `substBound`, `open`, `substFree`, `replace`, `close` |
| Semantics | `TypeModel`, `Model`, `Term.eval`, `Models`, `Theory.Entails` |
| Inference | Independent `Derivable` judgment and `Derivable.sound` |
| Executable kernel | `Thm`, twelve operations, `Thm.sound`, `Kernel.success_sound` |

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

`SUBST` checks that substituting all left sides into the template gives the
input conclusion. Its result substitutes all right sides simultaneously and
includes hypotheses of the equality theorems. `INST` and `SUBST` use the first
matching entry for repeated variables. Replacements are not substituted again.
`SYM`, `TRANS`, and `EQ_MP` are verified derivable-but-primitive rules, with
individual soundness cases, as opposed to unchecked host-language shortcuts.

`Equality.lean` proves that equal raw encodings of typed terms have equal types
and equal internal terms. The executable term comparison uses this theorem;
it never supplies a proof merely because an unverified Boolean comparison passed.

`Thm` stores its assumptions, Boolean conclusion, and a proof of `Derivable`.
Constructing a `Thm` directly also requires that proof; there is no oracle or
unchecked constructor. Hypotheses are lists, with order and duplicates preserved.
Their semantics is conjunction, so those representation choices do not affect
soundness. A theorem is indexed by its immutable theory; there is no implicit
cross-theory conversion.

`Derivable.sound` and `Kernel.success_sound` establish that every successful
output holds under every free-variable valuation satisfying its hypotheses,
in every model satisfying all theory axioms. Theory axioms are object-logic
assumptions, not new Lean axioms. No consistency claim is made for an arbitrary
user-supplied axiom list.

`Examples.composed_output` checks the exact assumptions and conclusion of an
actual computation using all five operations. `Examples.composed_succeeds`
proves it returns a theorem, and `Examples.composed_sound` supplies its semantic
guarantee. `Examples.model` supplies a model of the empty theory;
`Examples.falsehood_not_derivable` proves that `id = (lambda b. b = b)`, a false
Boolean-function equality, cannot be derived there. This establishes that the M1
soundness result is not vacuous; it is not the M3 foundation theorem.

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
| M2 | In progress: propositional rules, `INST`, `SUBST`, `SYM`, `TRANS`, and `EQ_MP` complete; `INST_TYPE` remains |
| M3 | Not implemented: checked declarations and definitions, model extensions, choice and infinity foundations |
| M4 | Not implemented: execution traces containing theory extensions and their global correctness theorem |

Before M2's `INST_TYPE`, prove interpretation transport under type substitution,
including polymorphic constants and merging free variables of distinct original
types. Checking an instantiated constant in M1 is not a proof of `INST_TYPE`.
Before M3, validate signature extensions and prove freshness, nonempty type
definitions, and old-language interpretation preservation. The existing `Theory`
structure does not certify that a signature or axiom list came from conservative
extensions.

## References

- [HOL4 Trindemossen-2: The HOL Logic in ML](https://hol-theorem-prover.org/docs/trindemossen-2/Description/)
  is the versioned logical-interface reference. M1 corresponds to `ASSUME`,
  `REFL`, `BETA_CONV`, `ABS`, and the derivable `MK_COMB` interface.
- [Candle standard development](https://github.com/CakeML/cakeml/tree/master/candle/standard)
  motivates the separation of syntax, semantic soundness, and executable
  refinement. This project does not port its set-theoretic proofs line by line.
- [Candle project](https://cakeml.org/candle/) verifies a HOL Light implementation
  through CakeML. Its end-to-end guarantee is outside HotaruKernel M1's scope.
