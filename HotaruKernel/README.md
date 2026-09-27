# HotaruKernel

HotaruKernel is a Lean 4 implementation of a HOL4-style logical kernel. It
defines the object logic, executes checked inference rules, and proves those
rules sound against a separately defined semantics. It covers polymorphic
inference, conservative theory construction, a model of the logical foundation,
and verified command sequences.

## The central guarantee

The central guarantee connects derivability in an object theory to truth in its
models. A `Theory` supplies a signature and object-logic axioms, and a theorem
has the form `assumptions |- conclusion` in that theory. Formally:

```text
Derivable theory assumptions conclusion
  -> Theory.Entails theory assumptions conclusion
```

A model of a theory must satisfy **all its axioms together**.
`Theory.Entails` quantifies over every such model, type assignment, and
free-variable valuation, and requires the conclusion to hold whenever the
assumptions hold. Satisfying individual axioms in separate models does not meet
this condition.

The assumptions determine what soundness implies about satisfiability. An
assumption-free conclusion holds in every model of the theory and is therefore
satisfiable if the theory has a model. With assumptions, the conclusion holds
only at valuations satisfying them; it is satisfiable in that same model if
the assumptions and axioms are jointly satisfiable.

The executable kernel preserves this guarantee through proof-carrying
theorems. Each returned `Thm theory` contains a `Derivable` proof, so a
successful kernel call cannot produce a theorem without its derivation.
[`Derivable.sound`](HotaruKernel/Inference.lean) establishes the semantic
guarantee, and [`Execution.execution_sound`](HotaruKernel/Execution.lean)
extends it to every theorem in a successful command sequence.

## How the layers fit together

The architecture separates syntax, semantics, derivation, execution, and
theory evolution into distinct layers.

| Question | Lean representation | Where to start |
| --- | --- | --- |
| What expressions are legal? | `HolType`, `Signature`, `RawTerm`, and typed `Term`; `check` validates raw syntax and preserves its exact encoding. | [Syntax](HotaruKernel/Syntax.lean), [Check](HotaruKernel/Check.lean) |
| What do expressions mean? | `TypeModel`, `PolymorphicModel`, and `Term.eval` interpret booleans as `Bool`, functions as full function spaces, and constants coherently across type assignments. | [Semantics](HotaruKernel/Semantics.lean), [PolymorphicModel](HotaruKernel/PolymorphicModel.lean) |
| Which proofs are legal? | The inductive `Derivable` judgment specifies inference independently of the executable kernel; `Derivable.sound` proves its rules preserve truth. | [Inference](HotaruKernel/Inference.lean) |
| How are proofs constructed? | `Kernel` checks inputs and returns either an error or a `Thm` containing a derivation, assumptions, conclusion, and source origin. | [Kernel](HotaruKernel/Kernel.lean) |
| How can a theory grow? | Checked declarations and definitions extend an immutable theory; model-extension proofs extend each old model to a model of the new theory. | [TheoryExtension](HotaruKernel/TheoryExtension.lean), [ConstantDefinitionModel](HotaruKernel/ConstantDefinitionModel.lean), [TypeDefinitionModel](HotaruKernel/TypeDefinitionModel.lean) |
| What happens across many steps? | `Execution` composes inference, definitions, theorem migration, and their proof obligations into a final state. | [Execution](HotaruKernel/Execution.lean) |

The separation between semantics and derivation prevents evaluation from
serving as a proof oracle. Semantic interpretation supplies the correctness
criterion, while kernel operations construct derivation evidence rather than
accepting "evaluates to true" as a proof. The proof of `Derivable.sound` then
applies to every theorem constructed by the executable interface.

Theory indexing makes changes of context explicit. Terms and theorems are
indexed by their signature or theory, so moving a theorem to a descendant
theory requires a checked migration.

## Models and consistency

The foundation model makes soundness nonvacuous for the initial theory.
Without a model, "true in every model" would say nothing.
[`Foundation.model`](HotaruKernel/FoundationModel.lean) constructs one, and
`Foundation.models` proves that it satisfies all four foundation axioms
together for every type assignment and valuation. This model interprets
individuals as `Nat`, functions as full function spaces, and the choice
constant as a coherent polymorphic family.

Conservative theory operations preserve model existence. Checked declarations
and definitions extend each old model to a model of the new theory, and a type
definition requires an assumption-free proof that its defining predicate is
nonempty. Consequently,
[`Execution.execution_consistent`](HotaruKernel/Execution.lean) proves that a
successful sequence of conservative commands cannot derive falsehood without
assumptions.

Arbitrary axiom addition does not preserve model existence. `addAxiom` may
introduce any Boolean axiom, so soundness remains relative to models of the
resulting theory, but consistency is not guaranteed. Inference preserves truth
in any model of the current axioms; conservative theory construction also
preserves the existence of such a model.

## Kernel interface

The inference API exposes eight basic HOL-style rules and five derived rules.
The basic interfaces are `ASSUME`, `REFL`, `BETA_CONV`, `ABS`, `DISCH`, `MP`,
`INST_TYPE`, and `SUBST`; `MK_COMB`, `SYM`, `TRANS`, `EQ_MP`, and `INST` are
derived rather than added as inference assumptions. Each operation takes an
explicit theory, checks its raw inputs, and returns
`Except KernelError (Thm theory)`. Repeated calls can instead share a
`CheckedTerm theory` produced by `checkClosed`; checked variants of the rules
consume that term without repeating validation. The Boolean antisymmetry
schema is proved valid in the model semantics rather than assumed as a Lean
axiom.

The theory API controls declarations, definitions, and theorem migration.
Its operations add types and constants, define constants and nonempty types,
and move theorems through checked extensions. Theories are immutable, and a
theorem from an unrelated theory cannot be used implicitly.
[`Execution.Command`](HotaruKernel/Execution.lean) exposes these operations
alongside inference and explicit axiom addition, starting from the foundation
theory and its four axiom theorems.

Provenance records construction dependencies without affecting logical
soundness. Theories and theorems carry source annotations that kernel
operations propagate from their theory and premises, including evidence used
in a type definition. These annotations record neither HOL proof steps nor
authentication of a named source.

## Build and use

The Lean build uses the pinned Lean 4.29.0 toolchain. Run these commands from
this directory:

```sh
lake build
lake test
lake build HotaruKernelAudit
LEAN_NUM_THREADS=2 lake env leanchecker HotaruKernelAudit
```

The verification commands check the implementation, examples, and proof
dependencies. `lake build` checks the implementation and proofs, while
`lake test` builds regression examples and the complete operation-sequence test.
The audit checks axiom dependencies, and `leanchecker` independently checks
compiled declarations. Root CI builds Lean on Linux, macOS, and Windows and
runs tests and the audit on Linux.

The Lean entry points separate the implementation from validation and native
exports. `import HotaruKernel` imports the implementation; tests live in
`HotaruKernelTests/`, `HotaruKernelAudit.lean` runs the audit, and
`HotaruKernelFFI.lean` defines internal native exports.

The Rust interface offers managed handles while retaining Lean as the logical
implementation. See [hotaru-sys](../hotaru-sys/README.md) for examples,
build requirements, and runtime restrictions. From the workspace root:

```sh
cargo build -p hotaru-sys
cargo test --workspace
cargo run -p hotaru-sys --example refl
```

## Trust boundary

The proof relies on Lean's kernel, foundations, and a restricted set of
standard axioms. The audit permits only `propext`, `Classical.choice`, and
`Quot.sound`; it rejects admitted and custom proof axioms.

The verified result concerns this Lean-defined logic rather than every HOL4
implementation. It does not verify HOL4's SML source, Lean's code generator
or native runtime, the Rust adapter, or script and file-format compatibility.
The object language is HOL4-style and does not reproduce HOL4's raw term
encoding exactly.

For the target logical interface and semantics, see the
[HOL4 logic reference](https://hol-theorem-prover.org/docs/trindemossen-2/Logic/)
and [HOL4 rule reference](https://hol-theorem-prover.org/docs/trindemossen-2/Description/).
