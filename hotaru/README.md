# hotaru

`hotaru` gives Rust programs managed access to HotaruKernel's Lean
implementation. Rust owns Lean value lifetimes, error conversion, and theory
identity checks; Lean checks logical inputs and constructs the theorems. The
`hotaru-kernel-bridge` crate contains the native bridge and is kept behind the
safe API, so `hotaru` does not implement a second set of inference rules.

## Logical contract

Rust inference methods call the Lean operations covered by the kernel's
soundness proof. A successful call returns a theorem whose Lean value carries
its assumptions, conclusion, and derivation. In every model satisfying all
axioms of the theorem's theory, its conclusion holds whenever its assumptions
hold. The [kernel README](../HotaruKernel/README.md) explains this guarantee and
the separate proof that conservative theory construction preserves a model.

The logical guarantee depends on the theory in which a theorem was produced.
An assumption-free conclusion is satisfiable when that theory has a model, but
`add_axiom` may destroy model existence. Its returned theorem is sound relative
to models satisfying the new axiom; the call does not establish consistency.

## Using the kernel

The typed public values keep Rust syntax construction separate from Lean validation.
`Type` and `Term` constructors build raw syntax, while `Theory::check` and
inference methods validate it in the current theory. `Theory::new()` starts
from the logical foundation, and `Theory::foundation` retrieves its axiom
theorems. Logical failures return `Error::Kernel` through `Result<T, Error>`;
the public methods are split across [src/syntax.rs](src/syntax.rs),
[src/theorem.rs](src/theorem.rs), and [src/theory.rs](src/theory.rs).

```rust
use hotaru::{Result, Term, Theory, Type};

fn main() -> Result<()> {
    let theory = Theory::new()?;
    let boolean = Type::bool()?;
    let p = Term::free("p", &boolean)?;
    let theorem = theory.refl(&p)?;

    assert_eq!(theorem.conclusion(), Term::equal(&p, &p)?);
    Ok(())
}
```

Repeated inference on the same term can reuse one checked representation.
`Theory::check_term(&term)` returns a `CheckedTerm` for that exact theory;
`refl_checked`, `assume_checked`, `beta_checked`, and `disch_checked` accept it
without checking the raw syntax again. A checked term retains its typed Lean
tree, so release the raw term when it is no longer needed and drop the checked
value when reuse ends. A descendant or sibling theory must check the term in
its own context.

The inference methods correspond to the thirteen Lean kernel interfaces.
They include assumption and reflexivity, beta conversion, equality and
implication rules, and term and type substitution.

Public FFI names describe logical rules rather than certificate-adapter steps.
An implementation may combine internal work when the exported operation has a
clear theorem-level meaning, as `inst_ty_term` does for simultaneous type and
term instantiation. Equality representation alignment, assumption
deduplication, and storage decisions stay inside those semantic rules, while
names that expose an execution sequence such as `eqMpThenCompact` are not part
of the interface.

The theory API provides checked declarations and definitions. `Theory`
exposes type and constant declarations and definitions; type definitions
require a theorem proving their defining predicate nonempty.

## Theories and ownership

Theory values preserve the identity of an immutable theory. An extension
returns a new theory, and a definition also returns a theorem owned by that
new theory. A theorem keeps its theory alive even if another value for that
theory is dropped. Inference rejects theorems from other theory identities,
including structurally identical sibling extensions; use
`theorem.rebase(&descendant)` to transport a theorem along its checked
extension path.

All typed values manage their Lean references automatically on one runtime thread.
`Type`, `Term`, `CheckedTerm`, `Theory`, and `Theorem` support `Clone` and
release their references on drop, but they are neither `Send` nor `Sync`. The
first thread to initialize Lean owns subsequent use, and initialization from
another thread returns `Error::WrongThread`. A second, independently
initialized Lean runtime in the same process is unsupported. Runtime
ownership and FFI calls are isolated in
the private [raw runtime module](../hotaru-kernel-bridge/src/raw/runtime.rs)
and its sibling raw modules.

## Provenance

Lean records and propagates sources as part of each theory and theorem.
`Theory::sources()` and `Theorem::sources()` expose the distinct sources
inherited from the theory and inference premises; Rust does not merge them.
`Source` identifies a claimed theory file or checkpoint by an artifact string.
Treat returned sources as a set, because their order is not a persistent
identifier.

Source annotations add context without changing logical validity.
`with_source(&source)` returns a new descendant when called on a theory and a
new theorem value in the same theory when called on a theorem. Existing theorems
must be rebased to an annotated descendant theory before use there. A source
label does not load a file, authenticate an artifact, or replace a proof.

## Build and deployment

The crate builds against the sibling Lean checkout and its pinned Lean 4.29.0
toolchain. Cargo invokes `lake build hotaruLean` and requires a C compiler and
libclang to generate bindings from the selected Lean runtime header. On
Debian or Ubuntu, install `clang libclang-dev`; on macOS, install Xcode
Command Line Tools. Set `LIBCLANG_PATH` when libclang is outside the usual
search locations. The crate requires this sibling checkout and is not a
standalone crates.io distribution.

Native builds target 64-bit little-endian macOS and Linux. Cross compilation
is unsupported because the Lean library and Rust target must match. Run the
following commands from the repository root:

```sh
cargo build -p hotaru
cargo test --workspace
cargo run -p hotaru --example refl
```

Downstream executables must be able to load the Lean shared libraries.
Tests and examples receive build-tree runtime search paths, but applications
must set their own paths or deploy the libraries in a loader-visible location.
A downstream build script can use `DEP_HOTARU_LEAN_LIB_DIR` and
`DEP_HOTARU_LEAN_RUNTIME_DIR` to configure those paths.

The [kernel benchmark protocol](../benchmarks/README.md) compares this public
interface with HOL Light and HOL4 under shared workloads.

## Trust boundary

The Lean proof covers logical operations and conservative theory extensions
as Lean definitions. Rust's unsafe adapter, native bindings, identity
bookkeeping, compilers, linker, and runtime are outside those proofs. Bindings
are generated from the pinned Lean header rather than relying on handwritten
runtime object layouts. Integration tests exercise the public inference and
theory workflows, but they do not extend the formal proof boundary.
