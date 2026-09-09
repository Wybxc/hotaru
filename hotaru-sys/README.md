# hotaru-sys

Safe Rust handles for Hotaru's verified Lean kernel. Ownership, error conversion,
and theory identity checks are implemented in Rust. Reference management calls
Lean's own runtime functions through generated bindings.
There is no public C API, C header, JSON protocol, or handwritten C shim.
Logical operations still execute the verified Lean definitions through private
native bindings.

## Build and use

Run from the repository root with Cargo and Lake on PATH:

```sh
cargo build -p hotaru-sys
cargo test --workspace
cargo run -p hotaru-sys --example refl
```

The build script invokes `lake build hotaruLean` in the sibling Lean package.
The pinned Lean 4.29.0 and its locked dependencies must be available.
Building also requires libclang and a C compiler. On Debian/Ubuntu, install
`clang libclang-dev`; on macOS, install Xcode Command Line Tools. Set
`LIBCLANG_PATH` if libclang is installed outside its usual search locations.
The adapter
supports native 64-bit little-endian macOS and Linux builds; cross compilation
and a separately initialized Lean runtime in the same process are unsupported.

```rust
use hotaru_sys::{Result, Term, Theory, Type};

fn main() -> Result<()> {
    let theory = Theory::new()?;
    let boolean = Type::bool()?;
    let p = Term::free("p", &boolean)?;
    let theorem = theory.refl(&p)?;
    assert_eq!(theorem.conclusion(), Term::equal(&p, &p)?);
    Ok(())
}
```

Type and term constructors construct raw syntax. `Theory::check` and inference
operations validate it using the Lean kernel. Strings are Rust UTF-8 strings and
preserve embedded NUL bytes. Names combine a theory scope and a local name.

## Ownership and theories

`Type`, `Term`, `Theory`, and `Theorem` own their references, support `Clone`,
and release them on drop. Their fields are private. They are neither `Send` nor
`Sync`; all use belongs to the first thread that initializes the runtime.
Attempts to initialize from another thread return `Error::WrongThread`.
In native integration tests, keep kernel scenarios within one test thread.

Theory extensions return a new immutable theory. Definitions also return a
theorem owned by that new theory. A theorem retains its owner even if the original
theory handle is dropped. Inference rejects theorems from other theory identities,
including structurally identical siblings. `theorem.rebase(&descendant)` explicitly
transports a theorem along verified extension steps. Type definitions require
a nonemptiness theorem as a mandatory argument.

The inference methods are `assume`, `refl`, `beta`, `abs`, `mk_comb`, `subst`,
`inst_type`, `disch`, `mp`, `inst`, `trans`, `symm`, and `eq_mp`.
Failures use `Result<T, Error>`, with logical errors in `Error::Kernel`.
`add_axiom` gives conditional soundness relative to models satisfying the new
axiom; it does not guarantee consistency.

## Provenance

All native inference and theory extension calls run through Lean's `Tracking`
layer, which maintains source metadata and proves its propagation. Rust does not
compute or merge sources itself.

`Source` contains a `SourceKind::TheoryFile` or `SourceKind::Checkpoint` and an
artifact string. `Theory::sources()` and `Theorem::sources()` return distinct
sources, including inherited context dependencies. Treat these lists as sets;
their ordering is not a persistent identifier.

`with_source(&source)` adds a claimed source without removing existing sources.
On a theory it returns a new descendant; existing theorem handles must be rebased
explicitly. On a theorem it returns a new handle in the same theory.
These methods annotate already valid objects. They do not load files, bypass
proofs, or establish artifact authenticity.

```rust
use hotaru_sys::{Result, Source, SourceKind, Term, Theory, Type};

fn main() -> Result<()> {
    let base = Theory::new()?;
    let source = Source::new(SourceKind::TheoryFile, "arithmetic");
    let theory = base.with_source(&source)?;
    let p = Term::free("p", &Type::bool()?)?;
    let theorem = theory.refl(&p)?;

    assert_eq!(theorem.sources()?, vec![source]);
    Ok(())
}
```

Even inference without theorem premises inherits the theory's sources.
A type definition also passes its nonemptiness proof's sources into the new
theory, so later proofs retain that dependency. All supplied SUBST equations
contribute sources, including equations unused by the template. Failed calls
leave existing handles unchanged.

Lean proves exact propagation against an independent source-reachability
relation, and that absence of a source kind excludes dependencies of that kind.
The tracked history is a shared provenance graph, not a stored HOL proof.
These guarantees concern construction history, not whether an alternative proof
could avoid the source, and do not establish that a source is trustworthy.

## Linking and trust

At build time, bindgen reads `include/lean/lean.h` from the selected Lean
toolchain and generates only the runtime bindings used by this crate.
Its [static-function wrapper support](https://rust-lang.github.io/rust-bindgen/faq.html#why-isnt-bindgen-generating-bindings-to-inline-functions)
generates C bridges for the header's inline reference counting, constructor,
string, and boxing functions. The `cc` build dependency compiles those bridges.
Both generated Rust and C files stay in Cargo's `OUT_DIR`.
Rust does not duplicate object layouts, pointer tagging, or reference counting.
The Lean-generated kernel exports and initialization entry points are absent
from `lean.h`, so their private declarations remain in `src/raw.rs`.

Cargo builds a Rust library and links the internal `libhotaru_lean` shared library
and Lean runtime libraries. Its own tests and examples get build-tree rpaths.
Downstream executables must supply their own runtime search paths or deploy these
shared libraries in a loader-visible directory. A downstream build script can
read `DEP_HOTARU_LEAN_LIB_DIR` and `DEP_HOTARU_LEAN_RUNTIME_DIR` to set rpaths.
This package currently requires the sibling Lean source checkout; it is not a
self-contained crates.io distribution.

Lean proves the kernel's logical soundness and extension properties.
Rust's unsafe runtime adapter, its identity bookkeeping, bindgen, the C compiler,
Lean's native compiler, the Rust compiler, linker, and runtime are outside those
proofs. Bindgen generates the layout assertions from the pinned header, and
build-time checks enforce the supported toolchain and targets.
Integration tests exercise every inference entry point, rejected side conditions,
polymorphic substitution, theory ancestry, definitions, and object lifetimes.
