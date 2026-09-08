# hotaru-sys

Safe Rust handles for Hotaru's verified Lean kernel. All ownership, runtime
reference management, error conversion, and theory identity checks are implemented
in Rust. There is no public C API, C header, JSON protocol, or handwritten C shim.
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
The pinned Lean 4.29.0 and its locked dependencies must be available. The adapter
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

## Linking and trust

Cargo builds a Rust library and links the internal `libhotaru_lean` shared library
and Lean runtime libraries. Its own tests and examples get build-tree rpaths.
Downstream executables must supply their own runtime search paths or deploy these
shared libraries in a loader-visible directory. A downstream build script can
read `DEP_HOTARU_LEAN_LIB_DIR` and `DEP_HOTARU_LEAN_RUNTIME_DIR` to set rpaths.
This package currently requires the sibling Lean source checkout; it is not a
self-contained crates.io distribution.

Lean proves the kernel's logical soundness and extension properties.
Rust's unsafe runtime adapter, its identity bookkeeping, Lean's native compiler,
the Rust compiler, linker, and runtime are outside those proofs. The adapter uses
the pinned Lean object layout, with build-time target checks and layout assertions.
Integration tests exercise every inference entry point, rejected side conditions,
polymorphic substitution, theory ancestry, definitions, and object lifetimes.
