# Rust and Lean Layers

The workspace has two Rust crates next to the independent `HotaruKernel`
Lean project:

- `hotaru` is the safe public API. Its `syntax`, `theorem`, `theory`, and
  `foundation` modules own the Rust-facing types and theorem workflows.
- `hotaru-kernel-bridge` is split into a private `raw` boundary and a public
  `typed` API. The raw side owns bindgen output, handwritten HotaruKernel FFI
  declarations, Lean runtime initialization, reference counting, native error
  decoding, and conversion helpers. The typed side owns distinct `Type`,
  `Term`, `CheckedTerm`, `Theorem`, and `Theory` wrappers.

The type-erased `Handle`, `Obj`, `Owned`, generated Lean runtime types, and raw
FFI calls are confined to `hotaru-kernel-bridge/src/raw`; no raw type appears
in a public signature or is re-exported by the crate root. `hotaru/src/lib.rs`
forbids unsafe code and re-exports only the typed bridge API. Typed theory
objects retain runtime context identity checks, so dynamically extended
theories remain compatible with the existing Lean semantics.

The Lean proofs and logical definitions remain in `HotaruKernel/` and are
built by the bridge's `build.rs` without changing their proof boundary.
