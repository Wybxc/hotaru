use std::env;

fn main() {
    // Link arguments from a dependency are not propagated to integration
    // tests and examples. Forward the bridge's runtime search paths so every
    // high-level consumer can load the Lean shared libraries.
    for key in ["DEP_HOTARU_LEAN_LIB_DIR", "DEP_HOTARU_LEAN_RUNTIME_DIR"] {
        if let Some(path) = env::var_os(key) {
            println!("cargo:rustc-link-arg=-Wl,-rpath,{}", path.to_string_lossy());
        }
    }
}
