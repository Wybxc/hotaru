use std::{env, fs, path::Path, process::Command};

fn lake(dir: &Path, args: &[&str]) -> String {
    let output = Command::new("lake")
        .current_dir(dir)
        .args(args)
        .output()
        .expect("lake must be installed and available on PATH");
    assert!(
        output.status.success(),
        "lake {args:?} failed:\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("lake output is UTF-8")
        .trim()
        .to_owned()
}

fn main() {
    assert_eq!(
        env::var("HOST").unwrap(),
        env::var("TARGET").unwrap(),
        "cross compilation is not supported: the Lean library must match the Rust target"
    );
    let os = env::var("CARGO_CFG_TARGET_OS").unwrap();
    assert!(
        os == "macos" || os == "linux",
        "supported targets are macOS and Linux"
    );
    assert_eq!(env::var("CARGO_CFG_TARGET_POINTER_WIDTH").unwrap(), "64");
    assert_eq!(env::var("CARGO_CFG_TARGET_ENDIAN").unwrap(), "little");
    let manifest = env::var_os("CARGO_MANIFEST_DIR").unwrap();
    let kernel = Path::new(&manifest)
        .join("../HotaruKernel")
        .canonicalize()
        .unwrap();
    for path in [
        "lean-toolchain",
        "lakefile.lean",
        "lake-manifest.json",
        "HotaruKernel.lean",
        "HotaruKernel",
        "HotaruKernelFFI.lean",
    ] {
        println!("cargo:rerun-if-changed={}", kernel.join(path).display());
    }
    println!("cargo:rerun-if-env-changed=MACOSX_DEPLOYMENT_TARGET");
    assert_eq!(
        fs::read_to_string(kernel.join("lean-toolchain"))
            .unwrap()
            .trim(),
        "leanprover/lean4:v4.29.0",
        "runtime bindings require Lean 4.29.0"
    );
    lake(&kernel, &["build", "hotaruLean"]);
    let prefix = lake(&kernel, &["env", "lean", "--print-prefix"]);
    let runtime = Path::new(&prefix).join("lib/lean");
    let library = kernel.join(".lake/build/lib");
    for path in [&library, &runtime] {
        println!("cargo:rustc-link-search=native={}", path.display());
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", path.display());
    }
    println!("cargo:rustc-link-lib=dylib=hotaru_lean");
    let ext = if os == "macos" { "dylib" } else { "so" };
    let mut libs = Vec::new();
    for entry in fs::read_dir(&runtime).unwrap() {
        let path = entry.unwrap().path();
        let name = path.file_name().unwrap().to_str().unwrap();
        if (name.starts_with("libleanshared") || name.starts_with("libInit_shared"))
            && path.extension().and_then(|e| e.to_str()) == Some(ext)
        {
            libs.push(
                name.strip_prefix("lib")
                    .unwrap()
                    .strip_suffix(&format!(".{ext}"))
                    .unwrap()
                    .to_owned(),
            );
        }
    }
    libs.sort();
    assert!(!libs.is_empty(), "Lean runtime shared libraries not found");
    for lib in libs {
        println!("cargo:rustc-link-lib=dylib={lib}");
    }
    println!("cargo:lib_dir={}", library.display());
    println!("cargo:runtime_dir={}", runtime.display());
}
