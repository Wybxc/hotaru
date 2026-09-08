import Lake
open Lake DSL System

package HotaruKernel where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, 3⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"
require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.29.0"

@[default_target] lean_lib HotaruKernel
@[test_driver] lean_lib HotaruKernelTests
lean_lib HotaruKernelAudit
lean_lib HotaruKernelFFI

input_file cSource where
  path := "ffi" / "hotaru.c"
  text := true

input_file cHeader where
  path := "ffi" / "hotaru.h"
  text := true

target cObject pkg : FilePath := do
  let header ← cHeader.fetch
  let source ← cSource.fetch
  let lean ← getLeanInstall
  header.bindM fun _ =>
    buildO (pkg.buildDir / "ffi" / "hotaru.o") source #["-I", lean.includeDir.toString]
      #["-fPIC", "-std=c11", "-Wall", "-Wextra", "-Werror", "-pthread"]

-- Link precisely the export module's imports, rather than all of mathlib.
target hotaruC pkg : Dynlib := do
  if Platform.isWindows then error "hotaruC currently supports macOS and Linux"
  let lean ← getLeanInstall
  let some root := pkg.findModule? `HotaruKernelFFI | error "missing FFI module"
  let imports ← (← root.transImports.fetch).await
  let mut objects := #[← cObject.fetch]
  for mod in imports.push root do
    for facet in mod.nativeFacets true do
      objects := objects.push (← facet.fetch mod)
  let runtimeLibs := (← lean.leanLibDir.readDir).filterMap fun entry =>
    if (entry.fileName.startsWith "libleanshared" ||
        entry.fileName.startsWith "libInit_shared") &&
        entry.fileName.endsWith s!".{sharedLibExt}" then some entry.path.toString else none
  -- Unlike a Lean plugin, an embedded C library must resolve every symbol at link time.
  buildSharedLib "hotaru" (pkg.sharedLibDir / nameToSharedLib "hotaru") objects #[]
    (#["-L", lean.leanLibDir.toString, s!"-Wl,-rpath,{lean.leanLibDir}"] ++
      lean.ccLinkSharedFlags ++ runtimeLibs)
    (#["-pthread"] ++ if Platform.isOSX then
      #["-Wl,-install_name,@rpath/libhotaru.dylib", "-Wl,-undefined,error"]
      else #["-Wl,-z,defs"]) lean.cc.toString

input_file cTestSource where
  path := "ffi" / "tests" / "test_hotaru.c"
  text := true

target hotaruCTest pkg : FilePath := do
  let lean ← getLeanInstall
  let header ← cHeader.fetch
  let source ← cTestSource.fetch
  let obj ← header.bindM fun _ =>
    buildO (pkg.buildDir / "ffi" / "test_hotaru.o") source
      #["-I", (pkg.dir / "ffi").toString]
      #["-std=c11", "-Wall", "-Wextra", "-Werror", "-pthread"]
  let lib ← hotaruC.fetch
  buildLeanExe (pkg.buildDir / "bin" / "test_hotaru") #[obj] #[lib]
    #[s!"-Wl,-rpath,{pkg.sharedLibDir}", s!"-Wl,-rpath,{lean.leanLibDir}"]
    #["-pthread"] (sharedLean := true)
