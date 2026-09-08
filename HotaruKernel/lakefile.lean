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

-- Link precisely the export module's imports, rather than all of mathlib.
target hotaruLean pkg : Dynlib := do
  if Platform.isWindows then error "hotaruLean currently supports macOS and Linux"
  let lean ← getLeanInstall
  let some root := pkg.findModule? `HotaruKernelFFI | error "missing FFI module"
  let imports ← (← root.transImports.fetch).await
  let mut objects := #[]
  for mod in imports.push root do
    for facet in mod.nativeFacets true do
      objects := objects.push (← facet.fetch mod)
  let runtimeLibs := (← lean.leanLibDir.readDir).filterMap fun entry =>
    if (entry.fileName.startsWith "libleanshared" ||
        entry.fileName.startsWith "libInit_shared") &&
        entry.fileName.endsWith s!".{sharedLibExt}" then some entry.path.toString else none
  -- The embedded runtime must resolve every symbol at link time.
  buildSharedLib "hotaru_lean" (pkg.sharedLibDir / nameToSharedLib "hotaru_lean") objects #[]
    (#["-L", lean.leanLibDir.toString, s!"-Wl,-rpath,{lean.leanLibDir}"] ++
      lean.ccLinkSharedFlags ++ runtimeLibs)
    (#["-pthread"] ++ if Platform.isOSX then
      #["-Wl,-install_name,@rpath/libhotaru_lean.dylib", "-Wl,-undefined,error"]
      else #["-Wl,-z,defs"]) lean.cc.toString
