#!/usr/bin/env python3
"""Import the recorded LIST_NOT_NIL proof in all three systems."""

from __future__ import annotations

import argparse
import json
import os
import platform
import shlex
import shutil
import statistics
import sys
from datetime import datetime, timezone
from pathlib import Path

import run_native as common


SYSTEMS = ("hotaru", "hol-light", "hol4")
MARKER = "LIST_NOT_NIL_REPLAY\t"
ARTICLE = common.SOURCE / "list_not_nil.art"
ARTICLE_SHA256 = "0b187bac4d8d3d41fcd1f485efc63fcd018e30c56311be029e4f36cef42431bd"


def parse(output: str, system: str, trials: int, iterations: int) -> list[int]:
    times: dict[int, int] = {}
    for line in output.splitlines():
        offset = line.find(MARKER)
        if offset < 0:
            continue
        fields = line[offset:].split("\t")
        if len(fields) != 5 or fields[:2] != ["LIST_NOT_NIL_REPLAY", system]:
            raise ValueError(f"malformed {system} result: {line}")
        trial, count, elapsed = map(int, fields[2:])
        if trial not in range(trials) or trial in times or count != iterations or elapsed <= 0:
            raise ValueError(f"unexpected {system} result: {line}")
        times[trial] = elapsed
    if len(times) != trials:
        raise ValueError(f"{system} reported {len(times)} of {trials} trials")
    return [times[trial] for trial in range(trials)]


def article_counts() -> dict[str, int]:
    rules = (
        "axiom", "absThm", "appThm", "assume", "betaConv",
        "deductAntisym", "eqMp", "refl", "subst", "sym", "trans",
    )
    lines = ARTICLE.read_text().splitlines()
    return {rule: lines.count(rule) for rule in rules}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("smoke", "standard"), default="standard")
    parser.add_argument("--systems", default="all")
    parser.add_argument("--trials", type=int)
    parser.add_argument("--iterations", type=int)
    parser.add_argument("--warmup", type=int)
    parser.add_argument("--hol-light-switch")
    parser.add_argument("--hol4-bin", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()

    systems = SYSTEMS if args.systems == "all" else tuple(args.systems.split(","))
    if not systems or len(systems) != len(set(systems)) or any(s not in SYSTEMS for s in systems):
        parser.error(f"--systems must select from {', '.join(SYSTEMS)}, or all")
    if "hol4" in systems and args.hol4_bin is None:
        parser.error("--hol4-bin is required when HOL4 is selected")
    defaults = (1, 1, 1) if args.profile == "smoke" else (7, 16, 1)
    trials = defaults[0] if args.trials is None else args.trials
    iterations = defaults[1] if args.iterations is None else args.iterations
    warmup = defaults[2] if args.warmup is None else args.warmup
    if min(trials, iterations, warmup, args.timeout) <= 0:
        parser.error("trials, iterations, warmup, and timeout must be positive")
    if not ARTICLE.is_file():
        raise RuntimeError(f"proof certificate not found: {ARTICLE}")
    if common.digest(ARTICLE) != ARTICLE_SHA256:
        raise ValueError("LIST_NOT_NIL article differs from the recorded proof")

    common.BUILD.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(
        LIST_NOT_NIL_ITERATIONS=str(iterations),
        LIST_NOT_NIL_TRIALS=str(trials),
        LIST_NOT_NIL_WARMUP=str(warmup),
        LIST_NOT_NIL_ARTICLE=str(ARTICLE),
    )
    results = []
    for system in systems:
        print(f"Running {system} certificate import...", file=sys.stderr, flush=True)
        if system == "hotaru":
            common.execute([
                "cargo", "build", "--release", "--locked", "--package", "hotaru",
                "--example", "list_not_nil_replay",
            ], timeout=args.timeout)
            binary = common.ROOT / "target" / "release" / "examples" / "list_not_nil_replay"
            lean_library = (common.ROOT / "HotaruKernel" / ".lake" / "build" / "lib"
                            / ("libhotaru_lean.dylib" if sys.platform == "darwin"
                               else "libhotaru_lean.so"))
            output = common.execute([str(binary), str(ARTICLE)], env=env, timeout=args.timeout)
            implementation = {
                "binary_sha256": common.digest(binary),
                "lean_library_sha256": common.digest(lean_library),
                "revision": common.execute(["git", "rev-parse", "HEAD"]).strip(),
                "rustc": common.execute(["rustc", "--version"]).strip(),
                "lean": common.execute(["lean", "--version"], cwd=common.ROOT / "HotaruKernel").strip(),
            }
        elif system == "hol-light":
            prefix = (["opam", "exec", f"--switch={args.hol_light_switch}", "--"]
                      if args.hol_light_switch else [])
            package = Path(common.execute(prefix + ["ocamlfind", "query", "hol_light"]).strip())
            preprocessor = f"camlp5o {shlex.quote(str(package / 'pa_j.cmo'))}"
            binary = common.BUILD / "hol_light_replay"
            source = common.BUILD / "hol_light_replay.ml"
            shutil.copyfile(common.SOURCE / "hol_light_replay.ml", source)
            common.execute(prefix + [
                "ocamlfind", "ocamlopt", "-package", "hol_light,unix", "-linkpkg",
                "-pp", preprocessor, "-o", str(binary), str(source),
            ], timeout=args.timeout)
            output = common.execute([str(binary), str(ARTICLE)], env=env, timeout=args.timeout)
            implementation = {
                "binary_sha256": common.digest(binary),
                "package_version": common.execute(prefix + [
                    "ocamlfind", "query", "-format", "%v", "hol_light",
                ]).strip(),
                "library_sha256": common.digest(package / "hol_lib.a"),
            }
        else:
            binary = args.hol4_bin.resolve()
            if not binary.is_file():
                parser.error(f"HOL4 executable does not exist: {binary}")
            reader_source = binary.parent.parent / "src" / "opentheory" / "reader" / "OpenTheoryReader.sml"
            reader = common.BUILD / "ListNotNilReader.sml"
            common.execute([
                sys.executable, str(common.SOURCE / "prepare_hol4_reader.py"),
                "--hol4-root", str(binary.parent.parent), "--output", str(reader),
            ], timeout=args.timeout)
            env["LIST_NOT_NIL_HOL4_READER"] = str(reader)
            output = common.execute(
                [str(binary)], cwd=binary.parent.parent, env=env,
                input_text=(common.SOURCE / "hol4_replay.sml").read_text(),
                timeout=args.timeout,
            )
            implementation = common.hol4_metadata(binary)
            implementation["reader_source_sha256"] = common.digest(reader_source)
            implementation["reader_adapter_sha256"] = common.digest(reader)
        elapsed = parse(output, system, trials, iterations)
        per_import = [n / iterations for n in elapsed]
        results.append({
            "system": system,
            "implementation": implementation,
            "elapsed_ns": elapsed,
            "median_ns_per_import": statistics.median(per_import),
            "min_ns_per_import": min(per_import),
            "max_ns_per_import": max(per_import),
        })

    now = datetime.now(timezone.utc)
    sources = [common.SOURCE / "run_replay.py", common.SOURCE / "list_not_nil.art"]
    sources += [
        common.SOURCE / name for name in
        ("hol_light_replay.ml", "hol4_replay.sml", "prepare_hol4_reader.py")
    ]
    sources.append(common.ROOT / "hotaru" / "examples" / "list_not_nil_replay.rs")
    sources += [
        common.ROOT / name for name in (
            "HotaruKernel/HotaruKernel/Equality.lean",
            "HotaruKernel/HotaruKernel/Kernel.lean",
            "HotaruKernel/HotaruKernelFFI.lean",
            "hotaru/src/lib.rs",
            "hotaru/src/syntax.rs",
            "hotaru-kernel-bridge/src/raw/exports.rs",
        )
    ]
    document = {
        "schema_version": 1,
        "mode": "certificate-import",
        "created_at_utc": now.isoformat(),
        "host": {"platform": platform.platform(), "machine": platform.machine()},
        "profile": args.profile,
        "trials": trials,
        "iterations_per_trial": iterations,
        "warmup_iterations": warmup,
        "article_inference_counts": article_counts(),
        "source_sha256": {str(path.relative_to(common.ROOT)): common.digest(path) for path in sources},
        "results": results,
    }
    path = args.output or common.BUILD / f"replay-{now:%Y%m%dT%H%M%SZ}.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(document, indent=2) + "\n")
    print("| System | Median per import | Range |")
    print("| --- | ---: | ---: |")
    for result in results:
        median = result["median_ns_per_import"] / 1e6
        low = result["min_ns_per_import"] / 1e6
        high = result["max_ns_per_import"] / 1e6
        print(f"| {result['system']} | {median:.3f} ms | {low:.3f}-{high:.3f} ms |")
    print(f"Raw results: {path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, ValueError) as error:
        print(f"benchmark failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
