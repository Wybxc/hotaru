#!/usr/bin/env python3
"""Measure native LIST_NOT_NIL proofs in HOL Light and HOL4."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import shlex
import shutil
import statistics
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SOURCE = Path(__file__).resolve().parent
BUILD = ROOT / "target" / "benchmarks" / "list_not_nil"
SYSTEMS = ("hol-light", "hol4")
MARKER = "LIST_NOT_NIL_BENCH\t"


def execute(
    command: list[str], *, cwd: Path = ROOT, env: dict[str, str] | None = None,
    input_text: str | None = None, timeout: int = 600,
) -> str:
    try:
        result = subprocess.run(
            command, cwd=cwd, env=env, input=input_text, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"failed to run {command[0]}: {error}") from error
    if result.returncode != 0:
        raise RuntimeError(
            f"{' '.join(command)} failed:\n"
            + "\n".join(result.stdout.splitlines()[-30:])
        )
    return result.stdout


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hol4_metadata(binary: Path) -> dict[str, str]:
    root = binary.parent.parent
    try:
        revision = execute(["git", "rev-parse", "HEAD"], cwd=root).strip()
    except RuntimeError:
        revision = "unavailable"
    metadata = {
        "executable": str(binary),
        "launcher_sha256": digest(binary),
        "revision": revision,
        "polyml": execute(["poly", "-v"]).strip(),
    }
    heapname = binary.parent / "heapname"
    if heapname.is_file():
        heap = Path(execute([str(heapname)], cwd=root).strip())
        if not heap.is_absolute():
            heap = root / heap
        metadata["heap_sha256"] = digest(heap)
    return metadata


def parse(output: str, system: str, trials: int, iterations: int) -> list[int]:
    times: dict[int, int] = {}
    for line in output.splitlines():
        offset = line.find(MARKER)
        if offset < 0:
            continue
        fields = line[offset:].split("\t")
        if len(fields) != 5 or fields[:2] != ["LIST_NOT_NIL_BENCH", system]:
            raise ValueError(f"malformed {system} result: {line}")
        trial, count, elapsed = map(int, fields[2:])
        if trial not in range(trials) or trial in times or count != iterations or elapsed <= 0:
            raise ValueError(f"unexpected {system} result: {line}")
        times[trial] = elapsed
    if len(times) != trials:
        raise ValueError(f"{system} reported {len(times)} of {trials} trials")
    return [times[trial] for trial in range(trials)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("smoke", "standard"), default="standard")
    parser.add_argument("--systems", default="hol-light,hol4")
    parser.add_argument("--trials", type=int)
    parser.add_argument("--iterations", type=int)
    parser.add_argument("--warmup", type=int)
    parser.add_argument("--hol-light-switch")
    parser.add_argument("--hol4-bin", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()

    systems = tuple(args.systems.split(","))
    if not systems or len(systems) != len(set(systems)) or any(s not in SYSTEMS for s in systems):
        parser.error(f"--systems must select from {', '.join(SYSTEMS)}")
    if "hol4" in systems and args.hol4_bin is None:
        parser.error("--hol4-bin is required when HOL4 is selected")
    defaults = (1, 4, 1) if args.profile == "smoke" else (7, 256, 4)
    trials = defaults[0] if args.trials is None else args.trials
    iterations = defaults[1] if args.iterations is None else args.iterations
    warmup = defaults[2] if args.warmup is None else args.warmup
    if min(trials, iterations, warmup, args.timeout) <= 0:
        parser.error("trials, iterations, warmup, and timeout must be positive")

    BUILD.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(
        LIST_NOT_NIL_ITERATIONS=str(iterations),
        LIST_NOT_NIL_TRIALS=str(trials),
        LIST_NOT_NIL_WARMUP=str(warmup),
    )
    results = []
    for system in systems:
        print(f"Running {system} native proof...", file=sys.stderr, flush=True)
        if system == "hol-light":
            prefix = (["opam", "exec", f"--switch={args.hol_light_switch}", "--"]
                      if args.hol_light_switch else [])
            package = Path(execute(prefix + ["ocamlfind", "query", "hol_light"]).strip())
            preprocessor = f"camlp5o {shlex.quote(str(package / 'pa_j.cmo'))}"
            binary = BUILD / "hol_light_native"
            source = BUILD / "hol_light_native.ml"
            shutil.copyfile(SOURCE / "hol_light.ml", source)
            execute(prefix + [
                "ocamlfind", "ocamlopt", "-package", "hol_light,unix", "-linkpkg",
                "-pp", preprocessor, "-o", str(binary), str(source),
            ], timeout=args.timeout)
            output = execute([str(binary)], env=env, timeout=args.timeout)
            implementation = {
                "package_directory": str(package),
                "package_version": execute(prefix + [
                    "ocamlfind", "query", "-format", "%v", "hol_light",
                ]).strip(),
                "ocaml": execute(prefix + ["ocamlc", "-version"]).strip(),
                "library_sha256": digest(package / "hol_lib.a"),
                "binary_sha256": digest(binary),
            }
        else:
            binary = args.hol4_bin.resolve()
            if not binary.is_file():
                parser.error(f"HOL4 executable does not exist: {binary}")
            output = execute(
                [str(binary)], cwd=binary.parent.parent, env=env,
                input_text=(SOURCE / "hol4.sml").read_text(), timeout=args.timeout,
            )
            counts = [
                int(line.split("\t")[-1]) for line in output.splitlines()
                if "LIST_NOT_NIL_INFERENCES\thol4\t" in line
            ]
            if len(counts) != 1 or counts[0] <= 25:
                raise ValueError(f"HOL4 inference count is missing or too small: {counts}")
            implementation = hol4_metadata(binary)
            implementation["inferences_per_proof"] = counts[0]
        elapsed = parse(output, system, trials, iterations)
        per_proof = [n / iterations for n in elapsed]
        results.append({
            "system": system,
            "implementation": implementation,
            "elapsed_ns": elapsed,
            "median_ns_per_proof": statistics.median(per_proof),
            "min_ns_per_proof": min(per_proof),
            "max_ns_per_proof": max(per_proof),
        })

    now = datetime.now(timezone.utc)
    document = {
        "schema_version": 1,
        "mode": "native-proof",
        "created_at_utc": now.isoformat(),
        "host": {"platform": platform.platform(), "machine": platform.machine()},
        "profile": args.profile,
        "trials": trials,
        "iterations_per_trial": iterations,
        "warmup_iterations": warmup,
        "source_sha256": {
            str(path.relative_to(ROOT)): digest(path)
            for path in (SOURCE / "run_native.py", SOURCE / "hol_light.ml", SOURCE / "hol4.sml")
        },
        "results": results,
    }
    path = args.output or BUILD / f"native-{now:%Y%m%dT%H%M%SZ}.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(document, indent=2) + "\n")
    print("| System | Median per proof | Range |")
    print("| --- | ---: | ---: |")
    for result in results:
        median = result["median_ns_per_proof"] / 1e6
        low = result["min_ns_per_proof"] / 1e6
        high = result["max_ns_per_proof"] / 1e6
        print(f"| {result['system']} | {median:.3f} ms | {low:.3f}-{high:.3f} ms |")
    print(f"Raw results: {path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, ValueError) as error:
        print(f"benchmark failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
