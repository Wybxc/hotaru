#!/usr/bin/env python3
"""Run the shared Hotaru, HOL Light, and HOL4 kernel workloads."""

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
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BENCHMARKS = ROOT / "benchmarks"
BUILD = ROOT / "target" / "benchmarks"
BATCH = 256
MARKER = "HOTARU_BENCH\t"
SYSTEMS = ("hotaru", "hol-light", "hol4")


@dataclass(frozen=True)
class Case:
    kind: str
    parameter: int
    iterations: int

    @property
    def label(self) -> str:
        return f"{self.kind}/{self.parameter}"


STANDARD_CASES = (
    Case("refl_reuse", 0, 131_072),
    Case("refl_reuse", 16, 131_072),
    Case("refl_reuse", 64, 131_072),
    Case("refl_reuse", 256, 131_072),
    Case("refl_checked", 0, 131_072),
    Case("refl_checked", 16, 131_072),
    Case("refl_checked", 64, 131_072),
    Case("refl_checked", 256, 131_072),
    Case("refl_retain", 0, 131_072),
    Case("refl_build", 16, 16_384),
    Case("refl_build", 64, 16_384),
    Case("refl_build", 256, 16_384),
    Case("assume", 0, 524_288),
    Case("eq_mp", 0, 524_288),
    Case("trans_hyps", 0, 65_536),
    Case("trans_hyps", 8, 65_536),
    Case("trans_hyps", 64, 65_536),
    Case("trace", 0, 131_072),
)


def command_output(
    command: list[str],
    *,
    cwd: Path = ROOT,
    env: dict[str, str] | None = None,
    input_text: str | None = None,
    timeout: int = 600,
) -> str:
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            env=env,
            input=input_text,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"failed to run {command[0]}: {error}") from error
    if result.returncode != 0:
        tail = "\n".join(result.stdout.splitlines()[-40:])
        raise RuntimeError(f"{' '.join(command)} failed:\n{tail}")
    return result.stdout


def version(command: list[str], *, cwd: Path = ROOT) -> str:
    return command_output(command, cwd=cwd).strip()


def git_revision(directory: Path) -> str:
    try:
        return version(["git", "rev-parse", "HEAD"], cwd=directory)
    except RuntimeError:
        return "unavailable"


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_systems(raw: str) -> tuple[str, ...]:
    selected = SYSTEMS if raw == "all" else tuple(raw.split(","))
    if not selected or len(selected) != len(set(selected)):
        raise ValueError("select each system at most once")
    if any(system not in SYSTEMS for system in selected):
        raise ValueError(f"systems must be comma-separated from {SYSTEMS}, or all")
    return selected


def parse_results(
    output: str, system: str, cases: tuple[Case, ...], trials: int
) -> list[dict[str, int | str]]:
    expected = {
        (case.kind, case.parameter, trial): case.iterations
        for case in cases
        for trial in range(trials)
    }
    seen: set[tuple[str, int, int]] = set()
    measurements = []
    for line in output.splitlines():
        offset = line.find(MARKER)
        if offset < 0:
            continue
        fields = line[offset:].split("\t")
        if len(fields) != 6 or fields[0] != "HOTARU_BENCH":
            raise ValueError(f"malformed benchmark output from {system}: {line}")
        try:
            _, kind, parameter, trial, iterations, elapsed_ns = fields
            parameter = int(parameter)
            trial = int(trial)
            iterations = int(iterations)
            elapsed_ns = int(elapsed_ns)
        except ValueError as error:
            raise ValueError(f"non-numeric benchmark output from {system}: {line}") from error
        key = kind, parameter, trial
        if key not in expected or key in seen or expected[key] != iterations:
            raise ValueError(f"unexpected or duplicate result from {system}: {line}")
        if elapsed_ns <= 0:
            raise ValueError(f"non-positive elapsed time from {system}: {line}")
        seen.add(key)
        measurements.append(
            {
                "system": system,
                "kind": kind,
                "parameter": parameter,
                "trial": trial,
                "iterations": iterations,
                "elapsed_ns": elapsed_ns,
            }
        )
    if seen != expected.keys():
        missing = sorted(expected.keys() - seen)
        raise ValueError(f"{system} omitted benchmark results: {missing}")
    return measurements


def summarize(
    measurements: list[dict[str, int | str]],
    cases: tuple[Case, ...],
    systems: tuple[str, ...],
) -> list[dict[str, float | int | str]]:
    summary = []
    for case in cases:
        for system in systems:
            values = [
                int(item["elapsed_ns"]) / case.iterations
                for item in measurements
                if item["system"] == system
                and item["kind"] == case.kind
                and item["parameter"] == case.parameter
            ]
            summary.append(
                {
                    "system": system,
                    "kind": case.kind,
                    "parameter": case.parameter,
                    "median_ns_per_iteration": statistics.median(values),
                    "min_ns_per_iteration": min(values),
                    "max_ns_per_iteration": max(values),
                }
            )
    return summary


def format_duration(nanoseconds: float) -> str:
    if nanoseconds < 1_000:
        return f"{nanoseconds:.1f} ns"
    if nanoseconds < 1_000_000:
        return f"{nanoseconds / 1_000:.2f} us"
    return f"{nanoseconds / 1_000_000:.2f} ms"


def print_summary(
    summary: list[dict[str, float | int | str]],
    cases: tuple[Case, ...],
    systems: tuple[str, ...],
) -> None:
    print("\nMedian time per transaction (startup and setup excluded)")
    print("| Workload | " + " | ".join(systems) + " |")
    print("| --- | " + " | ".join("---:" for _ in systems) + " |")
    for case in cases:
        values = []
        for system in systems:
            row = next(
                item
                for item in summary
                if item["system"] == system
                and item["kind"] == case.kind
                and item["parameter"] == case.parameter
            )
            values.append(format_duration(float(row["median_ns_per_iteration"])))
        print(f"| {case.label} | " + " | ".join(values) + " |")


def opam_prefix(switch: str | None) -> list[str]:
    return ["opam", "exec", f"--switch={switch}", "--"] if switch else []


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--systems", default="hotaru", help="comma-separated names or all")
    parser.add_argument("--profile", choices=("smoke", "standard"), default="standard")
    parser.add_argument("--trials", type=int, help="default: 1 for smoke, 7 for standard")
    parser.add_argument("--hol-light-switch", help="opam switch with hol_light and ocamlfind")
    parser.add_argument("--hol4-bin", type=Path, help="path to HOL4 bin/hol")
    parser.add_argument("--output", type=Path, help="JSON result path")
    parser.add_argument("--timeout", type=int, default=600, help="seconds per command")
    args = parser.parse_args()

    try:
        systems = parse_systems(args.systems)
    except ValueError as error:
        parser.error(str(error))
    if args.trials is not None and args.trials <= 0:
        parser.error("--trials must be positive")
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if "hol4" in systems and args.hol4_bin is None:
        parser.error("--hol4-bin is required for HOL4")

    trials = args.trials or (1 if args.profile == "smoke" else 7)
    warmup = BATCH if args.profile == "smoke" else 2_048
    cases = (
        tuple(Case(case.kind, case.parameter, BATCH) for case in STANDARD_CASES)
        if args.profile == "smoke"
        else STANDARD_CASES
    )
    spec = ";".join(
        f"{case.kind}:{case.parameter}:{case.iterations}" for case in cases
    )
    environment = os.environ.copy()
    environment.update(
        HOTARU_BENCH_SPEC=spec,
        HOTARU_BENCH_TRIALS=str(trials),
        HOTARU_BENCH_WARMUP=str(warmup),
    )
    BUILD.mkdir(parents=True, exist_ok=True)
    metadata: dict[str, dict[str, str]] = {}
    measurements: list[dict[str, int | str]] = []

    for system in systems:
        print(f"Running {system} ({args.profile})...", file=sys.stderr, flush=True)
        if system == "hotaru":
            command_output(
                [
                    "cargo", "build", "--release", "--locked", "--package",
                    "hotaru", "--example", "benchmark",
                ],
                timeout=args.timeout,
            )
            binary = ROOT / "target" / "release" / "examples" / "benchmark"
            lean_library = (ROOT / "HotaruKernel" / ".lake" / "build" / "lib"
                            / ("libhotaru_lean.dylib" if sys.platform == "darwin"
                               else "libhotaru_lean.so"))
            metadata[system] = {
                "revision": git_revision(ROOT),
                "rustc": version(["rustc", "--version"]),
                "lean": version(["lean", "--version"], cwd=ROOT / "HotaruKernel"),
                "binary_sha256": sha256_file(binary),
                "lean_library_sha256": sha256_file(lean_library),
            }
            output = command_output([str(binary)], env=environment, timeout=args.timeout)
        elif system == "hol-light":
            prefix = opam_prefix(args.hol_light_switch)
            package_dir = Path(
                version(prefix + ["ocamlfind", "query", "hol_light"])
            )
            preprocessor = f"camlp5o {shlex.quote(str(package_dir / 'pa_j.cmo'))}"
            binary = BUILD / "hol_light"
            source = BUILD / "hol_light.ml"
            shutil.copyfile(BENCHMARKS / "hol_light.ml", source)
            command_output(
                prefix + [
                    "ocamlfind", "ocamlopt", "-package", "hol_light,unix",
                    "-linkpkg", "-pp", preprocessor, "-o", str(binary),
                    str(source),
                ],
                timeout=args.timeout,
            )
            metadata[system] = {
                "package_version": version(
                    prefix + ["ocamlfind", "query", "-format", "%v", "hol_light"]
                ),
                "package_directory": str(package_dir),
                "ocaml": version(prefix + ["ocamlc", "-version"]),
                "library_sha256": sha256_file(package_dir / "hol_lib.a"),
                "binary_sha256": sha256_file(binary),
            }
            output = command_output([str(binary)], env=environment, timeout=args.timeout)
        else:
            binary = args.hol4_bin.resolve()
            if not binary.is_file():
                parser.error(f"HOL4 executable does not exist: {binary}")
            metadata[system] = {
                "revision": git_revision(binary.parent.parent),
                "polyml": version(["poly", "-v"]),
                "executable": str(binary),
                "launcher_sha256": sha256_file(binary),
            }
            heapname = binary.parent / "heapname"
            if heapname.is_file():
                heap = Path(version([str(heapname)], cwd=binary.parent.parent))
                if not heap.is_absolute():
                    heap = binary.parent.parent / heap
                metadata[system]["heap_sha256"] = sha256_file(heap)
            output = command_output(
                [str(binary)],
                cwd=binary.parent.parent,
                env=environment,
                input_text=(BENCHMARKS / "hol4.sml").read_text(),
                timeout=args.timeout,
            )
        measurements.extend(parse_results(output, system, cases, trials))

    summary = summarize(measurements, cases, systems)
    timestamp = datetime.now(timezone.utc)
    result = {
        "schema_version": 1,
        "created_at_utc": timestamp.isoformat(),
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "cpu_count": os.cpu_count(),
        },
        "benchmark": {
            "profile": args.profile,
            "batch_size": BATCH,
            "warmup_iterations": warmup,
            "trials": trials,
            "cases": [asdict(case) for case in cases],
        },
        "suite_sha256": {
            str(path.relative_to(ROOT)): sha256_file(path)
            for path in (
                BENCHMARKS / "run.py",
                BENCHMARKS / "hol_light.ml",
                BENCHMARKS / "hol4.sml",
                ROOT / "hotaru" / "examples" / "benchmark.rs",
            )
        },
        "implementations": metadata,
        "measurements": measurements,
        "summary": summary,
    }
    path = args.output or BUILD / f"results-{timestamp:%Y%m%dT%H%M%SZ}.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=2) + "\n")
    print_summary(summary, cases, systems)
    print(f"\nRaw results: {path}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, ValueError) as error:
        print(f"benchmark failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
