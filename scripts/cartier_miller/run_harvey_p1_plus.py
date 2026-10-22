#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""Passe 2 Harvey C++ du P1+ ground truth 92 premiers (issue #19452).

Drives the upstream harvey_adapter binary (compiled from the vendored
sources at pin 37a9b727df: harvey_adapter.cpp + upstream/hypellfrob.cpp +
upstream/recurrences_ntl.cpp, NTL/GMP via MSYS2 UCRT64 per run_windows.py)
and cross-checks it against the independent Python recurrences vendored in
generate_p1_plus_truth.py (passe 1, PR #19523):

- all stopping indices L in [0, (p-1)//2] for each of the 92 primes in
  [7, 499]: Harvey (B, a, U) == prefix_values(p)[L] / original_values(p)[L]
  (upstream retained validation: 10,809 stopping-point queries);
- forced arbitrary-precision path (--force-big) on the quarter-point of
  every prime <= 199 (superset of the upstream 26 forced-big checks);
- invalid inputs (composite modulus, L out of range, zero repetitions),
  each expected to fail closed;
- --version metadata (NTL version, compiler, threads).

Fail-closed: any mismatch or subprocess error => status != passed, exit 1.

Large-modulus checks (p ~ 1e8) are NOT re-run here: the Python reference
(original_values/prefix_values) costs ~1 min per prime at that size and
they are already delivered by PR #19510 (P1 integration, 7 paper primes).
"""

import argparse
import hashlib
import json
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate_p1_plus_truth import (  # noqa: E402 (vendored upstream, pin 37a9b72)
    list_92,
    original_values,
    prefix_values,
)

REPO_ROOT = Path(__file__).resolve().parents[2]


class HarveyWorker:
    """Persistent harvey_adapter process, one query per stdin line."""

    def __init__(self, executable: Path, force_big: bool = False):
        cmd = [str(executable)] + (["--force-big"] if force_big else [])
        self.process = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
        )

    def query(self, p: int, L: int, reps: int = 1) -> dict:
        assert self.process.stdin and self.process.stdout
        self.process.stdin.write(f"{p} {L} {reps}\n")
        self.process.stdin.flush()
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError(f"harvey_adapter died: {self.process.stderr.read()}")
        return json.loads(line)

    def close(self) -> None:
        if self.process.stdin:
            self.process.stdin.close()
        self.process.wait(timeout=30)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_prime_stopping_indices(worker: HarveyWorker, p: int) -> tuple[int, int]:
    """All L in [0, (p-1)//2]: Harvey vs independent Python recurrences.

    Returns (stopping_indices_checked, mismatches).
    """
    prefix = prefix_values(p)
    original = original_values(p)
    mismatches = 0
    for L in range((p - 1) // 2 + 1):
        row = worker.query(p, L)
        ref = prefix[L]
        if row["B"] != ref["B"] or row["a"] != ref["a"] or row["U"] != original[L]:
            mismatches += 1
    return (p - 1) // 2 + 1, mismatches


def expect_failure(executable: Path, p: int, L: int, reps: int) -> bool:
    """One invalid-input query on a fresh process: True iff it failed closed."""
    proc = subprocess.run(
        [str(executable)],
        input=f"{p} {L} {reps}\n",
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=60,
    )
    return proc.returncode != 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--executable",
        type=Path,
        default=Path(__file__).resolve().parent / "bin" / "harvey_adapter.exe",
        help="path to the compiled harvey_adapter binary",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "example_results" / "p1_plus_harvey_validation.json",
        help="output JSON path (upstream-comparable format)",
    )
    parser.add_argument(
        "--forced-big-max-p",
        type=int,
        default=199,
        help="quarter-points of primes <= this value re-checked with --force-big",
    )
    args = parser.parse_args()

    if not args.executable.is_file():
        print(f"harvey_adapter not found: {args.executable}", file=sys.stderr)
        return 2

    primes = list_92()
    report = {
        "utc_started": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        "executable": str(args.executable),
        "executable_sha256": sha256_file(args.executable),
    }

    version = json.loads(
        subprocess.check_output(
            [str(args.executable), "--version"],
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=30,
        )
    )
    report["harvey_version"] = version

    stopping_total = 0
    mismatch_total = 0
    per_prime = []
    worker = HarveyWorker(args.executable)
    try:
        for p in primes:
            checked, mismatches = check_prime_stopping_indices(worker, p)
            stopping_total += checked
            mismatch_total += mismatches
            per_prime.append({"p": p, "stopping_indices": checked, "mismatches": mismatches})
    finally:
        worker.close()

    forced_big_checks = 0
    forced_big_mismatches = 0
    forced = HarveyWorker(args.executable, force_big=True)
    try:
        for p in [q for q in primes if q <= args.forced_big_max_p]:
            L = (p - 1) // 4
            row = forced.query(p, L)
            ref = prefix_values(p)[L]
            forced_big_checks += 1
            if (
                row["B"] != ref["B"]
                or row["a"] != ref["a"]
                or row["U"] != original_values(p)[L]
                or row["backend"] != "ZZ_p_forced"
            ):
                forced_big_mismatches += 1
    finally:
        forced.close()

    invalid_input_checks = sum(
        [
            expect_failure(args.executable, 4, 0, 1),  # composite modulus
            expect_failure(args.executable, 7, 4, 1),  # L > (p-1)/2
            expect_failure(args.executable, 7, 0, 0),  # reps < 1
        ]
    )

    validation = {
        "all_stopping_indices": stopping_total,
        "stopping_index_mismatches": mismatch_total,
        "primes_all_indices": len(primes),
        "forced_big_cross_checks": forced_big_checks,
        "forced_big_mismatches": forced_big_mismatches,
        "invalid_input_checks": invalid_input_checks,
        "status": "passed"
        if (
            mismatch_total == 0
            and forced_big_mismatches == 0
            and stopping_total == 10809
            and invalid_input_checks == 3
        )
        else "failed",
    }
    report["validation"] = validation
    report["per_prime"] = per_prime

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"# wrote {args.out}")
    print(json.dumps(validation, indent=2))
    return 0 if validation["status"] == "passed" else 1


if __name__ == "__main__":
    sys.exit(main())
