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
import os
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


PIN_MANIFEST = Path(__file__).resolve().parent / "harvey_sources_pin.json"

# Sous-arborescences possibles du clone local des sources amont :
# <clone>/ et <clone>/Cartier_Miller_Benchmark/.
SOURCE_ROOT_CANDIDATES = ("", "Cartier_Miller_Benchmark")

# Code de sortie propre a la garde du pin : distinct de 2 (executable absent),
# pour que l'ordre des deux controles soit observable dans le rc seul.
PIN_FAILURE_EXIT = 3


def sha256_source(path: Path) -> str:
    """SHA-256 canonique d'une source : fins de ligne normalisees en LF.

    Le pin doit etre independant de core.autocrlf : sur un clone Windows, le
    fichier de travail porte CRLF alors que le blob Git porte LF. On normalise
    donc avant de hacher, et le manifeste documente les deux formes.
    """
    data = path.read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def load_pin_manifest(path: Path) -> dict:
    """Charge le manifeste de pin ; son absence est une erreur (fail-closed)."""
    if not path.is_file():
        raise FileNotFoundError(f"manifeste de pin introuvable : {path}")
    manifest = json.loads(path.read_text(encoding="utf-8"))
    if not manifest.get("files"):
        raise ValueError(f"manifeste de pin sans fichier : {path}")
    return manifest


def resolve_sources_root(explicit: Path | None, executable: Path) -> Path | None:
    """Racine du clone des sources : option, variable d'env, puis auto-decouverte."""
    if explicit is not None:
        return explicit
    env = os.environ.get("HARVEY_SOURCES_ROOT")
    if env:
        return Path(env)
    bases = [Path.cwd(), executable.resolve().parent, executable.resolve().parent.parent]
    for base in bases:
        for suffix in SOURCE_ROOT_CANDIDATES:
            candidate = base / suffix if suffix else base
            if (candidate / "harvey_adapter.cpp").is_file() and (
                candidate / "upstream" / "recurrences_ntl.cpp"
            ).is_file():
                return candidate
    return None


def verify_sources(root: Path, manifest: dict) -> dict:
    """Recalcule les empreintes des sources vendorisees ; echoue au premier ecart.

    Retourne le rapport ; ``verified`` est False des qu'un fichier manque ou
    differe du pin. Les sources ne sont jamais reecrites.
    """
    measured = {}
    problems = []
    for entry in manifest["files"]:
        path = root / entry["path"]
        if not path.is_file():
            problems.append(
                {"path": entry["path"], "reason": "absent", "expected_sha256": entry["sha256"]}
            )
            continue
        digest = sha256_source(path)
        measured[entry["path"]] = digest
        if digest != entry["sha256"]:
            problems.append(
                {
                    "path": entry["path"],
                    "reason": "sha256",
                    "expected_sha256": entry["sha256"],
                    "measured_sha256": digest,
                }
            )
    return {
        "verified": not problems,
        "measured_sha256": measured,
        "problems": problems,
        "commit": manifest.get("commit"),
    }


def pin_allows_passed(sources_report: dict | None) -> bool:
    """Une validation ne peut etre 'passed' que si le pin a ete verifie.

    Le mode debug (--no-verify-sources) rend ``sources_report`` a None : il
    court-circuite la garde, il ne dispense jamais du statut.
    """
    return bool(sources_report and sources_report.get("verified"))


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
    parser.add_argument(
        "--pin-manifest",
        type=Path,
        default=PIN_MANIFEST,
        help="manifeste de pin des sources vendorisees (sha256 canonique par fichier)",
    )
    parser.add_argument(
        "--sources-root",
        type=Path,
        default=None,
        help="racine du clone des sources amont ; par defaut HARVEY_SOURCES_ROOT ou auto-decouverte",
    )
    parser.add_argument(
        "--no-verify-sources",
        action="store_true",
        help=(
            "desactive le controle du pin (debug uniquement) : le rapport portera alors "
            "sources_pin.skipped=true et la validation ne pourra pas etre 'passed'"
        ),
    )
    args = parser.parse_args()

    # Garde de pin : fail-closed, AVANT tout lancement du binaire et toute requete.
    sources_report = None
    if not args.no_verify_sources:
        try:
            manifest = load_pin_manifest(args.pin_manifest)
        except (FileNotFoundError, ValueError, json.JSONDecodeError) as exc:
            print(f"pin des sources : {exc}", file=sys.stderr)
            return PIN_FAILURE_EXIT
        root = resolve_sources_root(args.sources_root, args.executable)
        if root is None:
            print(
                "pin des sources : racine introuvable ; passe --sources-root <racine du clone> "
                "ou pose HARVEY_SOURCES_ROOT",
                file=sys.stderr,
            )
            return PIN_FAILURE_EXIT
        sources_report = verify_sources(root, manifest)
        if not sources_report["verified"]:
            print(
                "pin des sources : ecart avec le commit "
                f"{manifest.get('commit')} ({manifest.get('commit_short')}) ; aucun appel au binaire",
                file=sys.stderr,
            )
            for problem in sources_report["problems"]:
                print(f"  - {problem}", file=sys.stderr)
            return PIN_FAILURE_EXIT

    if not args.executable.is_file():
        print(f"harvey_adapter not found: {args.executable}", file=sys.stderr)
        return 2

    primes = list_92()
    report = {
        "utc_started": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(),
        "python": platform.python_version(),
        # Identite portable : le nom du binaire, jamais le chemin du poste qui a
        # produit le resultat. L'empreinte ci-dessous est la provenance verifiable.
        "executable": args.executable.name,
        "executable_sha256": sha256_file(args.executable),
        "sources_pin": {
            "manifest": args.pin_manifest.name,
            "commit": sources_report["commit"] if sources_report else None,
            "verified": bool(sources_report and sources_report["verified"]),
            "measured_sha256": sources_report["measured_sha256"] if sources_report else {},
            "skipped": bool(args.no_verify_sources),
        },
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
        "sources_pin_verified": bool(sources_report and sources_report["verified"]),
        "status": "passed"
        if (
            mismatch_total == 0
            and forced_big_mismatches == 0
            and stopping_total == 10809
            and invalid_input_checks == 3
            and pin_allows_passed(sources_report)
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
