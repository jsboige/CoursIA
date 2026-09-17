#!/usr/bin/env python3
"""Vérifie la reproduction pinée d'Euler et de Navier–Stokes.

Le checkout, les journaux complets et les rapports d'audit restent hors Git. La
commande ``check`` émet uniquement un agrégat falsifiable : identité du dépôt,
empreintes des challenges, verdicts Comparator, noyaux, axiomes et postcondition
d'orphelins.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from typing import Any

PINNED_SHA = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
NANODA_LIB_SHA = "68d5ca9db226849b41a6fff59d796ff19d0a8840"
DEPENDENCY_PINS = {
    "Comparator": "19e111e2141cf333c7daff0f64c5f24acc91dd2e",
    "mathlib": "85e3a25e006c35636f0e53b0e9296caca2685bc0",
    "lean4export": "cacf989bd75f608700820f6afc595f32e7a99a4d",
}
PERMITTED_AXIOMS = ("Classical.choice", "Quot.sound", "propext")
PROJECT_DIR = "nse-15400"
AUDIT_DIR = "nse-15400-audit"
NANODA_DIR = "nanoda_lib"
LANDRUN_RELATIVE = "bin/landrun"
LANDRUN_VERSION = "landrun version 0.1.17"
EXPECTED_TRACKED_LEAN_FILES = 2486
EXPECTED_CHALLENGE_SORRIES = {
    (
        "ComparatorChallenges/Euler.lean",
        "euler_breakdown_R3",
        1,
    ),
    (
        "ComparatorChallenges/Euler.lean",
        "exists_compact_smooth_euler_singularity",
        1,
    ),
    (
        "ComparatorChallenges/NavierStokes.lean",
        "navier_stokes_breakdown_R3",
        1,
    ),
    (
        "ComparatorChallenges/NavierStokes.lean",
        "navier_stokes_breakdown_periodic",
        1,
    ),
}
EXPECTED_AXIOM_DECLARATIONS = (
    "Euler.euler_breakdown_R3",
    "Euler.exists_compact_smooth_euler_singularity",
    "EulerPacketInduction.exists_compact_smooth_euler_singularity",
    "EulerOrdinarySobolev.FiniteLifespan.vorticityIntegral_unbounded",
    "EulerOrdinarySobolev.logarithmic_gradient_bound_solenoidal",
    "NavierStokes.Comparator.navier_stokes_breakdown_R3",
    "NavierStokes.Comparator.navier_stokes_breakdown_periodic",
    "NavierStokes.ComparatorBridge.option_C_of_compact_candidate",
    "NavierStokes.ComparatorBridge.option_D_of_candidate",
    "NavierStokes.ComparatorBridge.compact_candidate_excludes_global_solution",
    "NavierStokes.MaximalLifespan.candidate_excludes_global_solution",
)
EXPECTED_INTEGRITY_SCANNER = "scripts/lean/count_code_sorry.py:scan_file"

CHALLENGES = {
    "euler": {
        "json": "ComparatorChallenges/Euler.json",
        "expected_sha256": (
            "56bc185a931f68d9a0f0265a3c00cb12771dccc85384eaf6546b37844b8adc84"
        ),
    },
    "navier_stokes": {
        "artifact": "navier-stokes",
        "json": "ComparatorChallenges/NavierStokes.json",
        "expected_sha256": (
            "7610ecead7b390d80ff7f4229a3ff8f18d630e046f7ad1de4f92c7e8e76845b8"
        ),
    },
}

SUCCESS_MARKERS = {
    "nanoda": "nanoda kernel accepts the solution",
    "lean_kernel": "Lean default kernel accepts the solution",
    "verdict": "Your solution is okay!",
}
REJECTION_RE = re.compile(
    r"rejected the solution|uncaught exception|permission denied|\berror:",
    re.IGNORECASE,
)
AXIOM_RE = re.compile(r"depends on axioms:\s*\[([^]]*)\]", re.MULTILINE)
AXIOM_DECL_RE = re.compile(
    r"'([^']+)'\s+depends on axioms:\s*\[([^]]*)\]", re.MULTILINE
)


@dataclass(frozen=True)
class WslReader:
    """Lecture bornée d'artefacts dans le checkout WSL ext4."""

    timeout: int = 120

    def run(self, command: str) -> str:
        proc = subprocess.run(
            ["wsl", "-e", "bash", "-lc", command],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=self.timeout,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(
                f"Commande WSL en échec (rc={proc.returncode}): {proc.stderr.strip()}"
            )
        return proc.stdout

    def home_path(self, relative: str) -> str:
        """Résout un chemin relatif au home WSL sans exposer son propriétaire."""
        return self.run(f"realpath -- \"$HOME/{relative}\"").strip()

    def read(self, relative: str) -> str:
        return self.run(f"cat -- \"$HOME/{relative}\"")

    def sha256(self, relative: str) -> str:
        return self.run(f"sha256sum -- \"$HOME/{relative}\"").split()[0]


def parse_confinement_record(version: str, probe: str) -> dict[str, Any]:
    """Valide l'identité de landrun et un probe fonctionnel refus/autorisation."""
    version = version.strip()
    functional_probe = probe.strip() == "denied=true allowed=true"
    return {
        "engine": "landrun",
        "version": version,
        "version_matches": version == LANDRUN_VERSION,
        "unauthorized_write_denied": functional_probe,
        "authorized_write_allowed": functional_probe,
        "verified": version == LANDRUN_VERSION and functional_probe,
    }


def probe_confinement(reader: WslReader) -> dict[str, Any]:
    """Observe le binaire landrun et exerce une politique minimale réelle."""
    landrun = reader.home_path(LANDRUN_RELATIVE)
    version = reader.run(f"{landrun!r} --version")
    command = (
        "set -euo pipefail; "
        "allowed=$(mktemp -d /tmp/nse-landlock-probe.XXXXXX); "
        'denied="$HOME/.nse-landlock-probe-denied"; '
        "trap 'rm -rf \"$allowed\" \"$denied\"' EXIT; "
        "set +e; "
        f"{landrun!r} --best-effort --ro / --rw \"$allowed\" --ldd "
        "--add-exec -- bash -c "
        "'if : > \"$1\" 2>/dev/null; then exit 10; fi; "
        ": > \"$2/allowed\"' bash \"$denied\" \"$allowed\"; "
        "rc=$?; set -e; test \"$rc\" -eq 0; "
        "test -f \"$allowed/allowed\"; test ! -e \"$denied\"; "
        "printf 'denied=true allowed=true\\n'"
    )
    return parse_confinement_record(version, reader.run(command))


def parse_axioms(text: str) -> list[list[str]]:
    """Extrait les listes d'axiomes imprimées par Lean."""
    return [
        sorted(item.strip() for item in match.split(",") if item.strip())
        for match in AXIOM_RE.findall(text)
    ]


def parse_axiom_declarations(text: str) -> dict[str, list[str]]:
    """Associe chaque déclaration sondée à sa fermeture axiomatique."""
    matches = AXIOM_DECL_RE.findall(text)
    declarations = {
        declaration: sorted(
            item.strip() for item in axioms.split(",") if item.strip()
        )
        for declaration, axioms in matches
    }
    return declarations if len(matches) == len(declarations) else {}


def axiom_evidence_verified(axioms: dict[str, list[str]]) -> bool:
    """Exige les onze cibles exactes et leur liste blanche complète."""
    return set(axioms) == set(EXPECTED_AXIOM_DECLARATIONS) and all(
        values == sorted(PERMITTED_AXIOMS) for values in axioms.values()
    )


def parse_integrity_record(
    evidence: dict[str, Any], *, expected_sha: str
) -> dict[str, Any]:
    """Valide le recensement externe des sources Lean suivies par Git."""
    solution_sorries = evidence.get("solution_sorry_locations")
    native_decide_locations = evidence.get("native_decide_locations")
    challenge_sorries = evidence.get("challenge_sorry_locations")
    challenge_sorry_count = (
        sum(
            item.get("count", 0)
            for item in challenge_sorries
            if isinstance(item, dict)
        )
        if isinstance(challenge_sorries, list)
        else None
    )
    challenge_signature = (
        {
            (item.get("file"), item.get("declaration"), item.get("count"))
            for item in challenge_sorries
            if isinstance(item, dict)
        }
        if isinstance(challenge_sorries, list)
        else set()
    )
    complete = (
        evidence.get("schema_version") == 1
        and evidence.get("scanner") == EXPECTED_INTEGRITY_SCANNER
        and evidence.get("tracked_lean_files") == EXPECTED_TRACKED_LEAN_FILES
        and isinstance(challenge_sorries, list)
        and len(challenge_sorries) == len(EXPECTED_CHALLENGE_SORRIES)
        and challenge_signature == EXPECTED_CHALLENGE_SORRIES
        and isinstance(solution_sorries, list)
        and isinstance(native_decide_locations, list)
    )
    sorry_count = evidence.get("solution_sorry_proof_count")
    native_decide_count = evidence.get("native_decide_count")
    verified = (
        complete
        and evidence.get("root_sha") == expected_sha
        and sorry_count == 0
        and native_decide_count == 0
        and solution_sorries == []
        and native_decide_locations == []
    )
    return {
        "scanner": evidence.get("scanner"),
        "tracked_lean_files": evidence.get("tracked_lean_files"),
        "root_sha": evidence.get("root_sha"),
        "root_sha_matches": evidence.get("root_sha") == expected_sha,
        "challenge_sorry_proof_count": challenge_sorry_count,
        "challenge_sorry_locations": sorted(
            challenge_sorries,
            key=lambda item: (item["file"], item["declaration"]),
        )
        if complete
        else [],
        "solution_sorry_proof_count": sorry_count,
        "native_decide_count": native_decide_count,
        "complete": complete,
        "verified": verified,
    }


def parse_comparator_record(
    *,
    organ: dict[str, Any],
    stdout: str,
    stderr: str,
    challenge_sha256: str,
    expected_sha256: str,
    started_utc: str,
    ended_utc: str,
    stdout_sha256: str,
    stderr_sha256: str,
) -> dict[str, Any]:
    """Construit un verdict sans faire confiance au seul code parent."""
    kernels = {
        name: "accepts" if marker in stdout else "missing"
        for name, marker in SUCCESS_MARKERS.items()
        if name != "verdict"
    }
    semantic_verdict = (
        SUCCESS_MARKERS["verdict"]
        if SUCCESS_MARKERS["verdict"] in stdout
        else None
    )
    semantic_rejection = bool(REJECTION_RE.search(stdout) or REJECTION_RE.search(stderr))
    process_ok = (
        organ.get("status") == "ok"
        and organ.get("child_exit_code") == 0
        and organ.get("exit_code") == 0
        and organ.get("killed") is False
    )
    orphan_postcondition_ok = organ.get("orphans") == []
    semantic_ok = (
        kernels == {"nanoda": "accepts", "lean_kernel": "accepts"}
        and semantic_verdict == SUCCESS_MARKERS["verdict"]
        and not semantic_rejection
    )
    return {
        "challenge_sha256": challenge_sha256,
        "challenge_hash_matches": challenge_sha256 == expected_sha256,
        "started_utc": started_utc.strip(),
        "ended_utc": ended_utc.strip(),
        "duration_s": organ.get("duration_s"),
        "backend": organ.get("backend"),
        "status": organ.get("status"),
        "child_exit_code": organ.get("child_exit_code"),
        "exit_code": organ.get("exit_code"),
        "killed": organ.get("killed"),
        "orphans": organ.get("orphans"),
        "orphan_postcondition_ok": orphan_postcondition_ok,
        "stdout_sha256": stdout_sha256,
        "stderr_sha256": stderr_sha256,
        "kernels": kernels,
        "semantic_verdict": semantic_verdict,
        "semantic_rejection": semantic_rejection,
        "verified": (
            process_ok
            and orphan_postcondition_ok
            and semantic_ok
            and challenge_sha256 == expected_sha256
        ),
    }


def build_report(reader: WslReader) -> dict[str, Any]:
    """Lit les preuves externes et assemble le rapport des deux gates."""
    project_dir = reader.home_path(PROJECT_DIR)
    root_sha = reader.run(f"git -C {project_dir!r} rev-parse HEAD").strip()
    dependency_shas = {
        name: reader.run(
            f"git -C {project_dir!r}/.lake/packages/{name} rev-parse HEAD"
        ).strip()
        for name in DEPENDENCY_PINS
    }
    nanoda_dir = reader.home_path(NANODA_DIR)
    nanoda_sha = reader.run(f"git -C {nanoda_dir!r} rev-parse HEAD").strip()
    dependency_pins_match = (
        dependency_shas == DEPENDENCY_PINS and nanoda_sha == NANODA_LIB_SHA
    )
    toolchain = reader.read(f"{PROJECT_DIR}/lean-toolchain").strip()
    confinement = probe_confinement(reader)
    axiom_text = reader.read(f"{AUDIT_DIR}/axioms.stdout")
    axiom_lists = parse_axioms(axiom_text)
    axiom_declarations = parse_axiom_declarations(axiom_text)
    integrity = parse_integrity_record(
        json.loads(reader.read(f"{AUDIT_DIR}/integrity.json")),
        expected_sha=PINNED_SHA,
    )
    axioms_within_permitted = axiom_evidence_verified(axiom_declarations)
    forbidden_axioms = sorted(
        {
            axiom
            for values in axiom_lists
            for axiom in values
            if axiom not in PERMITTED_AXIOMS
        }
    )

    gates: dict[str, Any] = {}
    for name, config in CHALLENGES.items():
        artifact = config.get("artifact", name)
        prefix = f"{AUDIT_DIR}/{artifact}"
        stdout = reader.read(f"{prefix}.stdout")
        stderr = reader.read(f"{prefix}.stderr")
        organ = json.loads(reader.read(f"{prefix}.organ.json"))
        gates[name] = parse_comparator_record(
            organ=organ,
            stdout=stdout,
            stderr=stderr,
            challenge_sha256=reader.sha256(f"{PROJECT_DIR}/{config['json']}"),
            expected_sha256=config["expected_sha256"],
            started_utc=reader.read(f"{prefix}.started_utc"),
            ended_utc=reader.read(f"{prefix}.ended_utc"),
            stdout_sha256=reader.sha256(f"{prefix}.stdout"),
            stderr_sha256=reader.sha256(f"{prefix}.stderr"),
        )

    all_verified = (
        root_sha == PINNED_SHA
        and dependency_pins_match
        and toolchain == TOOLCHAIN
        and confinement["verified"]
        and axioms_within_permitted
        and not forbidden_axioms
        and integrity["verified"]
        and all(gate["verified"] for gate in gates.values())
    )
    return {
        "schema_version": 1,
        "pinned_sha": PINNED_SHA,
        "observed_sha": root_sha,
        "sha_matches_pin": root_sha == PINNED_SHA,
        "toolchain": toolchain,
        "toolchain_matches": toolchain == TOOLCHAIN,
        "confinement": confinement,
        "dependency_pins": DEPENDENCY_PINS,
        "observed_dependency_shas": dependency_shas,
        "nanoda_lib_sha": nanoda_sha,
        "dependency_pins_match": dependency_pins_match,
        "axiom_probe_count": len(axiom_declarations),
        "axiom_declarations": sorted(axiom_declarations),
        "permitted_axioms": list(PERMITTED_AXIOMS),
        "forbidden_axioms": forbidden_axioms,
        "axioms_within_permitted": axioms_within_permitted,
        "integrity": integrity,
        "sorry_proof_count": integrity["solution_sorry_proof_count"],
        "native_decide_count": integrity["native_decide_count"],
        "gates": gates,
        "all_verified": all_verified,
    }


def cmd_check() -> int:
    try:
        report = build_report(WslReader())
    except (RuntimeError, subprocess.TimeoutExpired, OSError, ValueError, json.JSONDecodeError) as exc:
        print(json.dumps({"all_verified": False, "error": str(exc)}, ensure_ascii=False))
        return 1
    print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0 if report["all_verified"] else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", choices=("check",))
    args = parser.parse_args(argv)
    if args.command == "check":
        return cmd_check()
    return 2


if __name__ == "__main__":
    sys.exit(main())
