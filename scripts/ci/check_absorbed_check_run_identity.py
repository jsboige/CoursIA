#!/usr/bin/env python3
"""Positif-control d'identite byte-a-byte des gardes absorbes (#12396).

Le moteur fast lane emet un check-run nomme `guard.name`. Un garde absorbe
porte donc un nom qui DOIT etre byte-identique au nom de check-run que son
workflow source rendait. Le nom rendu suit la MEME convention que
`check_unique_check_run_names.py` (defect #11869) : `job.name` si declare,
sinon la cle du job. Sans cette identite, le rename casse la protection de
branche : le check requis porte l'ancien nom, et l'emission sous un nom
different ne le satisfait pas plus qu'elle ne le rougit (incident #12175).

Les tranches 1/2/3 ont absorbe des gardes par DECLARATION ; aucune emission
ni aucun test n'a cimente l'identite nom-du-garde == nom-rendu. Ce module
ferme ce trou : pour chaque garde absorbe du registre, il parse le workflow
source et exige que `guard.name` figure byte-identique parmi les noms de job
rendus.

Modes:
  --check  exit 0 si tous identiques ; 1 si un nom diverge ou un workflow
           source est introuvable ; 2 si l'instrument est casse (PyYAML
           indisponible, workflow illisible).
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parent
ROOT = CI_DIR.parents[1]
sys.path.insert(0, str(CI_DIR))

import fast_lane_registry as reg  # noqa: E402
from check_unique_check_run_names import _parse_workflow, _load_yaml  # noqa: E402

EXIT_OK, EXIT_MISMATCH, EXIT_BROKEN = 0, 1, 2
WORKFLOWS_DIR = ROOT / ".github" / "workflows"


def absorbed_guards():
    """Tous les gardes absorbes du registre, tranches 1/2/4 + 3 si merge."""
    for tranche_name in ("TRANCHE1", "TRANCHE2", "TRANCHE3", "TRANCHE4", "TRANCHE5"):
        yield from getattr(reg, tranche_name, [])


def rendered_job_names(workflow_file: Path, yaml) -> list[str] | None:
    """Noms de check-run que le workflow rendait (None = illisible).

    Meme logique que collect_rendered_names de check_unique_check_run_names :
    `job.name` si declare, sinon la cle du job. Les jobs reutilisables
    (`uses:`) sont sautes -- leur nom depend du callee apres templating.
    """
    try:
        text = workflow_file.read_text(encoding="utf-8")
    except OSError:
        return None
    data = _parse_workflow(text, yaml)
    if data is None:
        return None
    names: list[str] = []
    for job_key, job_def in (data.get("jobs") or {}).items():
        if not isinstance(job_def, dict) or "uses" in job_def:
            continue
        names.append(str(job_def.get("name") or job_key))
    return names


def mismatches() -> list[str]:
    """Descriptions des gardes absorbes dont le nom diverge de la source."""
    yaml = _load_yaml()
    if yaml is None:
        return ["PyYAML indisponible"]  # instrument casse
    out: list[str] = []
    for guard in absorbed_guards():
        source = WORKFLOWS_DIR / guard.source
        if not source.is_file():
            out.append(f"{guard.name!r}: workflow source introuvable "
                       f"({guard.source})")
            continue
        names = rendered_job_names(source, yaml)
        if names is None:
            out.append(f"{guard.name!r}: source illisible ({guard.source})")
        elif guard.name not in names:
            out.append(f"{guard.name!r} != noms rendus par "
                       f"{guard.source} {sorted(names)}")
    return out


def _main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Byte-identity des gardes fast-lane absorbes."
    )
    parser.add_argument("--check", action="store_true",
                        help="exit 0/1/2 par identite")
    args = parser.parse_args(argv[1:])

    problems = mismatches()
    if not problems:
        print(f"[absorbed-identity] OK -- {len(list(absorbed_guards()))} "
              "gardes absorbes byte-identiques a leur source.")
        return EXIT_OK
    for problem in problems:
        print(f"[absorbed-identity] MISMATCH: {problem}")
    if not args.check:
        return EXIT_OK
    # Une liste peuplant "PyYAML indisponible" = instrument casse, pas une
    # divergence de nom.
    if problems == ["PyYAML indisponible"]:
        print("[absorbed-identity] BROKEN INSTRUMENT: PyYAML absent. "
              "Verdict nul.", file=sys.stderr)
        return EXIT_BROKEN
    return EXIT_MISMATCH


if __name__ == "__main__":
    sys.exit(_main(sys.argv))