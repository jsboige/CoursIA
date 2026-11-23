"""Mesure du cout PAR ETAPE de `merge_ready.evaluate_pr` (#26799).

Le journal de la passe (`%LOCALAPPDATA%/CoursIA/merge_ready/journal.jsonl`)
porte une ligne par PR evaluee, horodatee : il dit QUELLE PR a ete refusee
et pourquoi, jamais ce que chaque etape a coute. Ce que le journal montre,
c'est le cout d'une PR -- 150 s pour une PR bloquee, 2 s pour une PR sans
approbation -- sans dire d'ou viennent ces 150 s.

Cet organe repond a la question manquante : il enveloppe chaque fonction
d'etape de `evaluate_pr` d'une horloge, appelle l'evaluation, et rend le
decoupage. Il ne MODIFIE rien et ne DECIDE rien : `evaluate_pr` ne merge
jamais (le merge est un geste du `run()`), donc l'organe est en lecture
seule -- il lit la vue de la PR et mesure.

Usage :

    python scripts/coordination/merge_ready_step_timing.py --pr 28166 28168
    python scripts/coordination/merge_ready_step_timing.py --pr 28166 --json

Le jeton est resolu comme dans `merge_ready` (`resolve_token`) : l'organe
tourne sous l'identite du coordinateur, qui est le seul a pouvoir lire ce
que l'organe de merge lit.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MERGE_READY_PATH = HERE / "merge_ready.py"

#: Les etapes horlogees. Une etape absente de cette liste n'est pas mesuree :
#: soit elle ne porte aucun cout significatif, soit son cout est celui du
#: runner (une lecture REST ou un `git`).
ETAPES = (
    "fetch_pr_files",
    "lean_build_attestation_reason",
    "coordinator_approval_reason",
    "run_nits",
    "twin_collision_reason",
    "slot_reservation_reason",
    "base_ref_liveness",
    "stacked_parent_state",
    "mergeable_state_and_head",
    "_combined_tree",
)


def charger_merge_ready():
    """Charge `merge_ready` comme module autonome (meme convention que les
    tests) : le module se trouve a cote de ce script, pas dans l'import
    path du depot."""
    spec = importlib.util.spec_from_file_location(
        "merge_ready_sous_mesure", MERGE_READY_PATH
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["merge_ready_sous_mesure"] = module
    spec.loader.exec_module(module)
    return module


def horloger(mr, nom: str, mesures: list[dict]) -> None:
    """Enveloppe une fonction d'etape du module : elle mesure son temps et
    l'ajoute aux mesures. L'originale est conservee."""
    original = getattr(mr, nom)

    def enveloppe(*args, **kwargs):
        debut = time.monotonic()
        try:
            return original(*args, **kwargs)
        finally:
            mesures.append({"etape": nom, "secondes": time.monotonic() - debut})

    setattr(mr, nom, enveloppe)


def mesurer(mr, pr: int, runner, gh_env: dict[str, str]) -> dict:
    """Evalue une PR et rend le decoupage par etape."""
    mesures: list[dict] = []
    for nom in ETAPES:
        horloger(mr, nom, mesures)
    vue = mr.fetch_pr_view(runner, pr, gh_env)
    debut = time.monotonic()
    verdict = mr.evaluate_pr(vue, pr, runner, gh_env)
    total = time.monotonic() - debut
    return {
        "pr": pr,
        "tete": str(vue.get("headRefOid") or ""),
        "base": vue.get("baseRefName"),
        "fichiers": vue.get("changedFiles"),
        "motif": verdict.reason,
        "verdict": verdict.verdict,
        "total_secondes": total,
        "etapes": mesures,
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--pr", nargs="+", type=int, required=True,
        help="numeros de PR a mesurer",
    )
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    mr = charger_merge_ready()
    runner = mr.SubprocessRunner()
    gh_env = {**os.environ, "GH_TOKEN": mr.resolve_token(runner)}
    resultats = []
    for pr in args.pr:
        try:
            resultats.append(mesurer(mr, pr, runner, gh_env))
        except mr.UnexpectedError as exc:
            print(f"PR #{pr} : lecture impossible -- {exc}", file=sys.stderr)
            resultats.append({"pr": pr, "erreur": str(exc)})
    if args.json:
        print(json.dumps(resultats, ensure_ascii=False, indent=2))
        return 0
    for r in resultats:
        if "erreur" in r:
            print(f"PR #{r['pr']} : ERREUR {r['erreur']}")
            continue
        print(f"\n=== PR #{r['pr']} — total {r['total_secondes']:.1f} s "
              f"— motif : {r['motif']}")
        for mesure in r["etapes"]:
            print(f"    {mesure['secondes']:>8.2f} s  {mesure['etape']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
