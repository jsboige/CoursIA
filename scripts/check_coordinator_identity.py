#!/usr/bin/env python3
"""Garde d'identite de lane — mesurer sa lane AVANT d'armer une cadence.

Une session qui arme `/coordinate` sans avoir mesure sa lane peut coordonner
depuis la mauvaise machine, le mauvais workspace, ou un clone jumeau. Cet organe
rend la mesure mecanique et son verdict opposable :

    lane = <machine>:<workspace>

ou `machine` est le hostname normalise et `workspace` le *basename* du clone
(worktree principal : un worktree secondaire appartient a la lane de son clone,
il n'en cree pas une nouvelle). Trois roles sont definis pour le cluster CoursIA (cf.
`.claude/rules/coordinator-discipline.md`, section « Garde d'identite ») :

    myia-ai-01:CoursIA        -> COORDINATOR  -> /coordinate
    myia-po-2025:CoursIA-2    -> ADJOINT      -> /coordinate-adjoint
    toute autre lane          -> WORKER       -> /continue

PORTEE DE LA MESURE (lire avant d'invoquer le verdict) : cet organe mesure la
LANE, et rien d'autre. Il ne peut PAS mesurer l'unicite de session — savoir si
une autre session CoursIA tourne deja sur la meme lane exige `ListAgents` PUIS
un aller-retour `SendMessage` (les noms de session n'encodent pas la lane), deux
gestes de niveau agent, hors de portee d'un script. Un `exit 0` dit donc « la
lane est la bonne », jamais « il est sur d'armer /coordinate ».

Codes de sortie :
    0 -- role VERIFIE conforme : la lane mesuree correspond au role exige
         par `--expect <role>`
    1 -- role VERIFIE non conforme ; la commande de repli est imprimee
    2 -- la mesure elle-meme a echoue (hors depot git, hostname introuvable)
    3 -- rapport seul (`--expect auto`, defaut) : la conformite n'est PAS
         verifiee -- sous `auto` le role attendu serait le role mesure
         (tautologie), le rapport le dit (`verified: false`) au lieu de la
         pretendre
"""

from __future__ import annotations

import argparse
import json
import os
import socket
import subprocess
import sys
from pathlib import Path
from typing import Optional

COORDINATOR_LANE = "myia-ai-01:CoursIA"
ADJOINT_LANE = "myia-po-2025:CoursIA-2"

ROLE_COMMANDS = {
    "coordinator": "/coordinate",
    "adjoint": "/coordinate-adjoint",
    "worker": "/continue",
}

# Racine canonique par lane privilegiee. Deux clones d'un meme depot portent le
# MEME basename, donc la MEME lane : sur ai-01, `D:/CoursIA` et `D:/dev/CoursIA`
# rendent tous deux `myia-ai-01:CoursIA`. La lane ne les discrimine pas — seul
# le chemin le fait, d'ou cette table.
CANONICAL_ROOTS = {
    COORDINATOR_LANE: "d:/coursia",
}

# Index de consultation insensible a la casse : sur Windows/NTFS le basename
# du clone peut arriver en casse non canonique (`coursia` vs `CoursIA`), et la
# cle brute raterait la table -> `canonical is None` -> clone_ok vrai pour un
# jumeau, silencieusement. Seul le LOOKUP se normalise ; la lane RENDUE dans
# le rapport garde la casse reelle du dossier (identite affichee).
_CANONICAL_ROOTS_NORM = {
    lane.lower(): root for lane, root in CANONICAL_ROOTS.items()
}

# Ligne de portee rendue sur TOUS les chemins de sortie, y compris l'echec de
# mesure (exit 2) : c'est le garde-fou voulu omnipresent — un chemin d'erreur
# ne doit pas le faire disparaitre.
_PORTEE_LINE = (
    "PORTEE    : l'unicite de session n'est PAS mesuree ici. "
    "Avant d'armer, enumerer les pairs (`ListAgents`) et qualifier chacun "
    "par un aller-retour `SendMessage` — un nom de session n'encode pas la lane."
)


def _normalise(path: str) -> str:
    return path.replace("\\", "/").rstrip("/").lower()


def measure_machine() -> str:
    """Hostname normalise. `COMPUTERNAME` prime sur Windows quand il est pose."""
    raw = os.environ.get("COMPUTERNAME") or socket.gethostname()
    return raw.split(".")[0].strip().lower()


def _git(args: list[str], cwd: Path) -> Optional[str]:
    try:
        out = subprocess.run(
            ["git", *args], cwd=str(cwd), capture_output=True,
            text=True, encoding="utf-8", errors="replace",
            timeout=30, check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    value = out.stdout.strip()
    return value or None


def measure_repo_root(start: Optional[Path] = None) -> Optional[Path]:
    """Racine du CLONE (worktree principal), ou None hors depot.

    `--show-toplevel` rendrait le worktree courant : depuis un worktree
    secondaire il donnerait son nom de dossier comme workspace, fabriquant une
    lane inexistante. Le worktree principal se deduit de `--git-common-dir`,
    qui pointe le `.git` partage par tous les worktrees du clone.
    """
    cwd = start or Path.cwd()
    common = _git(["rev-parse", "--git-common-dir"], cwd)
    if common is None:
        return None
    common_path = Path(common)
    if not common_path.is_absolute():
        common_path = (cwd / common_path).resolve()
    if common_path.name == ".git":
        return common_path.parent
    # Depot bare ou disposition inhabituelle : retomber sur le worktree courant.
    top = _git(["rev-parse", "--show-toplevel"], cwd)
    return Path(top) if top else None


def role_for_lane(lane: str) -> str:
    # Comparaison insensible a la casse : le basename du clone garde sa casse
    # reelle (NTFS), elle ne doit pas decider du role d'une lane privilegiee.
    key = lane.lower()
    if key == COORDINATOR_LANE.lower():
        return "coordinator"
    if key == ADJOINT_LANE.lower():
        return "adjoint"
    return "worker"


def build_report(expect: str) -> dict:
    machine = measure_machine()
    root = measure_repo_root()
    if root is None:
        return {
            "ok": False,
            "verified": False,
            "error": "hors depot git : le workspace ne peut pas etre mesure",
            "machine": machine,
            "workspace": None,
            "lane": None,
            "role": None,
            "expect": expect,
        }

    workspace = root.name
    # La lane garde la casse REELLE du dossier (identite affichee) ; seules
    # les consultations de tables se font en casse normalisee.
    lane = f"{machine}:{workspace}"
    role = role_for_lane(lane)

    canonical = _CANONICAL_ROOTS_NORM.get(lane.lower())
    measured_root = _normalise(str(root))
    clone_ok = canonical is None or measured_root == canonical

    if not clone_ok:
        # Bonne machine, bon nom de workspace, mauvais clone : la lane seule ne
        # peut pas le voir. On retrograde en worker plutot que de coordonner
        # depuis un jumeau (fail-CLOSED).
        role = "worker"

    # Forme (a) retenue pour `auto` : le rapport cesse de pretendre verifier.
    # `ok` vaudrait `role == role` (tautologie), donc il devient None, le
    # rapport porte `verified: false`, la ligne rendue dit « rapporte, non
    # verifie » et le code de sortie (3) se distingue de 0/1. L'unique
    # appelant repertorie du depot (.claude/rules/coordinator-discipline.md)
    # passe deja `--expect coordinator` explicite : aucun appelant existant
    # ne consomme le mode auto, qui reste ouvert pour la decouverte de lane.
    if expect == "auto":
        expected_role = None
        ok = None
        verified = False
    else:
        expected_role = expect
        ok = role == expected_role
        verified = True
    return {
        "ok": ok,
        "verified": verified,
        "error": None,
        "machine": machine,
        "workspace": workspace,
        "repo_root": str(root),
        "canonical_root": canonical,
        "clone_ok": clone_ok,
        "lane": lane,
        "role": role,
        "expect": expect,
        "expected_role": expected_role,
        "command": ROLE_COMMANDS[role],
        "uniqueness_measured": False,
    }


def render(report: dict) -> str:
    if report.get("error"):
        # La portee survit AUSSI au chemin d'echec : c'est le garde-fou voulu
        # omnipresent, un exit 2 ne doit pas le faire disparaitre.
        return (
            f"MESURE IMPOSSIBLE : {report['error']}\n"
            f"  machine : {report['machine']}\n{_PORTEE_LINE}"
        )

    lines = [
        f"machine   : {report['machine']}",
        f"workspace : {report['workspace']}  (racine {report['repo_root']})",
        f"lane      : {report['lane']}",
        f"role      : {report['role'].upper()}  -> cadence `{report['command']}`",
    ]
    if not report["clone_ok"]:
        lines.append(
            f"CLONE     : racine hors canonique ({report['canonical_root']}) — "
            "lane retrogradee en WORKER (fail-CLOSED)"
        )
    lines.append(_PORTEE_LINE)
    if not report["verified"]:
        lines.append(
            f"VERDICT   : role mesure `{report['role']}` — rapporte, non "
            "verifie ; passer `--expect <role>` pour un verdict opposable."
        )
    elif not report["ok"]:
        lines.append(
            f"VERDICT   : role attendu `{report['expect']}`, role mesure "
            f"`{report['role']}` — ne PAS armer `{ROLE_COMMANDS[report['expect']]}`, "
            f"armer `{report['command']}`."
        )
    else:
        lines.append(f"VERDICT   : lane conforme au role `{report['expect']}`.")
    return "\n".join(lines)


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Mesure la lane de la session et le role qui en decoule."
    )
    parser.add_argument(
        "--expect",
        choices=["auto", "coordinator", "adjoint", "worker"],
        default="auto",
        help="role attendu ; `auto` (defaut) RAPPORTE le role sans le verifier "
        "(exit 3) — pour un verdict opposable, exiger un role explicite",
    )
    parser.add_argument("--json", action="store_true", help="sortie JSON")
    args = parser.parse_args(argv)

    report = build_report(args.expect)
    print(json.dumps(report, indent=2, ensure_ascii=False) if args.json else render(report))

    if report.get("error"):
        return 2
    if not report["verified"]:
        # Mode rapport : aucun verdict de conformite n'a ete rendu — code de
        # sortie distinct de 0/1 pour qu'un wrapper ne le lise pas « conforme ».
        return 3
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
