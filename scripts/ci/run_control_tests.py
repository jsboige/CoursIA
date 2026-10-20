#!/usr/bin/env python3
"""Run a control organ's own tests, naming the cause when nothing is evaluated.

A raw `pytest <files>` invocation conflates three situations that call for three
different actions, and on 2026-10-10 two of them were observed accusing a pull
request of a defect it did not have (see #20174, #20200, #18312) :

  1. **The files are absent from disk though committed.** A persistent runner
     slot mounted a `_work` volume that survived a previous job, so the working
     tree served to this one is amputated -- committed files are simply not
     there. pytest exits 4 ("usage error"), which reads in the checks UI as a
     verdict of the PR.
  2. **The files are present but collect nothing.** The control reddens without
     having evaluated a single assertion -- the exact vacuity such an organ
     exists to refuse in others.
  3. **The tests actually ran and one failed.** That is a real finding, and the
     exit code is the one to propagate untouched.

Only (1) and (2) are re-diagnosed. Both still exit non-zero: this script makes a
red *honest*, it never makes it *green*.
"""
from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

EXIT_CAUSE = 1
CHECKOUT_HINT = "Voir #20174 (cause racine) / #18312 (objets introuvables)."
VACUITY_HINT = "Voir #20200."
COLLECTION_HINT = "Voir #21539."
# Fichiers lus par pytest pour son rootdir/configfile, dans l'ordre de priorite
# de la decouverte (-c accepte chacun d'eux).
CONFIG_NAMES = ("pytest.ini", "pyproject.toml", "setup.cfg", "tox.ini")


def _report(missing: list[str], label: str) -> int:
    listed = ", ".join(missing)
    print(
        f"::error title=Arbre de checkout incomplet::{label} -- fichier(s) committe(s) "
        f"mais absent(s) du disque : {listed}. Un slot persistant a servi un arbre ampute "
        f"(volume _work epingle, sparseCheckout herite). Ce n'est PAS un defaut de la PR. "
        f"{CHECKOUT_HINT}"
    )
    return EXIT_CAUSE


def _is_vacuous(returncode: int, output: str) -> bool:
    """pytest evaluated nothing: no tests collected, or it never got to collect."""
    if returncode in (4, 5):
        return True
    if "file or directory not found" in output:
        return True
    return bool(re.search(r"collected 0 items", output)) or "no tests ran" in output


def _is_collection_error(returncode: int, output: str) -> bool:
    """pytest stopped before running a single test (rc 2, INTERRUPTED).

    Distinct d'un echec de test a dessein (#21539) : une permission refusee, un
    chemin illisible ou un import casse n'est pas un constat sur la PR, et un
    appelant qui lit rc=1 comme « la PR a casse un test » l'accuse a tort.
    """
    if returncode == 2:
        return True
    lowered = output.lower()
    return "error during collection" in lowered or "interrupted:" in lowered


def _pytest_boundary(paths: list[str]) -> list[str]:
    """Epingle config/rootdir de pytest pour qu'il ne remonte jamais l'arbre.

    Sans argument de configuration, pytest cherche son rootdir en remontant
    depuis le repertoire commun des fichiers testes ; sur un poste Windows ce
    parcours atteint des points d'analyse proteges (`C:\\Documents and
    Settings`) et rend rc=2 avant toute collecte (#21539, mesure du 2026-10-20).
    Le configfile du depot est deja celui que pytest decouvre quand les
    controles partent de la racine ; le nommer rend la recherche inutile.
    """
    start = Path.cwd()
    for directory in (start, *start.parents):
        for name in CONFIG_NAMES:
            candidate = directory / name
            if candidate.is_file():
                return ["-c", str(candidate)]
    try:
        common = os.path.commonpath([os.path.abspath(p) for p in paths])
    except ValueError:  # chemins sur des volumes differents
        return []
    if os.path.isfile(common):
        common = os.path.dirname(common)
    return ["--rootdir", common]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Run a control organ's tests, naming an amputated checkout or an empty control."
    )
    parser.add_argument("paths", nargs="+", help="test files this control must actually run")
    parser.add_argument(
        "--label",
        default="controle",
        help="name under which the control appears in the message",
    )
    parser.add_argument(
        "--pytest-arg",
        action="append",
        default=[],
        help="extra argument forwarded to pytest (repeatable)",
    )
    args = parser.parse_args(argv)

    missing = [p for p in args.paths if not os.path.isfile(p)]
    if missing:
        return _report(missing, args.label)

    proc = subprocess.run(
        [
            sys.executable,
            "-m",
            "pytest",
            *_pytest_boundary(args.paths),
            *args.paths,
            "-v",
            *args.pytest_arg,
        ],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    sys.stdout.write(proc.stdout)
    sys.stderr.write(proc.stderr)

    if _is_collection_error(proc.returncode, proc.stdout + proc.stderr):
        print(
            f"::error title=Erreur de collecte::{args.label} n'a pas pu collecter ses tests "
            f"(pytest rc={proc.returncode}). La collecte a echoue AVANT toute execution : "
            f"permission refusee, chemin illisible ou import casse. Ce n'est ni un echec de "
            f"test de la PR, ni un controle vide -- verifier le journal de collecte ci-dessus. "
            f"{COLLECTION_HINT}"
        )
        return EXIT_CAUSE

    if _is_vacuous(proc.returncode, proc.stdout + proc.stderr):
        print(
            f"::error title=Controle vide::{args.label} n'a evalue aucune assertion "
            f"(pytest rc={proc.returncode}). Un organe de controle doit rougir sur sa propre "
            f"vacuite, pas seulement sur celle des autres. {VACUITY_HINT}"
        )
        return EXIT_CAUSE

    return proc.returncode


if __name__ == "__main__":
    sys.exit(main())
