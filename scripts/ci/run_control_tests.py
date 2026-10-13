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

EXIT_CAUSE = 1
CHECKOUT_HINT = "Voir #20174 (cause racine) / #18312 (objets introuvables)."
VACUITY_HINT = "Voir #20200."


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
        [sys.executable, "-m", "pytest", *args.paths, "-v", *args.pytest_arg],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
    )
    sys.stdout.write(proc.stdout)
    sys.stderr.write(proc.stderr)

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
