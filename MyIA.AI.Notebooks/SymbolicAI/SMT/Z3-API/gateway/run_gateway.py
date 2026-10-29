# -*- coding: utf-8 -*-
"""Lanceur du service Kernel Gateway Z3 Sudoku (issue #22439).

Deux defauts mesures sur le demarrage documente par #21100 :

1. **Le kernel demarre dans le repertoire du processus, pas dans celui du
   carnet.** Lance depuis un autre dossier avec un ``seed_uri`` absolu, le
   kernel meurt au seed sur ``ModuleNotFoundError: No module named
   'z3_sudoku_core'`` (la cellule de preparation fait
   ``sys.path.insert(0, os.getcwd())``).
2. **Un seed rate ne fait pas tomber le serveur, il le fige.** La ressource
   ``/sudoku/solve`` est enregistree, ``/_api/spec/swagger.json`` continue de
   rendre 200, mais ``POST /sudoku/solve`` ne repond jamais : le client expire
   sans pouvoir distinguer une panne d'un calcul lent.

Ce lanceur traite les deux : il se place dans son propre dossier (celui du
carnet et du coeur), publie ce dossier dans ``Z3_GATEWAY_CORE_DIR`` pour la
cellule de preparation, et **verifie le coeur avant de demarrer le gateway**.
Un coeur absent ou non importable sort immediatement avec un code retour non
nul et un message lisible, au lieu d'un service qui pend.

Usage :
    python run_gateway.py                    # port 8899
    python run_gateway.py --port 8900
    python run_gateway.py --check-only       # preflight seul, ne demarre rien
    python run_gateway.py -- --debug         # arguments transmis au gateway
"""
from __future__ import annotations

import argparse
import importlib.util
import os
import subprocess
import sys
from pathlib import Path
from typing import List, Sequence

CORE_MODULE = "z3_sudoku_core.py"
SERVICE_NOTEBOOK = "z3-sudoku-service.ipynb"
DEFAULT_PORT = 8899
CORE_DIR_ENV = "Z3_GATEWAY_CORE_DIR"

EXIT_PREFLIGHT = 2


def core_dir() -> Path:
    """Dossier du lanceur, donc celui du carnet et du coeur.

    Resolu depuis ``__file__`` : le resultat ne depend pas du repertoire
    courant, ce qui est precisement le defaut corrige ici.
    """
    return Path(__file__).resolve().parent


def preflight(directory: Path) -> List[str]:
    """Verifie que le service peut demarrer. Rend la liste des problemes.

    Ne demarre rien et ne change pas de repertoire : appelable depuis un test.
    Une liste vide signifie que le demarrage est sur.
    """
    problems: List[str] = []

    core = Path(directory) / CORE_MODULE
    notebook = Path(directory) / SERVICE_NOTEBOOK

    if not core.is_file():
        problems.append(f"coeur absent : {core}")
    if not notebook.is_file():
        problems.append(f"carnet de service absent : {notebook}")

    try:
        import kernel_gateway  # noqa: F401
    except ImportError:
        problems.append(
            "dependance manquante : kernel_gateway "
            "(le paquet PyPI s'appelle jupyter_kernel_gateway, "
            "mais son module s'importe kernel_gateway)"
        )

    if core.is_file():
        try:
            spec = importlib.util.spec_from_file_location("z3_sudoku_core_preflight", core)
            if spec is None or spec.loader is None:
                problems.append(f"coeur illisible comme module Python : {core}")
            else:
                module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(module)
                if not hasattr(module, "solve_request"):
                    problems.append("coeur importable mais sans fonction solve_request")
        except ImportError as exc:
            problems.append(
                f"coeur non importable, dependance manquante : {exc} "
                "(pip install -r requirements.txt)"
            )
        except Exception as exc:  # noqa: BLE001 - tout echec de seed doit tomber ici
            problems.append(f"coeur non importable : {exc!r}")

    return problems


def build_arguments(directory: Path, port: int, extra: Sequence[str]) -> List[str]:
    """Ligne de commande du gateway, ``seed_uri`` relatif au dossier servi."""
    return [
        sys.executable,
        "-m",
        "kernel_gateway",
        "--KernelGatewayApp.api=kernel_gateway.notebook_http",
        f"--KernelGatewayApp.seed_uri={SERVICE_NOTEBOOK}",
        f"--KernelGatewayApp.port={port}",
        "--JupyterWebsocketPersonality.list_kernels=True",
        *extra,
    ]


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Demarre le service Kernel Gateway Z3 Sudoku depuis son propre dossier."
    )
    parser.add_argument(
        "--port",
        type=int,
        default=DEFAULT_PORT,
        help=f"port d'ecoute (defaut {DEFAULT_PORT})",
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="n'execute que le preflight et sort (0 = pret, 2 = probleme)",
    )
    parser.add_argument(
        "gateway_args",
        nargs=argparse.REMAINDER,
        help="arguments transmis au gateway, apres --",
    )
    args = parser.parse_args(argv)

    directory = core_dir()
    problems = preflight(directory)
    if problems:
        for problem in problems:
            print(f"[gateway] {problem}", file=sys.stderr)
        print(
            "[gateway] demarrage refuse : dans cet etat le service repondrait 200 "
            f"sur /_api/spec/swagger.json sans jamais repondre sur /sudoku/solve "
            f"(voir #22439).",
            file=sys.stderr,
        )
        return EXIT_PREFLIGHT

    if args.check_only:
        print(f"[gateway] preflight OK : {directory}")
        return 0

    extra = [a for a in args.gateway_args if a != "--"]
    os.environ[CORE_DIR_ENV] = str(directory)
    os.chdir(directory)

    command = build_arguments(directory, args.port, extra)
    print(f"[gateway] dossier servi : {directory}")
    print(f"[gateway] endpoint      : http://127.0.0.1:{args.port}/sudoku/solve")
    sys.stdout.flush()
    return subprocess.call(command)


if __name__ == "__main__":
    sys.exit(main())
