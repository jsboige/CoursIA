"""Ligne de garde : verifie la signature d'execution des carnets qui en portent une.

Usage :

    python scripts/notebook_tools/check_execution_signature.py --all
    python scripts/notebook_tools/check_execution_signature.py --notebook <chemin> [--notebook <chemin>]
    python scripts/notebook_tools/check_execution_signature.py --stamp <chemin>
    python scripts/notebook_tools/check_execution_signature.py --self-test

`--all` parcourt le depot et verifie **les seuls carnets qui portent une signature**
(`metadata.execution_signature`) : l'organe est opt-in, il ne rend donc rouge aucun
carnet existant. `--notebook` verifie un carnet donne ; si ce carnet ne porte pas de
signature, il est signale (`SIGNATURE_ABSENTE`) et la commande echoue.

`--stamp` ecrit la signature dans le carnet (apres une execution) : c'est le geste
d'outillage qui remplace, cote .NET Interactive, le tampon `metadata.papermill`.

`--self-test` prouve le temoin negatif de l'organe : une source editee apres
l'execution doit etre detectee.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from execution_signature import (  # noqa: E402
    SIGNATURE_KEY,
    compute_signature,
    load_notebook,
    measure_tool_versions,
    save_notebook,
    stamp,
    verify,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOK_GLOBS = ("MyIA.AI.Notebooks", "GradeBookApp")


def iter_repo_notebooks(root: Path) -> list[Path]:
    """Parcourt les carnets du depot."""
    found: list[Path] = []
    for folder in NOTEBOOK_GLOBS:
        base = root / folder
        if base.is_dir():
            found.extend(sorted(base.rglob("*.ipynb")))
    return found


def check_notebook(path: Path, require_signature: bool = False) -> list[dict]:
    """Verifie un carnet et renvoie ses constats.

    `require_signature=False` (defaut) : un carnet **sans** signature est ignore
    -- la garde ne porte que sur les carnets qui en portent une. Avec
    `require_signature=True`, l'absence de signature est elle-meme un constat.
    """
    try:
        notebook = load_notebook(path)
    except (OSError, ValueError) as exc:
        return [{"code": "CARNET_ILLISIBLE", "detail": str(exc)}]
    findings = verify(notebook, require_signature=require_signature)
    for finding in findings:
        finding["notebook"] = str(path)
    return findings


def changed_notebooks(root: Path, base_ref: str) -> list[Path]:
    """Renvoie les carnets modifies entre `base_ref` et HEAD.

    C'est la fenetre **seule** ou une signature peut devenir perimee : une
    signature ne peut etre invalidee que par une edition du carnet qu'elle
    atteste, et cette edition figure alors dans le diff. Verifier le depot
    entier n'apporterait rien de plus, pour un cout de lecture de l'integralite
    des carnets.
    """
    try:
        completed = subprocess.run(
            ["git", "-C", str(root), "diff", "--name-only", f"{base_ref}...HEAD"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=120,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if completed.returncode != 0:
        return []
    out = []
    for line in completed.stdout.splitlines():
        candidate = (root / line.strip())
        if candidate.suffix == ".ipynb" and candidate.is_file():
            out.append(candidate)
    return out


def signed_notebooks(root: Path) -> list[Path]:
    """Renvoie les carnets du depot qui portent une signature d'execution.

    Le depistage se fait sur le **texte brut** : charger et deserialiser tous les
    carnets du depot pour y chercher une cle serait inutilement lent (le depot
    compte plus d'un millier de carnets). Le filtre textuel ne peut produire
    qu'un faux positif (une occurrence de la cle hors metadonnees), que la
    lecture JSON suivante ecarte.
    """
    signed = []
    needle = f'"{SIGNATURE_KEY}"'
    for path in iter_repo_notebooks(root):
        try:
            with open(path, "r", encoding="utf-8", errors="replace") as handle:
                if needle not in handle.read():
                    continue
            notebook = load_notebook(path)
        except (OSError, ValueError):
            continue
        if SIGNATURE_KEY in (notebook.get("metadata") or {}):
            signed.append(path)
    return signed


def stamp_notebook(path: Path, executed_at: str | None = None) -> dict:
    """Ecrit la signature d'execution dans un carnet et renvoie la signature."""
    notebook = load_notebook(path)
    signature = stamp(notebook, measure_tool_versions(), executed_at)
    save_notebook(path, notebook)
    return signature


def _synthetic_notebook() -> dict:
    """Carnet minimal pour l'auto-test."""
    return {
        "cells": [
            {"cell_type": "markdown", "source": ["# titre\n"]},
            {"cell_type": "code", "source": ["var a = 1;\n"], "execution_count": 1, "outputs": []},
            {"cell_type": "code", "source": ["var b = a + 1;\n"], "execution_count": 2, "outputs": []},
        ],
        "metadata": {"kernelspec": {"name": ".net-csharp", "display_name": ".NET (C#)"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def self_test() -> int:
    """Auto-test : le temoin negatif de l'organe doit etre detecte."""
    checks: list[tuple[str, bool]] = []

    notebook = _synthetic_notebook()
    stamp(notebook, {"dotnet_sdk": "self-test"})
    findings = verify(notebook)
    checks.append(("carnet signe et intact : aucun constat", not findings))

    edited = json.loads(json.dumps(notebook))
    edited["cells"][1]["source"] = ["var a = 2;\n"]
    codes = [f["code"] for f in verify(edited)]
    checks.append(("source editee apres execution : SIGNATURE_PERIMEE", "SIGNATURE_PERIMEE" in codes))

    unexecuted = json.loads(json.dumps(notebook))
    unexecuted["cells"][2]["execution_count"] = None
    codes = [f["code"] for f in verify(unexecuted)]
    checks.append(("cellule non executee : CELLULE_NON_EXECUTEE", "CELLULE_NON_EXECUTEE" in codes))

    moved = json.loads(json.dumps(notebook))
    moved["cells"][1], moved["cells"][2] = moved["cells"][2], moved["cells"][1]
    codes = [f["code"] for f in verify(moved)]
    checks.append(("cellule deplacee : SIGNATURE_PERIMEE", "SIGNATURE_PERIMEE" in codes))

    absent = verify(_synthetic_notebook())
    codes = [f["code"] for f in absent]
    checks.append(("carnet non signe : SIGNATURE_ABSENTE", "SIGNATURE_ABSENTE" in codes))

    ok = True
    for label, passed in checks:
        print(f"[{'OK' if passed else 'ECHEC'}] {label}")
        ok = ok and passed
    print("auto-test:", "SUCCES" if ok else "ECHEC")
    return 0 if ok else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", default=str(REPO_ROOT), help="racine du depot")
    parser.add_argument("--notebook", action="append", default=[], help="carnet a verifier (repetable)")
    parser.add_argument("--all", action="store_true", help="verifier tous les carnets signatures du depot")
    parser.add_argument(
        "--changed-from",
        help="verifier les carnets modifies entre cette reference et HEAD (ex: origin/main)",
    )
    parser.add_argument(
        "--require-signature",
        action="store_true",
        help="signaler l'absence de signature (defaut : les carnets sans signature sont ignores)",
    )
    parser.add_argument("--stamp", help="ecrire la signature d'execution dans ce carnet")
    parser.add_argument(
        "--executed-at",
        help="instant reel de l'execution attestee (YYYY-MM-DDTHH:MM:SSZ) ; par defaut, l'heure du tampon",
    )
    parser.add_argument("--json", action="store_true", help="sortie structuree")
    parser.add_argument("--self-test", action="store_true", help="executer l'auto-test de l'organe")
    args = parser.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.stamp:
        signature = stamp_notebook(Path(args.stamp), args.executed_at)
        print(json.dumps(signature, ensure_ascii=False, indent=2) if args.json else
              f"signature ecrite : {signature['source_digest']} "
              f"({signature['executed_cells']} cellules executees, noyau {signature['kernel']['name']})")
        return 0

    root = Path(args.root)
    targets: list[Path] = [Path(p) for p in args.notebook]
    if args.changed_from:
        targets.extend(changed_notebooks(root, args.changed_from))
    if args.all:
        targets.extend(signed_notebooks(root))

    if not targets:
        print("aucun carnet a verifier (preciser --notebook, --changed-from ou --all)")
        return 0

    findings: list[dict] = []
    for path in targets:
        findings.extend(check_notebook(path, require_signature=args.require_signature))

    if args.json:
        print(json.dumps({"checked": len(targets), "findings": findings}, ensure_ascii=False, indent=2))
    else:
        for finding in findings:
            print(f"[{finding['code']}] {finding.get('notebook', '')} : {finding.get('detail', '')}")
        print(f"{len(targets)} carnet(s) verifie(s), {len(findings)} constat(s)")
    return 1 if findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
