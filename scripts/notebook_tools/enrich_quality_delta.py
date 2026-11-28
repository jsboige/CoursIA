#!/usr/bin/env python3
"""Comparaison enrich-quality base-vs-head sur les carnets d'une PR (#26973).

Pourquoi cet organe existe
--------------------------
Le gate « No enrich-quality regression in changed notebooks »
(`.github/workflows/enrich-quality-gate.yml`) ne tourne que dans la CI : sa
logique (liste des carnets de la PR, filtre « introduit par la PR », extraction
de la version de base, comparaison base-vs-head carnet par carnet) est
ecrite dans le YAML du workflow, donc inaccessible a un auteur qui veut
verifier **avant** de pousser. C'est ce qui est arrive sur #25692 : trois
liens relatifs casses par une profondeur de chemin de trop, decouverts
seulement par la CI -- un aller-retour pour une faute d'un cran.

Cet organe est cette meme logique, **extraite** et appelable en local :

    python scripts/notebook_tools/enrich_quality_delta.py --base-ref origin/main

Il ne reecrit aucun des deux organes qu'il consomme :
`enrich_quality_ci.py` (la comparaison base-vs-head d'UN carnet, avec les
marqueurs de body #17744) et `filter_pr_introduced_notebooks.py` (le filtre
« ce carnet a ete touche par un commit PROPRE a la PR »). Il les appelle.

Fidélite au workflow d'origine (l'enumeration est celle de
`enrich-quality-gate.yml`, etape « Gate changed notebooks ») :

1. la liste des carnets vient de `git diff --name-status -M BASE...HEAD`
   (rename-aware : un renommage seul ne doit pas passer pour un carnet neuf) ;
2. le filtre « introduit par la PR » est applique ; il est **fail-open**
   (un ensemble indetermmable conserve tout) ;
3. un carnet **supprime** par la PR est saute ;
4. la version de base est extraite par `git show BASE:<chemin>` ; si le carnet
   n'existe pas a la base, la base est `NONE` (carnet neuf) ;
5. la comparaison est celle de `enrich_quality_ci.py`, carnet par carnet ;
6. le body de la PR alimente les marqueurs `enrich-quality: reecriture
   assumee` : par `--pr-body-file`, sinon par la variable d'environnement
   `ENRICH_QUALITY_PR_BODY` (canal recommande en CI).

Echecs :
  0 - aucune regression ;
  1 - au moins un carnet regresse (finding HIGH nouveau), ou un carnet n'a
      pas pu etre compare (base non resolue, gate non concluant) ;
  2 - usage invalide (refs illisibles, options manquantes).
"""

from __future__ import annotations

import argparse
import contextlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
sys.path.insert(0, str(REPO_ROOT / "scripts" / "notebook_tools"))

import enrich_quality_ci  # noqa: E402
import filter_pr_introduced_notebooks as pr_filter  # noqa: E402

NOTEBOOK_GLOB = "MyIA.AI.Notebooks/**/*.ipynb"
EXIT_OK = 0
EXIT_REGRESSION = 1
EXIT_USAGE = 2


@contextlib.contextmanager
def pushd(path: Path):
    """Change le repertoire courant, puis le restaure.

    `filter_pr_introduced_notebooks.py` appelle `git` sans `-C` : son
    resultat depend donc du repertoire courant. On l'execute dans l'arbre
    du depot vise, sans modifier l'organe consomme.
    """
    previous = Path.cwd()
    os.chdir(str(path))
    try:
        yield
    finally:
        os.chdir(str(previous))


def git(repo_root: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-c", "core.quotePath=false", "-C", str(repo_root), *args],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )


def changed_rows(repo_root: Path, base_ref: str, head_ref: str) -> list[tuple[str, str, str]]:
    """Lignes `--name-status -M` des carnets touches entre la base et la tete."""
    proc = git(repo_root, "diff", "--name-status", "-M",
               f"{base_ref}...{head_ref}", "--", NOTEBOOK_GLOB)
    if proc.returncode != 0:
        raise RuntimeError(
            "diff illisible entre {} et {} : {}".format(
                base_ref, head_ref, (proc.stderr or "").strip()))
    return pr_filter.parse_rows(proc.stdout)


def pr_introduced_rows(repo_root: Path, rows, base_ref: str, head_ref: str,
                       main_ref: str):
    """Lignes des carnets touches par un commit PROPRE a la PR.

    Le filtre est fail-open : si l'ensemble des chemins propres a la PR est
    indetermmable, tout est conserve (le gate garde le comportement du
    workflow d'origine plutot que de s'eteindre).
    """
    with pushd(repo_root):
        owned = pr_filter.pr_owned_paths(base_ref, head_ref, main_ref)
    kept, dropped = pr_filter.filter_rows(rows, owned)
    return kept, dropped


def extract_base(repo_root: Path, base_ref: str, base_path: str,
                 target: Path) -> str:
    """Ecrit la version de base du carnet dans `target`.

    Rend le chemin du fichier extrait, ou `NONE` quand le carnet n'existe
    pas a la base (carnet neuf : tout finding HIGH est alors nouveau).
    """
    proc = git(repo_root, "show", f"{base_ref}:{base_path}")
    if proc.returncode != 0 or not proc.stdout.strip():
        return "NONE"
    target.write_text(proc.stdout, encoding="utf-8")
    return str(target)


def compare_one(base_file: str, head_file: str, repo_root: Path,
                pr_body_file: str = "") -> int:
    """Comparaison base-vs-head d'UN carnet (code de sortie de l'organe)."""
    argv = ["--base", base_file, "--head", head_file, "--repo-root", str(repo_root)]
    if pr_body_file:
        argv += ["--pr-body-file", pr_body_file]
    return enrich_quality_ci.main(argv)


def run(args) -> tuple[int, str]:
    """Compare tous les carnets de la PR. Rend (code de sortie, rapport)."""
    repo_root = Path(args.repo_root).resolve()
    lines: list[str] = []
    try:
        rows = changed_rows(repo_root, args.base_ref, args.head_ref)
    except RuntimeError as exc:
        return EXIT_USAGE, "[enrich-quality-delta] {}".format(exc)
    if not rows:
        return EXIT_OK, "[enrich-quality-delta] aucun carnet touche par la PR."

    kept, dropped = pr_introduced_rows(repo_root, rows, args.base_ref,
                                       args.head_ref, args.main_ref)
    for (status, base_path, head_path), reason in dropped:
        lines.append("  - {} : {}".format(head_path or base_path, reason))

    failures = 0
    compared = 0
    with tempfile.TemporaryDirectory(prefix="enrich-quality-delta-") as tmp:
        tmp_dir = Path(tmp)
        for index, (status, base_path, head_path) in enumerate(kept):
            if status.startswith("D"):
                continue  # carnet supprime par la PR : rien a comparer
            head_rel = head_path or base_path
            base_rel = base_path or head_rel
            head_abs = repo_root / head_rel
            if not head_abs.exists():
                lines.append("  - {} : absent de l'arbre de tete (ignore)".format(head_rel))
                continue
            base_file = extract_base(repo_root, args.base_ref, base_rel,
                                     tmp_dir / f"base-{index}.ipynb")
            rc = compare_one(base_file, str(head_abs), repo_root, args.pr_body_file)
            compared += 1
            if rc != 0:
                failures += 1
                lines.append("  - {} : rc={}".format(head_rel, rc))

    summary = ("[enrich-quality-delta] {} carnet(s) compare(s), {} regression(s) "
               "(sur {} ligne(s) de diff, {} retiree(s) par le filtre PR-introduit)"
               .format(compared, failures, len(rows), len(dropped)))
    return (EXIT_REGRESSION if failures else EXIT_OK), "\n".join(lines + [summary])


# ---------------------------------------------------------------------------
# auto-test : la comparaison sans git
# ---------------------------------------------------------------------------

def _notebook_with_link(link: str) -> dict:
    """Carnet minimal contenant un lien markdown relatif."""
    return {
        "cells": [
            {
                "cell_type": "markdown",
                "metadata": {},
                "source": ["Un lien vers [cible]({})\n".format(link)],
            }
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def self_test() -> int:
    """Verifie que la comparaison distingue bien « nouveau » de « deja la ».

    Trois cas :
      - une base et une tete identiques ne donnent AUCUNE regression ;
      - une tete qui ajoute un lien casse donne UNE regression ;
      - une base et une tete qui portent DEJA le meme lien casse ne donnent
        aucune regression (le defaut preexistant ne bloque pas la PR).
    """
    with tempfile.TemporaryDirectory(prefix="enrich-quality-delta-selftest-") as tmp:
        root = Path(tmp)
        (root / "serie").mkdir()
        base_ok = root / "serie" / "base.ipynb"
        base_ok.write_text(json.dumps(_notebook_with_link("cible.md")), encoding="utf-8")
        head_same = root / "serie" / "head.ipynb"
        head_same.write_text(json.dumps(_notebook_with_link("cible.md")), encoding="utf-8")
        head_new = root / "serie" / "head_new.ipynb"
        head_new.write_text(json.dumps(_notebook_with_link("absente.md")), encoding="utf-8")
        base_broken = root / "serie" / "base_broken.ipynb"
        base_broken.write_text(json.dumps(_notebook_with_link("absente.md")), encoding="utf-8")

        same = enrich_quality_ci.regressions(str(base_ok), str(head_same), root)
        introduced = enrich_quality_ci.regressions(str(base_ok), str(head_new), root)
        preexisting = enrich_quality_ci.regressions(str(base_broken), str(head_new), root)

    if same:
        print("[self-test] KO : des findings identiques en base et en tete sont "
              "rapportes comme nouveaux : {}".format(same))
        return 1
    if not introduced:
        print("[self-test] KO : un lien casse AJOUTE par la tete n'est pas vu "
              "comme une regression")
        return 1
    if preexisting:
        print("[self-test] KO : un defaut deja present en base est rapporte "
              "comme nouveau : {}".format(preexisting))
        return 1
    print("[self-test] OK : base==tete -> 0, lien casse ajoute -> 1, "
          "defaut preexistant -> 0")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Comparaison enrich-quality base-vs-head sur les carnets d'une PR.")
    parser.add_argument("--base-ref", default="origin/main",
                        help="ref de base de la PR (defaut : origin/main)")
    parser.add_argument("--head-ref", default="HEAD",
                        help="ref de tete (defaut : HEAD)")
    parser.add_argument("--main-ref", default="origin/main",
                        help="ref de main, pour le filtre PR-introduit (defaut : origin/main)")
    parser.add_argument("--repo-root", default=str(REPO_ROOT),
                        help="racine du depot (defaut : la racine de ce script)")
    parser.add_argument("--pr-body-file", default="",
                        help="fichier portant le body de la PR ; sans lui, la variable "
                             "d'environnement ENRICH_QUALITY_PR_BODY est lue")
    parser.add_argument("--self-test", action="store_true",
                        help="verifie la comparaison sans git, puis sort")
    return parser


def main(argv=None) -> int:
    args = build_parser().parse_args(argv)
    if args.self_test:
        return self_test()
    if not Path(args.repo_root).is_dir():
        print("[enrich-quality-delta] racine de depot introuvable : {}".format(args.repo_root),
              file=sys.stderr)
        return EXIT_USAGE
    code, report = run(args)
    print(report)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
