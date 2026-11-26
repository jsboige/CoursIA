#!/usr/bin/env python3
"""Garde des dossiers de premier niveau sous `MyIA.AI.Notebooks/` (#27141).

Ce que fait cet organe
----------------------
Il **rougit** une PR qui ajoute un dossier directement sous
`MyIA.AI.Notebooks/` et que la liste d'autorisation ne couvre pas.

Pourquoi (#27092, decision du mainteneur du 17/11)
---------------------------------------------------
« Le critere d'eparpillement est le premier niveau. » Une serie soeur se range
dans un rayon ou sous un hub, elle ne s'ajoute pas a la racine. Le gel diffuse
sur les dashboards n'a pas suffi : la regle a besoin d'un controle qui la porte.

La liste d'autorisation
------------------------
`scripts/ci/toplevel_series_allowlist.txt` porte les dossiers de premier
niveau **autorises** :

- les dossiers **presents sur `main`** (leur autorisation est leur merge) ;
- les dossiers **autorises par un GO ecrit du mainteneur** qui ne sont pas
  encore sur `main` (le GO est cite en commentaire sur la ligne).

Une ligne = un dossier. `#` ouvre un commentaire ; une ligne vide est ignoree.

Le point de couture avec le GO
------------------------------
L'autorisation d'un dossier nouveau passe par **une PR qui l'ajoute a la liste
en citant le GO**. Comme la liste est lue dans l'arbre de travail (donc dans
l'etat de la tete), une PR qui ajoute le dossier ET sa ligne d'autorisation
passe -- c'est le reviewer qui verifie que le GO est ecrit. Une PR qui ajoute
un dossier sans toucher la liste est rougee.

Ports de sortie
---------------
- `0` : rien de neuf au premier niveau ;
- `1` : un ou plusieurs dossiers nouveaux sont nommes, avec le renvoi vers
  #27092 ;
- `2` : l'instrument lui-meme est en panne (diff illisible, liste introuvable
  ou illisible). **Jamais compte comme vert.**

Usage
-----
    python scripts/ci/check_toplevel_series.py                       # origin/main...HEAD
    python scripts/ci/check_toplevel_series.py --diff b82151be^..b82151be
    python scripts/ci/check_toplevel_series.py --json
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

SERIES_ROOT = "MyIA.AI.Notebooks"
DEFAULT_ALLOWLIST = Path(__file__).resolve().parent / "toplevel_series_allowlist.txt"
GO_ISSUE = "#27092"


# --- liste d'autorisation ----------------------------------------------------

def parse_allowlist(text: str) -> list[str]:
    """Lit la liste d'autorisation.

    Une ligne = un dossier. Le `#` ouvre un commentaire (il peut donc porter
    la citation du GO). Les lignes vides et les commentaires sont ignores.
    """
    entries: list[str] = []
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        entries.append(line)
    return entries


def load_allowlist(path: Path) -> list[str]:
    """Charge la liste d'autorisation. Leve si le fichier est illisible."""
    if not path.is_file():
        raise OSError(f"liste d'autorisation introuvable : {path}")
    return parse_allowlist(path.read_text(encoding="utf-8"))


# --- lecture du diff ---------------------------------------------------------

def changed_paths(diff_range: str, root: str = SERIES_ROOT,
                  cwd: Path | None = None) -> list[str]:
    """Chemins AJOUTES ou RENOMMES dans le range donne, sous `root`.

    Le filtre `AR` ecarte les modifications et les suppressions : une serie
    qui perd un fichier n'ouvre pas de dossier. Un renommage est compte par
    son chemin NOUVEAU (c'est la destination qui compte).

    `cwd` designe le depot ou le diff est lu (le repertoire courant par
    defaut) : il rend l'organe testable sur un depot jetable.
    """
    proc = subprocess.run(
        ["git", "diff", "--name-only", "-z", "--diff-filter=AR",
         diff_range, "--", f"{root}/"],
        capture_output=True, cwd=str(cwd) if cwd else None,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"git diff {diff_range} en echec : "
            f"{proc.stderr.decode('utf-8', errors='replace').strip()}")
    return [p for p in proc.stdout.decode("utf-8").split("\0") if p]


def top_level_series(paths: list[str], root: str = SERIES_ROOT) -> set[str]:
    """Dossiers de premier niveau touches par les chemins donnes.

    `MyIA.AI.Notebooks/GenAI/Image/x.ipynb` -> `GenAI`.
    Un fichier pose directement sous la racine (`MyIA.AI.Notebooks/x.ipynb`)
    n'appartient a aucun dossier de premier niveau : il n'est pas concerne
    (le critere porte sur les DOSSIERS).
    """
    prefix = f"{root}/"
    found: set[str] = set()
    for path in paths:
        if not path.startswith(prefix):
            continue
        rest = path[len(prefix):]
        head, _, _tail = rest.partition("/")
        if head and head != rest:
            found.add(head)
    return found


# --- controle ----------------------------------------------------------------

def find_new_series(paths: list[str], allowed: list[str],
                    root: str = SERIES_ROOT) -> list[str]:
    """Dossiers de premier niveau touches par le diff et NON autorises."""
    allowed_set = set(allowed)
    return sorted(top_level_series(paths, root) - allowed_set)


def check(diff_range: str, allowlist_path: Path,
          root: str = SERIES_ROOT, cwd: Path | None = None) -> tuple[int, dict]:
    """Controle complet. Retourne (rc, rapport)."""
    try:
        allowed = load_allowlist(allowlist_path)
    except OSError as exc:
        return 2, {"error": str(exc), "new_series": [], "allowed": []}

    try:
        paths = changed_paths(diff_range, root, cwd)
    except RuntimeError as exc:
        return 2, {"error": str(exc), "new_series": [], "allowed": allowed}

    new_series = find_new_series(paths, allowed, root)
    return (1 if new_series else 0), {
        "diff_range": diff_range,
        "allowed": allowed,
        "changed": paths,
        "new_series": new_series,
        "go_issue": GO_ISSUE,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Garde des dossiers de premier niveau sous MyIA.AI.Notebooks/ "
                    "(#27141)")
    parser.add_argument("--diff", default="origin/main...HEAD", metavar="RANGE",
                        help="range git a inspecter (ex : origin/main...HEAD)")
    parser.add_argument("--allowlist", default=str(DEFAULT_ALLOWLIST),
                        help="fichier de liste d'autorisation")
    parser.add_argument("--root", default=SERIES_ROOT,
                        help="racine des series (defaut : MyIA.AI.Notebooks)")
    parser.add_argument("--repo-root", default=".",
                        help="depot ou le diff est lu (defaut : repertoire courant)")
    parser.add_argument("--json", action="store_true",
                        help="sortie structuree (JSON)")
    args = parser.parse_args(argv)

    rc, report = check(args.diff, Path(args.allowlist), args.root,
                       Path(args.repo_root))

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return rc

    if rc == 2:
        print(f"[toplevel-series] INSTRUMENT EN PANNE : {report['error']}",
              file=sys.stderr)
        return 2

    if rc == 1:
        print("[toplevel-series] dossier(s) de premier niveau AJOUTE(S) sans "
              "autorisation :")
        for name in report["new_series"]:
            print(f"   - MyIA.AI.Notebooks/{name}/")
        print(f"   Un dossier de premier niveau n'ouvre pas sans GO ecrit du "
              f"mainteneur ({GO_ISSUE}).")
        print("   Deux voies : ranger la serie dans un rayon/hub existant, ou "
              "ajouter le dossier a la liste d'autorisation")
        print("   (scripts/ci/toplevel_series_allowlist.txt) en citant le GO.")
        return 1

    print(f"[toplevel-series] aucun dossier de premier niveau ajoute "
          f"({len(report['allowed'])} autorise(s))")
    return 0


if __name__ == "__main__":
    sys.exit(main())
