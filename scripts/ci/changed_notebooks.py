#!/usr/bin/env python3
"""Portee de la validation notebook : carnets modifies, pas l'arbre entier (#22468 tranche 2).

Mesure de l'issue (levier 6 de l'audit CI #22461) : la suite
`notebook-validation` parcourt tout l'arbre — 1 750 carnets — a chaque PR
qui touche UN carnet, soit 3 175 minutes-slot sur 48 h (5,3 % du CI),
alors que les carnets non modifies ont deja leur verdict vert sur main.

## Ce que cet organe rend

Un JSON sur stdout : ``{"mode": "restricted"|"full", "notebooks": [...],
"reason": "..."}``. La raison est toujours nommee — un repli muet vers la
pleine arbre annulerait le gain sans laisser de trace lisible.

## Contrat : fail-OPEN vers la pleine arbre

Toute incertitude rend la **pleine arbre** : lecteur de diff en echec, PR
introuvable, liste vide, carnet liste absent de l'arbre. Se tromper dans ce
sens coute du calcul ; se tromper dans l'autre valide moins que declenche.
Le cas particulier « portee restreinte vide » retombe aussi sur la pleine
arbre : c'est ce qui PRESERVE la garde anti-checkout-incomplet #14799 — un
workspace casse rend zero .ipynb par le find de la pleine arbre, et la
boucle aval fait toujours son erreur explicite sur NB_COUNT == 0.

## `workflow_dispatch` reste pleine arbre (intentionnel)

Le declencheur manuel existe PRECISEMENT pour revalider l'arbre final
apres un lot de fusions (#13861) : `cancel-in-progress` laisse le dernier
etat d'un batch non revalide. Restreindre ce mode casserait sa raison
d'etre.

## Organ-first : lecteurs herites de #22548

Les lecteurs de chemins modifies viennent de l'organe
`codeql_changed_languages` (issue #22548), qui a resolu le meme probleme
en CI : **diff local primaire** (`git diff HEAD^1 HEAD` sur le checkout
`fetch-depth: 2` du commit de fusion de la PR — sans reseau ni quota,
apres la mesure du 2026-10-25 : l'API en primaire tombait sur le quota
partage de l'installation), **API en repli** (paginee, echec si tronquee).
Ils ne sont pas dupliques ici.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Callable

try:
    from codeql_changed_languages import (  # type: ignore[attr-defined]
        _api_pr_paths,
        _describe,
        _local_diff_paths,
    )
except ImportError:  # chargement par spec_from_file_location (tests)
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from codeql_changed_languages import (  # noqa: E402
        _api_pr_paths,
        _describe,
        _local_diff_paths,
    )

Reader = Callable[[str], list[str]]


def is_notebook(path: str) -> bool:
    """Carnet eligible : extension .ipynb, hors checkpoints Jupyter."""
    norm = path.replace("\\", "/")
    return norm.endswith(".ipynb") and ".ipynb_checkpoints/" not in norm


def existing_notebooks(paths: list[str], root: str = ".") -> list[str]:
    """Filtre les carnes du diff qui existent dans l'arbre (un carnet
    supprime par la PR n'a rien a valider ; son chemin disparait ici)."""
    base = Path(root)
    return sorted({p for p in paths if is_notebook(p) and (base / p).is_file()})


def full_tree(root: str = ".") -> list[str]:
    """L'arbre entier — l'ancienne portee, et le repli de toute incertitude."""
    base = Path(root)
    out: list[str] = []
    for path in base.rglob("*.ipynb"):
        rel = path.relative_to(base).as_posix()
        if "/." in "/" + rel or rel.startswith(".") or ".ipynb_checkpoints/" in rel:
            continue
        if path.is_file():
            out.append(rel)
    return sorted(out)


def scope(
    event: str,
    repo: str = "",
    pr_number: int = 0,
    token: str | None = None,
    readers: list[tuple[str, Reader]] | None = None,
    tree_root: str = ".",
) -> tuple[str, list[str], str]:
    """Rend (mode, notebooks, raison). Fail-OPEN : pleine arbre en cas de doute.

    ``readers`` chaine les lecteurs de diff (etiquette, lecteur) pour les
    tests ; en production, PR = diff local puis API, push = diff HEAD~1.
    """
    if event == "workflow_dispatch":
        return "full", full_tree(tree_root), (
            "workflow_dispatch : revalidation complete apres batch (#13861)"
        )
    if event not in ("pull_request", "push"):
        return "full", full_tree(tree_root), (
            f"evenement {event or '?'} non restreint : pleine arbre"
        )

    paths: list[str] | None = None
    source = ""
    failures: list[str] = []
    if event == "pull_request":
        chain = readers or [
            ("diff HEAD^1", lambda _base: _local_diff_paths("HEAD^1")),
            ("api", lambda _base: _api_pr_paths(repo, pr_number, token)),
        ]
    else:
        chain = readers or [("diff HEAD~1", lambda _base: _local_diff_paths("HEAD~1"))]
    for label, reader in chain:
        try:
            paths = reader("HEAD^1" if event == "pull_request" else "HEAD~1")
        except Exception as exc:  # noqa: BLE001 - fail-open documente en tete
            failures.append(f"{label}: {_describe(exc)}")
            continue
        source = label
        break

    if paths is None:
        return "full", full_tree(tree_root), (
            "portee illisible (" + "; ".join(failures) + ") : pleine arbre"
        )
    notebooks = existing_notebooks(paths, root=tree_root)
    if not notebooks:
        return "full", full_tree(tree_root), (
            "aucun carnet modifie present dans l'arbre : pleine arbre"
        )
    return "restricted", notebooks, (
        f"{len(notebooks)} carnet(s) modifie(s) [source {source}]"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--event", default="",
                        help="github.event_name (pull_request, push, workflow_dispatch...)")
    parser.add_argument("--repo", default="",
                        help="owner/repo — pour le repli API (PR)")
    parser.add_argument("--pr", type=int, default=0,
                        help="numero de PR — pour le repli API")
    parser.add_argument("--token", default=None,
                        help="jeton API (GITHUB_TOKEN du runner)")
    args = parser.parse_args(argv)

    mode, notebooks, reason = scope(
        args.event, repo=args.repo, pr_number=args.pr, token=args.token
    )
    print(reason, file=sys.stderr)
    json.dump({"mode": mode, "notebooks": notebooks, "reason": reason},
              sys.stdout, indent=1)
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
