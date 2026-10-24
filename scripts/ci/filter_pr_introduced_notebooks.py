"""Filtre « introduit par la PR » pour la liste de carnets d'un gate.

Motif (#22298).  Un gate qui calcule ses carnets contre la **branche de base**
d'une PR empilee audite tout ce que cette base n'a pas encore vu de `main` :
sur #21650, `git diff --name-status -M BASE...HEAD` rend **287** carnets alors
que la PR n'en touche qu'**un**, et trois findings `MD_REWRITE` deja merges sur
`main` sont attribues a la PR.

Le critere retenu est l'**auteur** du changement, pas la fraicheur d'une ref :
un carnet n'est « introduit par la PR » que si un commit **propre a la PR** l'a
touche, c'est-a-dire un commit de `BASE..HEAD` qui n'est pas atteignable depuis
`main`.  Comparer les blobs a `main` ne suffit pas -- mesure sur #21650 :
287 -> 34 seulement, parce qu'un carnet que `main` a modifie **apres** le fork
differe aussi de la tete, sans que la PR l'ait ecrit.

Les commits de **merge** comptent, mais pour ce qu'ils ecrivent eux-memes : une
resolution de conflit -- ou une edition faite pendant le merge -- n'existe chez
aucun parent, et la sauter retirerait du gate un carnet que la PR a bel et bien
ecrit (faux negatif releve par l'adjoint sur #22302).  Ce que le merge a
seulement **transporte** depuis un parent n'est pas attribue a la PR : voir
`_changed_paths`.

Le filtre est **transparent** : il lit la sortie de `git diff --name-status -M`
sur stdin et ecrit les lignes conservees, dans le meme ordre et au meme format
TAB-separe.  Il est **fail-open** : si l'ensemble des chemins propres a la PR
n'est pas determinable (ref illisible, aucun commit propre), **tout est
conserve** -- le gate garde exactement son comportement d'origine plutot que de
s'eteindre.

Usage :

    git diff --name-status -M "$BASE"...HEAD -- 'MyIA.AI.Notebooks/**/*.ipynb' \
      | python scripts/ci/filter_pr_introduced_notebooks.py \
          --base "$BASE" --main-ref origin/main --head-ref HEAD --stats

Sortie : les lignes conservees sur stdout (vide si tout est retire), un
`::notice` de synthese sur stderr quand `--stats` est passe.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from typing import Iterable

# Une ligne `--name-status -M` : "M<TAB>chemin" ou "R100<TAB>ancien<TAB>nouveau".
Row = tuple[str, str, str]


def parse_rows(text: str) -> list[Row]:
    """Decoupe une sortie `--name-status -M` en triplets (statut, base, tete).

    La troisieme colonne est vide pour un statut non-renomme : l'appelant la
    remplace par le chemin de base, comme le fait deja le workflow.
    """
    rows: list[Row] = []
    for line in text.splitlines():
        line = line.rstrip("\r")
        if not line.strip():
            continue
        parts = line.split("\t")
        status = parts[0].strip()
        base = parts[1] if len(parts) > 1 else ""
        head = parts[2] if len(parts) > 2 and parts[2] else base
        if not base:
            continue
        rows.append((status, base, head))
    return rows


def _head_path(row: Row) -> str:
    status, base, head = row
    return head or base


def filter_rows(
    rows: Iterable[Row],
    owned_paths: "set[str] | None",
) -> tuple[list[Row], list[tuple[Row, str]]]:
    """Retire les lignes dont le carnet n'a ete touche par aucun commit de la PR.

    `owned_paths=None` signifie « non determinable » : rien n'est retire
    (fail-open).  Une suppression (`D`) traverse le filtre : la sauter est le
    role du workflow, et la retirer ici masquerait une difference de contrat
    entre les deux etages.
    """
    kept: list[Row] = []
    dropped: list[tuple[Row, str]] = []
    for row in rows:
        if owned_paths is None or row[0].startswith("D"):
            kept.append(row)
            continue
        path = _head_path(row)
        if path in owned_paths:
            kept.append(row)
        else:
            dropped.append((row, "aucun commit de la PR ne le touche"))
    return kept, dropped


def render_rows(rows: Iterable[Row]) -> str:
    """Rend les lignes au format `--name-status` d'origine."""
    out: list[str] = []
    for status, base, head in rows:
        if head and head != base:
            out.append(f"{status}\t{base}\t{head}")
        else:
            out.append(f"{status}\t{base}")
    return "\n".join(out)


def _git(*args: str) -> "str | None":
    """Sortie de `git <args>`, ou None si la commande echoue."""
    try:
        proc = subprocess.run(
            ["git", *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
    except OSError:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout


def _changed_paths(sha: str, parents: "list[str]") -> "set[str] | None":
    """Chemins qu'un commit ecrit, commits de merge compris.

    Un commit ordinaire se lit en differentiel de son parent. Un commit de
    merge se lit **contre chacun de ses parents**, et l'ensemble retenu est
    l'**intersection** : un chemin que le merge n'a pas touche est identique a
    au moins un parent (c'est ce que la fusion a transporte), tandis qu'une
    resolution de conflit -- ou une edition faite pendant le merge -- differe
    de **tous** les parents. L'intersection rend donc exactement ce que le
    merge a ecrit lui-meme, et rien de ce qu'il a transporte.

    `git diff-tree` sur un commit de merge rend une sortie **vide** par defaut
    (il faudrait `-m`/`-c`/`--cc`) : ce module ne l'interroge donc jamais nu,
    il differentie contre les parents explicites. Rend None des qu'une lecture
    echoue, pour que l'appelant conserve tout (fail-open).

    Mesure sur la fusion `main` -> branche de #21650 : intersection vide (le
    merge ne fait que transporter) ; sur une resolution de conflit ecrite a la
    main : intersection = le carnet resolu.
    """
    if not parents:
        # Premier commit d'une branche orpheline : `--root` le compare au vide.
        out = _git("diff-tree", "--no-commit-id", "-r", "-M", "--name-status", "--root", sha)
        if out is None:
            return None
        return {_head_path(row) for row in parse_rows(out)}
    per_parent: "list[set[str]]" = []
    for parent in parents:
        out = _git("diff-tree", "-r", "-M", "--name-status", parent, sha)
        if out is None:
            return None
        per_parent.append({_head_path(row) for row in parse_rows(out)})
    return set.intersection(*per_parent)


def pr_owned_paths(
    base_ref: str, head_ref: str, main_ref: str = "origin/main"
) -> "set[str] | None":
    """Chemins touches par un commit propre a la PR (merge compris), absent de main.

    Rend None -- donc « tout conserver » -- des qu'une ref est illisible, qu'un
    differentiel echoue, ou qu'aucun commit propre n'est trouve : un filtre
    fail-open ne peut pas eteindre un gate par accident.
    """
    listed = _git("rev-list", "--parents", f"{base_ref}..{head_ref}", "--not", main_ref)
    if listed is None:
        return None
    history: "list[tuple[str, list[str]]]" = []
    for line in listed.splitlines():
        parts = line.split()
        if parts:
            history.append((parts[0], parts[1:]))
    if not history:
        return None
    owned: set[str] = set()
    for sha, parents in history:
        paths = _changed_paths(sha, parents)
        if paths is None:
            return None
        owned |= paths
    return owned


def main(argv: "list[str] | None" = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--base", required=True, help="ref de base de la PR (BASE)")
    parser.add_argument("--main-ref", default="origin/main")
    parser.add_argument("--head-ref", default="HEAD")
    parser.add_argument(
        "--stats",
        action="store_true",
        help="emit un ::notice de synthese sur stderr (survit a la redirection)",
    )
    args = parser.parse_args(argv)

    rows = parse_rows(sys.stdin.read())
    owned = pr_owned_paths(args.base, args.head_ref, args.main_ref)
    kept, dropped = filter_rows(rows, owned)

    rendered = render_rows(kept)
    if rendered:
        sys.stdout.write(rendered + "\n")

    if args.stats:
        origin = (
            "indeterminable -- tout est conserve (fail-open)"
            if owned is None
            else f"{len(owned)} chemin(s) propre(s) a la PR"
        )
        summary = (
            f"filtre PR-introduit : {len(kept)} carnet(s) conserve(s), "
            f"{len(dropped)} retire(s) ; {origin} ({len(rows)} ligne(s) en entree)"
        )
        sys.stderr.write(f"::notice title=Enrich-quality gate::{summary}\n")
        for (status, base, head), reason in dropped:
            sys.stderr.write(f"  - {head or base} ({status}) : {reason}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
