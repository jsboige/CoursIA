#!/usr/bin/env python3
"""Retire les cles interdites des cellules markdown des carnets (issue #20167).

Au schema nbformat, une cellule ``markdown`` ne porte que ``cell_type``,
``id``, ``metadata``, ``source`` et ``attachments``. Des carnets du depot
portent pourtant ``execution_count`` et/ou ``outputs`` sur une cellule
markdown : artefact de conversion d'une cellule de code. Le MCP
``jupyter-papermill`` valide le carnet ENTIER avant d'ecrire et refuse alors
toute edition, meme d'une cellule saine.

Perimetre strict : seules ces deux cles, et seulement sur les cellules
``markdown``, sont retirees. Aucune ``source`` ni aucune sortie de cellule
``code`` n'est modifiee : aucune re-execution n'est due (C.2).

Serialisation a l'octet pres : le format du fichier est DETECTE par identite.
Un format n'est retenu que s'il reproduit EXACTEMENT les octets lus
(indentation, ``ensure_ascii``, ordre des cles, saut de ligne final). Le
carnet est alors reecrit dans ce format, et les seules differences sont les
cles retirees. Un fichier qu'aucun format candidat ne reproduit (espaces de
mise en forme parasites, escapes mixtes) est une EXCEPTION : il n'est jamais
reecrit, il est rapporte. ``--roundtrip`` mesure cette identite sur le corpus.

Modes :
    (defaut)        dry-run : liste carnet, cellules et cles, sans ecrire
    --apply         reecrit les carnets fautifs dont le format est reproductible
    --check         exit 1 si une cellule fautive existe dans les fichiers donnes
    --all           balaye MyIA.AI.Notebooks/ (exclusions habituelles)
    --roundtrip     mesure l'aller-retour octet a octet (compte, exceptions)
    --paths-only    n'imprime que les chemins fautifs (construction de lot)
    --list FICHIER  prend les chemins depuis un fichier (un par ligne, relatifs
                    a la racine du depot)

Codes de sortie :
    --check      0 propre, 1 au moins une cellule fautive, 2 fichier illisible
    --apply      0 tout corrige, 1 exception(s) non reecrite(s), 2 illisible(s)
    dry-run, --roundtrip : 0 (mesure)

Exemples :
    python scripts/notebook_tools/fix_markdown_cell_schema.py --all
    python scripts/notebook_tools/fix_markdown_cell_schema.py --all --paths-only > lot.txt
    python scripts/notebook_tools/fix_markdown_cell_schema.py --apply --list lot.txt
    python scripts/notebook_tools/fix_markdown_cell_schema.py --check <carnet> [...]
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
from collections import Counter
from pathlib import Path
from typing import NamedTuple, Optional

REPO_ROOT = Path(__file__).resolve().parents[2]
NOTEBOOKS_ROOT = REPO_ROOT / "MyIA.AI.Notebooks"

#: Cles que le schema nbformat interdit sur une cellule markdown.
FORBIDDEN_MARKDOWN_KEYS = ("execution_count", "outputs")

#: Fragments de chemin exclus du balayage ``--all`` (exclusions habituelles).
EXCLUDED_FRAGMENTS = (
    ".lake/", "_output", "checkpoints", "node_modules", "_archive/", "_site/",
)

#: Formats candidats : (indent, ensure_ascii, sort_keys, fin_de_fichier).
#: Le premier format qui reproduit les octets est retenu. Deux formats qui les
#: reproduisent donnent le meme rendu une fois les cles retirees.
_FORMATS = tuple(
    (indent, ensure_ascii, sort_keys, suffix)
    for indent in (1, 2, 4, None)
    for ensure_ascii in (False, True)
    for sort_keys in (True, False)
    for suffix in ("\n", "")
)


class Defect(NamedTuple):
    """Une cellule markdown fautive : index dans ``cells`` et cles interdites."""

    index: int
    keys: tuple


def load_notebook(path: Path) -> tuple[str, dict]:
    """Lit les octets, decode en UTF-8 strict, parse. Leve OSError ou ValueError."""
    text = path.read_bytes().decode("utf-8")
    nb = json.loads(text)
    if not isinstance(nb, dict):
        raise ValueError("racine JSON non objet")
    return text, nb


def find_defects(nb: dict) -> list[Defect]:
    """Cellules markdown portant une cle interdite (``execution_count``/``outputs``)."""
    defects: list[Defect] = []
    cells = nb.get("cells")
    if not isinstance(cells, list):
        return defects
    for index, cell in enumerate(cells):
        if isinstance(cell, dict) and cell.get("cell_type") == "markdown":
            keys = tuple(k for k in FORBIDDEN_MARKDOWN_KEYS if k in cell)
            if keys:
                defects.append(Defect(index, keys))
    return defects


def strip_markdown_keys(nb: dict) -> dict:
    """Copie du carnet sans ``execution_count``/``outputs`` sur les cellules markdown."""
    fixed = copy.deepcopy(nb)
    for cell in fixed.get("cells", []):
        if isinstance(cell, dict) and cell.get("cell_type") == "markdown":
            for key in FORBIDDEN_MARKDOWN_KEYS:
                cell.pop(key, None)
    return fixed


def render(nb: dict, fmt: tuple) -> str:
    """Serialise ``nb`` dans le format ``fmt``."""
    indent, ensure_ascii, sort_keys, suffix = fmt
    return json.dumps(nb, indent=indent, ensure_ascii=ensure_ascii, sort_keys=sort_keys) + suffix


def detect_format(text: str, nb: dict) -> Optional[tuple]:
    """Premier format candidat qui reproduit EXACTEMENT ``text``, ou None (exception)."""
    for fmt in _FORMATS:
        if render(nb, fmt) == text:
            return fmt
    return None


def plan_fix(text: str, nb: dict) -> tuple[Optional[str], str]:
    """Calcule le texte corrige. Retourne (texte, "") ou (None, motif d'exception)."""
    fmt = detect_format(text, nb)
    if fmt is None:
        return None, "format non reproductible (espaces de mise en forme ou escapes mixtes)"
    fixed = strip_markdown_keys(nb)
    new_text = render(fixed, fmt)
    # Garde : le texte produit se relit comme le carnet nettoye, sans defaut.
    if json.loads(new_text) != fixed or find_defects(fixed):
        return None, "verification post-ecriture echouee"
    return new_text, ""


def iter_notebooks(notebooks_root: Path, repo_root: Path = REPO_ROOT):
    """Carnets sous ``notebooks_root``, hors exclusions habituelles, triés."""
    for path in sorted(notebooks_root.rglob("*.ipynb")):
        rel = path.relative_to(repo_root).as_posix()
        if any(fragment in rel for fragment in EXCLUDED_FRAGMENTS):
            continue
        yield path


def _display(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return str(path)


def _analyse(path: Path):
    """Charge et classe un carnet. Retourne (statut, text, nb, defects, erreur)."""
    try:
        text, nb = load_notebook(path)
    except (OSError, ValueError) as exc:
        return "illisible", None, None, (), f"{type(exc).__name__}: {exc}"
    defects = tuple(find_defects(nb))
    return ("fautif" if defects else "propre"), text, nb, defects, ""


def _keys_label(defects) -> str:
    keys: list[str] = []
    for defect in defects:
        for key in defect.keys:
            if key not in keys:
                keys.append(key)
    return ", ".join(keys)


def _cells_label(defects) -> str:
    return ", ".join(str(d.index) for d in defects)


def _collect_targets(args, parser) -> list[Path]:
    targets: list[Path] = []
    if args.all:
        targets.extend(iter_notebooks(NOTEBOOKS_ROOT))
    if args.list:
        for line in Path(args.list).read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if line and not line.startswith("#"):
                targets.append(REPO_ROOT / line)
    targets.extend(Path(p) for p in args.paths)
    if not targets:
        parser.error("aucun carnet : passer des chemins, --list FICHIER ou --all")
    # Dedoublonnage en conservant l'ordre.
    return list(dict.fromkeys(targets))


def cmd_check(targets) -> int:
    fautifs = illisibles = 0
    for path in targets:
        status, _, _, defects, error = _analyse(path)
        if status == "illisible":
            illisibles += 1
            print(f"[ILLISIBLE] {_display(path)} : {error}")
        elif status == "fautif":
            fautifs += 1
            print(f"[FAUTIF] {_display(path)} : cellules {_cells_label(defects)} "
                  f"; cles {_keys_label(defects)}")
    print(f"Bilan --check : {fautifs} carnet(s) fautif(s), {illisibles} illisible(s), "
          f"sur {len(targets)} examine(s).")
    if fautifs:
        return 1
    return 2 if illisibles else 0


def cmd_dry_run(targets, paths_only: bool) -> int:
    counts: Counter = Counter()
    for path in targets:
        status, text, nb, defects, error = _analyse(path)
        if status == "illisible":
            counts["illisible"] += 1
            if not paths_only:
                print(f"[ILLISIBLE] {_display(path)} : {error}")
            continue
        if status == "propre":
            counts["propre"] += 1
            continue
        counts["fautif"] += 1
        counts["cellules"] += len(defects)
        if paths_only:
            print(_display(path))
            continue
        if detect_format(text, nb) is None:
            counts["exception"] += 1
            reecriture = "EXCEPTION (format non reproductible, non reecrit)"
        else:
            counts["reecrivable"] += 1
            reecriture = "reecriture possible"
        print(f"[FAUTIF] {_display(path)} : cellules {_cells_label(defects)} "
              f"; cles {_keys_label(defects)} ; {reecriture}")
    if not paths_only:
        print(f"Bilan dry-run : {counts['fautif']} carnet(s) fautif(s), "
              f"{counts['cellules']} cellule(s) markdown fautive(s), "
              f"{counts['reecrivable']} reecrivable(s), {counts['exception']} exception(s), "
              f"{counts['propre']} propre(s), {counts['illisible']} illisible(s).")
    return 0


def cmd_apply(targets) -> int:
    reecrits = exceptions = illisibles = cellules = 0
    for path in targets:
        status, text, nb, defects, error = _analyse(path)
        if status == "illisible":
            illisibles += 1
            print(f"[ILLISIBLE] {_display(path)} : {error}")
            continue
        if status == "propre":
            continue
        new_text, motif = plan_fix(text, nb)
        if new_text is None:
            exceptions += 1
            print(f"[EXCEPTION] {_display(path)} : {motif} -- non reecrit")
            continue
        path.write_bytes(new_text.encode("utf-8"))
        if path.read_bytes().decode("utf-8") != new_text:
            raise RuntimeError(f"relecture divergente apres ecriture : {_display(path)}")
        reecrits += 1
        cellules += len(defects)
        print(f"[REECRIT] {_display(path)} : {len(defects)} cellule(s) markdown "
              f"(cellules {_cells_label(defects)}) ; cles {_keys_label(defects)}")
    print(f"Bilan --apply : {reecrits} carnet(s) reecrit(s), {cellules} cellule(s) nettoyee(s), "
          f"{exceptions} exception(s), {illisibles} illisible(s).")
    if exceptions:
        return 1
    return 2 if illisibles else 0


def cmd_roundtrip(targets) -> int:
    """Aller-retour octet a octet : le format detecte reproduit-il le fichier ?"""
    by_class: dict[str, Counter] = {"propre": Counter(), "fautif": Counter()}
    exceptions: list[tuple[str, str]] = []
    illisibles: list[str] = []
    formats: Counter = Counter()
    for path in targets:
        status, text, nb, _, error = _analyse(path)
        if status == "illisible":
            illisibles.append(f"{_display(path)} : {error}")
            continue
        bucket = by_class[status]
        bucket["total"] += 1
        fmt = detect_format(text, nb)
        if fmt is None:
            bucket["exception"] += 1
            exceptions.append((_display(path), status))
        else:
            bucket["identique"] += 1
            formats[fmt] += 1
    for status, label in (("propre", "carnets sans defaut"), ("fautif", "carnets fautifs")):
        b = by_class[status]
        print(f"Aller-retour octet a octet, {label} : {b['identique']}/{b['total']} identiques, "
              f"{b['exception']} exception(s).")
    print("Formats detectes (indent, ensure_ascii, sort_keys, fin de fichier) :")
    for fmt, count in formats.most_common():
        print(f"  {fmt} : {count}")
    for name, status in exceptions:
        print(f"[EXCEPTION:{status}] {name}")
    for line in illisibles:
        print(f"[ILLISIBLE] {line}")
    return 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Retire execution_count/outputs des cellules markdown (#20167).",
    )
    parser.add_argument("paths", nargs="*", help="carnets a examiner (chemin depuis le cwd)")
    parser.add_argument("--all", action="store_true", help="balaye MyIA.AI.Notebooks/")
    parser.add_argument("--list", metavar="FICHIER",
                        help="chemins de carnets, un par ligne, relatifs a la racine du depot")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--apply", action="store_true", help="reecrit les carnets fautifs")
    mode.add_argument("--check", action="store_true",
                      help="exit 1 si une cellule markdown fautive existe")
    mode.add_argument("--roundtrip", action="store_true",
                      help="mesure l'aller-retour octet a octet sur les cibles")
    parser.add_argument("--paths-only", action="store_true",
                        help="dry-run : n'imprime que les chemins fautifs")
    args = parser.parse_args(argv)

    targets = _collect_targets(args, parser)
    if args.check:
        return cmd_check(targets)
    if args.apply:
        return cmd_apply(targets)
    if args.roundtrip:
        return cmd_roundtrip(targets)
    return cmd_dry_run(targets, args.paths_only)


if __name__ == "__main__":
    sys.exit(main())
