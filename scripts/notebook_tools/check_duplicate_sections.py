#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Garde des sections dupliquees par accretion.

Le defaut
---------
La campagne de densification #13410 ajoute une section a chaque tranche **sans
consolider celle qui existe deja**. Le notebook finit par porter le meme titre
plusieurs fois au meme endroit de sa hierarchie : ``SW-4-CSharp-SPARQL.ipynb``
porte « Resume » deux fois, cellules 60 et 61, **collees l'une a l'autre**.

Aucun organe ne le voyait. La famille des ratchets de sortie mesure ce que les
cellules PRODUISENT ; ``check_density_anchor.py`` mesure le RATTACHEMENT d'une
lecture a son ancre. Un titre en double ne casse ni l'un ni l'autre : le
notebook s'execute proprement de bout en bout, tous ses ``execution_count``
sont reels, et il reste illisible. Mesure du 2026-09-21 : ``DecPyMC-9`` portait
11 titres d'interpretation identiques en etant classe ``A_ALL_EXEC_OK``,
``reproducibility: EXECUTED``, ``cells_without_outputs: 0`` au catalogue
genere.

Le discriminant hierarchique
----------------------------
Un titre repete n'est PAS un defaut en soi. Un notebook a cinq exercices ecrit
legitimement « Objectif » cinq fois -- une fois sous **chaque** exercice. Ce
qui n'est jamais legitime, c'est le meme titre repete sous le **meme parent** :
la section qui suit n'est alors pas une nouvelle instance d'un gabarit, c'est
une seconde redaction de la meme chose.

Cet organe ne compte donc que les repetitions a parent identique. Sur le corpus
au 2026-09-21 le discriminant ramene 274 notebooks a 80, et 1100 titres en trop
a 274 : les 194 notebooks ecartes sont des gabarits par exercice, pas des
accretions.

Usage :

    # sur des fichiers locaux
    python scripts/notebook_tools/check_duplicate_sections.py notebook.ipynb ...

    # balayage d'un repertoire
    python scripts/notebook_tools/check_duplicate_sections.py MyIA.AI.Notebooks

    # sur une PR : cliquet, ne rougit que si la PR AGGRAVE le compte
    python scripts/notebook_tools/check_duplicate_sections.py --pr 17100

    # sortie machine
    python scripts/notebook_tools/check_duplicate_sections.py --pr 17100 --json

Code de sortie : 0 si aucune accretion (ou, en mode ``--pr``, aucune
aggravation), 1 si une accretion est mesuree, **2 si un notebook n'a pas pu
etre lu** -- une mesure impossible n'est pas une mesure a zero. Un appelant qui
branche sur ``rc == 1`` doit traiter le 2 comme un refus, jamais comme un vert.
"""
from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys

# L'infrastructure de lecture d'une PR est celle de l'organe frere : meme
# plafond `contents` a 1 Mo, meme rattrapage par l'API blobs. La dupliquer ici
# ferait deux implementations a corriger au prochain piege d'API.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_density_anchor import _run, cells_at_ref  # noqa: E402

# Titre ATX en debut de ligne. Les formes en conteneur (« - # Indice : ... »)
# sont exclues volontairement : elles relevent de `fix_hint_headings.py`, qui
# les repare comme un defaut de RENDU, pas comme une section.
HEADING = re.compile(r"^\s{0,3}(#{1,6})\s+(.+?)\s*#*\s*$")


def normalize(title: str) -> str:
    """Titre compare a l'emphase et aux espaces pres.

    « **Resume** » et « Resume » sont la meme section : la seconde redaction
    reprend rarement la graisse de la premiere.
    """
    return re.sub(r"\s+", " ", re.sub(r"[*_`]", "", title)).strip()


def headings(cells: list[dict]) -> list[tuple[int, str, int]]:
    """(niveau, titre normalise, index de cellule) pour chaque titre markdown."""
    found = []
    for index, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        source = cell.get("source", "")
        if isinstance(source, list):
            source = "".join(source)
        for line in source.split("\n"):
            match = HEADING.match(line)
            if match:
                found.append((len(match.group(1)), normalize(match.group(2)), index))
    return found


def accretions(cells: list[dict]) -> list[dict]:
    """Titres repetes sous un parent identique, du plus repete au moins repete.

    Le parent d'un titre est la pile des titres de niveau strictement inferieur
    encore ouverts -- la meme notion de section qu'un lecteur voit dans le
    sommaire.
    """
    stack: list[tuple[int, str]] = []
    keyed: list[tuple[tuple[str, ...], int, str, int]] = []
    for level, title, cell in headings(cells):
        while stack and stack[-1][0] >= level:
            stack.pop()
        keyed.append((tuple(t for _, t in stack), level, title, cell))
        stack.append((level, title))

    cells_of: dict[tuple, list[int]] = collections.defaultdict(list)
    for parent, level, title, cell in keyed:
        cells_of[(parent, level, title)].append(cell)

    found = []
    for (parent, level, title), where in cells_of.items():
        if len(where) > 1:
            found.append({
                "title": title,
                "level": level,
                "count": len(where),
                "excess": len(where) - 1,
                "cells": where,
                "parent": list(parent),
            })
    return sorted(found, key=lambda f: (-f["excess"], f["title"]))


def excess_of(cells: list[dict]) -> int:
    """Nombre total de sections en trop d'un notebook."""
    return sum(f["excess"] for f in accretions(cells))


def walk(root: str):
    """Notebooks du corpus sous `root`, worktrees et artefacts exclus."""
    skip = (".claude/worktrees", "_output", "/.ipynb_checkpoints", "/_archive",
            "/node_modules", "/.git/")
    for dirpath, dirnames, filenames in os.walk(root):
        if any(s in dirpath.replace("\\", "/") for s in skip):
            dirnames[:] = []
            continue
        for name in sorted(filenames):
            if name.endswith(".ipynb") and not name.endswith("_output.ipynb"):
                yield os.path.join(dirpath, name).replace("\\", "/")


def _local(path: str) -> dict:
    try:
        with open(path, encoding="utf-8") as handle:
            cells = json.load(handle)["cells"]
    except (OSError, ValueError, KeyError) as exc:
        return {"path": path, "error": str(exc)[:160]}
    return {"path": path, "findings": accretions(cells)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("paths", nargs="*", help="fichiers .ipynb ou repertoires")
    parser.add_argument("--pr", type=int,
                        help="numero de PR : cliquet, ne rougit que sur aggravation")
    parser.add_argument("--repo", default="jsboige/CoursIA")
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(argv)

    if not args.paths and args.pr is None:
        parser.error("donner des notebooks, un repertoire, ou --pr")

    results = []

    if args.pr is not None:
        meta = json.loads(_run(["gh", "pr", "view", str(args.pr), "-R", args.repo,
                                "--json", "headRefOid,baseRefOid,files"]))
        for entry in meta["files"]:
            path = entry["path"]
            if not path.endswith(".ipynb"):
                continue
            head = cells_at_ref(args.repo, path, meta["headRefOid"])
            if head is None:
                results.append({"path": path,
                                "error": "notebook illisible au head "
                                         "(blob non servi par contents ni blobs)"})
                continue
            base_cells = cells_at_ref(args.repo, path, meta["baseRefOid"])
            base = excess_of(base_cells) if base_cells else 0
            head_excess = excess_of(head)
            results.append({
                "path": path, "base_excess": base, "head_excess": head_excess,
                "regressed": head_excess > base,
                "findings": accretions(head) if head_excess > base else [],
            })

    for path in args.paths:
        if os.path.isdir(path):
            results.extend(_local(p) for p in walk(path))
        else:
            results.append(_local(path))

    # Un notebook illisible est un refus de mesurer, pas une mesure a zero :
    # le rendre vert ferait passer pour sain ce que l'organe n'a pas ouvert.
    unreadable = [r for r in results if "error" in r]
    if args.pr is not None:
        failed = any(r.get("regressed") for r in results)
    else:
        failed = any(r.get("findings") for r in results)

    if args.as_json:
        print(json.dumps({"ok": not failed and not unreadable, "results": results},
                         ensure_ascii=False, indent=2))
        return 2 if unreadable else (1 if failed else 0)

    carriers = 0
    for result in results:
        name = os.path.basename(result["path"])
        if "error" in result:
            print("??  %s : %s" % (name, result["error"]))
            continue
        if args.pr is not None:
            verdict = "!!" if result["regressed"] else "OK"
            print("%s  %-58s %d -> %d" % (verdict, name,
                                          result["base_excess"], result["head_excess"]))
        if not result.get("findings"):
            continue
        carriers += 1
        if args.pr is None:
            print("!!  %s  (%d section(s) en trop)"
                  % (result["path"], sum(f["excess"] for f in result["findings"])))
        for finding in result["findings"]:
            parent = finding["parent"][-1] if finding["parent"] else "(racine)"
            print("      x%d  h%d  %-46s  sous : %s"
                  % (finding["count"], finding["level"],
                     finding["title"][:46], parent[:44]))

    if failed and args.pr is None:
        readable = sum(1 for r in results if "error" not in r)
        print("\n%d notebook(s) sur %d portent une section ecrite deux fois au MEME"
              " endroit\nde leur hierarchie. Consolider les deux redactions, ou"
              " retitrer chacune\npour ce qu'elle lit -- ne pas supprimer la"
              " seconde a l'aveugle." % (carriers, readable))
    elif failed:
        print("\nLa PR AJOUTE des sections dupliquees. Le cliquet ne juge que le"
              " delta :\nles doublons deja presents sur la base ne lui sont pas"
              " imputes.")

    if unreadable:
        print("\n%d notebook(s) n'ont pas pu etre lus : leur etat est INCONNU,"
              " pas sain." % len(unreadable))
        return 2

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
