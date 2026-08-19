#!/usr/bin/env python3
"""Convertit les separateurs horizontaux `---` en `***` dans les cellules markdown.

Pourquoi
--------
Une ligne `---` seule ouvre un bloc de metadonnees YAML au sens Pandoc
(`yaml_metadata_block`), referme par un `---` ou `...` ulterieur. Dans un
notebook, un `---` ecrit comme separateur horizontal en debut de cellule ouvre
un tel bloc ; la prose et les titres des cellules suivantes sont alors lus
comme des paires cle/valeur -> `YAMLException` -> `quarto render` echoue.
Comme Quarto s'arrete au PREMIER echec, un seul notebook fait tomber tout le
site (incident #11451, 2026-08-17).

`***` rend exactement le meme `<hr>` en markdown et n'a aucune semantique YAML.
C'est la conversion appliquee ici.

Ce que l'outil NE touche PAS
----------------------------
- les `---` a l'interieur d'un bloc de code (``` ou ~~~) ;
- les `---` qui SOULIGNENT du texte : un `---` colle a une ligne non vide est
  un titre setext H2, pas un separateur — le convertir changerait le rendu ;
- un VRAI bloc de frontmatter en tete de notebook (cellule 0 commencant par
  `---` dont le contenu parse en mapping YAML) : Quarto s'en sert
  legitimement pour le titre, l'auteur, les options de rendu.

Distinction avec `detect_markdown_rendering.py`
-----------------------------------------------
Ce dernier vise les defauts de rendu VISUEL (bloc surdimensionne a l'ouverture)
cellule par cellule. Le present outil vise l'echec de BUILD Quarto, qui est
CROSS-CELLULE par nature (le `---` ouvrant et le `---` fermant sont dans deux
cellules differentes). Les deux populations se recouvrent sans coincider.

Usage
-----
    python scripts/notebook_tools/fix_hr_separator.py --check MyIA.AI.Notebooks/GameTheory
    python scripts/notebook_tools/fix_hr_separator.py --apply MyIA.AI.Notebooks/GameTheory

Sortie : 0 si rien a convertir (--check) ou conversion faite (--apply),
1 si des separateurs restent a convertir (--check), 2 en cas d'erreur.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

FENCE_RE = re.compile(r"^(`{3,}|~{3,})")
HR = "---"
REPLACEMENT = "***"


def _lines(source) -> list[str]:
    """Rend les lignes d'une source de cellule, quel que soit son encodage nbformat."""
    if isinstance(source, list):
        return "".join(source).split("\n")
    return (source or "").split("\n")


def _is_real_frontmatter(lines: list[str]) -> bool:
    """Vrai si la cellule EST un bloc de frontmatter YAML legitime.

    Forme : premiere ligne `---`, une ligne `---`/`...` de fermeture plus bas,
    et un contenu qui ressemble a des paires cle/valeur (au moins une ligne
    `cle: valeur` et aucune ligne de prose evidente). On reste volontairement
    grossier : en cas de doute on considere que c'en est un et on ne touche pas.
    """
    if not lines or lines[0].strip() != HR:
        return False
    close = None
    for i in range(1, len(lines)):
        if lines[i].strip() in (HR, "..."):
            close = i
            break
    if close is None:
        return False
    body = [x for x in lines[1:close] if x.strip()]
    if not body:
        return False
    return any(re.match(r"^[A-Za-z_][A-Za-z0-9_.-]*\s*:", x) for x in body)


def convert_cell(source, is_first_cell: bool) -> tuple[object, int]:
    """Rend (nouvelle_source, nb_conversions) pour une source de cellule markdown."""
    lines = _lines(source)
    if is_first_cell and _is_real_frontmatter(lines):
        return source, 0

    in_fence = False
    changed = 0
    out: list[str] = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        if FENCE_RE.match(stripped):
            in_fence = not in_fence
            out.append(line)
            continue
        if in_fence or stripped != HR:
            out.append(line)
            continue
        prev = lines[i - 1].strip() if i > 0 else ""
        if prev != "":
            out.append(line)  # soulignement setext : ne pas toucher
            continue
        out.append(line.replace(HR, REPLACEMENT, 1))
        changed += 1

    if not changed:
        return source, 0

    text = "\n".join(out)
    if isinstance(source, list):
        parts = text.split("\n")
        return [p + "\n" for p in parts[:-1]] + ([parts[-1]] if parts[-1] else []), changed
    return text, changed


def process(path: Path, apply: bool) -> int:
    """Rend le nombre de separateurs convertis (ou convertibles si apply=False)."""
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError) as exc:
        print(f"ILLISIBLE {path}: {exc}", file=sys.stderr)
        return 0

    total = 0
    seen_markdown = False
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "markdown":
            continue
        first = not seen_markdown
        seen_markdown = True
        new_source, n = convert_cell(cell.get("source"), first)
        if n:
            total += n
            if apply:
                cell["source"] = new_source

    if total and apply:
        path.write_text(
            json.dumps(nb, ensure_ascii=False, indent=1) + "\n", encoding="utf-8"
        )
    return total


def iter_notebooks(targets: list[str]):
    for t in targets:
        p = Path(t)
        if p.is_dir():
            for nb in sorted(p.rglob("*.ipynb")):
                s = str(nb).replace("\\", "/")
                if "/.ipynb_checkpoints/" in s or s.endswith("_output.ipynb"):
                    continue
                yield nb
        elif p.suffix == ".ipynb":
            yield p


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="ne rien ecrire, compter")
    mode.add_argument("--apply", action="store_true", help="ecrire les conversions")
    ap.add_argument("targets", nargs="+", help="fichiers .ipynb ou repertoires")
    args = ap.parse_args(argv)

    files = 0
    seps = 0
    for nb in iter_notebooks(args.targets):
        n = process(nb, apply=args.apply)
        if n:
            files += 1
            seps += n
            verbe = "converti" if args.apply else "a convertir"
            print(f"  {nb.as_posix()} : {n} separateur(s) {verbe}")

    verbe = "convertis" if args.apply else "a convertir"
    print(f"{seps} separateur(s) {verbe} dans {files} notebook(s)")
    if args.check and seps:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
