#!/usr/bin/env python3
"""fix_slides_html_block_markdown.py -- insere une ligne vide avant chaque
bloc markdown avale par un bloc HTML (cf #13216).

Trois regles :
  1. Run dry-run par defaut (imprime la liste des insertions prevues, exit 0
     si au moins un fix serait applique, exit 1 sinon -- lecture seule).
  2. --apply : modifie les fichiers EN PLACE.
  3. --root-dir : par defaut, balaie slides/ (recursive=False, conforme aux
     conventions scan_slides_image_refs / scan_slides_html_block_markdown).

Le scanner source (scan_slides_html_block_markdown.py, #13218) detecte les
lignes de markdown de bloc situees IMMEDIATEMENT apres une balise ouvrante
HTML (sans ligne vide). Le fix : inserer une ligne vide juste avant la
ligne signalee.

Cas fondateur (slides/06-apprentissage/slides.md, L286) :
    <div v-click="2">
  - **Tri des symboles selon**      <-- scanner hit (L286)
      - la frequence

apres fix :
    <div v-click="2">

  - **Tri des symboles selon**
      - la frequence

Le scanner utilise des index 1-based sortants. On reproduit fidelement son
`split('\n')` (pas splitlines : collapse les \\v, etc. et decalerait les
index -- c.574 lesson).

Les hits sont traites en ordre DECROISSANT (le plus haut d'abord) pour
que l'insertion precedente ne decale pas les index suivants.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable, NamedTuple

REPO = Path(__file__).resolve().parents[2]
DEFAULT_SCANNER = REPO / "scripts/notebook_tools/scan_slides_html_block_markdown.py"


class Hit(NamedTuple):
    file: Path
    line: int  # 1-based line in file


def parse_scanner_output(text: str) -> list[Hit]:
    """Parse the output of scan_slides_html_block_markdown.py.

    Format attendu :
        scanned 36 markdown file(s) under slides

        slides/01-introduction/slides.md  (1)
          L595    - Intelligence animale

        slides/06-apprentissage/slides.md  (39)
          L286    - **Tri des symboles selon**

        total: 49 line(s) of block markdown swallowed
    """
    hits: list[Hit] = []
    cur_file: Path | None = None
    for line in text.splitlines():
        m = re.match(r"^\s*(\S+\.md)\s+\(\d+\)\s*$", line)
        if m:
            cur_file = Path(m.group(1))
            continue
        m = re.match(r"^\s*L(\d+)\s+", line)
        if m and cur_file is not None:
            hits.append(Hit(cur_file, int(m.group(1))))
    return hits


def would_insert_blank(lines: list[str], hit_line: int) -> bool:
    """Verifie que la ligne hit_line est PRECEDEE d'une balise ouvrante HTML
    SANS ligne vide entre les deux. Si une ligne vide est deja la, retourne
    False (le scanner a sur-acuse ou le fichier a deja ete repare).
    Convention 1-based pour hit_line (aligne avec le scanner).

    Note : le scanner source utilise une regex stricte (_OPENING_TAG seule
    sur sa ligne, pas d'auto-fermeture), donc faire confiance a son verdict
    ici -- limiterait le scope de re-verification.
    """
    if hit_line <= 1:
        return False
    prev_idx = hit_line - 2  # 0-based index de la ligne juste avant
    if prev_idx >= len(lines):
        return False
    prev_line = lines[prev_idx].rstrip()
    if not prev_line:
        return False  # ligne vide deja presente -- deja reparee
    return True


def apply_fix(file: Path, hits: Iterable[int], dry_run: bool) -> list[str]:
    """Insere une ligne vide avant chaque hit. Retourne les chemins Lignes
    dans le fichier ORIGINAL (1-based, avant insertion) pour logging.
    """
    if not hits:
        return []
    # newline='' preserve les LF d'origine (c.574 lesson : en mode texte
    # Windows, open() sans newline='' convertit \n en \r\n et le diff explose
    # inutilement).
    with file.open("r", encoding="utf-8", newline="") as f:
        text = f.read()
    # split('\n') comme le scanner source (cf docstring)
    lines = text.split("\n")
    # DECROISSANT : insertion haute d'abord, pour eviter que l'insertion
    # precedente ne decale les index.
    sorted_hits = sorted(set(hits), reverse=True)
    insertions: list[str] = []
    for hit_line in sorted_hits:
        if not would_insert_blank(lines, hit_line):
            continue
        idx = hit_line - 2  # 0-based de la ligne precedant L hit_line (1-based)
        lines.insert(idx + 1, "")
        insertions.append(f"{file}:L{hit_line}")
    if not dry_run and insertions:
        out = "\n".join(lines)
        if text.endswith("\n") and not out.endswith("\n"):
            out += "\n"
        elif not text.endswith("\n") and out.endswith("\n"):
            out = out.rstrip("\n")
        # newline='' pour ne pas re-transformer les LF en CRLF.
        with file.open("w", encoding="utf-8", newline="") as f:
            f.write(out)
    return insertions


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--scanner-output", type=Path, default=None,
                    help="Sortie capturee de scan_slides_html_block_markdown.py (defaut : lancer le scanner)")
    ap.add_argument("--apply", action="store_true", help="Modifie les fichiers EN PLACE (defaut : dry-run)")
    ap.add_argument("--root-dir", type=Path, default=REPO / "slides")
    args = ap.parse_args()

    if args.scanner_output is not None:
        scanner_text = args.scanner_output.read_text(encoding="utf-8")
    else:
        proc = subprocess.run(
            [sys.executable, str(DEFAULT_SCANNER)],
            capture_output=True, text=True, cwd=str(REPO)
        )
        if proc.returncode not in (0, 1) and not proc.stdout:
            print(f"scanner echec (rc={proc.returncode}): {proc.stderr}", file=sys.stderr)
            return 2
        scanner_text = proc.stdout

    hits = parse_scanner_output(scanner_text)
    if not hits:
        print("Aucun hit scanne -- rien a fixer.")
        return 1

    by_file: dict[Path, list[int]] = {}
    for h in hits:
        by_file.setdefault(h.file, []).append(h.line)

    total_insertions: list[str] = []
    for file, line_nums in sorted(by_file.items()):
        insertions = apply_fix(file, line_nums, dry_run=not args.apply)
        total_insertions.extend(insertions)

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"[{mode}] {len(total_insertions)} insertion(s) prevue(s) :")
    for ins in total_insertions:
        print(f"  - {ins}")
    if not args.apply:
        print("Relancer avec --apply pour modifier.")
    return 0 if total_insertions else 1


if __name__ == "__main__":
    sys.exit(main())
