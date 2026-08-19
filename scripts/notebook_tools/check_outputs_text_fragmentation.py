#!/usr/bin/env python3
"""Detecteur de fragmentation character-par-character des outputs stream (cf. c.354-L2).

Le format nbformat specifie que ``outputs[].text`` (stream output de type
``output_type=stream``) doit etre une **liste de lignes**, chacune terminee par
``\\n``. Quand une chaine entiere est injectee directement (``text=[content]``
au lieu de ``content.splitlines(keepends=True)``), Jupyter stocke la sortie
**caractere par caractere** dans la liste.

Cas fondateur (c.354, 2026-08-18, PR #11664) : 9 lignes reelles (778 chars)
injectees via ``text=[content]`` -> nbformat stocke 778 strings d'1 char
chacune. La cellule reste valide (``execution_count != null``, ``outputs !=
[]``) et passe le pre-commit H.3 ``check_null_exec.py``, mais le rendu Jupyter
est degrade (chaque ligne est affichee comme une colonne de 778 lignes d'1
char).

Ce detecteur complete H.3 : il ne regarde pas si la cellule a execute, mais si
la sortie stream est structurellement bien formee.

Signature du cas (heuristique mediane + max conjonction) :
- ``output_type == "stream"``
- ``text`` est une liste non vide
- longueur mediane des items < 2 chars (= presque tout est 1 char)
- **ET** longueur max des items <= 2 chars (sinon c'est un faux positif : une
  sortie avec lignes vides ``\n``/``\r\n`` de 2 chars + quelques vraies lignes
  courtes — typique des stderr .NET / C# kernel — a une mediane a 2 tiree
  par les lignes vides, mais une vraie ligne de 200+ chars qui prouve la
  sortie est legitime).

La conjonction mediane + max est le fruit de l'audit #11668 cycle c.359 :
sur 17 cas mesures en ``--all``, 17/17 etaient des faux positifs avec
``min=2, max=60..444`` (alternance ``\r\n`` + vraie ligne). Seul le cas
fondateur (c.354) avait ``min=max=1`` (char-par-char reel). La conjonction
ferme ce trou.

Seuils (defaut) :
- MEDIAN_THRESHOLD = 2
- MAX_TEXT_LEN_THRESHOLD = 2
- MIN_TEXT_ITEMS = 10
- Verdict FRAGMENTED <=> mediane <= 2 AND max <= 2

Exemptions (ne PAS flagger) :
- cellule markdown (le defaut ne concerne que les code cells)
- outputs sans ``text`` (display_data sans stream, c'est legitime)
- cellule avec un seul output de 1 char (= cas degeneratif non signant)

Usage :
    python scripts/notebook_tools/check_outputs_text_fragmentation.py <staged.ipynb> [...]
    python scripts/notebook_tools/check_outputs_text_fragmentation.py --all
    python scripts/notebook_tools/check_outputs_text_fragmentation.py --check
    python scripts/notebook_tools/check_outputs_text_fragmentation.py --explain

Sortie JSON stable (cf. ``detect_md_content_loss.py`` #8655 et
``check_render_volume_delta.py`` #11656) :

    {
      "findings": [
        {
          "path": "MyIA.AI.Notebooks/.../foo.ipynb",
          "cell_index": 24,
          "n_outputs": 1,
          "median_text_len": 1.0,
          "min_text_len": 1,
          "max_text_len": 1,
          "n_text_items": 778,
          "severity": "FRAGMENTED"
        }
      ],
      "summary": {"files_scanned": 1, "findings_total": 1}
    }

Issue : #11667
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path
from typing import Any

MEDIAN_THRESHOLD = 2  # mediane <= 2 chars = fragment character-par-character
MAX_TEXT_LEN_THRESHOLD = 2  # max <= 2 chars en conjonction : sans ca, les sorties avec lignes vides (\n/\r\n) + vraies lignes courtes (stderr .NET) ont une mediane a 2 tiree par les vides, mais une vraie ligne de 200+ chars -> sortie saine, pas fragmented
MIN_TEXT_ITEMS = 10   # au moins 10 items avant de flagger (evite faux positifs sur sorties courtes)


def _code_cells(data: dict) -> list[tuple[int, dict]]:
    """Yield (index, cell) for code cells in notebook JSON data."""
    return [
        (i, c) for i, c in enumerate(data.get("cells", []))
        if c.get("cell_type") == "code"
    ]


def _is_stream_output(output: dict) -> bool:
    """True si output est de type stream avec champ text."""
    return output.get("output_type") == "stream" and "text" in output


def _text_items(output: dict) -> list[str]:
    """Return la liste ``text`` d'un output stream (peut etre str ou list)."""
    text = output.get("text", [])
    if isinstance(text, str):
        return [text]
    return list(text)


def _median_or_none(items: list[str]) -> float | None:
    """Mediane des longueurs d'items, ou None si vide."""
    if not items:
        return None
    return statistics.median(len(x) for x in items)


def scan_notebook(path: Path) -> list[dict[str, Any]]:
    """Scan un notebook et retourne la liste des findings (vide si rien)."""
    findings: list[dict[str, Any]] = []
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return findings  # pas un notebook ou invalide -- ignore

    for cell_idx, cell in _code_cells(data):
        for out_idx, output in enumerate(cell.get("outputs", [])):
            if not _is_stream_output(output):
                continue
            items = _text_items(output)
            if len(items) < MIN_TEXT_ITEMS:
                continue
            med = _median_or_none(items)
            max_len = max(len(x) for x in items)
            # Conjonction mediane + max : un fragment character-par-character
            # a TOUS ses items d'1 char (max=1). Une sortie avec lignes vides
            # + vraies lignes courtes a max>2 -> sortie saine.
            if med is None or med > MEDIAN_THRESHOLD or max_len > MAX_TEXT_LEN_THRESHOLD:
                continue
            findings.append({
                "path": str(path),
                "cell_index": cell_idx,
                "output_index": out_idx,
                "n_outputs": len(cell.get("outputs", [])),
                "median_text_len": med,
                "min_text_len": min(len(x) for x in items),
                "max_text_len": max_len,
                "n_text_items": len(items),
                "severity": "FRAGMENTED",
            })
    return findings


def _iter_notebooks(roots: list[Path]) -> list[Path]:
    """Iter sur tous les .ipynb sous roots."""
    out: list[Path] = []
    for root in roots:
        if root.is_file() and root.suffix == ".ipynb":
            out.append(root)
        elif root.is_dir():
            out.extend(sorted(root.rglob("*.ipynb")))
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Detecte les outputs stream fragmentes character-par-character (c.354-L2).",
    )
    parser.add_argument("paths", nargs="*", help="Notebooks ou repertoires (defaut: stdin)")
    parser.add_argument("--all", action="store_true", help="Scan tout le repo (MyIA.AI.Notebooks)")
    parser.add_argument("--check", action="store_true", help="Exit 1 si finding (CI parity)")
    parser.add_argument("--explain", action="store_true", help="Resume de la regle")
    parser.add_argument("--json", action="store_true", help="Sortie JSON stable")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("MyIA.AI.Notebooks"),
        help="Racine du scan (defaut: MyIA.AI.Notebooks)",
    )
    args = parser.parse_args(argv)

    if args.explain:
        print(__doc__)
        return 0

    if args.all:
        roots = [args.root]
    else:
        roots = [Path(p) for p in args.paths] if args.paths else [args.root]

    notebooks = _iter_notebooks(roots)
    all_findings: list[dict[str, Any]] = []
    for nb in notebooks:
        all_findings.extend(scan_notebook(nb))

    if args.json:
        print(json.dumps({
            "findings": all_findings,
            "summary": {
                "files_scanned": len(notebooks),
                "findings_total": len(all_findings),
            },
        }, ensure_ascii=False, indent=2))
    else:
        for f in all_findings:
            print(
                f"[FRAGMENTED] {f['path']} cell#{f['cell_index']} "
                f"output#{f['output_index']} : median={f['median_text_len']} "
                f"items={f['n_text_items']} (min={f['min_text_len']}, max={f['max_text_len']})"
            )
        print(f"# {len(all_findings)} findings / {len(notebooks)} notebooks scanned", file=sys.stderr)

    if args.check and all_findings:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
