#!/usr/bin/env python3
"""Mesure du critere a deux niveaux propose sur #18411 (instrument, pas un gate).

La proposition du 2026-09-20 (issue #16762, commentaire 5752001803) remplace le
plancher de volume `DENSITY_THRESHOLD = 1200` chars/cellule de
``pedagogy_density.py`` par deux niveaux :

1. **Couverture** -- toute cellule de code a sortie substantielle porte une
   cellule de lecture ancree ;
2. **Delta d'information** -- part des mots *rares* d'une lecture (df <= 4 dans
   le carnet, meme definition que #16786) qui n'apparaissent ni dans la sortie
   de la cellule ancree, ni dans la prose voisine.

Le motif du remplacement est mesure : un plancher de volume se satisfait par
reformulation et par empilement de lectures redondantes, exactement la classe
que #16762 a du corriger (84 findings, 4 triplons exacts dans #16817).

**Perimetre.** Ce fichier est un INSTRUMENT DE MESURE : lecture seule, sortie
JSON/texte, **toujours exit 0**, aucun workflow cable, aucun seuil applique.
La bascule (retirer le seuil de 1200 et re-exprimer la campagne de densite)
reste gelee tant que le veto #13410 tient -- l'issue le dit elle-meme. La
machinerie de rarete est CONSOMMEE depuis ``check_split_reading_cells`` /
``detect_repeated_prose`` (#16786), jamais reecrite : le jour ou le critere est
cable, les deux doivent lire le meme df.

**Perimetre de la redondance (arbitrage #18411 (c)).** Le delta mesure la
nouveaute d'une lecture contre SA sortie ancree et la prose voisine -- pas
contre les autres lectures. La redondance exacte ENTRE lectures (triplons,
prose repetee d'une cellule a l'autre) reste le domaine de
``detect_repeated_prose`` (#16762) : la mesure du census 2026-09-29 montre que
ce critere ne l'attrape pas.

Usage::

    python reading_information_delta.py --json            # census corpus
    python reading_information_delta.py <carnet.ipynb>    # un carnet
    python reading_information_delta.py --min-delta 0.5   # filtre d'echantillon
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import asdict, dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_split_reading_cells import (  # noqa: E402
    cell_output_text,
    is_reading_cell,
    is_reading_or_prose,
)
from count_exercises import EXCLUDE_DIRS, NOTEBOOKS_DIR  # noqa: E402
from detect_repeated_prose import content_words, markdown_cells  # noqa: E402

#: Un mot est rare quand il apparait dans <= 4 cellules markdown du carnet
#: (definition #16786, cf check_split_reading_cells.MAX_DF).
MAX_DF = 4

#: Une sortie est "substantielle" au-dela de ce nombre de caracteres de texte.
#: En dessous, il n'y a rien a commenter : une cellule qui imprime
#: "Tableau cree." ne reclame pas une lecture. Plancher bas assume -- le census
#: publie la distribution pour que le seuil soit arbitre sur des chiffres.
MIN_OUTPUT_CHARS = 40


@dataclass
class ReadingDelta:
    """Une lecture ancree et la part de son vocabulaire qui est nouveau."""

    reading_cell: int
    code_cell: int
    anchor: str  # 'after' (canonique) ou 'before'
    rare_words: int
    novel_words: int
    delta: float | None  # novel / rare ; None si la lecture n'a aucun mot rare
    novel_sample: list[str] = field(default_factory=list)


@dataclass
class NotebookCensus:
    path: str
    code_with_output: int
    covered: int
    readings: list[ReadingDelta] = field(default_factory=list)
    unreadable: str = ""


def _cell_source(cell: dict) -> str:
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def _is_structural_header(cell: dict) -> bool:
    """En-tete structurel seul : toutes lignes vides ou titres markdown ``#``.

    Arbitrage #18411 (a) : ces cellules sortent du jeu de lectures de l'instrument.
    Un titre seul ne commente rien -- y compris un titre d'interpretation sans
    corps (``### Analyse`` seul passe ``is_reading_cell`` et etait mesure avec un
    corps vide). Le census 2026-09-29 doit a cette classe ses non-lectures de
    queue basse et une couverture gonflee.
    """
    src = _cell_source(cell).strip()
    if not src:
        return True
    return all(
        (not line.strip()) or line.lstrip().startswith("#")
        for line in src.splitlines()
    )


def _is_reading(cell: dict) -> bool:
    """Lecture au sens #16786 (titre de lecture) ou prose d'interpretation.

    Arbitrage #18411 (a) : un en-tete structurel seul n'est pas une lecture.
    """
    if _is_structural_header(cell):
        return False
    return is_reading_cell(cell) or is_reading_or_prose(cell)


def _reading_body(cell: dict) -> str:
    """Corps de la lecture, **titre exclu**.

    Le titre EST le discriminant (#17777 : « le discriminant est le titre, pas
    la longueur du corps ») et rien d'autre : ses mots (« lecture », « sortie »)
    ne sont pas un apport d'information. Les compter gonflait le delta de deux
    mots rares sur toute lecture titree -- mesure faite sur les tests de cet
    instrument avant correction.
    """
    lines = _cell_source(cell).splitlines()
    for k, line in enumerate(lines):
        if line.strip():
            if line.lstrip().startswith("#"):
                return "\n".join(lines[k + 1:])
            return "\n".join(lines[k:])
    return ""


def _significant_output(cell: dict) -> bool:
    return len(cell_output_text(cell).strip()) >= MIN_OUTPUT_CHARS


def _anchor(cells: list[dict], i: int) -> tuple[int, str] | None:
    """Cellule de lecture ancree a la cellule de code ``i``, ou ``None``.

    Canonique = la markdown qui SUIT l'output (la lecture commente ce qui vient
    d'etre produit). Repli = la markdown qui la PRECEDE, marque 'before' : le
    census les separe pour ne pas surestimer la couverture.
    """
    nxt = cells[i + 1] if i + 1 < len(cells) else None
    if nxt is not None and nxt.get("cell_type") == "markdown" and _is_reading(nxt):
        return i + 1, "after"
    prv = cells[i - 1] if i > 0 else None
    if prv is not None and prv.get("cell_type") == "markdown" and _is_reading(prv):
        return i - 1, "before"
    return None


def _delta_for(
    cells: list[dict],
    reading_idx: int,
    code_idx: int,
    df: Counter[str],
) -> ReadingDelta:
    """Part des mots rares de la lecture absents de l'output et de la prose voisine.

    ``anchored`` = mots de la sortie ancree + mots des markdown immediatement
    voisines (celle qui precede la cellule de code, celle qui suit la lecture) :
    une lecture peut legitimement reprendre un terme introduit par la prose
    d'a cote sans que ce soit une redite de sa propre sortie.
    """
    wi = content_words(_reading_body(cells[reading_idx]))
    rare = {w for w in wi if df[w] <= MAX_DF}
    anchored: set[str] = set(content_words(cell_output_text(cells[code_idx])))
    for j in (code_idx - 1, reading_idx + 1):
        if 0 <= j < len(cells) and j != reading_idx and cells[j].get("cell_type") == "markdown":
            anchored |= content_words(_cell_source(cells[j]))
    anchored |= content_words(_cell_source(cells[code_idx]))
    novel = rare - anchored
    return ReadingDelta(
        reading_cell=reading_idx,
        code_cell=code_idx,
        anchor="after" if reading_idx > code_idx else "before",
        rare_words=len(rare),
        novel_words=len(novel),
        delta=round(len(novel) / len(rare), 3) if rare else None,
        novel_sample=sorted(novel)[:10],
    )


def _repo_relative(path: Path) -> str:
    """Chemin repo-relatif quand c'est possible (jamais un chemin machine).

    Le census est publie (issue #18411) : un chemin absolu de la machine qui l'a
    produit n'y a pas de sens, et il rend les strates par famille illisibles.
    """
    try:
        return path.resolve().relative_to(REPO_ROOT).as_posix()
    except (ValueError, OSError):
        return path.as_posix()


def census_notebook(nb: dict, path: str) -> NotebookCensus:
    """Census d'un carnet : couverture des sorties substantielles + deltas."""
    cells = nb.get("cells", [])
    words = {ci: content_words(t) for ci, t in markdown_cells(nb)}
    df: Counter[str] = Counter()
    for ws in words.values():
        df.update(ws)

    out = NotebookCensus(path=path, code_with_output=0, covered=0)
    seen_readings: set[int] = set()
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "code" or not _significant_output(cell):
            continue
        out.code_with_output += 1
        anchor = _anchor(cells, i)
        if anchor is None:
            continue
        ridx, _kind = anchor
        out.covered += 1
        if ridx in seen_readings:
            continue
        seen_readings.add(ridx)
        out.readings.append(_delta_for(cells, ridx, i, df))
    return out


def _iter_targets(targets: list[str], from_stdin: bool) -> list[Path]:
    raw = list(targets)
    if from_stdin:
        raw += [ln.strip() for ln in sys.stdin if ln.strip()]
    paths: list[Path] = []
    seen: set[str] = set()
    for r in raw:
        p = Path(r)
        if p.is_dir():
            for q in sorted(p.rglob("*.ipynb")):
                s = str(q)
                if any(part in EXCLUDE_DIRS for part in q.parts) or s in seen:
                    continue
                seen.add(s)
                paths.append(q)
            continue
        if p.suffix != ".ipynb" or not p.exists() or str(p) in seen:
            continue
        seen.add(str(p))
        paths.append(p)
    return paths


def _percentile(values: list[float], q: float) -> float:
    if not values:
        return 0.0
    ordered = sorted(values)
    k = min(len(ordered) - 1, max(0, int(round(q * (len(ordered) - 1)))))
    return ordered[k]


def render_text(censuses: list[NotebookCensus], min_delta: float | None) -> str:
    deltas = [r.delta for c in censuses for r in c.readings if r.delta is not None]
    code_total = sum(c.code_with_output for c in censuses)
    covered = sum(c.covered for c in censuses)
    lines = [
        f"Carnets lus           : {len(censuses)}",
        f"Sorties substantielles: {code_total}",
        f"Couvertes par lecture : {covered}"
        + (f" ({100 * covered / code_total:.1f}%)" if code_total else ""),
        f"Lectures mesurees     : {len(deltas)}",
    ]
    if deltas:
        lines += [
            "Delta d'information (part des mots rares absents de l'output",
            "et de la prose voisine) :",
            f"  p10={_percentile(deltas, 0.10):.3f}  p50={_percentile(deltas, 0.50):.3f}"
            f"  p90={_percentile(deltas, 0.90):.3f}  max={max(deltas):.3f}",
        ]
    if min_delta is not None:
        hits = [
            (c.path, r)
            for c in censuses for r in c.readings
            if r.delta is not None and r.delta >= min_delta
        ]
        lines.append(f"\n--- Lectures a delta >= {min_delta} ({len(hits)}) ---")
        for path, r in hits[:60]:
            lines.append(
                f"  [{r.delta}] {path} c.{r.reading_cell} (code c.{r.code_cell},"
                f" {r.novel_words}/{r.rare_words} mots rares nouveaux)"
            )
        if len(hits) > 60:
            lines.append(f"  ... (+{len(hits) - 60} autres)")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Census du critere a deux niveaux de #18411 (couverture + delta "
            "d'information). Instrument de mesure : lecture seule, aucune "
            "bascule, toujours exit 0."
        ),
    )
    parser.add_argument("targets", nargs="*", default=[])
    parser.add_argument("--stdin", action="store_true")
    parser.add_argument("--json", dest="json_out", action="store_true")
    parser.add_argument("--min-delta", type=float, default=None)
    args = parser.parse_args(argv)

    targets = args.targets
    if not targets and not args.stdin:
        targets = [str(NOTEBOOKS_DIR)]
    paths = _iter_targets(targets, args.stdin)

    censuses: list[NotebookCensus] = []
    for path in paths:
        try:
            nb = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            censuses.append(
                NotebookCensus(
                    path=_repo_relative(path), code_with_output=0,
                    covered=0, unreadable=str(exc),
                )
            )
            continue
        censuses.append(census_notebook(nb, _repo_relative(path)))

    if args.json_out:
        print(json.dumps([asdict(c) for c in censuses], indent=2, ensure_ascii=False))
    else:
        print(render_text(censuses, args.min_delta))
    return 0


if __name__ == "__main__":
    sys.exit(main())