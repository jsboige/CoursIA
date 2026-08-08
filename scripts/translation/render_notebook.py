#!/usr/bin/env python3
"""Render a notebook into a target language from a translation CSV.

Companion to :file:`scripts/translation/extract_cells_to_csv.py` (T1 extraction)
and :file:`scripts/translation/translate_csv.py` (T3 fill). This is **T4 — the
re-import**: take a notebook source + the per-cell CSV, and produce a translated
``<notebook>_<lang>.ipynb`` where markdown cells are substituted from the CSV
and code cells are copied byte-for-byte (source, outputs, execution_count).

CLI usage
---------
    python render_notebook.py \\
        --csv translations/genai/finetuning.csv \\
        --notebook MyIA.AI.Notebooks/GenAI/FineTuning/FT-01-Introduction-FineTuning.ipynb \\
        --lang en --out /tmp/FT-01_en.ipynb [--dry-run] [--verbose]

The output language's column in the CSV (``text_<lang>``) supplies the
translated prose. Empty cells fall back to the FR source (never a blank cell,
never a placeholder). Cells in the CSV that are absent from the notebook
(orphan ``cell_id``) raise a warning and are kept in a sidecar ``.stale`` file
rather than silently dropped. Conversely, cells in the notebook that are absent
from the CSV keep their FR text (with a debug-level note when ``--verbose``).

The three invariants (issue #10039, also mandated by #10038 §3) :

1. **Markdown cells** : substituted from ``text_<lang>`` with FR fallback.
2. **Code cells** : copied byte-for-byte (``source``, ``outputs``,
   ``execution_count``). The CSV has no code-output column (cf. schema #4957
   §1) and won't get one — outputs come from real execution of the source,
   which is identical to the bit, so the proven-same applies. This is what
   avoids re-executing 703 notebooks × N languages (some of which are
   GPU-only or QC Cloud, i.e. partially impossible).
3. **Structure preserved** : count, order and ``cell_id`` of cells identical
   to the source. A rendered notebook that gains or loses a cell is a bug,
   not a variant.

Corollary (CLAUDE.md §E) : comments and printed literals in code remain in
French. This is part of the convention and is the price of honest outputs.
"""

from __future__ import annotations

import argparse
import csv
import difflib
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple


@dataclass
class RenderStats:
    """Counters emitted by :func:`render` for diagnostics + tests."""

    n_md_cells: int = 0  # markdown cells in source
    n_code_cells: int = 0  # code cells in source
    n_translated: int = 0  # markdown cells translated (CSV had non-empty text_<lang>)
    n_fallback: int = 0  # markdown cells fell back to FR (CSV text_<lang> empty)
    n_orphan_keys: int = 0  # CSV rows whose cell_id is not in the notebook
    n_id_mismatch: int = 0  # cells in notebook whose id is not in CSV (kept as-is)
    n_byte_identical: int = 0  # rendered cells whose text is identical to source


@dataclass
class RenderResult:
    """Result of a single render."""

    out_path: Optional[Path]  # None when --dry-run
    nb_cells_out: int  # cell count in output notebook
    stats: RenderStats
    orphan_keys: List[str] = field(default_factory=list)


def read_csv_for_lang(csv_path: Path, notebook_keys: List[str], lang: str) -> Tuple[List[str], Dict[str, str]]:
    """Read the CSV and extract rows for a single notebook + language.

    ``notebook_keys`` is a list of path forms to match against the CSV's
    ``notebook`` column. The first form to yield any hit wins; the others are
    silently ignored. This forgives path-style mismatches : ``extract_cells_to_csv.py``
    writes the repo-relative POSIX path (``MyIA.AI.Notebooks/.../nb.ipynb``) but
    callers may pass a Windows absolute path (``C:/.../nb.ipynb``) or the bare
    basename (``nb.ipynb``).

    Returns ``(ordered_cell_ids, text_map)`` where ``text_map[cell_id]`` is the
    translated text in the target language, or empty string if absent. The
    ordered list preserves the CSV row order (which is the canonical order
    used by ``extract_cells_to_csv.py``).
    """
    if not csv_path.exists():
        raise FileNotFoundError(f"CSV introuvable : {csv_path}")
    with csv_path.open(encoding="utf-8", newline="") as fh:
        reader = csv.DictReader(fh)
        if reader.fieldnames is None:
            raise ValueError(f"CSV vide ou illisible : {csv_path}")
        text_col = f"text_{lang}"
        if text_col not in reader.fieldnames:
            raise ValueError(
                f"Colonne {text_col!r} absente du CSV. Colonnes disponibles : "
                f"{reader.fieldnames}"
            )
        # First pass : collect all rows keyed by notebook. We then pick the form
        # that yields the largest matching subset (most rows = canonical form).
        by_key: Dict[str, List[dict]] = {}
        for row in reader:
            nb_key = row.get("notebook", "")
            by_key.setdefault(nb_key, []).append(row)
        # Choose the form whose row count is highest (most specific match).
        chosen_key = None
        chosen_rows: List[dict] = []
        for key in notebook_keys:
            if key in by_key and len(by_key[key]) > len(chosen_rows):
                chosen_key = key
                chosen_rows = by_key[key]
        if chosen_key is None:
            return [], {}
        ordered_ids: List[str] = []
        text_map: Dict[str, str] = {}
        for row in chosen_rows:
            cid = row.get("cell_id", "")
            if not cid:
                continue
            ordered_ids.append(cid)
            text_map[cid] = row.get(text_col, "") or ""
        return ordered_ids, text_map


def render(
    nb_path: Path,
    csv_path: Path,
    lang: str,
    out_path: Optional[Path],
    *,
    dry_run: bool = False,
    verbose: bool = False,
) -> RenderResult:
    """Render the notebook at ``nb_path`` to ``out_path`` in language ``lang``.

    Returns a :class:`RenderResult` with stats + orphan keys (cells in the CSV
    that were not found in the notebook). When ``dry_run`` is set, no file is
    written; the function still computes everything to surface stats.

    The output language's column in the CSV (``text_<lang>``) supplies the
    translated prose. Empty cells fall back to the FR source. Structure is
    preserved bit-for-bit : ``nbformat``, ``metadata`` (sans
    ``metadata.papermill``), cell order, ``cell_id``, and code cells' ``source``
    + ``outputs`` + ``execution_count``.
    """
    if not nb_path.exists():
        raise FileNotFoundError(f"Notebook introuvable : {nb_path}")
    if dry_run and out_path is None:
        raise ValueError("--dry-run nécessite --out (chemin où il aurait écrit)")
    if not dry_run and out_path is None:
        raise ValueError("--out est requis sauf avec --dry-run")

    try:
        nb = json.loads(nb_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        raise ValueError(f"Notebook illisible : {nb_path} ({exc})") from exc

    # Build candidate notebook-key forms : the renderer must match whatever the
    # CSV carries (full Windows path, full POSIX path, repo-relative POSIX,
    # or bare basename). ``read_csv_for_lang`` picks the form with the most rows.
    notebook_keys = [nb_path.as_posix(), str(nb_path), nb_path.name]
    # Repo-relative POSIX path (forward slashes from repo root) — what
    # ``extract_cells_to_csv.py`` writes.
    try:
        # Walk up to find the first parent that contains ``MyIA.AI.Notebooks``
        # (the canonical repo root marker). If we don't find it, skip.
        for parent in [nb_path.parent, *nb_path.parents]:
            if (parent / "MyIA.AI.Notebooks").is_dir():
                rel = nb_path.relative_to(parent).as_posix()
                if rel not in notebook_keys:
                    notebook_keys.append(rel)
                break
    except Exception:
        pass
    ordered_csv_ids, text_map = read_csv_for_lang(csv_path, notebook_keys, lang)
    csv_ids_set: Set[str] = set(ordered_csv_ids)

    stats = RenderStats()
    orphan_keys: List[str] = []
    out_nb = dict(nb)  # shallow copy — preserves nbformat, metadata, etc.
    new_cells: List[dict] = []

    for cell in nb.get("cells", []):
        cell_id = cell.get("id", "")
        cell_type = cell.get("cell_type", "unknown")
        if cell_type == "markdown":
            stats.n_md_cells += 1
            new_cell = dict(cell)
            original_source = "".join(cell.get("source", []))
            translated = text_map.get(cell_id, "") if cell_id else ""
            if translated.strip():
                stats.n_translated += 1
                new_cell["source"] = [translated]
                if translated == original_source:
                    stats.n_byte_identical += 1
            else:
                stats.n_fallback += 1
                # FR fallback = keep original source verbatim, do not modify.
            new_cells.append(new_cell)
            continue
        if cell_type == "code":
            stats.n_code_cells += 1
            # Invariant #2 : code cells copied byte-for-byte (source, outputs,
            # execution_count). We don't even check the CSV for code cells —
            # the CSV doesn't carry outputs by design.
            new_cells.append(dict(cell))
            continue
        # Unknown cell_type — preserve as-is, do not touch.
        new_cells.append(dict(cell))

    # Orphan CSV keys (in CSV but not in notebook) : preserved in sidecar
    # .stale (CSV keys whose cell_id was not present in the source notebook).
    nb_ids_set: Set[str] = {c.get("id", "") for c in nb.get("cells", []) if c.get("id")}
    orphan_keys = [cid for cid in ordered_csv_ids if cid not in nb_ids_set]
    stats.n_orphan_keys = len(orphan_keys)
    stats.n_id_mismatch = len(nb_ids_set - csv_ids_set - {""})  # cells in nb but not in CSV

    out_nb["cells"] = new_cells

    if not dry_run and out_path is not None:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        # Atomic write : write to a sibling .tmp then rename. This prevents
        # leaving a partial notebook on disk if the process is killed mid-write.
        tmp_path = out_path.with_suffix(out_path.suffix + ".tmp")
        tmp_path.write_text(json.dumps(out_nb, ensure_ascii=False, indent=1), encoding="utf-8")
        tmp_path.replace(out_path)

    if orphan_keys and not dry_run and out_path is not None:
        stale_path = out_path.with_suffix(out_path.suffix + ".stale")
        stale_path.write_text(
            "\n".join(orphan_keys) + "\n", encoding="utf-8"
        )
        if verbose:
            print(f"  WARN: {len(orphan_keys)} orphan CSV key(s) -> {stale_path.name}")

    return RenderResult(
        out_path=out_path if not dry_run else None,
        nb_cells_out=len(new_cells),
        stats=stats,
        orphan_keys=orphan_keys,
    )


# --- Falsification helpers (used by tests) --------------------------------- #


def diff_summary(src_path: Path, out_path: Path, lang: str) -> str:
    """Return a unified-diff-style summary of markdown-cell substitutions.

    Used by tests and by humans via ``--verbose``. Walks both notebooks'
    markdown cells in order, prints the before/after for cells whose text
    differs. Useful to spot-check that no French slipped through.
    """
    src = json.loads(src_path.read_text(encoding="utf-8"))
    out = json.loads(out_path.read_text(encoding="utf-8"))
    src_md = ["".join(c.get("source", [])) for c in src.get("cells", []) if c.get("cell_type") == "markdown"]
    out_md = ["".join(c.get("source", [])) for c in out.get("cells", []) if c.get("cell_type") == "markdown"]
    if len(src_md) != len(out_md):
        return f"## CELL COUNT MISMATCH src={len(src_md)} out={len(out_md)}"
    diffs = []
    for i, (a, b) in enumerate(zip(src_md, out_md)):
        if a == b:
            continue
        diff_lines = list(difflib.unified_diff(
            a.splitlines(keepends=True),
            b.splitlines(keepends=True),
            fromfile=f"cell[{i}].fr",
            tofile=f"cell[{i}].{lang}",
            n=2,
        ))
        diffs.append("".join(diff_lines))
    return "\n".join(diffs) if diffs else "(no markdown diffs)"


# --- CLI ------------------------------------------------------------------- #


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Render a notebook into a target language from a translation CSV."
    )
    p.add_argument("--csv", required=True, type=Path, help="Translation CSV (schema #4957 §1)")
    p.add_argument("--notebook", required=True, type=Path, help="Source notebook (FR)")
    p.add_argument("--lang", required=True, help="Target language code (e.g. en, es, ar)")
    p.add_argument("--out", type=Path, help="Output notebook path (e.g. X_en.ipynb)")
    p.add_argument("--dry-run", action="store_true", help="Compute diff/stats, do not write")
    p.add_argument("--verbose", action="store_true", help="Print per-cell diagnostics")
    args = p.parse_args(argv)

    dry_run = args.dry_run or args.out is None
    if not dry_run and args.out is None:
        p.error("--out is required unless --dry-run")

    try:
        result = render(
            nb_path=args.notebook,
            csv_path=args.csv,
            lang=args.lang,
            out_path=args.out,
            dry_run=dry_run,
            verbose=args.verbose,
        )
    except (FileNotFoundError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    s = result.stats
    mode = "(dry-run)" if dry_run else f"-> {result.out_path}"
    print(
        f"[render] {args.notebook} ({args.lang}) {mode}\n"
        f"  cells out: {result.nb_cells_out}\n"
        f"  markdown:  {s.n_md_cells} (translated={s.n_translated}, "
        f"fallback={s.n_fallback}, byte-identical={s.n_byte_identical})\n"
        f"  code:      {s.n_code_cells} (copied verbatim)\n"
        f"  orphans:   {s.n_orphan_keys} (CSV keys absent from notebook)\n"
        f"  unmatched: {s.n_id_mismatch} (notebook cells without CSV row)"
    )
    if args.verbose and not dry_run:
        diff = diff_summary(args.notebook, args.out, args.lang)
        if diff and diff != "(no markdown diffs)":
            print("\n--- markdown diff ---")
            print(diff[:2000])
            if len(diff) > 2000:
                print(f"... ({len(diff) - 2000} more chars)")
    return 0


if __name__ == "__main__":
    sys.exit(main())