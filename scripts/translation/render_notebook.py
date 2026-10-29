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
        --notebook MyIA.AI.Notebooks/GenAI/FineTuning/FT-01-Introduction-FineTuning-Python.ipynb \\
        --lang en --out /tmp/FT-01_en.ipynb [--dry-run] [--verbose]

    # Re-stamper la provenance d'un jumeau deja derive (sans re-render) :
    python render_notebook.py --reprovenance \\
        --notebook MyIA.AI.Notebooks/GenAI/FineTuning/FT-05-...-Python_en.ipynb \\
        --source MyIA.AI.Notebooks/GenAI/FineTuning/FT-05-...-Python.ipynb \\
        --lang en [--apply]

The output language's column in the CSV (``text_<lang>``) supplies the
translated prose. Empty cells fall back to the FR source (never a blank cell,
never a placeholder). Cells in the CSV that are absent from the notebook
(orphan ``cell_id``) REFUSE the render outright (#13544 §3) : a CSV row whose
``cell_id`` matches no notebook cell is never benign, it is a source
desynchronisation. Conversely, cells in the notebook that are absent from
the CSV keep their FR text (with a debug-level note when ``--verbose``).

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

Provenance (issue #21496, reserve adjointe 6399643921)
------------------------------------------------------
A derived notebook carries **copied** outputs, not its own execution: its
``metadata.papermill`` must never describe a run of the derived file itself,
and it must never inherit the source's papermill block either (a reader would
mistake the source's execution for the twin's). The render therefore strips
``metadata.papermill`` (notebook level AND per-cell blocks) and stamps an
explicit copy-provenance block instead::

    metadata.t4 = {
        "tool": "render_notebook.py",
        "lang": "en",
        "source": "<repo-relative POSIX path of the FR source>",
        "source_papermill": { ...verbatim block of the source notebook... },
    }

``source_papermill`` preserves the execution provenance of the run that
produced the copied outputs (start/end/duration, input/output paths) without
claiming any execution of the twin. The stamp derives from the source content
only — no wall-clock — so re-renders stay byte-identical (idempotence).

:func:`reprovenance` is the canonical repair path for an existing derived
notebook whose provenance is incoherent (e.g. FR outputs assembled onto a twin
that still carries an older native run's papermill). It verifies the copy
preconditions first — cell count, ``cell_id`` order, code ``source`` /
``outputs`` / ``execution_count`` byte-identical to the source — and refuses
to stamp anything otherwise: the stamp is earned by measurement, never
cosmetic. Markdown cells are left untouched (translation drift is the CSV's
business, not provenance's).
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


@dataclass
class ReprovenanceStats:
    """Counters emitted by :func:`reprovenance` for diagnostics + tests."""

    n_cells: int = 0  # total cells compared (must match between twin and source)
    n_code_cells: int = 0  # code cells verified byte-identical (source+outputs+exec_count)
    n_papermill_blocks_stripped: int = 0  # per-cell papermill blocks removed
    n_execution_blocks_stripped: int = 0  # per-cell metadata.execution blocks removed
    stamped: bool = False  # metadata.t4 written


# --- Provenance helpers (#21496) ------------------------------------------- #

T4_PROVENANCE_KEY = "t4"


def _canonical_source_ref(nb_path: Path) -> str:
    """Repo-relative POSIX path of a notebook when derivable, else its basename.

    The render must stamp a path form that does not depend on the caller's
    cwd or absolute location (idempotence across invocations): the walk-up
    finds the ``MyIA.AI.Notebooks`` repo-root marker, as in :func:`render`.
    """
    try:
        for parent in [nb_path.parent, *nb_path.parents]:
            if (parent / "MyIA.AI.Notebooks").is_dir():
                return nb_path.relative_to(parent).as_posix()
    except Exception:
        pass
    return nb_path.name


def _t4_stamp(source_nb: dict, source_path: Path, lang: str) -> Dict[str, object]:
    """Build the copy-provenance block stamped on every T4 output.

    ``source_papermill`` is the verbatim papermill block of the SOURCE notebook
    (or ``None``): it documents the execution that produced the copied outputs
    without ever claiming an execution of the derived file. Derived from source
    content only — deterministic, no wall-clock.
    """
    src_meta = source_nb.get("metadata") or {}
    return {
        "tool": "render_notebook.py",
        "lang": lang,
        "source": _canonical_source_ref(source_path),
        "source_papermill": src_meta.get("papermill"),
    }


# Per-cell metadata keys that describe an execution of THAT cell. On a derived
# twin both are either stale (an old native run) or borrowed (the source's run),
# and both misattribute the copied outputs (#21496). They are stripped, never
# re-stamped: the honest provenance of a copied output is recorded once, at
# notebook level, in ``metadata.t4.source_papermill``.
_CELL_EXECUTION_PROVENANCE_KEYS = ("papermill", "execution")


def _strip_cell_execution_provenance(cell: dict) -> dict:
    """Copy of ``cell`` whose metadata no longer carries an execution block.

    ``metadata.papermill`` and ``metadata.execution`` both describe an execution
    of the cell. A derived twin copies the source's *outputs*, so keeping either
    channel makes the cell claim an execution that did not produce them — a
    stale EN run down to the ``execute_input`` timestamps (#21496).
    """
    new_cell = dict(cell)
    meta = cell.get("metadata")
    if isinstance(meta, dict):
        kept = {k: v for k, v in meta.items()
                if k not in _CELL_EXECUTION_PROVENANCE_KEYS}
        if len(kept) != len(meta):
            new_cell["metadata"] = kept
    return new_cell


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
    require_translated: bool = False,
    min_coverage: float = 1.0,
    # deprecated no-op : le refus orphelin est inconditionnel (#13544 §3) ;
    # le parametre survit pour la compatibilite CLI (translation-sync.yml
    # passe --fail-on-stale) et les appelants kwargs existants.
    fail_on_stale: bool = False,
) -> RenderResult:
    """Render the notebook at ``nb_path`` to ``out_path`` in language ``lang``.

    Returns a :class:`RenderResult` with stats + orphan keys (cells in the CSV
    that were not found in the notebook). When ``dry_run`` is set, no file is
    written; the function still computes everything to surface stats.

    The output language's column in the CSV (``text_<lang>``) supplies the
    translated prose. Empty cells fall back to the FR source. Structure is
    preserved bit-for-bit : ``nbformat``, ``metadata`` (sans
    ``metadata.papermill``), cell order, ``cell_id``, and code cells' ``source``
    + ``outputs`` + ``execution_count``. Per-cell execution blocks
    (``metadata.papermill``, ``metadata.execution``) are stripped — see
    :func:`_strip_cell_execution_provenance` (#21496).

    Guardrails (issue #13544) :

    * ``require_translated=True`` refuses a render with 0 translated cells
      (FR-clone guard, #10349). Always off by default to preserve the
      re-render idempotent contract.
    * ``min_coverage=<float>`` (0.0-1.0, default 1.0) refuses when the
      fraction of translated markdown cells is below the threshold. The
      default is fail-closed : a partial render must be explicitly requested
      by lowering the flag (#13544 §2). A notebook with 0 markdown cells is
      treated as full coverage (1.0) — the gate has nothing to enforce.
    * orphan ``cell_id`` s (CSV rows whose id matches no notebook cell)
      refuse the render unconditionally -- no flag disables it. Such an
      orphan signals a source desynchronisation (the CSV row references a
      cell the notebook no longer has) and never silently produces a render
      (#13544 : a missing ``cell_id`` is never benign).

    Both gates sit BEFORE the atomic write so no partial / clone file
    reaches disk. The coverage gate is fail-closed by default and the
    orphan gate is unconditional : the permissive behaviour that produced
    the #12850 artefacts no longer exists in this engine. Issue #13544 §3 :
    the gates are structural, not advisory.
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
    out_nb = dict(nb)  # shallow copy — preserves nbformat, etc.
    # Provenance (#21496) : the output NEVER inherits the source's papermill
    # block (notebook level) — it gets an explicit copy-provenance stamp
    # instead. The docstring contract « metadata (sans metadata.papermill) »
    # is enforced here, not assumed.
    out_meta = {k: v for k, v in (nb.get("metadata") or {}).items()
                if k not in ("papermill", T4_PROVENANCE_KEY)}
    out_meta[T4_PROVENANCE_KEY] = _t4_stamp(nb, nb_path, lang)
    out_nb["metadata"] = out_meta
    new_cells: List[dict] = []

    for cell in nb.get("cells", []):
        cell_id = cell.get("id", "")
        cell_type = cell.get("cell_type", "unknown")
        if cell_type == "markdown":
            stats.n_md_cells += 1
            new_cell = _strip_cell_execution_provenance(cell)
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
            # the CSV doesn't carry outputs by design. The per-cell papermill
            # block is stripped (#21496) : it describes an execution of the
            # source, never of the twin.
            new_cells.append(_strip_cell_execution_provenance(cell))
            continue
        # Unknown cell_type — preserve as-is, do not touch.
        new_cells.append(_strip_cell_execution_provenance(cell))

    # Orphan CSV keys (in CSV but not in notebook) : preserved in sidecar
    # .stale (CSV keys whose cell_id was not present in the source notebook).
    nb_ids_set: Set[str] = {c.get("id", "") for c in nb.get("cells", []) if c.get("id")}
    orphan_keys = [cid for cid in ordered_csv_ids if cid not in nb_ids_set]
    stats.n_orphan_keys = len(orphan_keys)
    stats.n_id_mismatch = len(nb_ids_set - csv_ids_set - {""})  # cells in nb but not in CSV

    out_nb["cells"] = new_cells

    # Guardrail (#10349) : refuse to write a language render whose CSV carried
    # ZERO translated markdown cells. Such a render is a verbatim FR clone (every
    # cell fell back to source) — a garbage file, not a translation. Opt-in via
    # ``require_translated`` : the default (False) preserves the idempotent
    # re-render contract where an untranslated in-scope lang renders as a FR
    # placeholder (#10039 criterion 3). The check sits BEFORE the atomic write so
    # no partial/clone file reaches disk.
    if require_translated and stats.n_md_cells > 0 and stats.n_translated == 0:
        raise ValueError(
            f"--require-translated : 0 cellule markdown traduite sur "
            f"{stats.n_md_cells} (lang={lang}, {csv_path.name}). "
            f"Refus d'ecrire un clone FR verbatim."
        )

    # Gate #13544 §3 — seuil de couverture, fail-closed par defaut (1.0).
    # Justification du defaut : 1.0 est la seule borne non arbitraire -- les
    # deux artefacts de l'incident (#12850) mesuraient 51 % et 57 %, et toute
    # valeur intermediaire legitimerait un rendu partiel non demande. Une
    # couverture partielle declaree passe par un --min-coverage explicite
    # (#13544 §2 : livrer en declarant explicitement la couverture partielle).
    if not 0.0 <= min_coverage <= 1.0:
        raise ValueError(
            f"--min-coverage doit etre dans [0.0, 1.0], "
            f"recu : {min_coverage!r}"
        )
    if stats.n_md_cells > 0:
        coverage = stats.n_translated / stats.n_md_cells
    else:
        coverage = 1.0  # a notebook without markdown has no defect to enforce
    if coverage < min_coverage:
        raise ValueError(
            f"--min-coverage {min_coverage:.2f} non atteint : "
            f"couverture = {coverage:.2%} "
            f"({stats.n_translated}/{stats.n_md_cells}, "
            f"lang={lang}, {csv_path.name}). "
            f"Par defaut le moteur refuse le rendu partiel ; une livraison "
            f"partielle declaree exige un --min-coverage explicite (#13544 §2)."
        )

    # Gate #13544 §3 — orphelins inconditionnels : un cell_id du CSV absent du
    # notebook n'est jamais benin (desalignement de source). Aucun flag ne le
    # desactive : la correction est le CSV, pas une option. (Supersede le
    # guardrail opt-in #13546 : --fail-on-stale est un no-op deprecie.)
    if stats.n_orphan_keys > 0:
        sample = ", ".join(orphan_keys[:5])
        raise ValueError(
            f"orphelin(s) CSV : {stats.n_orphan_keys} cle(s) sans cellule "
            f"correspondante dans le notebook "
            f"(lang={lang}, {csv_path.name}). "
            f"Premier(s) : [{sample}{'...' if len(orphan_keys) > 5 else ''}]. "
            f"Refus inconditionnel -- resynchroniser le CSV plutot que de rendre."
        )

    if not dry_run and out_path is not None:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        # Atomic write : write to a sibling .tmp then rename. This prevents
        # leaving a partial notebook on disk if the process is killed mid-write.
        tmp_path = out_path.with_suffix(out_path.suffix + ".tmp")
        tmp_path.write_text(json.dumps(out_nb, ensure_ascii=False, indent=1), encoding="utf-8")
        tmp_path.replace(out_path)

    return RenderResult(
        out_path=out_path if not dry_run else None,
        nb_cells_out=len(new_cells),
        stats=stats,
        orphan_keys=orphan_keys,
    )


def reprovenance(
    nb_path: Path,
    source_path: Path,
    lang: str,
    *,
    apply: bool = False,
) -> ReprovenanceStats:
    """Re-stamp the copy-provenance of an existing derived notebook (#21496).

    Canonical repair for a twin whose provenance is incoherent — e.g. FR
    outputs assembled onto a derived file that still carries an older native
    run's ``metadata.papermill`` (reserve adjointe 6399643921 : le dérivé
    « assemble les sorties FR et la provenance d'exécution EN antérieure »).
    The tool owns the stamp so the repair goes through the generation path,
    never through hand-edited JSON.

    Precondition gates (fail-closed, the stamp is earned by measurement):

    * cell count and ``cell_id`` order identical between twin and source;
    * every code cell byte-identical to its source counterpart on
      ``source``, ``outputs`` and ``execution_count`` — the copied outputs
      must be the source's outputs, or there is nothing to attest;
    * the source must exist and be readable.

    On success (``apply=True``) the twin's notebook-level ``metadata.papermill``
    and every per-cell execution block (``metadata.papermill`` and
    ``metadata.execution``) are removed, ``metadata.t4`` is stamped from the
    source, and the file is atomically rewritten. Markdown cells, widget state
    and every other metadata key are left untouched. The stamp derives from the
    source content only, so the operation is idempotent : a second run rewrites
    byte-identical content.

    Raises :class:`ValueError` on any gate failure — no file is written.
    """
    if not nb_path.exists():
        raise FileNotFoundError(f"Notebook derivé introuvable : {nb_path}")
    if not source_path.exists():
        raise FileNotFoundError(f"Notebook source introuvable : {source_path}")

    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    src = json.loads(source_path.read_text(encoding="utf-8"))

    nb_cells = nb.get("cells", [])
    src_cells = src.get("cells", [])
    stats = ReprovenanceStats(n_cells=len(nb_cells))

    if len(nb_cells) != len(src_cells):
        raise ValueError(
            f"gate structure : {len(nb_cells)} cellules dans le dérivé vs "
            f"{len(src_cells)} dans la source — le stamp T4 exige la parité "
            f"de structure (refus, aucun fichier écrit)."
        )
    for i, (twin_cell, src_cell) in enumerate(zip(nb_cells, src_cells)):
        if twin_cell.get("id") != src_cell.get("id"):
            raise ValueError(
                f"gate structure : cellule {i} — id dérivé "
                f"{twin_cell.get('id')!r} != id source {src_cell.get('id')!r} "
                f"(refus, aucun fichier écrit)."
            )
        if twin_cell.get("cell_type") != src_cell.get("cell_type"):
            raise ValueError(
                f"gate structure : cellule {i} (id={twin_cell.get('id')!r}) — "
                f"type dérivé {twin_cell.get('cell_type')!r} != type source "
                f"{src_cell.get('cell_type')!r}. Un changement de type ferait "
                f"échapper la cellule à la porte de copie : un code devenu "
                f"markdown ne serait plus comparé du tout (refus, aucun "
                f"fichier écrit)."
            )
        if twin_cell.get("cell_type") == "code":
            stats.n_code_cells += 1
            for field_name in ("source", "outputs", "execution_count"):
                if twin_cell.get(field_name) != src_cell.get(field_name):
                    raise ValueError(
                        f"gate copie : cellule {i} (id={twin_cell.get('id')!r}) "
                        f"— le champ code {field_name!r} du dérivé diffère de "
                        f"la source. Le stamp attesterait une copie qui n'est "
                        f"pas byte-identique (refus, aucun fichier écrit)."
                    )

    new_cells = []
    for cell in nb_cells:
        meta = cell.get("metadata")
        if isinstance(meta, dict):
            stats.n_papermill_blocks_stripped += 1 if "papermill" in meta else 0
            stats.n_execution_blocks_stripped += 1 if "execution" in meta else 0
        new_cells.append(_strip_cell_execution_provenance(cell))

    nb_out = dict(nb)
    out_meta = {k: v for k, v in (nb.get("metadata") or {}).items()
                if k not in ("papermill", T4_PROVENANCE_KEY)}
    out_meta[T4_PROVENANCE_KEY] = _t4_stamp(src, source_path, lang)
    nb_out["metadata"] = out_meta
    nb_out["cells"] = new_cells

    if apply:
        tmp_path = nb_path.with_suffix(nb_path.suffix + ".tmp")
        tmp_path.write_text(
            json.dumps(nb_out, ensure_ascii=False, indent=1), encoding="utf-8"
        )
        tmp_path.replace(nb_path)
        stats.stamped = True

    return stats


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
    p.add_argument("--csv", type=Path, help="Translation CSV (schema #4957 §1) — requis hors mode --reprovenance")
    p.add_argument("--notebook", required=True, type=Path, help="Source notebook (FR) — ou notebook dérivé en mode --reprovenance")
    p.add_argument("--lang", required=True, help="Target language code (e.g. en, es, ar)")
    p.add_argument("--out", type=Path, help="Output notebook path (e.g. X_en.ipynb)")
    p.add_argument(
        "--reprovenance", action="store_true",
        help="Mode réparation de provenance (#21496) : --notebook désigne le "
             "dérivé, --source le carnet source (FR). Vérifie la parité de "
             "structure et de copie code (source/outputs/execution_count), "
             "retire metadata.papermill (notebook + cellules) et stamp "
             "metadata.t4. Sans --apply : contrôle seul, aucun écrit.",
    )
    p.add_argument(
        "--source", type=Path,
        help="Mode --reprovenance : carnet source (FR) dont les sorties ont "
             "été copiées dans le dérivé.",
    )
    p.add_argument(
        "--apply", action="store_true",
        help="Mode --reprovenance : écrire le re-stamp (défaut : dry-run).",
    )
    p.add_argument("--dry-run", action="store_true", help="Compute diff/stats, do not write")
    p.add_argument("--verbose", action="store_true", help="Print per-cell diagnostics")
    p.add_argument(
        "--require-translated", action="store_true",
        help="Refuse a render whose CSV carried 0 translated markdown cells "
             "(guardrail against FR-clone files, #10349). Default off: preserves "
             "the FR-placeholder re-render contract (#10039 criterion 3).",
    )
    p.add_argument(
        "--min-coverage", type=float, default=1.0,
        help="Refuse a render whose translated markdown fraction is below the "
             "threshold (0.0-1.0, #13544 §3). Default 1.0 (fail-closed) : a "
             "partial render must be explicitly requested by lowering this "
             "flag (#13544 §2). When 0 markdown cells are present the gate "
             "is bypassed (no defect to enforce).",
    )
    p.add_argument(
        "--fail-on-stale", action="store_true",
        help="Deprecated no-op (kept for translation-sync.yml compatibility) : "
             "orphan CSV rows now refuse the render unconditionally "
             "(#13544 §3, supersedes the #13546 opt-in).",
    )
    args = p.parse_args(argv)

    if args.reprovenance:
        if args.source is None:
            p.error("--reprovenance exige --source (le carnet source FR)")
        try:
            rstats = reprovenance(
                nb_path=args.notebook,
                source_path=args.source,
                lang=args.lang,
                apply=args.apply,
            )
        except (FileNotFoundError, ValueError) as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            return 2
        mode = f"-> {args.notebook} (re-stamp)" if args.apply else "(dry-run, aucun écrit)"
        print(
            f"[reprovenance] {args.notebook} <- {args.source} ({args.lang}) {mode}\n"
            f"  cells:     {rstats.n_cells} (structure vérifiée)\n"
            f"  code:      {rstats.n_code_cells} byte-identiques à la source\n"
            f"  stripped:  {rstats.n_papermill_blocks_stripped} bloc(s) papermill cellulaires\n"
            f"             {rstats.n_execution_blocks_stripped} bloc(s) execution cellulaires\n"
            f"  stamped:   {rstats.stamped}"
        )
        return 0

    if args.csv is None:
        p.error("--csv est requis hors mode --reprovenance")

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
            require_translated=args.require_translated,
            min_coverage=args.min_coverage,
            fail_on_stale=args.fail_on_stale,
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