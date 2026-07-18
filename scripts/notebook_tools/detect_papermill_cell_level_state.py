#!/usr/bin/env python3
"""Detect notebooks whose papermill run failed at the cell level.

Companion to ``detect_papermill_failed_state.py`` (#7079). That detector
inspects the **top-level** ``metadata.papermill`` block and reports two
defect classes: ``papermill_hard_failure`` (exception non-None) and
``papermill_pending`` (status="pending"). It does **not** inspect
**cell-level** metadata — and papermill writes per-cell status metadata
alongside the top-level block.

This detector picks up that cell-level layer. Three defect classes:

  * **Cell-level hard failure**: ``cells[i].metadata.papermill.exception``
    is truthy (typically ``True``). papermill caught an exception while
    executing cell ``i``; the cell's own metadata records the failure
    even when the top-level block does not (e.g. when a re-execution
    after the failure cleaned the top-level state but left the cell
    metadata behind).
  * **Cell-level pending**: ``cells[i].metadata.papermill.status == "pending"``.
    papermill started but never finished cell ``i`` — the cell looks
    like it was executed but the metadata is stale. Re-executing the
    notebook overwrites these fields with fresh values.
  * **Cell-level error tag**: ``"papermill-error-cell-tag"`` is in
    ``cells[i].metadata.tags``. papermill (or its underlying nbconvert
    pipeline) tags the cell that raised the exception. This is a
    complementary fingerprint to ``exception=True`` — it persists even
    after the metadata block is rewritten — and it is the only signal
    some notebook formats expose when the ``metadata.papermill`` block
    was scrubbed but the tag was left behind.

**Why a separate detector (vs. extending ``detect_papermill_failed_state``).**

The top-level and cell-level layers are independent failure surfaces:

- A notebook can have a **clean top-level** ``metadata.papermill`` (clean
  run) but **dirty cell-level** metadata from an earlier failed run that
  was retried successfully — papermill overwrites the top-level block on
  every run, but cell-level fields are merged into existing metadata, so
  stale fields can survive.
- The inverse is also possible: the top-level block can be ``hard_failure``
  while every cell reports ``status == "completed"`` if papermill ran
  per-cell execution through ``--prepare-only`` / ``--execute`` flows that
  populated cells before the failure point but recorded the global failure
  on shutdown.

A single detector would conflate these and force reviewers to read every
flag — a top-level ``exception`` is a single critical defect, while 50
cell-level ``status=pending`` flags might be one stale run worth one fix.
Keeping the layers separate matches how a triage process works and how
the dashboards (#7079 vs this detector) are routed.

**Scope vs ``detect_papermill_path_leak.py`` / ``detect_papermill_failed_state.py``**.

- ``detect_papermill_path_leak.py`` (#7076) inspects **paths** in
  ``metadata.papermill.{input,output}_path`` and inside output streams.
- ``detect_papermill_failed_state.py`` (#7079) inspects top-level
  ``metadata.papermill.{exception,status,start_time,end_time}``.
- **This detector** inspects the same fields on ``cells[i].metadata.papermill``
  plus ``cells[i].metadata.tags``.

All three are read-only CI-friendly companions; they can run sequentially
in the same CI step without conflict.

**Usage.**

    # Single file:
    python detect_papermill_cell_level_state.py --scan path/to/notebook.ipynb

    # Whole directory tree (skips .git/_archives/__pycache__/node_modules):
    python detect_papermill_cell_level_state.py --scan-all .

    # CI gate: exit 1 if any notebook has a cell-level defect:
    python detect_papermill_cell_level_state.py --scan-all . --check

    # Human-readable summary alongside JSON:
    python detect_papermill_cell_level_state.py --scan-all . --summary

**Design choices.**

- **No external deps** beyond the Python 3.10 stdlib (``json``, ``re``,
  ``argparse``, ``pathlib``).
- **Cell-level classification mirrors the top-level one**: ``exception``
  is the dominant defect, ``status="pending"`` is the secondary one,
  the ``papermill-error-cell-tag`` is its own class (medium severity —
  it is a fingerprint, not a runtime state).
- **Severity ladder** matches the top-level detector: ``high`` for
  ``exception`` (the cell's own outputs may be partial / missing),
  ``medium`` for ``status="pending"`` and ``error-tag``. A defect is
  emitted **per cell** so a reviewer can pinpoint the failure point in
  the notebook without re-scanning.
- **Cell with both ``exception=True`` and ``error-tag``** produces a
  single ``cell_papermill_hard_failure`` defect (the more severe class
  absorbs the tag) — same single-defect-per-cell discipline as the
  top-level detector's single-defect-per-notebook.
- **Output files (``_output.ipynb``)** are intentionally scanned alongside
  source notebooks: they are exactly where papermill writes its per-cell
  metadata. A committed ``_output.ipynb`` with stale cell-level metadata
  is the regression this detector is designed to catch.
- **No ``--apply``**: this is a read-only detector. Fix is to re-execute
  the notebook through papermill (which overwrites both top-level and
  cell-level metadata). Fix-up stays in the user's hands.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


# --- Cell-level defect classification ---


def _classify_cell_level_state(cell_meta: dict) -> list[dict]:
    """Return a list of defects for the papermill state of ONE cell.

    Empty list = clean cell. The discipline mirrors
    ``detect_papermill_failed_state._classify_papermill_state``: hard
    failure dominates pending, and the ``papermill-error-cell-tag`` is
    folded into the hard-failure defect (single defect per cell).
    """
    defects: list[dict] = []

    if not isinstance(cell_meta, dict):
        return defects

    pm = cell_meta.get("papermill")
    exception = pm.get("exception") if isinstance(pm, dict) else None
    status = pm.get("status") if isinstance(pm, dict) else None
    start_time = pm.get("start_time") if isinstance(pm, dict) else None
    end_time = pm.get("end_time") if isinstance(pm, dict) else None

    # Hard failure: the cell itself failed during papermill execution.
    # ``exception`` is None for clean runs; ``False`` is the explicit
    # success baseline (papermill stamps ``False`` on every cell that
    # did not raise). Only truthy values (typically ``True``, sometimes a
    # string traceback in some papermill versions) signal a failure.
    if exception:
        defects.append({
            "kind": "cell_papermill_hard_failure",
            "location": "metadata.papermill.exception",
            "exception": exception,
            "status": status,
            "start_time": start_time,
            "end_time": end_time,
            "severity": "high",
        })
        return defects  # hard failure dominates pending AND error-tag

    # Tag-based fingerprint: even if ``metadata.papermill`` was scrubbed,
    # papermill (or nbconvert) leaves a tag on the cell that raised.
    # Only emitted when the cell is NOT already flagged as a hard
    # failure (single defect per cell, hard-failure absorbs the tag).
    tags = cell_meta.get("tags") or []
    if isinstance(tags, list) and "papermill-error-cell-tag" in tags:
        defects.append({
            "kind": "cell_papermill_error_tag",
            "location": "metadata.tags",
            "tag": "papermill-error-cell-tag",
            "severity": "medium",
        })

    # Soft failure: cell started but never finished.
    if status == "pending":
        defects.append({
            "kind": "cell_papermill_pending",
            "location": "metadata.papermill.status",
            "exception": exception,
            "status": status,
            "start_time": start_time,
            "end_time": end_time,
            "severity": "medium",
        })

    return defects


# --- Scanner glue ---


def _read_notebook(nb_path: Path) -> dict | None:
    try:
        with nb_path.open(encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError, UnicodeDecodeError):
        return None
    return data if isinstance(data, dict) else None


# Directories skipped during recursive scans. Mirrors the conventions in
# ``scrub_papermill_paths.py``, ``detect_papermill_path_leak.py`` and
# ``detect_papermill_failed_state.py``.
_SKIP_DIR_NAMES = frozenset({
    ".git",
    "_archives",
    "__pycache__",
    "node_modules",
    ".venv",
    "venv",
})


def iter_notebooks(root: Path) -> list[Path]:
    """Yield every ``*.ipynb`` under ``root`` recursively, skipping noise dirs."""
    if root.is_file():
        return [root] if root.suffix == ".ipynb" else []
    if not root.is_dir():
        return []
    out: list[Path] = []
    for p in root.rglob("*.ipynb"):
        if any(part in _SKIP_DIR_NAMES for part in p.parts):
            continue
        out.append(p)
    return sorted(out)


def scan_notebook(nb_path: Path) -> list[dict]:
    """Return the defects list for a single notebook.

    One defect per affected cell (not per cell field): a cell with both
    ``exception=True`` and ``error-tag`` yields a single
    ``cell_papermill_hard_failure`` defect. Defects are returned in cell
    order so a reviewer can match them to the notebook structure.
    """
    nb = _read_notebook(nb_path)
    if nb is None:
        return [{
            "kind": "unreadable_notebook",
            "location": str(nb_path),
            "severity": "high",
            "reason": "JSON decode error or unreadable file",
        }]

    cells = nb.get("cells") or []
    if not isinstance(cells, list):
        return []

    defects: list[dict] = []
    for idx, cell in enumerate(cells):
        if not isinstance(cell, dict):
            continue
        cell_meta = cell.get("metadata") or {}
        for d in _classify_cell_level_state(cell_meta):
            defects.append({
                "cell_index": idx,
                "file": str(nb_path),
                **d,
            })
    return defects


def scan_tree(root: Path) -> list[dict]:
    """Scan every notebook under ``root``; return a flat defects report.

    Each defect is augmented with ``file`` (relative to ``root`` when
    possible) and ``cell_index`` so a CI gate can pinpoint the offender
    cell. Defects from different notebooks are not merged — order is
    preserved (notebook order, then cell order within a notebook).
    """
    report: list[dict] = []
    for nb_path in iter_notebooks(root):
        try:
            rel = str(nb_path.relative_to(root))
        except ValueError:
            rel = str(nb_path)
        for d in scan_notebook(nb_path):
            # Spread ``d`` first, then override ``file`` with the
            # relative path. (In a dict literal the last key wins, so
            # ``{"file": rel, **d}`` would keep the absolute path
            # stamped by ``scan_notebook``.)
            d_with_rel = {**d, "file": rel}
            report.append(d_with_rel)
    return report


# --- CLI ---


def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="detect_papermill_cell_level_state.py",
        description=(
            "Detect notebooks whose papermill run failed at the cell "
            "level (read-only, CI-friendly)."
        ),
    )
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument(
        "--scan", metavar="PATH",
        help="Scan a single notebook file (.ipynb).",
    )
    mode.add_argument(
        "--scan-all", metavar="DIR", nargs="?", const=".",
        help="Scan every notebook under DIR (default: current directory).",
    )
    p.add_argument(
        "--check", action="store_true",
        help="CI gate: exit 1 if any defect is found, suppress JSON.",
    )
    p.add_argument(
        "--summary", action="store_true",
        help="Print a human-readable summary alongside the JSON report.",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = _build_arg_parser().parse_args(argv)
    target = Path(args.scan if args.scan is not None else args.scan_all)
    if not target.exists():
        print(f"error: path does not exist: {target}", file=sys.stderr)
        return 2

    if args.scan is not None:
        report = scan_notebook(target)
    else:
        report = scan_tree(target)

    if args.summary and not args.check:
        _print_summary(report)
    elif not args.check:
        print(json.dumps(report, indent=2, ensure_ascii=False))

    if args.check and report:
        if args.summary:
            _print_summary(report)
        return 1
    return 0


def _print_summary(report: list[dict]) -> None:
    n = len(report)
    by_kind: dict[str, int] = {}
    files_with_defects: set[str] = set()
    for d in report:
        by_kind[d.get("kind", "?")] = by_kind.get(d.get("kind", "?"), 0) + 1
        if "file" in d:
            files_with_defects.add(d["file"])
    print(
        f"[detect_papermill_cell_level_state] {n} defect(s) in "
        f"{len(files_with_defects)} file(s).",
        file=sys.stderr,
    )
    for kind, count in sorted(by_kind.items()):
        print(f"  - {kind}: {count}", file=sys.stderr)


if __name__ == "__main__":
    raise SystemExit(main())
