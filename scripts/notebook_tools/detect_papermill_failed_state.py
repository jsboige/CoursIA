#!/usr/bin/env python3
"""
Detect notebooks whose papermill run did not complete cleanly.

When papermill executes a notebook it stamps ``metadata.papermill`` with a
small status block. A clean run leaves ``exception == None`` and ``status``
unset (or set to ``completed``). Two failure modes leave **detectable
fingerprints**:

  * **Hard failure**: ``metadata.papermill.exception`` is truthy (a
    non-``None`` value, typically ``True``). papermill caught an exception
    during execution and recorded the notebook as failed. The cell
    outputs may contain a partial traceback and the cells after the
    failure point never ran. Committing such a notebook is a C.2 violation
    (regression of substance — outputs do not reflect the source).

  * **Soft failure (pending)**: ``metadata.papermill.status == "pending"``.
    papermill started the run but never finished writing the metadata
    block — typically because the executor process was killed (OOM, manual
    abort, machine reboot). The notebook looks like it executed but the
    metadata is stale; re-executing it produces fresh metadata.

**Scope vs ``detect_papermill_path_leak.py``.** That detector inspects
**paths** inside papermill metadata and output streams. This one inspects
**state fields** (``exception``, ``status``, ``end_time``, ``start_time``).
Both are read-only companions of the same family of papermill hygiene
checks. They can be combined in a single CI step without conflict.

**Usage.**

    # Single file:
    python detect_papermill_failed_state.py --scan path/to/notebook.ipynb

    # Whole directory tree (skips .git/_archives/__pycache__/node_modules):
    python detect_papermill_failed_state.py --scan-all .

    # CI gate: exit 1 if any notebook is in a failed state:
    python detect_papermill_failed_state.py --scan-all . --check

    # Human-readable summary alongside JSON:
    python detect_papermill_failed_state.py --scan-all . --summary

**Design choices.**

- **No external deps** beyond the Python 3.10 stdlib (``json``, ``re``,
  ``argparse``, ``pathlib``).
- **State semantics**: ``exception is None and status != 'pending'`` →
  clean. Anything else is flagged with a ``severity`` (``high`` for hard
  failures, ``medium`` for pending). The JSON defect entry includes the
  raw ``exception``/``status`` value and the run's ``end_time`` /
  ``start_time`` (when present) so a reviewer can triage quickly.
- **Output files (``_output.ipynb``)** are intentionally scanned alongside
  source notebooks: they are exactly where papermill writes its metadata
  block, and committing a failed-output notebook into the repo is the
  regression this detector is designed to catch.
- **No ``--apply``**: this is a read-only detector. The fix is to
  re-execute the notebook through papermill (or to drop the failed output
  if the source is the canonical artifact). Fix-up stays in the user's
  hands; the detector's job is to surface the failure list.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


# --- Defect classification ---


def _classify_papermill_state(pm: dict) -> list[dict]:
    """Return a list of defects for the papermill state of one notebook.

    Empty list = clean state. One defect per failure mode, not per field:
    a notebook with both ``exception`` truthy and ``status == "pending"``
    produces a single ``hard_failure`` defect (the more severe class).
    """
    defects: list[dict] = []
    if not isinstance(pm, dict):
        return defects

    exception = pm.get("exception")
    status = pm.get("status")
    end_time = pm.get("end_time")
    start_time = pm.get("start_time")

    # Hard failure: papermill caught an exception during execution.
    # ``exception`` is None for clean runs; any other value (typically
    # True, but papermill also records a string traceback in some
    # versions) means a failure occurred.
    if exception is not None:
        defects.append({
            "kind": "papermill_hard_failure",
            "location": "metadata.papermill.exception",
            "exception": exception,
            "status": status,
            "start_time": start_time,
            "end_time": end_time,
            "severity": "high",
        })
        return defects  # hard failure dominates pending

    # Soft failure: status is "pending" (run was started but never
    # finished writing the metadata block).
    if status == "pending":
        defects.append({
            "kind": "papermill_pending",
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
# ``scrub_papermill_paths.py`` and ``detect_papermill_path_leak.py``.
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
    """Return the defects list for a single notebook."""
    nb = _read_notebook(nb_path)
    if nb is None:
        return [{
            "kind": "unreadable_notebook",
            "location": str(nb_path),
            "severity": "high",
            "reason": "JSON decode error or unreadable file",
        }]
    pm = nb.get("metadata", {}).get("papermill")
    if pm is None:
        # No papermill metadata at all = the notebook was not run through
        # papermill. We intentionally do NOT flag this as a defect; manual
        # execution is a valid authoring path.
        return []
    return _classify_papermill_state(pm)


def scan_tree(root: Path) -> list[dict]:
    """Scan every notebook under ``root``; return a flat defects report.

    Each defect is augmented with ``file`` (relative to ``root`` when
    possible) so a CI gate can pinpoint the offender. Defects from
    different notebooks are not merged — order is preserved.
    """
    report: list[dict] = []
    for nb_path in iter_notebooks(root):
        try:
            rel = str(nb_path.relative_to(root))
        except ValueError:
            rel = str(nb_path)
        for d in scan_notebook(nb_path):
            d_with_file = {"file": rel, **d}
            report.append(d_with_file)
    return report


# --- CLI ---


def _build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="detect_papermill_failed_state.py",
        description=(
            "Detect notebooks whose papermill run did not complete "
            "cleanly (read-only, CI-friendly)."
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
        report = [
            {"file": str(target), **d}
            for d in scan_notebook(target)
        ]
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
        f"[detect_papermill_failed_state] {n} defect(s) in "
        f"{len(files_with_defects)} file(s).",
        file=sys.stderr,
    )
    for kind, count in sorted(by_kind.items()):
        print(f"  - {kind}: {count}", file=sys.stderr)


if __name__ == "__main__":
    raise SystemExit(main())