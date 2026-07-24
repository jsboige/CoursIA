#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Diagnostic: per-notebook ``sorry`` tally for ``lean4-wsl`` notebooks.

Context (Epic #8051 — maturity 3-axes). The third maturity axis
``scientific_review`` (UNREVIEWED / AUTHOR_REVIEWED / PEER_REVIEWED /
FORMALLY_VERIFIED) is currently non-functional for Lean notebooks: catalog
generation cannot honestly emit ``FORMALLY_VERIFIED`` because (a) cell-level
``sorry`` absence does NOT imply transitive sorry-freeness (companion
``*_lean/`` lakes may carry their own debt), and (b) there is no aggregated
Lean-CI sorry-count artifact for the catalog to consume. This script gathers
the notebook-level half of that data so the axis can be designed honestly.

Scope (HONEST, read-only diagnostic):
  * scans inline Lean code cells of ``lean4-wsl`` kernelspec notebooks only;
  * strips Lean comments first (``--`` line, ``/- ... -/`` block) then counts
    word-bounded ``sorry`` — mirroring the canonical
    ``lean_notebook_utils._strip_lean_comments`` (FX-6 #1453, regression #7414);
  * does NOT aggregate companion-lake debt and is NOT authoritative. The
    authoritative sorry count for a lake remains
    ``lean_notebook_utils.count_sorry(project_path)`` / ``lake build`` warnings.
    A notebook reported ``SORRY-FREE`` here is a *candidate* only, NOT
    transitively verified.

Exit code: always 0 (diagnostic, not a gate — Lean sorry-debt is acknowledged
research, cf ``sorry-debt-easy-lakes-drained``). ``--json`` emits a machine
record for catalog/coordination consumption.

Usage::

    python scripts/audit/check_lean_notebook_sorry.py            # human table
    python scripts/audit/check_lean_notebook_sorry.py --json     # machine record
    python scripts/audit/check_lean_notebook_sorry.py --no-pager  # CI / pipe
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

# Canonical Lean comment-stripper (FX-6 #1453, regression #7414). Reused rather
# than duplicated so the tally stays byte-identical to count_sorry's semantics.
_REPO_ROOT = Path(__file__).resolve().parents[2]
_LEAN_UTILS_DIR = _REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean"
if str(_LEAN_UTILS_DIR) not in sys.path:
    sys.path.insert(0, str(_LEAN_UTILS_DIR))
try:
    from lean_notebook_utils import _strip_lean_comments as _strip_lean_comments  # type: ignore
except Exception:  # pragma: no cover - fallback only if canonical module moves
    _strip_lean_comments = None  # type: ignore

_NOTEBOOKS_ROOT = _REPO_ROOT / "MyIA.AI.Notebooks"
_LEAN_KERNEL = "lean4-wsl"
# Word-bounded ``sorry``: not preceded/followed by an identifier char, so
# ``sorryFoo`` / ``notsorry`` are excluded. Matches count_sorry's intent.
_SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")


@dataclass
class NotebookSorry:
    """Per-notebook cell-level sorry tally."""

    rel_path: str
    kernel: str
    code_cells: int
    sorry_count: int

    @property
    def verdict(self) -> str:
        return "SORRY-FREE-CANDIDATE" if self.sorry_count == 0 else "HAS-SORRY-DEBT"


@dataclass
class AuditReport:
    """Aggregate report across all lean4-wsl notebooks."""

    notebooks: list[NotebookSorry] = field(default_factory=list)
    scanned: int = 0
    skipped_nonlean: int = 0

    @property
    def total_sorry(self) -> int:
        return sum(n.sorry_count for n in self.notebooks)

    @property
    def sorry_free_count(self) -> int:
        return sum(1 for n in self.notebooks if n.sorry_count == 0)

    def to_dict(self) -> dict:
        return {
            "scope": "cell-level lean4-wsl notebooks only (NOT transitive; see module docstring)",
            "canonical_authoritative": "lean_notebook_utils.count_sorry(lake) / lake build warnings",
            "scanned_lean_notebooks": len(self.notebooks),
            "skipped_nonlean_notebooks": self.skipped_nonlean,
            "total_sorry_cell_level": self.total_sorry,
            "sorry_free_candidates": self.sorry_free_count,
            "sorry_debt_notebooks": len(self.notebooks) - self.sorry_free_count,
            "notebooks": [
                {
                    "path": n.rel_path,
                    "kernel": n.kernel,
                    "code_cells": n.code_cells,
                    "sorry_count": n.sorry_count,
                    "verdict": n.verdict,
                }
                for n in sorted(self.notebooks, key=lambda x: (-x.sorry_count, x.rel_path))
            ],
        }


def _kernel_name(nb: dict) -> str:
    return (
        ((nb.get("metadata") or {}).get("kernelspec") or {}).get("name") or ""
    )


def _count_cell_sorry(source_lines: list[str]) -> int:
    """Count word-bounded ``sorry`` in a notebook cell's joined source."""
    if not source_lines:
        return 0
    joined = "\n".join(source_lines)
    stripped = _strip_lean_comments(joined) if _strip_lean_comments else joined
    return len(_SORRY_RE.findall(stripped))


def scan_notebook(nb_path: Path, root: Path | None = None) -> NotebookSorry | None:
    """Return a ``NotebookSorry`` for a lean4-wsl notebook, else None.

    None signals "not a lean4-wsl notebook" (counted separately). Parse errors
    raise — a corrupt .ipynb in the tree is a real defect worth surfacing.
    ``root`` scopes ``rel_path``; if the notebook is not under ``root`` the full
    path is used so standalone calls (e.g. tests) never crash on relative_to.
    """
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    kernel = _kernel_name(nb)
    if kernel != _LEAN_KERNEL:
        return None
    code_cells = 0
    sorry_total = 0
    for cell in nb.get("cells") or []:
        if (cell.get("cell_type") or "") != "code":
            continue
        code_cells += 1
        sorry_total += _count_cell_sorry(cell.get("source") or [])
    root = root or _REPO_ROOT
    try:
        rel = nb_path.relative_to(root).as_posix()
    except ValueError:
        rel = nb_path.as_posix()
    return NotebookSorry(rel_path=rel, kernel=kernel, code_cells=code_cells, sorry_count=sorry_total)


def run_audit(root: Path | None = None) -> AuditReport:
    """Scan every ``*.ipynb`` under root, tally sorry for lean4-wsl ones."""
    root = root or _NOTEBOOKS_ROOT
    report = AuditReport()
    for nb_path in sorted(root.rglob("*.ipynb")):
        try:
            result = scan_notebook(nb_path, root=root)
        except (json.JSONDecodeError, KeyError) as exc:  # pragma: no cover
            raise RuntimeError(f"corrupt notebook {nb_path}: {exc}") from exc
        if result is None:
            report.skipped_nonlean += 1
        else:
            report.notebooks.append(result)
            report.scanned += 1
    return report


def _human_report(report: AuditReport) -> str:
    lines = [
        "Lean4-wsl notebook sorry audit (CELL-LEVEL, not transitive)",
        "=" * 64,
        f"scanned lean4-wsl notebooks : {len(report.notebooks)}",
        f"skipped non-lean notebooks  : {report.skipped_nonlean}",
        f"total sorry (cell-level)    : {report.total_sorry}",
        f"SORRY-FREE candidates       : {report.sorry_free_count}",
        f"HAS-SORRY-DEBT notebooks    : {len(report.notebooks) - report.sorry_free_count}",
        "",
        "per-notebook (sorry desc, then path):",
    ]
    for n in sorted(report.notebooks, key=lambda x: (-x.sorry_count, x.rel_path)):
        lines.append(
            f"  {n.sorry_count:>3} sorry | {n.code_cells:>3} cells | {n.verdict:<22} | {n.rel_path}"
        )
    lines.extend([
        "",
        "NOTE: cell-level only. Companion *_lean/ lake debt is NOT aggregated.",
        "Authoritative: lean_notebook_utils.count_sorry(lake) / lake build warnings.",
        "A SORRY-FREE-CANDIDATE here is NOT transitively verified (Epic #8051).",
    ])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="emit machine record instead of human table")
    parser.add_argument("--no-pager", action="store_true", help="plain stdout (CI/pipe); default already plain")
    args = parser.parse_args(argv)
    report = run_audit()
    if args.json:
        print(json.dumps(report.to_dict(), indent=2, ensure_ascii=False))
    else:
        print(_human_report(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
