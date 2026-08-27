#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Gate/diagnostic: ``lean4-wsl`` notebooks committed with broken-repl outputs.

Context (Epic #11703, incident #11874). The ``lean4-wsl`` "kernel" is
``lake env repl`` through a wrapper. When the ``repl`` binary's toolchain
mismatches the lake's resolved toolchain, the kernel is ``REPL_STDLIB_BROKEN``:
even ``#eval 2+2`` fails, and imports fail *silently* (``{"env": N}`` MUET).
The alectryon renderer then commits outputs like::

    #check Regex
           ─────▶ ❌ Unknown identifier `Regex`
    #eval 2+2
           ─────▶ ❌ Unknown constant `OfNat`
    import Finiteness.Basic
           ─────▶ ❌ invalid 'import' command, it must be used in the beginning of the file

Crucially, such cells carry ``execution_count != null`` AND non-empty
``outputs``, so the existing output-presence guards (``check_null_exec``,
``validate_pr_notebooks`` under H.3/C.2) do *not* fire: a notebook can be
committed with a burned-out kernel and still pass every presence check. This
script closes that gap — it flags any ``lean4-wsl`` notebook whose code-cell
outputs carry an alectryon broken-repl error signature.

Honest scope (mirrors ``check_lean_notebook_sorry.py``):
  * scans ``lean4-wsl`` kernelspec notebooks only;
  * matches the alectryon error marker ON THE OUTPUT (``text/plain`` /
    ``text/html``), NOT the Lean source — a cell can legitimately contain an
    error demo; the signal here is a *runnable* cell that the kernel failed to
    resolve (the ``❌`` red-X alectryon prefix on ``Unknown *`` /
    ``invalid 'import'``);
  * diagnostic by default (exit 0); ``--fail`` turns a finding into exit 1 for
    the pre-commit / PR safety net. Calling without ``--fail`` never blocks a
    deliberate pedagogical error demo.

Exit code: 0 normally; 1 with ``--fail`` if any notebook has at least
``--fail-threshold`` (default 2) code cells carrying a signature. ``--json``
emits a machine record for catalog/coordination consumption.

Usage::

    python scripts/notebook_tools/check_lean_output_health.py                # human table (exit 0)
    python scripts/notebook_tools/check_lean_output_health.py --json         # machine record
    python scripts/notebook_tools/check_lean_output_health.py --fail         # gate (exit 1 on finding)
    python scripts/notebook_tools/check_lean_output_health.py --path <file>  # single notebook
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

_REPO_ROOT = Path(__file__).resolve().parents[2]
_NOTEBOOKS_ROOT = _REPO_ROOT / "MyIA.AI.Notebooks"
_LEAN_KERNEL = "lean4-wsl"
# Lean interpreter error indicators that a broken/mismatched ``repl`` emits on
# cells that were meant to succeed. "Unknown constant `OfNat`" on ``#eval 2+2``
# is the canonical #11874 control-positive failure; "invalid 'import' command"
# is the silent-import symptom. We match the alectryon `❌` marker so a benign
# prose mention of these strings (e.g. a docstring) is not counted.
_ALECTRYON_ERR_RE = re.compile(
    r"(?:❌\s*)?"                # optional alectryon red-X marker
    r"(?:Unknown (?:identifier|constant)|unknown constant|invalid 'import' command)",
)
# Minimum failing cells per notebook before ``--fail`` considers it a finding.
# A single cell can be a deliberate error demo; 2+ is a systemic broken execute.
_DEFAULT_FAIL_THRESHOLD = 2


@dataclass
class CellFinding:
    index: int
    matched: str


@dataclass
class NotebookHealth:
    """Per-notebook lean4-wsl output-health tally."""

    rel_path: str
    kernel: str
    code_cells: int
    findings: list[CellFinding] = field(default_factory=list)
    matched_strings: set[str] = field(default_factory=set)
    failing_cell_indices: set[int] = field(default_factory=set)

    @property
    def failing_cell_count(self) -> int:
        """Number of DISTINCT code cells carrying at least one finding."""
        return len(self.failing_cell_indices)

    @property
    def healthy(self) -> bool:
        return not self.findings


@dataclass
class AuditReport:
    """Aggregate health report across all lean4-wsl notebooks."""

    notebooks: list[NotebookHealth] = field(default_factory=list)
    scanned: int = 0
    skipped_nonlean: int = 0

    @property
    def affected(self) -> list[NotebookHealth]:
        return [n for n in self.notebooks if n.findings]

    def to_dict(self) -> dict:
        return {
            "scope": "lean4-wsl notebooks only; output-level alectryon broken-repl signatures (#11874)",
            "scanned_lean_notebooks": len(self.notebooks),
            "skipped_nonlean_notebooks": self.skipped_nonlean,
            "affected_notebooks": len(self.affected),
            "notebooks": [
                {
                    "path": n.rel_path,
                    "kernel": n.kernel,
                    "code_cells": n.code_cells,
                    "failing_cells": n.failing_cell_count,
                    "healthy": n.healthy,
                    "matched_signatures": sorted(n.matched_strings),
                    "findings": [
                        {"cell_index": f.index, "matched": f.matched} for f in n.findings
                    ],
                }
                for n in sorted(self.notebooks, key=lambda x: (-x.failing_cell_count, x.rel_path))
            ],
        }


def _kernel_name(nb: dict) -> str:
    return ((nb.get("metadata") or {}).get("kernelspec") or {}).get("name") or ""


def _output_text(output: dict) -> str:
    """Join ``text/plain`` (and ``text/html``) of an output into one string."""
    data = output.get("data") or {}
    parts: list[str] = []
    for key in ("text/plain", "text/html"):
        val = data.get(key)
        if isinstance(val, list):
            parts.append("".join(val))
        elif isinstance(val, str):
            parts.append(val)
    return "\n".join(parts)


def _scan_cell_outputs(cell: dict) -> list[CellFinding]:
    """Return findings for a single code cell's outputs."""
    findings: list[CellFinding] = []
    for output in cell.get("outputs") or []:
        text = _output_text(output)
        if not text:
            continue
        for match in _ALECTRYON_ERR_RE.finditer(text):
            findings.append(CellFinding(index=0, matched=match.group(0).strip()))
    return findings


def scan_notebook(nb_path: Path, root: Path | None = None) -> NotebookHealth | None:
    """Return a ``NotebookHealth`` for a lean4-wsl notebook, else None.

    ``root`` scopes ``rel_path``; if the notebook is not under ``root`` the full
    path is used so standalone calls never crash on ``relative_to``. Parse
    errors raise — a corrupt .ipynb is a real defect worth surfacing.
    """
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    kernel = _kernel_name(nb)
    if kernel != _LEAN_KERNEL:
        return None
    health = NotebookHealth(
        rel_path="",
        kernel=kernel,
        code_cells=sum(1 for c in nb.get("cells") or [] if (c.get("cell_type") or "") == "code"),
    )
    for idx, cell in enumerate(nb.get("cells") or []):
        if (cell.get("cell_type") or "") != "code":
            continue
        found = _scan_cell_outputs(cell)
        if found:
            health.failing_cell_indices.add(idx)
        for f in found:
            f.index = idx
            health.findings.append(f)
            health.matched_strings.add(f.matched)
    root = root or _REPO_ROOT
    try:
        rel = nb_path.relative_to(root).as_posix()
    except ValueError:
        rel = nb_path.as_posix()
    health.rel_path = rel
    return health


def run_audit(root: Path | None = None, explicit_path: Path | None = None) -> AuditReport:
    """Scan every ``*.ipynb`` under root (or a single file), tally lean4-wsl health."""
    report = AuditReport()
    if explicit_path is not None:
        result = scan_notebook(explicit_path, root=root)
        if result is None:
            report.skipped_nonlean += 1
        else:
            report.notebooks.append(result)
            report.scanned += 1
        return report
    root = root or _NOTEBOOKS_ROOT
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
        "Lean4-wsl notebook output-health audit (broken-repl signatures, #11874)",
        "=" * 72,
        f"scanned lean4-wsl notebooks : {len(report.notebooks)}",
        f"skipped non-lean notebooks  : {report.skipped_nonlean}",
        f"affected notebooks          : {len(report.affected)}",
        "",
        "per-notebook (failing cells desc, then path):",
    ]
    if not report.affected:
        lines.append("  (none — all lean4-wsl notebooks look output-healthy)")
    for n in sorted(report.notebooks, key=lambda x: (-x.failing_cell_count, x.rel_path)):
        if not n.findings:
            continue
        lines.append(f"  {n.failing_cell_count:>3} failing | {n.code_cells:>3} cells | {n.rel_path}")
        for sig in sorted(n.matched_strings):
            lines.append(f"        x {sig}")
    lines.append(
        "\nNOTE: output-level diagnostic. A finding means a runnable cell was "
        "committed with an alectryon broken-repl error (#11874) — the cell "
        "'executed' but the kernel never resolved it. Review, do not auto-merge."
    )
    return "\n".join(lines)


def _fails(report: AuditReport, threshold: int) -> bool:
    return any(n.failing_cell_count >= threshold for n in report.notebooks)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", action="store_true", help="emit machine record instead of human table")
    parser.add_argument("--fail", action="store_true", help="exit 1 if a finding meets the threshold")
    parser.add_argument("--fail-threshold", type=int, default=_DEFAULT_FAIL_THRESHOLD,
                        help=f"failing cells per notebook to trigger --fail (default {_DEFAULT_FAIL_THRESHOLD})")
    parser.add_argument("--path", type=Path, default=None,
                        help="scan a single notebook instead of the whole tree")
    parser.add_argument("--root", type=Path, default=None,
                        help="notebook tree root (default: MyIA.AI.Notebooks)")
    args = parser.parse_args(argv)
    report = run_audit(root=args.root, explicit_path=args.path)
    if args.json:
        print(json.dumps(report.to_dict(), indent=2, ensure_ascii=False))
    else:
        print(_human_report(report))
    if args.fail and _fails(report, args.fail_threshold):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
