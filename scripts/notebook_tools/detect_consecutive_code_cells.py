#!/usr/bin/env python3
"""Detect runs of consecutive code cells in pedagogical notebooks (#12797).

The user's observation (2026-08-24) -- in a pedagogical notebook, two code
cells that **follow each other** (no markdown cell in between) are "almost
always an opportunity to propose an intermediate markdown cell, and otherwise
a reason to merge." Identify these notebooks and surface them as a CI
advisory, not a blocking gate.

The detector reuses (never re-implements) the corpus/kind classification of
``count_exercises.py`` (#10479 pattern, #12797 acceptance #1): out-of-corpus
notebooks (``artifact`` / ``template`` / ``vendored`` / ``archive`` /
``legacy`` / ``tooling`` / ``student``) and the ``setup`` exemption are
imported, not duplicated -- the label and the canonical tool cannot diverge.
This means: a notebook classified ``setup`` (environment scaffolding with no
prose budget) is exempt; an out-of-corpus notebook is exempt. The detector
runs ONLY on ``standard`` + ``lean`` corpus kinds (the same kinds the density
floor judges), because out-of-corpus / setup notebooks would otherwise
trigger the label for structural reasons unrelated to pedagogy.

This is the missing ORGAN for that observation: it wires the consecutive-code-
cells measure to PRs, exactly as ``pedagogy_density.py`` did for the
``chars / code cell`` floor and as ``count_exercises.py`` did for the
``>= 3 exercises`` convention (#8814). It is ADVISORY by design (#12797
acceptance, decision user 2026-08-24): the job ALWAYS exits 0; the
actionable payload is the ``consecutive-code-cells`` LABEL the workflow
poses, never the green conclusion of the job (green by construction -- the
same trap that let non-conforming PRs through #8797 and #8819).

A SECOND label, ``consecutive-code-cells-unmeasured``, covers notebooks the
detector could not read (JSON parse failure) or that have no code cell at
all. The #8819 lesson applied: "I could not measure" and "I measured, run
detected" call for different reactions, so they never collapse into one
label -- and the summary never claims conformity while ``unmeasured > 0``.

The threshold is deliberately NOT a CLI flag: it is locked by the user's
decision 2026-08-24 at ``MIN_RUN = 2`` ("lecture littérale cellules qui se
suivent", 38% du corpus). A mutable threshold would silently change what
the label means from one invocation to the next.

Usage:
    python detect_consecutive_code_cells.py                              # whole corpus
    python detect_consecutive_code_cells.py MyIA.AI.Notebooks/Search     # one family
    python detect_consecutive_code_cells.py path/to/a.ipynb path/to/b.ipynb
    python detect_consecutive_code_cells.py --paths a.ipynb --json
    git diff --name-only BASE HEAD -- '*.ipynb' \\
        | python detect_consecutive_code_cells.py --stdin --json
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

try:
    import nbformat
    from nbformat.warnings import MissingIDFieldWarning
    import warnings as _warnings
    # nbformat >= 5.1 emits a MissingIDFieldWarning on read for legacy
    # notebooks that lack cell ids. The cells still parse, the ids are
    # auto-filled by nbformat, and the warning is the same noise that
    # pedagogy_density.py and count_exercises.py ship with. Filter it at
    # the source so the JSON stdout stays clean for the workflow parser.
    _warnings.filterwarnings("ignore", category=MissingIDFieldWarning)
except ImportError:
    nbformat = None  # type: ignore[assignment]

THIS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(THIS_DIR))

from count_exercises import classify_notebook  # noqa: E402  (path-managed import)

NOTEBOOKS_DIR = Path(__file__).resolve().parents[2] / "MyIA.AI.Notebooks"

#: Threshold locked by user decision 2026-08-24 ("cellules qui se suivent",
#: lecture litterale). 38% du corpus depasse ce seuil ; baisser ou monter le
#: seuil change silencieusement le label.
MIN_RUN = 2

#: Kinds judges against the consecutive-code-cells convention. Mirror
#: :data:`DENSITY_JUDGED_KINDS` in pedagogy_density.py -- a corpus notebook
#: is a pedagogical artefact ; out-of-corpus + setup ne sont JAMAIS concernes.
JUDGED_KINDS = frozenset({"standard", "lean"})


@dataclass
class Run:
    """One run of consecutive code cells in a single notebook.

    ``start_cell`` / ``end_cell`` are 0-indexed cell positions in the notebook.
    ``length`` is the number of code cells in the run (>= MIN_RUN by
    construction; a run of length < MIN_RUN is filtered at detection time).
    """

    start_cell: int
    end_cell: int
    length: int


@dataclass
class Verdict:
    """One notebook's consecutive-code-cells verdict.

    ``kind`` is the corpus/kind label re-used from count_exercises. ``exempt``
    is True when the notebook is out-of-corpus or ``setup`` -- never judged.
    ``status`` is one of ``"detected"`` (a run >= MIN_RUN), ``"clean"``
    (no run), ``"exempt"`` (out of corpus or setup), ``"unmeasured"`` (could
    not read the file or no code cell to divide by).
    """

    path: str
    kind: str
    exempt: bool
    status: str
    max_run: int = 0
    run_count: int = 0
    runs: list[Run] = field(default_factory=list)


@dataclass
class Result:
    detected: list[Verdict] = field(default_factory=list)
    clean: list[Verdict] = field(default_factory=list)
    exempt: list[Verdict] = field(default_factory=list)
    unmeasured: list[Verdict] = field(default_factory=list)

    def as_payload(self) -> dict:
        return {
            "summary": {
                "detected": len(self.detected),
                "clean": len(self.clean),
                "exempt": len(self.exempt),
                "unmeasured": len(self.unmeasured),
                "threshold": MIN_RUN,
                "judged_kinds": sorted(JUDGED_KINDS),
            },
            "detected": [dataclasses.asdict(v) for v in self.detected],
            "clean": [dataclasses.asdict(v) for v in self.clean],
            "exempt": [dataclasses.asdict(v) for v in self.exempt],
            "unmeasured": [dataclasses.asdict(v) for v in self.unmeasured],
        }


def _detect_runs(cells: list[dict]) -> list[Run]:
    """Find every maximal run of consecutive code cells.

    A run is a contiguous subsequence of ``cells`` whose entries are all of
    type ``code``. A single isolated code cell is NOT a run (length 1 < the
    threshold). A markdown cell anywhere breaks the run. The function returns
    only runs of length >= MIN_RUN; callers receive the same list shape
    regardless of threshold so the verification (test fixtures) stays
    deterministic.
    """
    runs: list[Run] = []
    start = None
    length = 0
    for i, cell in enumerate(cells):
        if cell.get("cell_type") == "code":
            if start is None:
                start = i
                length = 1
            else:
                length += 1
        else:
            if start is not None and length >= MIN_RUN:
                runs.append(Run(start_cell=start, end_cell=start + length - 1,
                                 length=length))
            start = None
            length = 0
    if start is not None and length >= MIN_RUN:
        runs.append(Run(start_cell=start, end_cell=start + length - 1,
                         length=length))
    return runs


def _read_cells(path: Path) -> tuple[list[dict] | None, str | None]:
    """Read a notebook's cells.

    Returns ``(cells, None)`` on success, ``(None, reason)`` on a parse
    failure or missing nbformat. ``reason`` is one of ``"no_nbformat"``,
    ``"read_error"``.
    """
    if nbformat is None:
        return None, "no_nbformat"
    try:
        nb = nbformat.read(str(path), as_version=4)
    except Exception:
        return None, "read_error"
    cells = nb.get("cells", [])
    if not cells:
        return None, "read_error"
    return cells, None


def judge(path: Path) -> Verdict:
    """Judge one notebook against the consecutive-code-cells convention."""
    rel = str(path)
    try:
        kind, _thr = classify_notebook(path)
    except Exception:
        kind = "unknown"
    if kind not in JUDGED_KINDS:
        return Verdict(path=rel, kind=kind, exempt=True, status="exempt")
    cells, reason = _read_cells(path)
    if reason is not None:
        return Verdict(path=rel, kind=kind, exempt=False,
                        status="unmeasured")
    if not any(c.get("cell_type") == "code" for c in cells):
        # A notebook with NO code cell cannot be measured against this rule;
        # treat it like the density floor treats no-code-cell notebooks.
        return Verdict(path=rel, kind=kind, exempt=False,
                        status="unmeasured")
    runs = _detect_runs(cells)
    if not runs:
        return Verdict(path=rel, kind=kind, exempt=False, status="clean",
                        max_run=0, run_count=0)
    return Verdict(path=rel, kind=kind, exempt=False, status="detected",
                    max_run=max(r.length for r in runs),
                    run_count=len(runs), runs=runs)


def _collect_paths(targets: Iterable[str], read_stdin: bool) -> list[Path]:
    """Resolve CLI targets + stdin into a deduplicated list of notebook paths.

    Directories are walked recursively for ``*.ipynb``. Non-existent paths
    raise ``FileNotFoundError`` so a typo can never be mistaken for an empty
    corpus (the same trap pedagogy_density.py closed in #10479). When no
    target is given AND stdin is closed, scan the default corpus root.
    """
    seen: set[Path] = set()
    out: list[Path] = []
    for t in targets:
        p = Path(t)
        if p.is_dir():
            for q in sorted(p.rglob("*.ipynb")):
                rp = q.resolve()
                if rp not in seen:
                    seen.add(rp)
                    out.append(q)
        elif p.suffix == ".ipynb" and p.is_file():
            rp = p.resolve()
            if rp not in seen:
                seen.add(rp)
                out.append(p)
        else:
            raise FileNotFoundError(f"not a notebook nor a directory: {t}")
    if read_stdin:
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            p = Path(line)
            if not (p.suffix == ".ipynb" and p.is_file()):
                raise FileNotFoundError(f"stdin path is not a notebook: {line}")
            rp = p.resolve()
            if rp not in seen:
                seen.add(rp)
                out.append(p)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Detect runs of consecutive code cells in pedagogical notebooks "
            "(#12797). Always exits 0 (advisory): the signal is the "
            "'consecutive-code-cells' label, not this exit code."
        ),
    )
    parser.add_argument(
        "targets", nargs="*", default=[],
        help="Notebook files or directories to scan (default: whole corpus).",
    )
    parser.add_argument(
        "--paths", nargs="*", default=[],
        help="Explicit notebook paths (PR mode).",
    )
    parser.add_argument(
        "--stdin", action="store_true",
        help="Also read paths from stdin (one per line; e.g. git diff output).",
    )
    parser.add_argument(
        "--json", dest="json_out", action="store_true",
        help="Emit machine-readable JSON (the workflow parses this for the label).",
    )
    args = parser.parse_args(argv)

    targets = list(args.paths) + list(args.targets)
    if not targets and not args.stdin:
        targets = [str(NOTEBOOKS_DIR)]
    try:
        paths = _collect_paths(targets, args.stdin)
    except FileNotFoundError as e:
        sys.stderr.write(f"detect_consecutive_code_cells: {e}\n")
        return 2

    result = Result()
    if not paths:
        msg = "No notebooks to measure."
        if args.json_out:
            payload = result.as_payload()
            payload["note"] = msg
            print(json.dumps(payload, indent=2))
        else:
            sys.stderr.write(msg + "\n")
        return 0

    for p in paths:
        v = judge(p)
        if v.status == "detected":
            result.detected.append(v)
        elif v.status == "clean":
            result.clean.append(v)
        elif v.status == "exempt":
            result.exempt.append(v)
        else:
            result.unmeasured.append(v)

    if args.json_out:
        print(json.dumps(result.as_payload(), indent=2))
    else:
        print(f"=== {len(result.detected)}/{len(paths)} notebook(s) with a "
              f"run of >= {MIN_RUN} consecutive code cells ===")
        for v in result.detected:
            print(f"  [{v.kind}] max_run={v.max_run} "
                  f"runs={v.run_count}  {v.path}")
    # ADVISORY: always exit 0. The label is the actionable signal.
    return 0


if __name__ == "__main__":
    raise SystemExit(main())