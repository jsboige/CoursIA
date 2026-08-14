#!/usr/bin/env python3
"""Measure pedagogy DENSITY (prose per code cell) per notebook (#10479 Grain 2).

The user's observation (2026-08-11) was that the introductive part of a series
can lack pedagogical notes in markdown. The metric the user proposed --
percentage of markdown -- was MEASURED and detects nothing: on the five
incriminated Lean notebooks the markdown share was 44-51%, with no run of >=3
code cells without prose between. The metric that discriminates is **chars of
prose per code cell** -- how much text accompanies each thing to explain:

    chars / cellule code = sum(len(markdown cell sources)) / count(code cells)

Calibration (this tool's definition, verified against the issue table): for
every notebook published in #10479, the raw ``len()`` of the joined markdown
sources divided by the code-cell count reproduces the published value EXACTLY
(Lean-15b 1126=1126, Lean-13 1985=1985; and the post-enrichment values
Lean-2 1620, Lean-4 2100, Lean-5 1039, Lean-6 1263 on the enriched files).
Whitespace and newlines count: the length is the raw source length.

This is the missing ORGAN for that observation: it wires the density measure to
PRs, exactly as check_pr_exercises.py did for the >=3 exercises convention
(#8814). It is ADVISORY by design (issue #10479 acceptance): it always exits 0;
the actionable payload is the ``pedagogy-density-below-threshold`` LABEL the
workflow poses, never the green conclusion of the job (green by construction --
the same trap that let #8797 through for exercises).

Consumes, never re-implements, the corpus/kind classification of
``count_exercises.py`` (issue #10479 acceptance): the out-of-corpus kinds
(artifact/template/vendored/archive/legacy/tooling/student) and the setup
exemption are imported, not duplicated -- the label and the canonical tool must
not diverge. The density floor applies to the ``standard`` AND ``lean`` kinds
(the series that motivated the issue is a Lean series); a ``setup`` notebook is
exempt (environment scaffolding has no prose budget); an out-of-corpus notebook
is exempt. The md% share is REPORTED but never the criterion (measured: it
cannot discriminate).

A SECOND label, ``pedagogy-density-unmeasured``, covers notebooks the tool could
not read (JSON parse failure) or that have no code cell to divide by. This is
the #8819 lesson applied to density: "I could not measure" and "I measured, it
is below threshold" call for different reactions, so they never collapse into
one label -- and the summary never claims conformity while ``unmeasured > 0``.

Usage:
    python pedagogy_density.py                                   # whole corpus
    python pedagogy_density.py MyIA.AI.Notebooks/SymbolicAI/Lean # one family
    python pedagogy_density.py path/to/a.ipynb path/to/b.ipynb   # explicit
    python pedagogy_density.py --paths a.ipynb --json
    git diff --name-only BASE HEAD -- '*.ipynb' \\
        | python pedagogy_density.py --stdin --json

Always exits 0 (advisory): the signal is the label, not this exit code.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

# Import the canonical classification rather than re-implementing it (issue
# #10479 acceptance: the two must not diverge).
_TOOLS_DIR = Path(__file__).resolve().parent
if str(_TOOLS_DIR) not in sys.path:
    sys.path.insert(0, str(_TOOLS_DIR))

from count_exercises import (  # noqa: E402
    EXCLUDE_DIRS,
    NOTEBOOKS_DIR,
    OUT_OF_CORPUS_KINDS,
    classify_notebook,
)

#: The density floor: chars of markdown prose per code cell. Calibrated on the
#: Lean series (#10479): the five language-teaching notebooks stood at 303-550
#: chars/code-cell vs ~2000 in the applied notebooks; the floor is the bottom
#: of the applied band (Lean-18 at 1056, Lean-15b at 1126), not its mean (a
#: homage-notebook target unsuited to a learning notebook).
DENSITY_THRESHOLD = 1200

#: Kinds judged against the density floor. ``standard`` is the ordinary course
#: notebook; ``lean`` stays in the density corpus even though the exercises
#: rule exempts it (0-2) -- the series that motivated this organ IS a Lean
#: series, so exempting Lean would make the tool detect nothing where it is
#: needed. The exercises exemption and the density exemption are different
#: rules with different rationales; each consumes ``classify_notebook`` and
#: applies its own judgment on top.
DENSITY_JUDGED_KINDS = frozenset({"standard", "lean"})

#: Label for "measured, below the density floor" (issue #10479 acceptance).
LABEL_NAME = "pedagogy-density-below-threshold"
#: A SECOND, distinct label for notebooks the tool could NOT measure (issue
#: #8819 lesson, transposed): unparseable JSON or zero code cells. Never
#: collapsed into the below-threshold label.
LABEL_UNMEASURED = "pedagogy-density-unmeasured"


@dataclass
class DensityVerdict:
    """One notebook's density verdict, with the evidence the label needs."""

    path: str
    kind: str
    exempt: bool  # exempt from the density floor (out of corpus, or setup)
    threshold: int  # the floor it would be judged against (1200), for display
    prose_chars: int  # total markdown source chars
    code_cells: int
    md_cells: int
    density: int | None  # chars per code cell; None if exempt or unmeasured
    md_pct: float | None  # reported, never the criterion (#10479 measurement)
    status: str  # 'below_threshold' | 'ok' | 'exempt' | 'unmeasured'
    detail: str = ""


@dataclass
class DensityResult:
    """Aggregate verdict over all scanned notebooks."""

    below_threshold: list[DensityVerdict] = field(default_factory=list)
    ok: list[DensityVerdict] = field(default_factory=list)
    exempt: list[DensityVerdict] = field(default_factory=list)
    unmeasured: list[DensityVerdict] = field(default_factory=list)

    def as_payload(self) -> dict:
        """Machine-readable payload for the workflow to decide the labels.

        Issue #8819 applied to density: a notebook the tool could not measure is
        NOT conforming -- it is UNMEASURED. The summary exposes ``unmeasured``
        FIRST, and carries TWO labels: ``below_threshold`` (measured, below the
        floor) and ``unmeasured`` (could not measure). The workflow raises each
        when its count is > 0 and never claims "all meet the floor" while
        ``unmeasured > 0``.
        """
        n_below = len(self.below_threshold)
        n_un = len(self.unmeasured)
        n_ok = len(self.ok)
        n_exempt = len(self.exempt)
        return {
            "labels": {
                "below_threshold": {"name": LABEL_NAME, "count": n_below},
                "unmeasured": {"name": LABEL_UNMEASURED, "count": n_un},
            },
            "summary": {
                # unmeasured FIRST: a glance makes the gap obvious (#8819).
                "unmeasured": n_un,
                "total": n_below + n_ok + n_exempt + n_un,
                "judged": n_below + n_ok + n_un,  # subject to the floor
                "exempt": n_exempt,  # out of corpus, or setup
                "below_threshold": n_below,
            },
            "below_threshold": [asdict(v) for v in self.below_threshold],
            "ok": [asdict(v) for v in self.ok],
            "exempt": [asdict(v) for v in self.exempt],
            "unmeasured": [asdict(v) for v in self.unmeasured],
        }


def _cell_source(cell: dict) -> str:
    """The cell source as one string (nbformat may store a list of lines)."""
    src = cell.get("source", "")
    if isinstance(src, list):
        return "".join(src)
    return src or ""


def _measure(path: Path) -> tuple[int, int, int, int]:
    """Return ``(prose_chars, code_chars, n_code, n_md)`` for a notebook.

    ``prose_chars`` is the raw length of every markdown cell source -- the
    definition calibrated against the #10479 table (whitespace and newlines
    count). ``code_chars`` (raw length of every code cell source) feeds the
    REPORTED markdown share. Raises ValueError on JSON parse failure.
    """
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:  # unreadable = unmeasured
        raise ValueError(f"cannot parse: {exc}") from exc
    md_chars = 0
    code_chars = 0
    n_code = 0
    n_md = 0
    for cell in data.get("cells", []):
        ctype = cell.get("cell_type")
        if ctype == "markdown":
            md_chars += len(_cell_source(cell))
            n_md += 1
        elif ctype == "code":
            code_chars += len(_cell_source(cell))
            n_code += 1
    return md_chars, code_chars, n_code, n_md


def check_paths(paths: list[Path]) -> DensityResult:
    """Classify + measure each path, bucketing by density status.

    A notebook is ``below_threshold`` only when it is a density-judged kind
    (standard or lean), measurable (>=1 code cell, parseable), and its
    chars-per-code-cell is below :data:`DENSITY_THRESHOLD`. A ``setup`` or
    out-of-corpus notebook is exempt -- the classification is CONSUMED from
    ``count_exercises.py``, not re-decided here.
    """
    result = DensityResult()
    for path in paths:
        kind, _ = classify_notebook(path)
        exempt = kind in OUT_OF_CORPUS_KINDS or kind == "setup"
        if exempt:
            result.exempt.append(
                DensityVerdict(
                    path=str(path), kind=kind, exempt=True,
                    threshold=DENSITY_THRESHOLD, prose_chars=0, code_cells=0,
                    md_cells=0, density=None, md_pct=None, status="exempt",
                    detail=(
                        f"exempt from the density floor (kind={kind}) -- "
                        "the rule does not apply"
                    ),
                )
            )
            continue
        try:
            prose_chars, code_chars, n_code, n_md = _measure(path)
        except ValueError as exc:
            result.unmeasured.append(
                DensityVerdict(
                    path=str(path), kind=kind, exempt=False,
                    threshold=DENSITY_THRESHOLD, prose_chars=0, code_cells=0,
                    md_cells=0, density=None, md_pct=None, status="unmeasured",
                    detail=str(exc),
                )
            )
            continue
        if n_code == 0:
            result.unmeasured.append(
                DensityVerdict(
                    path=str(path), kind=kind, exempt=False,
                    threshold=DENSITY_THRESHOLD, prose_chars=prose_chars,
                    code_cells=0, md_cells=n_md, density=None, md_pct=None,
                    status="unmeasured",
                    detail="no code cell to divide by -- density undefined",
                )
            )
            continue
        density = prose_chars // n_code
        # Reported, never the criterion: #10479 measured that the markdown
        # share alone cannot discriminate (44-51% on both sides of the gap).
        md_pct = round(100 * prose_chars / max(prose_chars + code_chars, 1), 1)
        status = "ok" if density >= DENSITY_THRESHOLD else "below_threshold"
        verdict = DensityVerdict(
            path=str(path), kind=kind, exempt=False,
            threshold=DENSITY_THRESHOLD, prose_chars=prose_chars,
            code_cells=n_code, md_cells=n_md, density=density,
            md_pct=md_pct, status=status,
        )
        if density < DENSITY_THRESHOLD:
            result.below_threshold.append(verdict)
        else:
            result.ok.append(verdict)
    return result


def _collect_paths(argv_paths: list[str], from_stdin: bool) -> list[Path]:
    """Resolve targets from CLI args and/or stdin into notebook paths.

    A target may be a notebook file OR a directory (globbed for ``*.ipynb``
    under it, skipping the canonical excluded dirs). Blank lines and duplicates
    are dropped; non-existent targets are warned and skipped.
    """
    raw: list[str] = list(argv_paths)
    if from_stdin:
        raw += [ln.strip() for ln in sys.stdin if ln.strip()]
    seen: set[str] = set()
    paths: list[Path] = []
    for r in raw:
        if r in seen:
            continue
        seen.add(r)
        p = Path(r)
        if p.is_dir():
            paths.extend(
                q for q in _glob_notebooks(p)
                if str(q) not in seen and not seen.add(str(q))
            )
            continue
        if not p.exists():
            print(f"warning: {r} does not exist (deleted?), skipping", file=sys.stderr)
            continue
        if p.suffix != ".ipynb":
            continue
        paths.append(p)
    return paths


def _glob_notebooks(directory: Path) -> list[Path]:
    """All ``*.ipynb`` under ``directory``, skipping canonical excluded dirs.

    Consumes :data:`EXCLUDE_DIRS` from ``count_exercises.py`` so the scan mode
    and the fleet scan see the same world.
    """
    out: list[Path] = []
    for p in sorted(directory.rglob("*.ipynb")):
        if any(part in EXCLUDE_DIRS for part in p.parts):
            continue
        if p.name.startswith("."):  # .ipynb_checkpoints/* (also in EXCLUDE_DIRS)
            continue
        out.append(p)
    return out


def _render_text(result: DensityResult) -> str:
    """Human-readable summary (the workflow log; the labels are separate).

    Mirrors check_pr_exercises: the closing line asserts ONLY what was
    measured -- ``unmeasured > 0`` means the honest statement is "N not
    measured", never a blanket conformity claim over notebooks never read.
    """
    s = result.as_payload()["summary"]
    lines = [
        f"Notebooks scanned   : {s['total']}",
        f"Judged vs floor     : {s['judged']}",
        f"Exempt              : {s['exempt']}",
        f"Below {DENSITY_THRESHOLD} c/cell: {s['below_threshold']}",
        f"Unmeasured          : {s['unmeasured']}",
    ]
    if result.below_threshold:
        lines.append(f"\n--- Below threshold (label: {LABEL_NAME}) ---")
        for v in result.below_threshold:
            lines.append(
                f"  [{v.density}/{v.threshold}] ({v.kind}) "
                f"md%={v.md_pct} {v.path}"
            )
    if result.exempt:
        lines.append("\n--- Exempt (kind-classified, not labelled) ---")
        for v in result.exempt:
            lines.append(f"  ({v.kind}) {v.path} -- {v.detail}")
    if result.unmeasured:
        lines.append(f"\n--- Unmeasured (label: {LABEL_UNMEASURED}) ---")
        for v in result.unmeasured:
            lines.append(f"  {v.path}: {v.detail[:120]}")
    if s["unmeasured"] > 0:
        lines.append(
            f"\n{s['unmeasured']} notebook(s) could not be measured -- "
            "conformity neither claimed nor denied."
        )
    elif not result.below_threshold:
        lines.append(
            "\nAll judged notebooks meet the density floor."
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Measure pedagogy density (chars of prose per code cell) per "
            "notebook (#10479). Always exits 0 (advisory): the signal is the "
            f"'{LABEL_NAME}' label, not this exit code."
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
    # The floor is deliberately NOT a CLI flag: it is locked by calibration
    # against the #10479 table. A mutable threshold would silently change what
    # the label means from one invocation to the next.
    args = parser.parse_args(argv)

    targets = list(args.paths) + list(args.targets)
    if not targets and not args.stdin:
        targets = [str(NOTEBOOKS_DIR)]  # fleet scan mode (like count_exercises)
    paths = _collect_paths(targets, args.stdin)
    if not paths:
        msg = "No notebooks to measure."
        if args.json_out:
            payload = DensityResult().as_payload()
            payload["note"] = msg
            print(json.dumps(payload, indent=2, ensure_ascii=False))
        else:
            print(msg)
        return 0

    result = check_paths(paths)
    if args.json_out:
        print(json.dumps(result.as_payload(), indent=2, ensure_ascii=False))
    else:
        print(_render_text(result))
    # Advisory: NEVER exit non-zero (issue #10479 acceptance).
    return 0


if __name__ == "__main__":
    sys.exit(main())
