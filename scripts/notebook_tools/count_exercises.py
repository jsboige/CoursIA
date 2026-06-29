#!/usr/bin/env python3
"""Count exercises per pedagogical notebook (issue #2161 tooling).

Counts exercise cells -- the convention is >= 3 exercises per notebook. This
tool exists because the historical scan used a strict `^#+\\s*Exercice` regex
that UNDERCOUNTED two real cases (the G.1 finding from the #2161 audit cycle):

  1. Exercise headers in forms the strict regex misses, e.g.
        `## 8. Exercice : ...`   (numbered section header)
        `### Exercice - Exploration`  (dash separator, no number)
     The strict `^#+\\s*Exercice` requires the word right after the hashes with
     no intervening number/dash, so `## 8. Exercice` was missed.
  2. Exercise CODE cells with NO markdown header at all -- a stub code cell
     whose first comment is `# Exercice ...` but is not preceded by any markdown
     "Exercice" header. A header-only counter never sees these.

This tool counts `\bexercice\b` ANYWHERE in a markdown header (numbered or not)
PLUS stub code cells whose source comments reference an exercise, then
de-duplicates so an exercise that is both a markdown header AND the following
code cell counts once.

An exercise is defined here as a STUB (work for the student), per the
exercise/example labeling convention:
  - markdown "Exercice" header whose following code cell is a stub, OR
  - a stub code cell whose own source comments contain "Exercice".
A markdown "Exemple" header + working code is an EXAMPLE, not counted.

Usage:
    python count_exercises.py                                  # all pedagogical notebooks
    python count_exercises.py --family IIT                     # single family
    python count_exercises.py MyIA.AI.Notebooks/IIT/IIT-1-IntroToPyPhi.ipynb   # single notebook
    python count_exercises.py --threshold 3                    # default: flag < 3
    python count_exercises.py --json                           # machine-readable
    python count_exercises.py --check                          # exit 1 if any sub-threshold

Exit codes:
    0 -- no sub-threshold notebooks (or non-check mode)
    1 -- one or more pedagogical notebooks below threshold (--check only)

Excludes (same convention as count_notebooks_by_series.py): .ipynb_checkpoints,
research, archive, _output, partner-course, examples, obj, bin, .git, plus
`.QuantConnect`/`TrashBin` (QuantConnect CLI app-data + recycle bin of deleted
project notebooks -- not pedagogical content).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
NOTEBOOKS_DIR = REPO_ROOT / "MyIA.AI.Notebooks"

EXCLUDE_DIRS = {
    ".ipynb_checkpoints", ".git", "__pycache__", "obj", "bin",
    "_output", "research", "archive", "partner-course", "examples",
    ".venv", "node_modules",
    # QuantConnect CLI app-data: the hidden `.QuantConnect/` directory holds the
    # CLI's metadata + `TrashBin/` (a recycle bin of deleted project research.ipynb).
    # Counting 450+ trashed notebooks as "pedagogical" inflated the sub-threshold
    # tally (false sub-3) -- same class of artifact gap as `_output.ipynb`.
    ".QuantConnect", "TrashBin",
}

# \bexercice\b anywhere in the line, case-insensitive, French or English form.
# Matches `### Exercice 1`, `## 8. Exercice`, `### Exercice - ...`, `### Exercise`.
EXERCISE_WORD_RE = re.compile(r"\bexercic(?:e|es)\b", re.IGNORECASE)
EXERCISE_WORD_EN_RE = re.compile(r"\bexercises?\b", re.IGNORECASE)

# An ATX markdown header line starts with `#` (1-6 hashes) followed by a space
# and the header text. We deliberately do NOT match Setext headers (underlines
# of `---`/`===`) because a horizontal rule `---` on its own line would be a
# false positive (a `---` separator is a `<hr>`, not a header) -- this is what
# initially mis-paired a `---` cell with the exercise code cell below it.
MARKDOWN_HEADER_RE = re.compile(r"^\s{0,3}#{1,6}\s+(.*)", re.MULTILINE)

# Stub indicators inside a code cell source (mirrors detect_solution_leaks.py +
# the notebook-conventions C.1 patterns). An exercise cell is a STUB; a complete
# solution is an EXAMPLE and is not counted as an exercise.
#
# NOTE: `# Exercice` is intentionally NOT a stub pattern here. A bare
# `# Exercice ...` comment with no code is a stub (caught by the <=1 effective
# code-line rule below), but a `# Exercice ...` comment ABOVE real working code
# is a solution/example and must NOT be classified as a stub. Detecting that a
# code cell *mentions* an exercise is a separate concern (_code_cell_mentions_
# exercise); whether it is a *stub* is answered only by these patterns + the
# code-line count.
STUB_PATTERNS = [
    re.compile(r'print\(["\']Exercice[s]? a completer', re.IGNORECASE),
    re.compile(r"^\s*pass\s*$", re.MULTILINE),
    re.compile(r"\breturn\s+None\b"),
    re.compile(r"#\s*TODO", re.IGNORECASE),
    re.compile(r"#\s*Indice", re.IGNORECASE),
    re.compile(r'Console\.WriteLine\(["\']Exercice', re.IGNORECASE),
    re.compile(r"^\s*result\s*=\s*None\b", re.MULTILINE | re.IGNORECASE),
    re.compile(r"^\s*raise\s+NotImplementedError", re.MULTILINE),
    re.compile(r"^\s*assert\s+False\b", re.MULTILINE),
]


@dataclass
class ExerciseHit:
    """A single detected exercise occurrence with evidence."""

    cell_index: int
    cell_type: str  # 'markdown' or 'code'
    source: str  # full cell source (joined)
    detected_by: str  # 'markdown_header' | 'code_cell_comment'

    @property
    def preview(self) -> str:
        # For a markdown header, show the actual header line (the one carrying
        # the exercise word), not necessarily the first line of the cell (which
        # may be a `---` separator or an anchor that obscures the evidence).
        if self.cell_type == "markdown":
            for line in self.source.split("\n"):
                stripped = line.strip()
                if stripped.startswith("#"):
                    m = MARKDOWN_HEADER_RE.match(line)
                    if m and (
                        EXERCISE_WORD_RE.search(m.group(1))
                        or EXERCISE_WORD_EN_RE.search(m.group(1))
                    ):
                        return stripped[:90]
            # Fallback: first non-empty line.
            for line in self.source.split("\n"):
                if line.strip():
                    return line.strip()[:90]
        first_line = (self.source.split("\n") or [""])[0].strip()
        return first_line[:90]


@dataclass
class NotebookCount:
    """Exercise count for one notebook with per-hit evidence."""

    path: Path
    exercises: list[ExerciseHit] = field(default_factory=list)
    parse_error: str | None = None

    @property
    def count(self) -> int:
        return len(self.exercises)

    @property
    def conforming(self) -> bool:
        # parse errors are reported separately, never a silent conform
        return self.parse_error is None


def _is_stub_code(source: str) -> bool:
    """True if the code cell source looks like a student stub, not a solution.

    Mirrors detect_solution_leaks.is_stub_code but broadened to the C.1
    convention: a cell with <= 1 effective code line, or any stub marker.
    """
    if not source.strip():
        return True
    for pat in STUB_PATTERNS:
        if pat.search(source):
            return True
    lines = [
        ln.strip()
        for ln in source.strip().split("\n")
        if ln.strip()
        and not ln.strip().startswith("#")
        and not ln.strip().startswith("//")
    ]
    code_lines = [
        ln for ln in lines
        if not ln.startswith("import ") and not ln.startswith("from ")
        and not ln.startswith("using ")
    ]
    return len(code_lines) <= 1


def _code_cell_mentions_exercise(source: str) -> bool:
    """A code cell whose comments name an exercise (`# Exercice ...`)."""
    comments = [ln for ln in source.split("\n") if ln.strip().startswith("#")]
    blob = "\n".join(comments)
    return bool(EXERCISE_WORD_RE.search(blob) or EXERCISE_WORD_EN_RE.search(blob))


def _markdown_mentions_exercise(source: str) -> bool:
    """True if any markdown header line contains the exercise word."""
    for m in MARKDOWN_HEADER_RE.finditer(source):
        header_text = m.group(1)
        if EXERCISE_WORD_RE.search(header_text) or EXERCISE_WORD_EN_RE.search(header_text):
            return True
    return False


def count_exercises_in_notebook(path: Path) -> NotebookCount:
    """Count exercises in one notebook, with per-cell evidence.

    Deduplication: a markdown header at cell i followed by the matching code
    stub at cell i+1 is ONE exercise. We pair them. A code-cell exercise with
    no preceding markdown header is its own exercise.
    """
    result = NotebookCount(path=path)
    try:
        with open(path, "r", encoding="utf-8-sig") as f:
            nb = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        result.parse_error = f"Failed to parse notebook: {exc}"
        return result

    cells = nb.get("cells", [])

    # First pass: detect markdown-header exercises and their paired code stub.
    header_cell_indices: set[int] = set()
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        source = "".join(cell.get("source", []))
        if _markdown_mentions_exercise(source):
            result.exercises.append(
                ExerciseHit(
                    cell_index=i,
                    cell_type="markdown",
                    source=source,
                    detected_by="markdown_header",
                )
            )
            header_cell_indices.add(i)

    # Track which code cells are the paired stub of a header just above them
    # so we do not double-count them in the second pass.
    paired_code_indices: set[int] = set()
    for idx in sorted(header_cell_indices):
        for j in range(idx + 1, min(idx + 4, len(cells))):
            cell = cells[j]
            if cell.get("cell_type") == "code":
                paired_code_indices.add(j)
                break

    # Second pass: code-cell exercises with NO preceding markdown header.
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "code":
            continue
        if i in paired_code_indices:
            continue
        source = "".join(cell.get("source", []))
        if _code_cell_mentions_exercise(source) and _is_stub_code(source):
            result.exercises.append(
                ExerciseHit(
                    cell_index=i,
                    cell_type="code",
                    source=source,
                    detected_by="code_cell_comment",
                )
            )

    return result


def iter_pedagogical_notebooks(root: Path) -> list[Path]:
    """Yield pedagogical .ipynb paths, applying the standard exclusions.

    Excludes execution-artifact notebooks whose filename ends in `_output.ipynb`
    (the papermill convention used in this repo: each lab has both
    `LabN-Name.ipynb` and `LabN-Name_output.ipynb`; counting both double-counts).
    """
    out: list[Path] = []
    if not root.exists():
        return out
    for nb_path in sorted(root.rglob("*.ipynb")):
        parts = nb_path.parts
        if any(exc in parts for exc in EXCLUDE_DIRS):
            continue
        if nb_path.stem.endswith("_output"):
            continue
        out.append(nb_path)
    return out


def _family_of(path: Path, notebooks_dir: Path) -> str:
    try:
        rel = path.relative_to(notebooks_dir)
        return rel.parts[0] if rel.parts else "_root"
    except ValueError:
        return "_root"


def run(
    targets: list[Path],
    threshold: int,
    json_out: bool,
    check: bool,
) -> int:
    """Execute the count over the given targets. Returns exit code for --check."""
    if json_out:
        return _run_json(targets, threshold)
    return _run_text(targets, threshold, check)


def _run_text(targets: list[Path], threshold: int, check: bool) -> int:
    sub_threshold: list[tuple[Path, NotebookCount]] = []
    parse_errors: list[tuple[Path, str]] = []
    total_notebooks = 0
    total_exercises = 0

    for nb_path in targets:
        total_notebooks += 1
        cnt = count_exercises_in_notebook(nb_path)
        if cnt.parse_error:
            parse_errors.append((nb_path, cnt.parse_error))
            continue
        total_exercises += cnt.count
        if cnt.count < threshold:
            sub_threshold.append((nb_path, cnt))

    print(f"Notebooks scanned : {total_notebooks}")
    print(f"Total exercises   : {total_exercises}")
    print(f"Threshold         : >= {threshold} per notebook")
    print(f"Conforming        : {total_notebooks - len(sub_threshold) - len(parse_errors)}")
    print(f"Sub-threshold     : {len(sub_threshold)}")
    if parse_errors:
        print(f"Parse errors      : {len(parse_errors)}")

    if sub_threshold:
        print("\n--- Sub-threshold notebooks (with evidence) ---")
        for nb_path, cnt in sub_threshold:
            rel = nb_path.relative_to(REPO_ROOT) if nb_path.is_absolute() else nb_path
            print(f"\n[{cnt.count}/{threshold}] {rel}")
            for hit in cnt.exercises:
                print(f"    cell {hit.cell_index:>3} ({hit.cell_type:<8} {hit.detected_by}): {hit.preview}")
    else:
        print("\nAll scanned notebooks meet the threshold.")

    if parse_errors:
        print("\n--- Parse errors (investigate manually) ---")
        for nb_path, err in parse_errors:
            print(f"  {nb_path}: {err[:120]}")

    if check and sub_threshold:
        return 1
    return 0


def _run_json(targets: list[Path], threshold: int) -> int:
    payload = {"threshold": threshold, "notebooks": []}
    for nb_path in targets:
        cnt = count_exercises_in_notebook(nb_path)
        entry = {
            "path": str(nb_path.relative_to(REPO_ROOT))
            if nb_path.is_absolute()
            else str(nb_path),
            "count": cnt.count,
            "conforming": cnt.count >= threshold and cnt.parse_error is None,
            "parse_error": cnt.parse_error,
            "evidence": [
                {
                    "cell_index": h.cell_index,
                    "cell_type": h.cell_type,
                    "detected_by": h.detected_by,
                    "preview": h.preview,
                }
                for h in cnt.exercises
            ],
        }
        payload["notebooks"].append(entry)
    print(json.dumps(payload, indent=2, ensure_ascii=False))
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Count exercises per pedagogical notebook (#2161).",
    )
    parser.add_argument(
        "paths",
        nargs="*",
        help="Notebook paths or directories. Defaults to all pedagogical notebooks.",
    )
    parser.add_argument(
        "--family",
        help="Restrict to a top-level family under MyIA.AI.Notebooks/ (e.g. IIT, ML).",
    )
    parser.add_argument(
        "--threshold",
        type=int,
        default=3,
        help="Minimum exercises per notebook (default: 3, per #2161).",
    )
    parser.add_argument(
        "--json",
        dest="json_out",
        action="store_true",
        help="Emit machine-readable JSON.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Exit 1 if any notebook is below threshold (for CI / gates).",
    )
    args = parser.parse_args(argv)

    # Resolve targets.
    targets: list[Path] = []
    if args.paths:
        for raw in args.paths:
            p = Path(raw)
            if not p.exists():
                print(f"warning: {raw} does not exist, skipping", file=sys.stderr)
                continue
            if p.is_dir():
                targets.extend(iter_pedagogical_notebooks(p))
            elif p.suffix == ".ipynb":
                targets.append(p)
    elif args.family:
        targets = iter_pedagogical_notebooks(NOTEBOOKS_DIR / args.family)
    else:
        targets = iter_pedagogical_notebooks(NOTEBOOKS_DIR)

    if not targets:
        print("No notebooks matched the given targets.", file=sys.stderr)
        return 0

    return run(
        targets,
        threshold=args.threshold,
        json_out=args.json_out,
        check=args.check,
    )


if __name__ == "__main__":
    sys.exit(main())
