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
     whose first comment is `# Exercice ...` (Python/F#/Lean) or
     `// Exercice ...` (C# / .NET Interactive) but is not preceded by any
     markdown "Exercice" header. A header-only counter never sees these.

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

Beyond those directory exclusions, each remaining notebook is classified into
the pedagogical corpus or out of it (see "Corpus scope" below), because the
convention answers two questions and not one: which notebooks are course
material, and what minimum applies to those that are. The count of what scope
removed is reported as `Out of corpus`, so a narrowed run stays distinguishable
from a clean one.
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

#: Standard exercise budget for an ordinary course notebook (#2161).
DEFAULT_THRESHOLD = 3

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

# ---------------------------------------------------------------------------
# Corpus scope and per-kind thresholds (#2161 exception table)
#
# `.claude/rules/three-exercises-per-notebook.md` states the convention in two
# parts that this script historically collapsed into a single "count < 3 =
# violation" test:
#
#   (a) WHICH notebooks belong to the pedagogical corpus at all. Research
#       artifacts, quantbooks, templates, probes, vendored sub-repos and
#       archives are not course material, so they have no exercise budget.
#   (b) WHAT threshold applies to a notebook that IS course material. The rule
#       publishes an exception table: Setup/Environment 0-1, purely-Lean 0-2,
#       Archive/Legacy 0 ("pas maintenir"), everything else 3.
#
# Collapsing (a) into (b) makes the output unreadable rather than merely
# imprecise: a run over the whole repo reported 168 "sub-threshold" notebooks,
# of which 133 were QuantConnect research/quantbook artifacts and nearly all the
# rest were setup, Lean or archive notebooks that the rule explicitly exempts.
# A tally that mixes "should never have been counted" with "counted, and
# legitimately below 3" cannot be acted on and cannot be gated -- the same
# defect class as a bare counter published without its denominator (#8678).
# Classifying first makes the denominator visible and leaves a residue that is
# actually actionable.
#
# Every pattern below is derived from a path observed in this repo; none is
# speculative. Filename rules are preferred over directory lists because the
# historical directory list drifted into near-misses that silently matched
# nothing: `archive` never matched `_archives/`, and `partner-course` never
# matched `partner-course-quant-trading/`.
# ---------------------------------------------------------------------------

#: Directories whose notebooks are not course material.
#: Underscore-prefixed directories are handled generically below: every one of
#: them under MyIA.AI.Notebooks/ today is internal (`_archives/`, `_probes/`,
#: `_docs/`, `_legacy/`, `__pycache__/`), and no taught series uses that form.
NON_PEDAGOGICAL_DIRS = {
    "semantic-fleet",  # vendored sub-repo under GenAI/SemanticKernel/
    "ML-Training-Pipeline",  # QC model-training research, not a taught series
    "Research-Executor",  # QC batch-run harness (`runner.ipynb`)
}

#: Minimum exercise count per notebook kind, transcribed from the rule's
#: "Exceptions" table. Note the column is *Minimum exercices* and the exempt
#: rows read "0-1" (setup) and "0-2" (Lean): the acceptable count INCLUDES zero,
#: with the upper figure describing the expected ceiling, not a floor. So a
#: setup or Lean notebook is never sub-threshold. Encoding 1 and 2 as floors
#: here would invent a stricter policy than the rule states and would re-create,
#: at small scale, exactly the noise this change removes -- eight GenAI
#: `00-*-Environment` notebooks flagged for a requirement the rule exempts them
#: from. Only `standard` carries the real budget.
KIND_MINIMUM: dict[str, int | None] = {
    "setup": 0,
    "lean": 0,
}

#: Execution / research artifacts, matched on the notebook stem.
#: Covers `research.ipynb`, `Research.ipynb`, `quantbook.ipynb`, `output_v2.ipynb`,
#: `research_robustness.ipynb`, `m12_har_rv_j_research.ipynb`,
#: `sector_momentum_research_v2.ipynb`, `CrossSubmissionCaptureRepro.ipynb`.
ARTIFACT_STEM_RE = re.compile(
    r"^(?:research|quantbook|output)(?:[_-]v?\d+)?$"
    r"|^research[_-]"
    r"|[_-]research(?:[_-]v?\d+)?$"
    r"|[_-]output(?:[_-]v?\d+)?$"
    r"|repro$",
    re.IGNORECASE,
)

#: Setup / environment notebooks -- rule threshold 0-1.
#: `Lean-1-Setup`, `Sudoku-0-Environment-Csharp`, `SC-1-Setup-Foundry`,
#: `QC-Py-01-Setup`, `Argument_Analysis_Agentic-0-init`, `..-0-init_agent`.
SETUP_STEM_RE = re.compile(
    r"(?:^|[-_])(?:setup|environment|init)(?:$|[-_])", re.IGNORECASE
)

#: A directory that scopes a whole environment sub-series, e.g.
#: `GenAI/00-GenAI-Environment/` (whose 00-2..00-6 stems carry no setup marker)
#: and `Planners/00-Environment/`.
SETUP_DIR_RE = re.compile(r"environment", re.IGNORECASE)

#: Purely-Lean notebooks -- rule threshold 0-2.
#: `Lean-3-Propositions-Proofs`, `GameTheory-11b-Lean-BayesianGamesExt`,
#: `DecInfer-9-Lean-Gittins`.
LEAN_STEM_RE = re.compile(r"(?:^|[-_])lean(?:$|[-_])", re.IGNORECASE)

#: Legacy material -- rule "Archive / Legacy" row. Matched on DIRECTORY parts
#: only (`SemanticWeb/RDF.Net-Legacy/`), never on the notebook stem: a filename
#: match would drop `GenAI/Image/04-Applications/04-4-Cross-Stitch-Pattern-Maker
#: -Legacy.ipynb`, where "Legacy" names the notebook's SUBJECT (a legacy
#: pattern-maker) and not its status -- it is a maintained lesson in a numbered
#: series (04-1..04-4) and it already carries 4 exercises. A scope rule that
#: silently removes a conforming course notebook from the denominator is the
#: same failure as one that leaves artifacts in it, just harder to notice.
LEGACY_RE = re.compile(r"legacy", re.IGNORECASE)

#: Kinds that carry no exercise budget: they are outside the corpus entirely.
OUT_OF_CORPUS_KINDS = frozenset(
    {"artifact", "template", "vendored", "archive", "legacy", "tooling", "student"}
)


def classify_notebook(path: Path) -> tuple[str, int | None]:
    """Return ``(kind, threshold)`` for a notebook path.

    ``threshold`` is ``None`` when the notebook is outside the pedagogical
    corpus (kind in :data:`OUT_OF_CORPUS_KINDS`); such notebooks are never
    sub-threshold because the convention does not apply to them.

    ``standard_threshold`` applies to ordinary course notebooks. Setup and Lean
    notebooks stay in the corpus -- they ARE course material -- but carry a
    minimum of 0 per :data:`KIND_MINIMUM`, so raising ``--threshold`` never
    invents an exercise budget for a notebook the rule exempts.
    """
    return _classify(path, standard_threshold=DEFAULT_THRESHOLD)


def _scope_parts(path: Path, root: Path | None = None) -> tuple[str, ...]:
    """Path components that may carry classification signal.

    The directory rules below (underscore, legacy, `groupe-`) must only see the
    part of the path INSIDE the scanned tree. The absolute prefix above it
    belongs to whoever cloned the repo, and it is not signal: a checkout under
    `.../_worktrees/` or `.../legacy-box/` would otherwise classify every
    notebook in the repository as archive -- silently, and with a green
    `--check`, since an empty corpus cannot fail. Caught by a unit test whose
    own `tmp_path` happened to contain the substring `legacy`.
    """
    for anchor in (root, NOTEBOOKS_DIR, REPO_ROOT):
        if anchor is None:
            continue
        try:
            return path.resolve().relative_to(anchor.resolve()).parts
        except (ValueError, OSError):
            continue
    return path.parts


def _classify(
    path: Path, standard_threshold: int, root: Path | None = None
) -> tuple[str, int | None]:
    parts = _scope_parts(path, root)
    stem = path.stem

    if any(part in NON_PEDAGOGICAL_DIRS for part in parts):
        return ("archive", None)
    if any(part.startswith("_") for part in parts[:-1]):
        return ("archive", None)
    if any(LEGACY_RE.search(part) for part in parts[:-1]):
        return ("legacy", None)
    if any(part.casefold().startswith("groupe-") for part in parts):
        # Student group deliverables (`groupe-I2-contre-arguments-aspic/`) are
        # submissions, not course material we author.
        return ("student", None)
    if "template" in stem.casefold():
        return ("template", None)
    if ARTIFACT_STEM_RE.search(stem):
        return ("artifact", None)
    if stem.startswith("_"):
        # `_e2e_quant_validation.ipynb` -- internal harness notebook.
        return ("tooling", None)

    # A notebook sitting directly at the top of MyIA.AI.Notebooks/ belongs to no
    # series; every taught series lives in a family directory. `GradeBook.ipynb`
    # (the grading engine) is the only such file today. Gate on the NORMALIZED
    # `parts` (form-invariant), NOT on `path.is_absolute()`: a relative path --
    # exactly what `check_pr_exercises.py --stdin` receives from
    # `git diff --name-only` -- silently skipped the rule, so the PR gate and the
    # fleet scan returned different verdicts for the same file, and the liar was
    # the one posing labels (#8835). `parts` (= `_scope_parts`) already resolves
    # both forms to the identical tuple, so every directory rule must consume it.
    if len(parts) == 1:
        return ("tooling", None)

    if SETUP_STEM_RE.search(stem) or any(SETUP_DIR_RE.search(p) for p in parts[:-1]):
        return ("setup", KIND_MINIMUM["setup"])
    if LEAN_STEM_RE.search(stem):
        return ("lean", KIND_MINIMUM["lean"])
    return ("standard", standard_threshold)

# \bexercice\b anywhere in the line, case-insensitive, French or English form.
# Matches `### Exercice 1`, `## 8. Exercice`, `### Exercice - ...`, `### Exercise`.
# Used for CODE-cell comment detection (broad: a code stub's comment is always an
# instance reference; plural section headers do not appear as code comments).
EXERCISE_WORD_RE = re.compile(r"\bexercic(?:e|es)\b", re.IGNORECASE)
EXERCISE_WORD_EN_RE = re.compile(r"\bexercises?\b", re.IGNORECASE)

# SINGULAR-only forms for MARKDOWN instance-header counting (#6051). A markdown
# header is one EXERCISE INSTANCE only when it names a singular exercise
# (`### Exercice 1`, `## 8. Exercice`, `### Exercise`). A PLURAL section header
# (`## 9. Exercices`, `## Exercises`) groups exercises without being one -- it
# must NOT count as an instance NOR steal the forward-pairing of the next code
# cell (Bug 2: `## 9. Exercices` was forward-pairing the real Exercice 1 stub,
# so the section header stood in for the exercise and hid the real count).
# `\bexercice\b` does not match `exercices` (no word boundary between `e` and
# `s`), so these cleanly separate singular instances from plural sections.
EXERCISE_INSTANCE_RE = re.compile(r"\bexercice\b", re.IGNORECASE)
EXERCISE_INSTANCE_EN_RE = re.compile(r"\bexercise\b", re.IGNORECASE)
# Plural-only detection (a markdown header whose exercise word is ONLY plural is
# a section, not an instance). Used to decide whether a header cell that mentions
# the exercise word carries any real instance.
EXERCISE_SECTION_RE = re.compile(r"\bexercices\b", re.IGNORECASE)
EXERCISE_SECTION_EN_RE = re.compile(r"\bexercises\b", re.IGNORECASE)

# An ATX markdown header line starts with `#` (1-6 hashes) followed by a space
# and the header text. We deliberately do NOT match Setext headers (underlines
# of `---`/`===`) because a horizontal rule `---` on its own line would be a
# false positive (a `---` separator is a `<hr>`, not a header) -- this is what
# initially mis-paired a `---` cell with the exercise code cell below it.
MARKDOWN_HEADER_RE = re.compile(r"^\s{0,3}#{1,6}\s+(.*)", re.MULTILINE)

# The exercise NUMBER a cell references, e.g. ``Exercice 3`` -> ``'3'``,
# ``Exercice 3b`` -> ``'3b'``, ``Exercise 2`` -> ``'2'``. Used ONLY to gate
# backward stub/header pairing (see count_exercises_in_notebook): a stub that
# PRECEDES a header is absorbed into it only when both reference the same
# number, so a stub belonging to the *previous* exercise in a sequential
# layout (header N -> stub N -> header N+1) is never wrongly absorbed. The
# optional trailing letter distinguishes ``3`` from ``3b`` (two distinct
# exercises). Numberless references (``# Exercice : ...``) return None and are
# left unpaired -- conservative (may leave a residual double-count, but never
# under-counts by absorbing a foreign stub).
EXERCISE_NUMBER_RE = re.compile(
    r"\b(?:exercic(?:e|es)|exercises?)\s*([-+]?\d+[a-z]?)", re.IGNORECASE
)

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
    # TODO / Indice markers. Python/F#/Lean use `#`, C# / .NET Interactive
    # use `//`. A scaffolded C# exercise (class skeleton + `// TODO etudiant`
    # + multiple code lines) is a student stub, not a solution: without the
    # `//` form it escaped the `<= 1 effective code-line` rule and was
    # silently under-counted (e.g. Search-11-Metaheuristics-Csharp cells
    # 24-26, each `// Exercice N` + `// TODO etudiant` + partial skeleton).
    re.compile(r"#\s*TODO", re.IGNORECASE),
    re.compile(r"//\s*TODO", re.IGNORECASE),
    re.compile(r"#\s*Indice", re.IGNORECASE),
    re.compile(r"//\s*Indice", re.IGNORECASE),
    # Lean 4 / Haskell line comments use ``--``. A scaffolded Lean exercise
    # (``-- Exercice N`` + ``-- TODO etudiant`` + partial skeleton) is a student
    # stub, not a solution: without the ``--`` form it escaped both STUB_PATTERNS
    # and the ``<= 1 effective code-line`` rule (Lean comment lines were counted
    # as code lines), so Lean notebooks were silently under-counted (e.g.
    # GameTheory/SocialChoice/02-Lean-SocialChoice-Formal cells 32-34, each
    # ``-- EXERCICE N`` + ``-- TODO etudiant`` + formalisation skeleton; and
    # GameTheory-2b/4b/15b-Lean ``-- Exercice N`` stubs). Analogous to the C#
    # ``//`` blind-spot fixed in #5179, now closed for the Lean family.
    re.compile(r"--\s*TODO", re.IGNORECASE),
    re.compile(r"--\s*Indice", re.IGNORECASE),
    # `$?` accepts both regular (`"..."`) and interpolated (`$"..."`) strings:
    # `Console.WriteLine($"Exercice 2 a completer ...")` is the idiomatic C#
    # interpolated form and was not matched by the quote-only variant.
    # `display(...)` (not `Console.WriteLine`) is the .NET Interactive idiom for
    # stub markers: `Console.WriteLine` is SWALLOWED in headless papermill, so
    # authors use `display("Exercice ... a completer")` instead. Without the
    # `display` form, such stubs were under-counted (e.g. GameTheory-5 cell Ex2,
    # `display("Exercice 2 a completer ...")` with no `// TODO`/`// Indice`).
    re.compile(r'(?:Console\.WriteLine|display)\(\$?["\']Exercice', re.IGNORECASE),
    re.compile(r"^\s*result\s*=\s*None\b", re.MULTILINE | re.IGNORECASE),
    re.compile(r"^\s*raise\s+NotImplementedError", re.MULTILINE),
    re.compile(r"^\s*assert\s+False\b", re.MULTILINE),
    # "a completer" / "to complete" LINE-COMMENT stub markers. A scaffolded
    # cell whose comment line is itself the marker -- ``# A COMPLETER``,
    # ``// a completer``, ``-- à compléter`` -- is a student stub, but this
    # phrase is not one of the TODO/Indice/pass/return markers above, so a
    # multi-line skeleton cell bearing only such a comment escaped STUB_PATTERNS
    # and was under-counted (e.g. Search-11 cell 43: ``# A COMPLETER`` + a
    # truncated ``problem_profit = Problem(`` skeleton). The phrase must be the
    # LEADING content of the comment (right after the ``#``/``//``/``--`` marker,
    # optional parenthesis): a mid-sentence ``# ... la cellule est a completer``
    # in a worked solution's prose is NOT a stub marker and must not match.
    # Accented and English forms covered.
    re.compile(
        r"^\s*(?:#|//|--)\s*\(?[ \t]*(?:a compl[eé]ter|to complete)\b",
        re.IGNORECASE | re.MULTILINE,
    ),
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
        # Lean 4 / Haskell line comments start with ``--``; without this they
        # were counted as effective code lines, so a Lean stub cell full of
        # ``--`` scaffold comments read as multi-line "code" and escaped the
        # ``<= 1 effective code-line`` rule.
        and not ln.strip().startswith("--")
    ]
    code_lines = [
        ln for ln in lines
        if not ln.startswith("import ") and not ln.startswith("from ")
        and not ln.startswith("using ")
    ]
    return len(code_lines) <= 1


def _code_cell_mentions_exercise(source: str) -> bool:
    """A code cell whose comments name an exercise.

    Language-agnostic comment detection: a full-line comment is one whose
    stripped form starts with ``#`` (Python / F#) OR ``//`` (C# /
    .NET Interactive) OR ``--`` (Lean 4 / Haskell). Inline trailing comments
    (``code // Exercice``) are intentionally NOT matched -- a stub marker is a
    full-line comment, not a reference buried after executable code.

    Historically this only matched ``#``, which made every C# notebook blind
    to ``// Exercice N`` stubs (the .NET family uses ``//``). Agents then
    re-discovered the undercount ad-hoc, notebook by notebook (Probas/Infer,
    ML.Net). Matching ``//`` here closes that blind-spot at the source.
    Matching ``--`` closes the analogous Lean blind-spot (GameTheory-Lean
    ``-- Exercice N`` stubs were invisible to the canonical tool).
    """
    comments = [
        ln for ln in source.split("\n")
        if ln.strip().startswith("#")
        or ln.strip().startswith("//")
        or ln.strip().startswith("--")
    ]
    blob = "\n".join(comments)
    return bool(EXERCISE_WORD_RE.search(blob) or EXERCISE_WORD_EN_RE.search(blob))


def _markdown_mentions_exercise(source: str) -> bool:
    """True if any markdown header line contains the exercise word."""
    for m in MARKDOWN_HEADER_RE.finditer(source):
        header_text = m.group(1)
        if EXERCISE_WORD_RE.search(header_text) or EXERCISE_WORD_EN_RE.search(header_text):
            return True
    return False


def _markdown_instance_header_lines(source: str) -> list[str]:
    """Markdown header texts that each name a SINGULAR exercise instance.

    Returns one entry per INSTANCE header line, so a single markdown cell that
    groups several exercise statements under sub-headers (`### Exercice 1`,
    `### Exercice 2`, `### Exercice 3`) yields 3 instances, not 1 (#6051 Bug 1:
    such a grouped cell was under-counted because pass 1 added one hit per CELL).

    PLURAL section headers (`## 9. Exercices`, `## Exercises`) are excluded:
    a section groups exercises without being one. A header line is an instance
    only when it carries a SINGULAR exercise word. This also prevents a plural
    section header from acting as a header cell that forward-pairs the next code
    cell (Bug 2: the section `## 9. Exercices` stole the real Exercice 1 stub).

    A line that contains BOTH a plural and a singular form is treated as an
    instance (the singular reference dominates): e.g. ``## Exercices : Exercice 1
    recapitulatif`` still counts. A line with ONLY the plural is a section.
    """
    instances: list[str] = []
    for m in MARKDOWN_HEADER_RE.finditer(source):
        header_text = m.group(1)
        has_singular = bool(
            EXERCISE_INSTANCE_RE.search(header_text)
            or EXERCISE_INSTANCE_EN_RE.search(header_text)
        )
        if has_singular:
            instances.append(header_text)
    return instances


def _exercise_number(source: str) -> str | None:
    """Exercise number token a cell references, e.g. ``'3'`` or ``'3b'``.

    Returns the first ``Exercice <n>`` / ``Exercise <n>`` capture found
    anywhere in ``source`` (markdown header text or code comment), sign-stripped
    and lowercased. Returns None when the cell names an exercise with NO number
    (``# Exercice : ...``): numberless references cannot be safely pair-matched,
    so the caller treats them as unpaired.
    """
    m = EXERCISE_NUMBER_RE.search(source)
    if not m:
        return None
    return m.group(1).lstrip("+-").lower()


def count_exercises_in_notebook(path: Path) -> NotebookCount:
    """Count exercises in one notebook, with per-cell evidence.

    Deduplication: an exercise may appear as BOTH a markdown header AND an
    adjacent code stub. We pair them so it counts once. Pairing covers two
    layouts -- the common one (header at cell i, stub at cell i+1) and the
    "fill-in box then description" layout (stub at cell i, header at cell
    i+1). The backward layout is gated by a matching exercise NUMBER so a stub
    belonging to the *previous* exercise in a sequential layout (header N ->
    stub N -> header N+1) is never absorbed. A code-cell exercise with no
    paired header is its own exercise.
    """
    result = NotebookCount(path=path)
    try:
        with open(path, "r", encoding="utf-8-sig") as f:
            nb = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        result.parse_error = f"Failed to parse notebook: {exc}"
        return result

    cells = nb.get("cells", [])

    # First pass: detect markdown-header exercises, counting ONE instance per
    # SINGULAR exercise header LINE (not per cell). A markdown cell that groups
    # several exercise statements (`### Exercice 1`, `### Exercice 2`, ...) under
    # sub-headers therefore yields N instances, not 1 (#6051 Bug 1). PLURAL
    # section headers (`## 9. Exercices`) carry no instance and do NOT make the
    # cell a header cell -- so they neither count nor forward-pair the next code
    # cell (Bug 2: the section used to steal the real Exercice 1 stub below it).
    header_cell_indices: set[int] = set()
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "markdown":
            continue
        source = "".join(cell.get("source", []))
        instance_lines = _markdown_instance_header_lines(source)
        if not instance_lines:
            continue
        for _line in instance_lines:
            result.exercises.append(
                ExerciseHit(
                    cell_index=i,
                    cell_type="markdown",
                    source=source,
                    detected_by="markdown_header",
                )
            )
        header_cell_indices.add(i)

    # Track which code cells are the paired stub of an exercise header so we
    # do not double-count them in the second pass. A stub may sit EITHER just
    # below its header (common) OR just above it (a "fill-in box then
    # description" layout, where the stub at cell i precedes its own header at
    # cell i+1). The backward direction is gated by a MATCHING EXERCISE NUMBER
    # so we never absorb a stub that belongs to the *previous* exercise in the
    # normal sequential layout (header N -> stub N -> header N+1): there the
    # stub's number N differs from the following header's number N+1, so the
    # match fails and both are counted as distinct exercises (no under-count).
    paired_code_indices: set[int] = set()
    for idx in sorted(header_cell_indices):
        # Forward (common): the stub just below the header, within 3 cells.
        for j in range(idx + 1, min(idx + 4, len(cells))):
            if cells[j].get("cell_type") == "code":
                paired_code_indices.add(j)
                break
        # Backward (stub-then-header layout): the nearest preceding code cell,
        # absorbed only when it references the SAME exercise number as the
        # header. Numberless headers/stubs are left unpaired (conservative).
        header_source = "".join(cells[idx].get("source", []))
        header_num = _exercise_number(header_source)
        if header_num is None:
            continue
        for j in range(idx - 1, max(idx - 4, -1), -1):
            cell = cells[j]
            if cell.get("cell_type") != "code":
                continue
            stub_source = "".join(cell.get("source", []))
            if (
                _code_cell_mentions_exercise(stub_source)
                and _exercise_number(stub_source) == header_num
            ):
                paired_code_indices.add(j)
            break  # nearest preceding code cell is the only candidate

    # Second pass: code-cell exercises with NO preceding markdown header.
    #
    # A stub cell qualifies when it MENTIONS an exercise and IS a stub. The
    # mention check has two layers: (1) the comment-aware `_code_cell_mentions_
    # exercise` (a full-line comment names the exercise), AND (2) a broader
    # full-source scan for the exercise word. Layer (2) catches stubs whose
    # exercise reference is NOT in a `#`/`//`/`--` comment -- e.g. a C#
    # `display("Exercice 2 a completer ...")` or Python `print("Exercice ...")
    # stub marker, or a stub whose `# Partie N` / `# Etape` header carries no
    # "exercice" word at all but the cell prints one (SC-26-Final-Project
    # Parties 2/3/4). Layer (2) is safe because pass-2 still requires
    # `_is_stub_code`, so a complete solution mentioning "exercice" in prose is
    # never counted; and `paired_code_indices` (built in the unchanged
    # pairing pass) already excludes header-paired stubs, so this only adds
    # genuinely-unpaired stubs -- monotonic non-decrease per notebook by
    # construction (pairing is untouched, the disjunct only widens detection).
    for i, cell in enumerate(cells):
        if cell.get("cell_type") != "code":
            continue
        if i in paired_code_indices:
            continue
        source = "".join(cell.get("source", []))
        mentions_exercise = (
            _code_cell_mentions_exercise(source)
            or bool(EXERCISE_WORD_RE.search(source))
            or bool(EXERCISE_WORD_EN_RE.search(source))
        )
        if mentions_exercise and _is_stub_code(source):
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

    Also excludes notebooks that :func:`classify_notebook` places outside the
    pedagogical corpus (research artifacts, quantbooks, templates, probes,
    vendored sub-repos, archives). Without that filter the default target list
    is not the corpus, and every aggregate computed from it -- conforming count,
    sub-threshold tally, ``--check`` exit code -- carries a denominator that
    silently includes material the convention never applied to.
    """
    return corpus_scope(root)[0]


def corpus_scope(root: Path) -> tuple[list[Path], dict[str, int]]:
    """Return ``(corpus, removed_by_kind)`` for a tree.

    The second element is the part a plain filter throws away. Reporting the
    corpus size alone would leave the reader unable to tell a tool that
    inspected everything from one that quietly narrowed its own scope -- the
    failure this change exists to fix, so it must not be reintroduced by the
    fix itself. `--check` prints it as `Out of corpus`.
    """
    out: list[Path] = []
    removed: dict[str, int] = {}
    if not root.exists():
        return out, removed
    for nb_path in sorted(root.rglob("*.ipynb")):
        # #8858-class guard: root.rglob yields ABSOLUTE paths, so filtering
        # on nb_path.parts (absolute components) matches the repo's ABSOLUTE
        # path whenever the clone lives under a skip-named ancestor (e.g.
        # .../archive/CoursIA/... or .../research/...) and silently empties
        # the entire corpus -- a false-empty corpus then passes --check
        # trivially. Filter on the path RELATIVE to the scan root instead.
        rel_parts = nb_path.relative_to(root).parts
        if any(exc in rel_parts for exc in EXCLUDE_DIRS):
            continue
        if nb_path.stem.endswith("_output"):
            continue
        kind, _ = _classify(nb_path, standard_threshold=DEFAULT_THRESHOLD, root=root)
        if kind in OUT_OF_CORPUS_KINDS:
            removed[kind] = removed.get(kind, 0) + 1
            continue
        out.append(nb_path)
    return out, removed


def _family_of(path: Path, notebooks_dir: Path) -> str:
    try:
        rel = path.relative_to(notebooks_dir)
        return rel.parts[0] if rel.parts else "_root"
    except ValueError:
        return "_root"


def _display_path(path: Path) -> Path:
    """Repo-relative form for reporting, falling back to the path itself.

    `relative_to` raises for an absolute path outside the repo, so reporting a
    target collected from elsewhere would crash the run rather than print it.
    """
    if not path.is_absolute():
        return path
    try:
        return path.relative_to(REPO_ROOT)
    except ValueError:
        return path


def run(
    targets: list[Path],
    threshold: int,
    json_out: bool,
    check: bool,
    root: Path | None = None,
    removed_by_kind: dict[str, int] | None = None,
) -> int:
    """Execute the count over the given targets. Returns exit code for --check.

    ``root`` is the tree the targets were collected from; it anchors path-based
    classification so the prefix above it never carries signal (:func:`_scope_parts`).
    """
    if json_out:
        return _run_json(targets, threshold, root, removed_by_kind)
    return _run_text(targets, threshold, check, root, removed_by_kind)


def _run_text(
    targets: list[Path],
    threshold: int,
    check: bool,
    root: Path | None = None,
    removed_by_kind: dict[str, int] | None = None,
) -> int:
    sub_threshold: list[tuple[Path, NotebookCount, str, int]] = []
    parse_errors: list[tuple[Path, str]] = []
    exempt: list[tuple[Path, str]] = []
    by_kind: dict[str, int] = {}
    total_notebooks = 0
    total_exercises = 0

    for nb_path in targets:
        kind, effective = _classify(nb_path, standard_threshold=threshold, root=root)
        by_kind[kind] = by_kind.get(kind, 0) + 1
        if effective is None:
            exempt.append((nb_path, kind))
            continue
        total_notebooks += 1
        cnt = count_exercises_in_notebook(nb_path)
        if cnt.parse_error:
            parse_errors.append((nb_path, cnt.parse_error))
            continue
        total_exercises += cnt.count
        if cnt.count < effective:
            sub_threshold.append((nb_path, cnt, kind, effective))

    print(f"Notebooks in corpus : {total_notebooks}")
    print(f"Total exercises     : {total_exercises}")
    print(
        f"Threshold           : >= {threshold} for course notebooks "
        f"(setup / Lean exempt -- #2161 table)"
    )
    print(
        f"Conforming          : "
        f"{total_notebooks - len(sub_threshold) - len(parse_errors)}"
    )
    print(f"Sub-threshold       : {len(sub_threshold)}")
    if parse_errors:
        print(f"Parse errors        : {len(parse_errors)}")
    # The denominator, spelled out: without it, "N sub-threshold" is not
    # actionable because it silently mixes exempt material into the tally.
    removed = dict(removed_by_kind or {})
    for _, kind in exempt:  # explicitly-passed paths the scan never saw
        removed[kind] = removed.get(kind, 0) + 1
    if removed:
        detail = ", ".join(f"{k}={v}" for k, v in sorted(removed.items()))
        print(f"Out of corpus       : {sum(removed.values())} ({detail})")

    if sub_threshold:
        print("\n--- Sub-threshold notebooks (with evidence) ---")
        for nb_path, cnt, kind, effective in sub_threshold:
            rel = _display_path(nb_path)
            print(f"\n[{cnt.count}/{effective}] ({kind}) {rel}")
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


def _run_json(
    targets: list[Path],
    threshold: int,
    root: Path | None = None,
    removed_by_kind: dict[str, int] | None = None,
) -> int:
    payload = {
        "threshold": threshold,
        "out_of_corpus": dict(sorted((removed_by_kind or {}).items())),
        "notebooks": [],
    }
    for nb_path in targets:
        kind, effective = _classify(nb_path, standard_threshold=threshold, root=root)
        cnt = count_exercises_in_notebook(nb_path)
        entry = {
            "path": str(_display_path(nb_path)),
            "count": cnt.count,
            "kind": kind,
            # None => outside the pedagogical corpus, so never sub-threshold.
            "effective_threshold": effective,
            "in_corpus": effective is not None,
            "conforming": effective is None
            or (cnt.count >= effective and cnt.parse_error is None),
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
        default=DEFAULT_THRESHOLD,
        help=(
            f"Minimum exercises for an ordinary course notebook "
            f"(default: {DEFAULT_THRESHOLD}, per #2161). Setup and Lean "
            f"notebooks are exempt by the rule's exception table and are never "
            f"flagged, whatever value is passed here."
        ),
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
    removed_by_kind: dict[str, int] = {}
    scan_root: Path | None = None

    def _absorb(root: Path) -> None:
        found, removed = corpus_scope(root)
        targets.extend(found)
        for kind, n in removed.items():
            removed_by_kind[kind] = removed_by_kind.get(kind, 0) + n

    if args.paths:
        for raw in args.paths:
            p = Path(raw)
            if not p.exists():
                print(f"warning: {raw} does not exist, skipping", file=sys.stderr)
                continue
            if p.is_dir():
                _absorb(p)
            elif p.suffix == ".ipynb":
                targets.append(p)
    elif args.family:
        scan_root = NOTEBOOKS_DIR / args.family
        _absorb(scan_root)
    else:
        scan_root = NOTEBOOKS_DIR
        _absorb(scan_root)

    if not targets:
        print("No notebooks matched the given targets.", file=sys.stderr)
        return 0

    return run(
        targets,
        threshold=args.threshold,
        json_out=args.json_out,
        check=args.check,
        root=scan_root,
        removed_by_kind=removed_by_kind,
    )


if __name__ == "__main__":
    sys.exit(main())
