#!/usr/bin/env python3
"""
Detect solution leaks in Jupyter notebooks.

A "solution leak" is an exercise cell (labeled "Exercice N") that contains
complete working code instead of a stub (pass, print("Exercice a completer"),
return None, # TODO, // TODO).

Usage:
    python detect_solution_leaks.py --scan <path>
    python detect_solution_leaks.py --scan-all
    python detect_solution_leaks.py --scan-all --check  (exit 1 if leaks found)

Severity levels:
    HIGH   = "Exercice N" label + complete solution code (not stub)
    MEDIUM = Duplicate exercise numbering
    LOW    = "Exemple guide" label with stub code (inconsistency)
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

STUB_PATTERNS = [
    r'print\(["\']Exercice a completer',
    r'print\(["\']Exercices a completer',
    r'^\s*pass\s*$',
    r'return None',
    r'#\s*TODO',
    r'//\s*TODO',
    r'Console\.WriteLine\(["\']Exercice a completer',
    r'Console\.WriteLine\(["\']Exercices a completer',
    # Lean stub idioms (Lean line comments start with `--`).
    r'--\s*TODO',
    # Lean `sorry` tactic admits the goal — an exercise cell using it is a stub
    # (the proof is unverified, intentionally left for the student).
    r'\bsorry\b',
    # .NET Interactive / F# `.Display("...a completer")` idiom (the existing
    # patterns only cover Console.WriteLine / print).
    r'\.Display\s*\([^)]*(?:a compl[ée]ter|compl[ée]ter)',
    # Python assignment-stub: `result = None  # TODO etudiant` /
    # `matrice = None  # Remplacez None`. `return None` only matches a return
    # statement, not an assignment that defers the work to the student.
    r'=\s*None\s*#.*(?:TODO|Remplacez|a compl[ée]ter|compl[ée]ter)',
]

EXERCISE_HEADER_RE = re.compile(
    r'^#+\s*(?:\d+[.:]\s*)?(?:Exercice|Exercise)\s*(\d*)\s*[:.]?\s*(.*)',
    re.MULTILINE | re.IGNORECASE,
)

SOUMIS_PAR_RE = re.compile(r'soumis par|submitted by', re.IGNORECASE)

SOLUTION_MARKER_RE = re.compile(
    r'[Ss]olution|[Rr][eé]ponse|[Rr]esultat|ref\s*:',
    re.IGNORECASE,
)

# A worked-example header line (Exemple guide / Exemple resolu / Example / Worked).
# Used for closest-preceding-header attribution: a code cell whose nearest header
# is a worked example is NOT an exercise solution leak, even if a broader
# "Exercices" section header sits further back (cf exercise-example-labeling.md,
# content-based rule). Distinguished from EXERCISE_HEADER_RE (Exercice/Exercise).
EXAMPLE_HEADER_RE = re.compile(
    r'^#+\s*(?:\d+[.:]\s*)?(?:Exempl?es?|Examples?|Worked)',
    re.IGNORECASE,
)

# Any markdown ATX/SETEXT-like header line, for closest-header attribution.
HEADER_LINE_RE = re.compile(r'^#{1,6}\s+.+$', re.MULTILINE)

# A worked-example label appearing as the FIRST code comment line of a code cell
# (e.g. "# Exemple guide : ...", "// Example 1 : ...", "-- Exemple resolu").
# Mirrors EXAMPLE_HEADER_RE for the case where the worked-example label lives in
# a leading code comment rather than a markdown header. Cf exercise-example-labeling.md
# (content-based rule): a code cell that self-labels as a worked example is never an
# exercise solution leak, even under a broader "## Exercices" section header.
EXAMPLE_CODE_COMMENT_RE = re.compile(
    r'^\s*(?:#|//|--)\s*(?:\d+[.:]\s*)?(?:Exempl?es?|Examples?|Worked)',
    re.IGNORECASE,
)


def closest_preceding_header_is_example(cells, code_idx):
    """Return True if the closest preceding markdown header line is a worked
    example.

    Scans backwards from ``code_idx``; within a markdown cell, the LAST header
    line wins (it is the closest to the code that follows). A code cell owned by
    a worked example is never an exercise solution leak — this suppresses false
    positives where a code cell sits under a ``## Exercices`` section header but
    its actual nearest sub-header is ``### Exemple guide`` (in the same cell or
    an intervening one). Cf exercise-example-labeling.md (content-based rule).
    """
    for k in range(code_idx - 1, -1, -1):
        cell = cells[k]
        if cell.get('cell_type') != 'markdown':
            continue
        src = ''.join(cell.get('source', []))
        header_lines = HEADER_LINE_RE.findall(src)
        if not header_lines:
            continue  # prose-only markdown cell; keep scanning further back
        return bool(EXAMPLE_HEADER_RE.search(header_lines[-1]))
    return False


def code_cell_first_comment_labels_example(source: str) -> bool:
    """Return True if the first non-empty line of the code is a worked-example
    comment label.

    Some notebooks label a worked example via a leading code comment
    (``# Exemple guide : ...``, ``// Example 1 : ...``) sitting under a
    ``## Exercices`` section header, with NO intervening markdown sub-header.
    Such a cell is a worked example, not an exercise solution leak — it would be
    a false positive under header-only attribution. Suppresses that FP.
    Cf exercise-example-labeling.md (content-based rule).
    """
    for line in source.split('\n'):
        if not line.strip():
            continue
        return bool(EXAMPLE_CODE_COMMENT_RE.search(line))
    return False


def _header_level(line: str) -> int:
    """Return the ATX heading level (count of leading ``#``), or 0 if not a
    header line."""
    m = re.match(r'^(#{1,6})\s', line)
    return len(m.group(1)) if m else 0


def intervening_section_breaks_attribution(cells, exercise_idx, code_idx) -> bool:
    """Return True if a markdown header at the same or higher level than the
    exercise header appears between ``exercise_idx`` and ``code_idx``.

    A same-or-higher-level header (e.g. ``## Conclusion``, ``## Section 6``)
    starts a new section and breaks the attribution of the code cell to the
    exercise: the code then belongs to that later section, not the exercise.
    A DEEPER sub-header (e.g. ``### Indice`` under a ``## Exercice 1``) does
    NOT break the section (it is a child of the exercise, common in worked
    exercise scaffolding).

    Recall-safety: ``### Indice`` and ``### Interpretation`` (level 3) under
    ``### Exercice 1`` (level 3) are structurally indistinguishable from a
    visualisation sub-header at the same level — we MUST NOT over-suppress
    real exercise code cells. Therefore the level threshold is computed from
    the FIRST exercise header line (the num-less parent, e.g. ``## Exercices``
    at level 2), NOT the LAST numbered sub-header. With the parent level,
    ``### Indice`` (deeper, level 3) and ``### Interprétation`` (deeper,
    level 3) are correctly preserved.

    This suppresses cross-cell false positives where a demo/visualisation code
    cell sits a few cells after an exercise header but is actually owned by a
    later ``## Conclusion`` / ``## Section N`` section. Cf exercise-example-labeling.md
    (content-based rule). Safe default: if the exercise header level cannot be
    determined, do not suppress.

    Additional check: a numbered subsection header (``### 3.4 Title``,
    ``### 6.1 Diagrammes``) ALWAYS breaks attribution regardless of level.
    These announce a NEW topic (cf Tweety-4 cell#24 FP class: ``## Exercice``
    at level 2, then ``### 3.4 MaxSAT`` (level 3, deeper, but a real topic
    transition, not an exercise-internal sub-header). The number distinguishes
    a section/subsection boundary from exercise-internal scaffolding like
    ``### Indice`` or ``### Interprétation`` which are NEVER numbered.
    """
    ex_src = ''.join(cells[exercise_idx].get('source', []))
    # First exercise header line is the num-less parent (e.g. ``## 7. Exercices``
    # or ``## Exercices``). Its level is the threshold for the level-based check.
    first_match = EXERCISE_HEADER_RE.search(ex_src)
    if not first_match:
        return False
    matched_line = ex_src[first_match.start():first_match.end()]
    ex_level = _header_level(matched_line)
    if not ex_level:
        return False
    for k in range(exercise_idx + 1, code_idx):
        cell = cells[k]
        if cell.get('cell_type') != 'markdown':
            continue
        src = ''.join(cell.get('source', []))
        for header_line in HEADER_LINE_RE.findall(src):
            if _header_level(header_line) <= ex_level:
                return True
        # Numbered subsection header (`### 3.4 Title`, `### 6.1 Diagrammes`):
        # always breaks attribution regardless of level — these announce a
        # new topic, not an exercise-internal sub-detail. Cf Tweety-4 cell#24.
        if NUMBERED_SUBSECTION_HEADER_RE.search(src):
            return True
    return False


def _last_exercise_header_match(source: str):
    """Return the last exercise-header match in ``source`` (markdown cell).

    A single markdown cell may hold a parent section header (``## N. Exercices``,
    num-less because the ``N.`` is a section number) AND a numbered sub-header
    (``### Exercice 1 — ...``) describing the actual exercise. With
    ``re.MULTILINE``, ``EXERCISE_HEADER_RE.search(source)`` returns the FIRST
    match — the num-less parent — hiding the real numbered sub-header one line
    below. The LAST header line is closest to the code cell that follows (cf
    ``closest_preceding_header_is_example``, which already uses
    ``header_lines[-1]`` for the same reason).

    Prefer the LAST numbered match (closes the ``Exercice ?`` message class
    for the single-sub-header MULTI-HEADER pattern: num-less parent + ONE
    numbered child). Falls back to ``EXERCISE_HEADER_RE.search`` (first match)
    when there are MULTIPLE numbered matches in the cell — that is the
    "suggestions block" pattern (``## Exercices suggeres`` + ``#### Exercice 1,
    2, 3`` siblings), where the original first-match behaviour is correct: the
    suggestions are a SEPARATE numbering, not duplicates of earlier exercises.

    Recall-safe: never converts a numbered attribution to num-less; never
    re-orders numbered matches relative to their declaration order.
    """
    matches = list(EXERCISE_HEADER_RE.finditer(source))
    if not matches:
        return None
    numbered = [m for m in matches if m.group(1)]
    # Multi-sub-header suggestions block: keep the original first-match
    # behaviour (the suggestions are a SEPARATE numbering, not duplicates).
    if len(numbered) > 1:
        return matches[0]
    if numbered:
        return numbered[-1]
    return matches[-1]


def _numbered_exercise_header_between(cells, start_idx, end_idx) -> bool:
    """Return True if a markdown cell strictly between ``start_idx`` and
    ``end_idx`` (exclusive) holds a NUMBERED exercise header.

    A separate-cell num-less ``## Exercices`` section header followed by a
    numbered ``### Exercice N`` sub-header independently scans forward to the
    same code cell, producing a duplicate HIGH (``Exercice ?`` from the parent
    and ``Exercice N`` from the child). The numbered header is the closer
    attribution; the duplicate ``Exercice ?`` is the FP class. Caller skips
    the num-less iteration when this returns True.
    """
    for k in range(start_idx + 1, end_idx):
        cell = cells[k]
        if cell.get('cell_type') != 'markdown':
            continue
        src = ''.join(cell.get('source', []))
        if any(m.group(1) for m in EXERCISE_HEADER_RE.finditer(src)):
            return True
    return False


# A markdown header line that is a numbered subsection ("### N.M Title" or
# "## N. Title"). Distinguished from exercise-internal sub-headers like
# "### Indice", "### Etape N", "### Solution" (which are children of an
# exercise and SHOULD NOT break attribution). The numbered subsection
# pattern uses a digit-then-dot prefix at the start of the title — these
# are topic-level transitions ("### 3.4 MaxSAT", "### 6.1 Diagrammes 2D")
# that genuinely start a new section, even when nested under a level-2
# "## Exercice" header (which itself was promoted to level 2 because the
# notebook author dropped the section number prefix, e.g. "## Exercice : Enumeration de MUS").
NUMBERED_SUBSECTION_HEADER_RE = re.compile(
    r'^#{1,6}\s+\d+(?:\.\d+)*\.?\s+\S', re.MULTILINE,
)


def _numbered_subsection_header_between(cells, start_idx, end_idx) -> bool:
    """Return True if a markdown cell strictly between ``start_idx`` and
    ``end_idx`` (exclusive) holds a numbered subsection header (``### N.M Title``).

    Used by ``intervening_section_breaks_attribution`` to disambiguate: a deeper
    sub-header that introduces a NEW topic (numbered ``### N.M``) breaks
    attribution, while exercise-internal sub-headers (``### Indice``, ``### Etape N``,
    ``### Solution``, ``### Reponses``, ``### Interpretation``) do NOT.

    Recall-safety: a real solution cell never self-labels with a numbered
    subsection header (``# --- 3.4.1 Title ---``) when it sits between an
    exercise header and the next code cell — the exercise cell would own its
    own header. The only legitimate uses of numbered subsection headers are
    new topic transitions.
    """
    for k in range(start_idx + 1, end_idx):
        cell = cells[k]
        if cell.get('cell_type') != 'markdown':
            continue
        src = ''.join(cell.get('source', []))
        if NUMBERED_SUBSECTION_HEADER_RE.search(src):
            return True
    return False


def is_stub_code(source: str) -> bool:
    """Check if code cell source is a stub (not a real solution)."""
    lines = source.strip().split('\n')
    non_empty = [l.strip() for l in lines if l.strip() and not l.strip().startswith('//') and not l.strip().startswith('#')]

    if not non_empty:
        return True

    for pattern in STUB_PATTERNS:
        # re.MULTILINE so anchored patterns like `^\s*pass\s*$` match an
        # INDENTED `pass` inside a function body (the real-world stub case),
        # not just a top-level `pass` at the start of the cell source.
        if re.search(pattern, source, re.IGNORECASE | re.MULTILINE):
            return True

    code_lines = [l for l in non_empty if not l.startswith('import ') and not l.startswith('from ')]
    if len(code_lines) <= 1:
        return True

    return False


# A code line that DEFINES a new construct (function/class/proof). When such a
# line is EXECUTABLE (not commented out), the cell contains a real definition and
# cannot be a pure commented-template stub. Used by commented_template_stub as a
# fast early-exit (the real recall guard is the "non-trivial executable line"
# fallback below it).
EXECUTABLE_DEFINITION_RE = re.compile(
    r'^\s*(?:def |class |struct |namespace |interface |enum |theorem |lemma |defn |'
    r'inductive |instance |record |void |int |bool |string |float |double |var )',
)

# A prompt / TODO marker indicating the cell is a skeleton left for the student.
# A real complete solution never carries one of these.
PROMPT_MARKER_RE = re.compile(
    r'(?:TODO|a compl[ée]ter|compl[ée]ter|impl[ée]mentez|impl[ée]menter|'
    r'[àa] compl|votre code|student fills|etudiant|r[ée]pondez|r[ée]aliser)',
    re.IGNORECASE,
)


def commented_template_stub(source: str) -> bool:
    """Return True if the cell is a "commented-template" exercise stub.

    Some exercise cells embed the FULL solution as COMMENTED-OUT code (``# ...``,
    ``// ...``, ``-- ...``) plus a small amount of executable scaffolding (data
    assignments, a prompt print), so the student uncomments and fills the TODOs.
    Such a cell is a legitimate exercise skeleton, NOT a solution leak — but it
    trips ``len(source) > 8`` and has no matching STUB_PATTERN, so it is a HIGH
    false positive. Suppresses that FP.

    Recall-safe: a real (complete) solution always has EITHER an executable
    definition (``def``/``class``/``theorem``/...) OR at least one non-trivial
    executable line (a loop, a solver call, ...). Both make this return False.
    Only cells whose executable code is ENTIRELY trivial (assignments, prints,
    imports, collection literals) AND that carry a prompt/TODO marker are
    suppressed. A complete solution never carries a prompt marker.

    Cf exercise-example-labeling.md (content-based rule).
    """
    exec_lines = []
    for raw in source.split('\n'):
        s = raw.strip()
        if not s:
            continue
        # comment lines for the languages in this repo
        if (s.startswith('#') or s.startswith('//') or s.startswith('--')
                or s.startswith('(*') or s.startswith('/*') or s.endswith('*)') or s.endswith('*/')):
            continue
        exec_lines.append(s)

    # Fast early-exit: an executable definition => real code, not a template.
    if any(EXECUTABLE_DEFINITION_RE.search(l) for l in exec_lines):
        return False

    # Every executable line must be trivial (assignment / print / import /
    # collection literal / closing bracket). ANY non-trivial line (loop, call,
    # statement) => real code => not a template.
    for s in exec_lines:
        if s.startswith(('print(', 'Print(', 'Console.', 'Display(', 'printf', 'puts(', 'puts ')):
            continue
        if s.startswith(('import ', 'from ', 'using ', 'open ', 'require ', '#!')):
            continue
        if re.match(r'^[A-Za-z_][\w\[\]."\']*\s*(?:=|:=)', s):  # assignment target = / :=
            continue
        if s.startswith(('[', '(', '{', '{|')) or s.endswith((']', ')', '}', ',', '|}')):
            continue  # collection literal / continuation
        if s in (']', ')', '}', '|}'):
            continue
        return False  # non-trivial executable line -> not a pure template

    # Must carry a prompt/TODO marker (a complete solution never does).
    return bool(PROMPT_MARKER_RE.search(source))


# Markers that show the cell contains an explicit instructions block for the
# student (not just a comment about a code section). Found in cells where a
# real skeleton function/class is followed by `pass` at the end and a header
# block like "Instructions : 1. ... 2. ... 3. ..." / "Objectif : ..." /
# "Indices : ..." / "A implementer : ..." / "A vous de jouer". Anchored on
# `^` or `\n` followed by optional whitespace, so we don't match inside
# identifiers or inside a docstring that is preceded by a blank line.
SKELETON_INSTRUCTION_MARKER_RE = re.compile(
    r'(?:^|\n)(?:[ \t]*\n)*[ \t]*(?:(?:#|//|--)\s*)?(?:'
    r'Instructions?\s*[:：]'
    r'|Objectif\s*[:：]'
    r'|Indices?\s*[:：]'
    r'|A\s+(?:impl[ée]menter|compl[ée]ter)\s*[:：]'
    r'|Am[ée]liorations?\s+a\s+(?:impl[ée]menter|compl[ée]ter)'
    r'|Competences?\s+vis[ée]es?\s*[:：]'
    r'|Difficult[ée]\s*[:：]'
    r'|Algorithme\s*[:：]'
    r'|A\s+vous\s+de\s+jouer'
    r'|Vous\s+(?:pouvez|allez|devez)'
    r'|Etapes?\s*[:：]'
    r'(?:Fonctionnalit[ée]s?|Func)\s+a\s+(?:impl[ée]menter|compl[ée]ter)'
    r')',
    re.IGNORECASE,
)

# Short stub markers that show the cell has no real solution body — the
# student is meant to fill the gap. A complete solution never carries these.
SHORT_STUB_MARKER_RE = re.compile(
    r'(?:'
    r'A\s+COMPLETER'
    r'|A\s+impl[ée]menter'
    r'|Remplissez d\'abord'
    r'|en\s+attente\s+de\s+votre\s+impl[ée]mentation'
    r'|Remplissez les TODO'
    r'|D[ée]commentez et compl[ée]tez'
    r'|Remplacez le texte'
    r'|et compl[ée]ter la'
    r'|\bautre\s+strat[ée]gie\b'
    r'|vous\s+adapter\s+au\s+nouveau\s+contexte'
    r')',
    re.IGNORECASE,
)


def skeleton_with_instructions_stub(source: str) -> bool:
    """Return True if the cell is a real skeleton with a leading instructions block.

    Pattern: ``def foo(...): ...`` (or ``class Foo: ...`` etc.) with a real
    executable body (e.g. param checks, guards) AND at least 2 instruction
    markers (Indent: / Objectif: / Indices: / A implementer: / Algorithme: /
    A vous de jouer / ...) AND a trailing ``pass`` (the TODO marker).

    Such a cell is a legitimate exercise skeleton: the student replaces the
    guard branches or fills the body. The detector trips it because the body
    has real executable lines + the cell is longer than 8 lines.

    Recall-safe: a real solution has at least one *substantive* executable
    line in the body (a return, an assignment, a call) but does NOT match
    ``^\\s*pass\\s*(?:#.*)?$`` at the end of the cell. A complete solution
    never carries 2+ numbered instruction markers in leading comments.

    Cf exercise-example-labeling.md (content-based rule).
    """
    # Need at least 2 instruction markers in leading comments.
    markers = SKELETON_INSTRUCTION_MARKER_RE.findall(source)
    if len(markers) < 2:
        return False

    # Need a trailing `pass` (the TODO marker) somewhere near the end — a
    # real solution never ends in `pass`.
    lines = [l for l in source.split('\n') if l.strip()]
    if not lines:
        return False

    # Tolerate either:
    # (a) last non-empty line is `pass` (optionally with a trailing comment)
    # (b) last non-empty line is a `print(...)` announce + the line above it
    #     is `pass` (App-13-TSP pattern: `pass  # Exercice: ...` then
    #     `print('Fonction ... definie')`)
    # (c) last non-empty line is a `print(...)` and the cell contains a
    #     `pass` followed by `# Exercice` somewhere (CSP-3-Advanced C#,
    #     App-1b-NQueens where the trailing `; Console.WriteLine` follows
    #     the definition block).
    last = lines[-1].strip()
    last_is_pass = bool(re.match(r'^\s*pass\s*(?:#.*)?$', last))
    last_is_print_after_pass = (
        bool(re.match(r'^\s*(?:print|Console\.WriteLine|Display|Print)\s*\(', last))
        and len(lines) >= 2
        and bool(re.match(r'^\s*pass\s*(?:#.*)?$', lines[-2].strip()))
    )
    has_trailing_pass_comment = bool(re.search(
        r'^\s*pass\s*#\s*Exercice', source, re.MULTILINE | re.IGNORECASE
    ))
    if not (last_is_pass or last_is_print_after_pass or has_trailing_pass_comment):
        return False

    return True


def exercise_with_none_stub_or_marker(source: str) -> bool:
    """Return True if the cell is an exercise with ``= None`` stub assignments
    (or short "A COMPLETER" markers) + a trailing print/console announce.

    Pattern: a real ``def``/``class`` skeleton whose body assigns local
    variables to ``None`` (or contains short stub markers like ``A COMPLETER``)
    AND ends with a ``print(...)`` / ``Console.WriteLine(...)`` announce. The
    student replaces the None values with real computations.

    Recall-safe: a complete solution has substantive body lines (assignments
    to computed values, returns, function calls) — not just ``= None`` stubs.
    The cell must have at least 2 ``= None`` assignments OR 2 ``A COMPLETER``
    markers to be flagged — single None is too lenient.
    """
    # Must have at least 2 None-stub assignments OR 2 short stub markers.
    none_count = len(re.findall(r'=\s*None\s*(?:#.*)?$', source, re.MULTILINE))
    short_marker_count = len(SHORT_STUB_MARKER_RE.findall(source))
    if none_count < 2 and short_marker_count < 2:
        return False

    # Must end with a print/console announce (the TODO marker).
    lines = [l for l in source.split('\n') if l.strip()]
    if not lines:
        return False
    last = lines[-1].strip()
    if not re.match(r'^\s*(?:print|Console\.WriteLine|Display|Print|puts)\s*\(', last):
        return False

    return True


def exercise_with_a_completer_minizinc(source: str) -> bool:
    """Return True if the cell is a MiniZinc/C# exercise with ``A COMPLETER`` /
    ``A implémenter`` markers in the body. These are model-text stubs where the
    student fills in missing constraints; the source contains the SKELETON of
    a model in a triple-quoted string with TODO markers.

    Recall-safe: a complete solution has no ``A COMPLETER`` markers and no
    ``???`` placeholder expressions in MiniZinc constraints.
    """
    # MiniZinc patterns: % A COMPLETER, % A implémenter, % A vous de jouer
    # C# patterns: // A COMPLETER, // A implémenter
    # Python patterns: # A COMPLETER (case-insensitive)
    pattern = re.compile(
        r'(?:^|\n)\s*[#/%]\s*A\s+(?:COMPLETER|impl[ée]menter|compl[ée]ter|vous)',
        re.IGNORECASE | re.MULTILINE,
    )
    matches = pattern.findall(source)
    # Also count MiniZinc placeholder constraints — `???` inside a constraint
    # is the canonical MiniZinc "to be filled" marker. A complete solution
    # never has `???` placeholders.
    has_placeholder = bool(re.search(r'\?\?\?', source))
    if len(matches) < 1 and not has_placeholder:
        return False

    # Must contain a model definition (display_model or solve satisfy) or
    # be a multi-line string with IntentBlock markers.
    has_model = bool(re.search(r'display_model|solve\s+(?:satisfy|minimize|maximize)', source))
    return has_model or len(source) < 3000  # small enough to be a model snippet


def exercise_with_attente_implementation(source: str) -> bool:
    """Return True if the cell is a C# exercise announcing ``en attente de
    votre implementation`` (or ``à compléter``) via ``Console.WriteLine`` /
    ``Show`` / ``print``, with the body being scaffolding (variable setup,
    placeholders, model constructors) and NO real constraint declarations or
    real solver calls.

    Pattern: ``Console.WriteLine($"... en attente de votre implementation")``
    followed or preceded by informational prints about expected results. The
    student writes the actual constraint / solver code in place.

    Recall-safe: a complete solution has substantive solver calls
    (``model.Add(...)``, ``model.Solve()``, ``solver.Solve()``, ``Solver.Solve()``)
    and lacks the ``en attente`` / ``à compléter`` announcement.
    """
    # Must announce the placeholder state.
    has_attente = bool(re.search(
        r'(?:en\s+attente\s+de\s+votre\s+impl[ée]mentation|à\s+compl[ée]ter)',
        source, re.IGNORECASE
    ))
    if not has_attente:
        return False

    # Must use a console announce as the marker (Console.WriteLine / Show / print).
    has_print_marker = bool(re.search(
        r'(?:Console\.WriteLine|Show|print)\s*\([^)]*(?:attente|compl[ée]ter)',
        source, re.IGNORECASE
    ))
    if not has_print_marker:
        return False

    # Must NOT contain real solver calls — that would be a real solution.
    has_real_solver_call = bool(re.search(
        r'(?:model\.Solve|solver\.Solve|Solver\.Solve|\.Add\([^)]*\bconstraint|\.Add\([^)]*==|\.Add\([^)]*<=|\.Add\([^)]*>=)',
        source
    ))
    return not has_real_solver_call


def exercise_with_exercice_indice_skeleton(source: str) -> bool:
    """Return True if the cell is a Python exercise with ``# Exercice`` headers
    and ``# Indice`` (or ``# Etape``) guidance, no real solution body — the
    student follows the indicesteps to build the result.

    Pattern: a cell with 2+ ``# Exercice:`` / ``# Exercice 1:`` / ``# Indice:``
    style markers, OR contains multiple bare ``# Exercice`` / ``# Indice``
    lines, AND the body is mostly variable setup + guidance, NOT substantive
    solution code.

    Recall-safe: a complete solution has at least one substantive executable
    line (a return, a function call) that produces a real result and lacks
    the bare ``# Exercice`` / ``# Indice`` markers in the body.
    """
    pattern = re.compile(
        r'(?:^|\n)[ \t]*#[ \t]*(?:Exercice|Indice|Etape)\b',
        re.IGNORECASE | re.MULTILINE,
    )
    matches = pattern.findall(source)
    if len(matches) < 2:
        return False

    # Must not contain real solution patterns.
    # Solution signals: returns, function calls producing values, asserts.
    has_substantive_call = bool(re.search(
        r'(?:^\s*[a-z_][a-z0-9_]*\s*=\s*[a-zA-Z_]\w*\(|^\s*return\b)',
        source, re.MULTILINE
    ))
    return not has_substantive_call


def scan_notebook(path: str) -> list[dict]:
    """Scan a single notebook for solution leaks."""
    findings = []
    try:
        with open(path, 'r', encoding='utf-8-sig') as f:
            nb = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError):
        return [{"path": path, "severity": "ERROR", "message": "Failed to parse notebook"}]

    cells = nb.get('cells', [])
    exercise_numbers = {}

    for i, cell in enumerate(cells):
        if cell.get('cell_type') != 'markdown':
            continue

        source = ''.join(cell.get('source', []))

        # Last-numbered-match wins within a markdown cell (closes the
        # 'Exercice ?' message class for multi-header cells where a num-less
        # parent '## N. Exercices' sits above a numbered sub-header
        # '### Exercice M — ...'). See _last_exercise_header_match.
        m = _last_exercise_header_match(source)
        if not m:
            continue

        num = m.group(1)
        title = m.group(2)
        has_soumis = bool(SOUMIS_PAR_RE.search(source))

        if num:
            if num in exercise_numbers:
                findings.append({
                    "path": path,
                    "cell_index": i,
                    "cell_type": "markdown",
                    "severity": "MEDIUM",
                    "exercise_num": num,
                    "message": f"Duplicate Exercice {num} (first at cell {exercise_numbers[num]})",
                    "preview": source[:100],
                })
            else:
                exercise_numbers[num] = i

        next_code_idx = None
        next_code_source = None
        for j in range(i + 1, min(i + 4, len(cells))):
            if cells[j].get('cell_type') == 'code':
                next_code_idx = j
                next_code_source = ''.join(cells[j].get('source', []))
                break

        if next_code_source is None:
            continue

        # Num-less section header in its own cell ("## Exercices"): if a
        # NUMBERED exercise sub-header sits between this cell and the next code
        # cell, the numbered header owns the code (processed in its own
        # iteration). Without this skip the code cell is flagged twice —
        # "Exercice ?" here and "Exercice N" at the numbered header. Suppresses
        # the duplicate FP. The numbered header still flags the code if it is a
        # real leak, so this is recall-safe.
        if not num and _numbered_exercise_header_between(cells, i, next_code_idx):
            continue

        if has_soumis:
            if not is_stub_code(next_code_source):
                findings.append({
                    "path": path,
                    "cell_index": next_code_idx,
                    "cell_type": "code",
                    "severity": "HIGH",
                    "exercise_num": num or "?",
                    "message": f"Solution leak: Exercice {num or '?'} with 'soumis par' has complete code (not stub)",
                    "preview": next_code_source[:150],
                    "fix": f"Relabel cell {i} from 'Exercice' to 'Exemple guide'",
                })
            continue

        if not is_stub_code(next_code_source):
            # Closest-preceding-header attribution: a code cell whose nearest
            # header is a worked example (Exemple guide / Exemple resolu / ...)
            # is not an exercise leak, even if a broader "## Exercices" section
            # header sits further back. Suppress the false positive.
            # Also suppress when the code cell SELF-LABELS as a worked example
            # via its first comment line ('# Exemple guide : ...') under such a
            # section — no markdown sub-header to attribute to. Cf exercise-example-labeling.md.
            if (closest_preceding_header_is_example(cells, next_code_idx)
                    or code_cell_first_comment_labels_example(next_code_source)):
                continue
            # Cross-cell attribution guard: if a same-or-higher-level markdown
            # section header (e.g. "## Conclusion", "## Section 6", a "### 6.1"
            # sibling) appears between the exercise header and this code cell,
            # the code belongs to that later section, not the exercise. Suppress
            # the false positive. A deeper sub-header ("### Indice" under
            # "## Exercice 1") does not break the section.
            if intervening_section_breaks_attribution(cells, i, next_code_idx):
                continue
            # Commented-template stub: the whole solution is commented out and
            # only data assignments + a prompt print execute (the student
            # uncomments and fills the TODOs). A legitimate exercise skeleton,
            # not a leak. Suppresses the commented-solution-prompt FP class.
            # Recall-safe: a real solution has an executable def/class or a
            # non-trivial executable line, which makes the helper return False.
            if commented_template_stub(next_code_source):
                continue
            # Skeleton-with-instructions stub: a real ``def`` / ``class`` with
            # a guard body + trailing ``pass`` is paired with at least 2
            # numbered instruction markers (Instructions: / Objectif: /
            # Indices: / A implementer: / Algorithme: / A vous de jouer / ...).
            # The student replaces the guard branches or fills the body.
            # Suppresses the "real skeleton + pass + instructions block" FP
            # class that tripped the detector on App-13-TSP, Lean-8/10,
            # Lean-15/17, App-1b-NQueens, CSP-3-Advanced, EdgeDetection, etc.
            # Recall-safe: a real solution has 1) at least one substantive
            # line in the body (return/assignment/call) and 2) ends with
            # something other than `pass`. Both make the helper return False.
            if skeleton_with_instructions_stub(next_code_source):
                continue
            # Exercise with None-stub assignments + print trailer: real def/class
            # with `Q1 = None`, `IQR = None`, `nb_doublons = None`, etc. The
            # student replaces the None values with real computations. Lab4
            # DataWrangling, SW-12 GraphRAG, Planners-1, Arrow-33 pattern.
            # Suppresses the "def-with-None-stubs + print" FP class.
            # Recall-safe: a complete solution has substantive body lines
            # (returns, calls, computed assignments), not None stubs.
            if exercise_with_none_stub_or_marker(next_code_source):
                continue
            # MiniZinc/C# exercise with `A COMPLETER` markers in a model string.
            # App-8-MiniZinc pattern (% A COMPLETER :...). The student fills
            # the missing constraints. Not a leak.
            if exercise_with_a_completer_minizinc(next_code_source):
                continue
            # C# exercise with `en attente de votre implementation` announcement.
            # CSP-3-Advanced / CSP-7-Soft / App-1b-NQueens pattern: a model
            # constructor + informational Console.WriteLine about expected
            # results, with NO real solver calls. The student writes the
            # constraints in place.
            if exercise_with_attente_implementation(next_code_source):
                continue
            # Python exercise with `# Exercice` / `# Indice` / `# Etape`
            # guidance headers, no substantive call/return body. Arrow-33
            # pattern. The student follows the indicesteps.
            if exercise_with_exercice_indice_skeleton(next_code_source):
                continue
            solution_markers = bool(SOLUTION_MARKER_RE.search(next_code_source))
            if solution_markers or len(next_code_source.strip().split('\n')) > 8:
                findings.append({
                    "path": path,
                    "cell_index": next_code_idx,
                    "cell_type": "code",
                    "severity": "HIGH",
                    "exercise_num": num or "?",
                    "message": f"Solution leak: Exercice {num or '?'} has {len(next_code_source)} chars of code (not stub)",
                    "preview": next_code_source[:150],
                    "fix": "Relabel header to 'Exemple guide' or replace code with stub",
                })

    return findings


def discover_notebooks(root: str) -> list[str]:
    """Find all .ipynb files under root, excluding _output, .ipynb_checkpoints, and nested git worktrees.

    Nested git worktrees have a `.git` *file* (not directory) pointing to <parent>/.git/worktrees/<name>.
    Descending into them would double-count all notebooks (e.g. orphan worktree `feat/c741-grothendieck-readme`
    inside MyIA.AI.Notebooks/, which shares the same .git dir as the main repo).
    """
    notebooks = []
    for dirpath, dirnames, filenames in os.walk(root):
        # Skip dirs whose `.git` entry is a FILE (git worktree pointer) — descend-bait.
        # Plain `.git` directory is already excluded by the dirnames filter below.
        if '.git' in filenames and not os.path.isdir(os.path.join(dirpath, '.git')):
            dirnames[:] = []
            continue
        dirnames[:] = [d for d in dirnames if d not in ('.ipynb_checkpoints', '_output', '.git', '__pycache__', 'node_modules')]
        for f in filenames:
            if f.endswith('.ipynb') and not f.endswith('_output.ipynb'):
                notebooks.append(os.path.join(dirpath, f))
    return sorted(notebooks)


def main():
    parser = argparse.ArgumentParser(description="Detect solution leaks in notebooks")
    parser.add_argument("--scan", help="Scan a specific notebook or directory")
    parser.add_argument("--scan-all", action="store_true", help="Scan all notebooks in repo")
    parser.add_argument("--check", action="store_true", help="Exit 1 if any HIGH findings")
    parser.add_argument("--verbose", action="store_true", help="Show all findings including LOW")
    args = parser.parse_args()

    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    nb_root = os.path.join(repo_root, "MyIA.AI.Notebooks")

    if args.scan_all:
        notebooks = discover_notebooks(nb_root)
    elif args.scan:
        target = args.scan
        if os.path.isdir(target):
            notebooks = discover_notebooks(target)
        elif os.path.isfile(target):
            notebooks = [target]
        else:
            candidates = discover_notebooks(nb_root)
            notebooks = [n for n in candidates if target.lower() in n.lower()]
            if not notebooks:
                print(f"No notebooks matching '{target}'")
                return 1
    else:
        parser.print_help()
        return 1

    print(f"Scanning {len(notebooks)} notebooks...")

    all_findings = []
    for nb_path in notebooks:
        findings = scan_notebook(nb_path)
        all_findings.extend(findings)

    high = [f for f in all_findings if f.get('severity') == 'HIGH']
    medium = [f for f in all_findings if f.get('severity') == 'MEDIUM']
    errors = [f for f in all_findings if f.get('severity') == 'ERROR']

    print(f"\nResults: {len(high)} HIGH (leaks), {len(medium)} MEDIUM (duplicates), {len(errors)} errors")
    print(f"Scanned: {len(notebooks)} notebooks\n")

    if high:
        print("=== HIGH SEVERITY (Solution Leaks) ===")
        for f in high:
            rel = os.path.relpath(f['path'], repo_root)
            print(f"  [{f['severity']}] {rel}:cell {f['cell_index']} — {f['message']}")
            if args.verbose and 'preview' in f:
                print(f"    Preview: {f['preview'][:120]}...")
            if 'fix' in f:
                print(f"    Fix: {f['fix']}")
        print()

    if medium:
        print("=== MEDIUM SEVERITY (Duplicate Numbers) ===")
        for f in medium:
            rel = os.path.relpath(f['path'], repo_root)
            print(f"  [{f['severity']}] {rel}:cell {f['cell_index']} — {f['message']}")
        print()

    if errors:
        print("=== ERRORS ===")
        for f in errors:
            print(f"  {f['path']}: {f['message']}")
        print()

    if args.check and high:
        return 1

    return 0


if __name__ == '__main__':
    sys.exit(main())
