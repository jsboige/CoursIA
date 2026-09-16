"""Advisory ratchet: a diff must not silently collapse the SOURCE volume of a
notebook cell -- the source-side counterpart of check_output_collapse.py.

Issue #15901 (opened by ai-01 2026-09-13, before any merge of #15862).

Founding case, measured firsthand on
``MyIA.AI.Notebooks/GameTheory/GameTheory-06e-Open-Source-Game-Theory.ipynb``
(merge-base ``244c7c54f032`` -> head ``7a355873de32``): 7 -> 7 code cells, and
the cell ``c989_independent_v2`` loses 8425 -> 5309 characters of SOURCE
(-37.0 %, an absolute loss of 3116). What disappears: the declarative table
``EXPECTED_TABLE_V2`` (25 hand-encoded entries) and an ENTIRE external
verifier call -- replaced by a loop that re-derives the table. Source
identical nowhere else in the notebook: the material is simply gone.

The PR that did this turned EVERY notebook ratchet green --
``Output-collapse ratchet``, ``Papermill ratchet``, ``Exec-sequence ratchet``,
``Source-output ratchet`` and ``H.4 outputs-required`` -- because all five
measure OUTPUTS, execution sequences or structure. None measured the source.
The reason is structural, not accidental: what was deleted is a declarative
data table and an ``assert`` that is SILENT when it succeeds. Removing a good
guard does not shrink the output -- that is the definition of a good guard --
so an output-side instrument is blind to it BY CONSTRUCTION.

Design constraint taken from the founding case (it rules out the obvious
threshold): ``c989_independent_v2`` contracts by a factor of only 1.59. A
"loses an order of magnitude" rule -- the one its output-side sibling uses --
would NOT fire on the incident that motivated this organ, and an instrument
that stays silent on its own founding case is not delivered. The discriminant
is therefore an ABSOLUTE loss over a floor, with a modest ratio, not a large
factor:

  MAGNITUDE  a cell whose base source is substantial (>= BASE_FLOOR), whose
             head source is strictly smaller, and which loses at least
             LOSS_FLOOR characters AND at least LOSS_FRACTION of its base
             source. Founding case: 3116 chars and 37.0 % -- both clear.
             Two mechanically detectable legitimate causes are exempted:

               - MOVED CONTENT: the removed text reappears in the head source
                 of ANOTHER cell of the SAME notebook (the issue's
                 "intersection des textes supprimes avec les textes ajoutes
                 ailleurs dans le meme notebook"). Char-weighted, and only
                 substantial lines count as evidence so that a purge of
                 punctuation or blank lines cannot manufacture the exemption.
               - DIAGNOSTIC PURGE: this fraction of the REMOVED characters
                 sits on diagnostic-shaped lines (CS####/warning family) --
                 commented-out warnings and debug scaffolding that a
                 legitimate PR sweeps. Same contract and same constant as the
                 output-side sibling.

A SECOND, narrower detector -- the disappearance of a guard FORM (``assert``,
``subprocess.run`` followed by a returncode test, declarative reference
table) -- is described by the issue as "plus precis sur ce cas, mais
heuristique -- je ne le propose pas en premier". It is deliberately NOT
implemented here: heuristic, and it needs its own arbitration.

A THIRD mechanism, same family, is the SOURCE-side counterpart taken by the
other end (issue #16110): the source SURVIVES in volume and loses its
STRUCTURE. Founding case, measured firsthand on PR #16097 (head
``1209b5357``, cell ``40cb37d5`` of ``Lean-18-Sendov-Complex-Analysis.ipynb``,
base ``origin/main``): every newline of the cell was stripped at write time,
so the 44 source items joined into ONE line whose first character is ``#`` --
the whole code becomes a comment. The cell kept its 312-character stream
output. Measured, base -> head:

                     items   chars   ast.parse(source).body
    origin/main        44     1132            10
    1209b5357          12     1728             0

Two instruments were blind BY CONSTRUCTION, and neither is a defect in them:

  - VOLUME cannot fire: the head is LONGER (1728 > 1132), because the same
    write that stripped the newlines also APPENDED a 639-character recovery
    note. The magnitude gate (``h_chars >= b_chars``) stops before any floor
    is even compared -- verified: ``analyze()`` reports zero findings there.
  - SYNTAX cannot fire: a cell folded entirely into a comment PARSES
    perfectly. This is why the BLOCKING ``notebook-cell-source-parses``
    guard (#13326) stayed green on a cell whose code is gone -- syntax
    validity is the wrong instrument, and the issue says so itself.

The discriminant is therefore the STATEMENT COUNT, and the two criteria kept
are the ones that survive measurement (see "criterion 1" below):

  EMPTIED       a matched cell whose source parsed to > 0 statements on the
                base and parses to 0 on the head. Content-based, so it does
                not care HOW the newlines disappeared.
  ORPHAN OUTPUT the head cell carries non-empty ``outputs`` while its source
                yields 0 statements -- a result no statement can have
                produced. Base-free by design: it needs neither the baseline
                nor a diff, only the cell (the issue's third criterion).

Criterion 1 of the issue ("the number of source items without a trailing
newline, last excluded, INCREASES") is REFUTED BY MEASUREMENT and is NOT
implemented. That count is a property of the SERIALIZATION GRANULARITY, not
of correctness: ``GenAI/Texte/21_LoRA_FineTuning.ipynb`` cell ``69b296cb``
on ``main`` is serialized CHARACTER BY CHARACTER (``['#', ' ', 'P', ...]``,
820 items), reports 802 unterminated items, and is perfectly healthy --
``ast.parse`` yields 10 statements and its output is real. Repo-wide
histogram over the 11 970 code cells of the 953 Python notebooks of ``main``:
``{0: 11970, 1: 1, 802: 1}``. A detector whose firing depends on which tool
serialized the cell would flag legitimate re-serializations, so the signal is
dropped rather than shipped with a threshold -- and the fold cases it was
meant to catch are already covered twice: a fold whose first line is CODE
loses its syntax and is caught by the BLOCKING sibling above; a fold whose
first line is a comment is caught here by EMPTIED.

Two measured traps shape the ORPHAN OUTPUT predicate, both found by sweeping
``main`` before writing it:

  - MAGICS. The first sweep, without a magic guard, flagged 6 cells -- all of
    them ``# comment`` + ``!python ...`` / ``%pip install ...``. Those outputs
    HAVE a producer (the magic), and ``ast`` sees none because
    ``_strip_ipython_magics`` removes the line. The predicate therefore
    requires NO magic in the cell (same logical-line rule as the stripper).
    With that guard, the sweep over ``main`` returns ZERO cells, i.e. the
    criterion has no pre-existing instance to be conservative about.
  - PAST. A finding that only a PR can CREATE never settles the past: the
    predicate needs a cell that asserts an output with no producer, and
    ``main`` holds none. It is therefore deliberately NOT scoped to cells the
    PR edited -- where the claim is intra-cell, the baseline adds nothing.

The MAGNITUDE exemptions (moved content, diagnostic purge) arbitrate the
comparative signals -- they mean "no collapse happened here", which is a
statement about the base-to-head relation. They deliberately do NOT arbitrate
ORPHAN OUTPUT, whose claim is intra-cell and true whatever happened to the
code: content moved to another cell still leaves a stale output above an
emptied cell. On the founding case both exemption fractions measure 0.00, so
they would have suppressed nothing.

Cells are matched BASE -> HEAD by nbformat cell ``id`` when both sides carry
one, falling back to positional index (same contract as the output-side
siblings). A cell DELETED by the PR has no head counterpart and produces no
finding (deleting code cells is legitimate, and the surviving cells already
report the loss); a notebook ADDED by the branch has no baseline and is never
judged -- the structural criteria honour that boundary too, since a wholly new
notebook is read as new content while an added CELL among existing ones is
what slips through unnoticed. An added CELL inside a JUDGED notebook has no
baseline either, so EMPTIED cannot speak about it -- but ORPHAN OUTPUT can,
since it consults only the head cell.

Placement: ADVISORY (``blocking=False`` in the fast lane). The verdict is
published under a neutral conclusion -- it never gates. The judgment stays
with the reviewer; the organ makes the loss VISIBLE. The threshold is
deliberately conservative in the direction that favours reporting: a false
advisory costs a line of review, a silent source collapse cost 3116
characters and a verifier that nothing else watched.

Usage:
    python check_source_collapse.py <base-ref> [--json]
    python check_source_collapse.py --self-test

Base ref is resolved to merge-base(base-ref, HEAD), same as the siblings.

Exit 1 iff at least one changed notebook carries a non-exempt finding. With
``--json`` the full row structure (including exempted findings and their
reasons) is emitted for calibration.
"""

import argparse
import ast
import json
import re
import sys
import unicodedata
from collections import Counter

# Reuse the siblings' git plumbing so the ratchets share one implementation of
# "what changed between the merge base and HEAD".
from check_output_failure_text import (
    _cell_source,
    changed_notebooks,
    read_notebook_at,
    resolve_base,
)
from check_output_flood import _cell_key

# The structural criteria share the magic semantics of the BLOCKING sibling
# (#13326) instead of re-deriving them: `_scan_line` is the state machine that
# decides what a magic line is (logical-line start only), and reusing it is
# what keeps the two organs from disagreeing about the same cell.
from check_cell_source_parses import (
    _is_python_kernel,
    _scan_line,
    _strip_ipython_magics,
)

# A base source below this many chars is noise (a stub, a two-line cell):
# never judged. The founding case's guilty cell sits at 8425 chars.
BASE_FLOOR = 500

# Absolute loss floor: the founding case removed 3116 characters. Below this
# the contraction is ordinary refactoring churn, whatever its ratio.
LOSS_FLOOR = 1000

# Ratio floor: the founding case lost 37.0 % of the cell. Set well under it so
# the incident clears it with margin, and well over benign churn (a 10 %
# rewrite of a cell is not a collapse).
LOSS_FRACTION = 0.25

# Moved-content exemption: this fraction of the REMOVED characters must be
# found again in the head source of ANOTHER cell of the same notebook.
MOVED_FRACTION = 0.8

# A removed line shorter than this (after stripping) is not evidence of a
# move: punctuation and blank lines reappear everywhere. Counting them would
# manufacture the exemption, so they are excluded from the numerator only --
# the denominator stays the full removed volume, which biases the organ
# towards REPORTING, never towards silence.
MIN_MOVED_LINE_CHARS = 4

# Diagnostic-purge exemption: same constant and same contract as the
# output-side sibling (Sudoku-06 #15144 purged 21 CS8632 warnings).
DIAGNOSTIC_LINE_FRACTION = 0.8

# Diagnostic-shaped lines (removed-text classification). CS#### is the C#
# compiler; the warning family covers Python and both spellings of the French
# "warning : CS####".
DIAGNOSTIC_RE = re.compile(
    r"\bCS\d{4}\b"
    r"|warning"
    r"|deprecationwarning"
    r"|futurewarning"
    r"|userwarning"
    r"|runtimewarning"
    r"|pendingdeprecationwarning"
)

# Founding case (#15901 / #15862), replayed by --self-test. The head is the
# PR commit; the base is the merge base the issue names.
SELF_TEST_BASE = "244c7c54f032"
SELF_TEST_HEAD = "7a355873de32"
SELF_TEST_NOTEBOOK = (
    "MyIA.AI.Notebooks/GameTheory/GameTheory-06e-Open-Source-Game-Theory.ipynb")
SELF_TEST_CELL = "c989_independent_v2"

# Structural founding case (#16110), replayed the same way. The head is the
# live head of PR #16097, which is still OPEN: once that branch is squashed
# away the commit becomes unreachable and the replay degrades to the SKIP the
# sibling already prints -- the synthetic controls below are what stays
# durable, this one is the real-world witness.
SELF_TEST_16110_BASE = "7cc2fb2d203f"  # merge-base(main, #16097)
SELF_TEST_16110_HEAD = "1209b5357"
SELF_TEST_16110_NOTEBOOK = (
    "MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-18-Sendov-Complex-Analysis.ipynb")
SELF_TEST_16110_CELL = "40cb37d5"


def _normalize(text):
    """Lowercase, accents stripped: motif matching is accent-blind."""
    decomposed = unicodedata.normalize("NFD", text)
    stripped = "".join(c for c in decomposed
                       if unicodedata.category(c) != "Mn")
    return stripped.lower()


def _cell_chars(cell):
    """Source volume of one code cell, in characters."""
    return len(_cell_source(cell))


def _code_cells(nb):
    """{(id-or-positional-key): cell} for every code cell."""
    if not nb:
        return {}
    out = {}
    for i, c in enumerate(nb.get("cells", []) or []):
        if c.get("cell_type") != "code":
            continue
        out[_cell_key(c, i)] = c
    return out


def _removed_lines(base_text, head_text):
    """Multiset of lines the diff removed from one cell (duplicates count)."""
    return Counter(base_text.splitlines()) - Counter(head_text.splitlines())


def _has_ipython_magic(src):
    """True iff the source carries a `!`/`%` line at a LOGICAL line start.

    Mirrors `_strip_ipython_magics` exactly (same state machine, same rule:
    a magic can only open a logical line, never continue one), because this
    predicate exists to know whether stripping REMOVED executable content --
    and a stripper that dropped a line is the only witness of that.
    """
    depth, in_triple = 0, None
    for line in src.splitlines():
        if depth == 0 and in_triple is None:
            stripped = line.lstrip()
            if stripped.startswith("!") or stripped.startswith("%"):
                return True
        depth, in_triple = _scan_line(line, depth, in_triple)
    return False


def _python_statements(src):
    """Statement count of a cell's Python, or None when not measurable.

    None means "no verdict possible", never "zero statements" -- the
    distinction is the whole predicate:

      - the magic-stripped source holds nothing (a magic-only cell, an empty
        cell): there is no Python to count, so nothing is claimed;
      - the source does not parse: the BLOCKING ``notebook-cell-source-parses``
        guard (#13326) owns that case, and a heuristic count here would only
        duplicate it worse.

    A fully commented cell -- the founding case -- parses fine and yields 0,
    which is exactly the reading that no other instrument produces.
    """
    stripped = _strip_ipython_magics(src)
    if not stripped.strip():
        return None
    try:
        return len(ast.parse(stripped).body)
    except (SyntaxError, ValueError):
        return None


def _diagnostic_fraction(removed):
    """Char-weighted fraction of the REMOVED lines that is diagnostic-shaped.

    Weighted by CHARS, not lines: the ratchet guards source VOLUME, so a
    purge that also swallows a large real statement must not ride along a
    handful of short warnings.
    """
    total = sum(len(line) * n for line, n in removed.items())
    if total == 0:
        return 0.0
    diag = sum(len(line) * n for line, n in removed.items()
               if DIAGNOSTIC_RE.search(_normalize(line)))
    return diag / total


def _moved_fraction(removed, other_head_text):
    """Char-weighted fraction of the REMOVED lines found again elsewhere.

    ``other_head_text`` is the concatenated head source of every OTHER code
    cell of the same notebook. Only substantial lines (>= MIN_MOVED_LINE_CHARS
    after stripping) count as evidence of a move; the denominator is the full
    removed volume, so the exemption is hard to obtain by accident.
    """
    total = sum(len(line) * n for line, n in removed.items())
    if total == 0:
        return 0.0
    moved = sum(len(line) * n for line, n in removed.items()
                if len(line.strip()) >= MIN_MOVED_LINE_CHARS
                and line in other_head_text)
    return moved / total


def _format_delta(finding):
    """Signed character delta of one finding, or `no baseline` when there is
    none.

    Signed on purpose: a STRUCTURE finding can GROW -- the founding case gains
    596 characters, because the same write that stripped the newlines also
    appended a recovery note -- and printing that as a negative loss would
    hide exactly why the volume signal stayed silent.
    """
    if finding.get("loss") is None:
        return "no baseline"
    pct = ("n/a" if finding.get("ratio") is None
           else str(int(finding["ratio"] * 100)) + "%")
    return "%+d chars, %s" % (finding["loss"], pct)


def analyze(base_nb, head_nb):
    """Pure per-notebook source-collapse analysis on two parsed notebooks.

    ``base_nb`` is None for a notebook ADDED by the branch (never judged).
    Returns one row dict; every finding carries its own exemption verdict.
    """
    added = base_nb is None
    b_cells, h_cells = _code_cells(base_nb), _code_cells(head_nb)

    b_total = sum(_cell_chars(c) for c in b_cells.values())
    h_total = sum(_cell_chars(c) for c in h_cells.values())

    findings = []
    python = _is_python_kernel(head_nb.get("metadata") or {})
    for key, h_cell in h_cells.items():
        b_cell = b_cells.get(key)
        b_chars = _cell_chars(b_cell) if b_cell is not None else 0
        h_chars = _cell_chars(h_cell)
        h_src = _cell_source(h_cell)

        # VOLUME signal (#15901): a substantial base cell that contracted past
        # both floors. Blind to a fold, which is why #16110 exists.
        volume = None
        if b_cell is not None and b_chars >= BASE_FLOOR and h_chars < b_chars:
            loss = b_chars - h_chars
            if loss >= LOSS_FLOOR and (loss / b_chars) >= LOSS_FRACTION:
                volume = loss

        # STRUCTURE signals (#16110), Python kernels only: what is counted is
        # the statement, and only Python has one. A .NET cell lands on None
        # (no parse), which is already a no-verdict.
        b_body = h_body = None
        structural = []
        if python and not added:
            h_body = _python_statements(h_src)
            if b_cell is not None:
                b_body = _python_statements(_cell_source(b_cell))
            # A magic line is executable content whose output the cell MAY
            # have produced: `_python_statements` cannot see it (the stripper
            # removed it), so the cell is not orphan. Measured necessity --
            # without this guard the sweep flags 6 healthy cells of `main`,
            # all `# comment` + `!python ...`.
            no_magic = not _has_ipython_magic(h_src)
            if (h_cell.get("outputs") or []) and h_body == 0 and no_magic:
                structural.append("orphan-output")
            if b_body is not None and b_body > 0 and h_body == 0 and no_magic:
                structural.append("emptied")

        signals = (["magnitude"] if volume is not None else []) + structural
        if not signals:
            continue

        b_src = _cell_source(b_cell) if b_cell is not None else ""
        removed = (_removed_lines(b_src, h_src) if b_cell is not None
                   else Counter())
        other_head = "".join(_cell_source(c) for k, c in h_cells.items()
                             if k != key)
        diag_frac = _diagnostic_fraction(removed)
        moved_frac = _moved_fraction(removed, other_head)
        exempt = None
        if diag_frac >= DIAGNOSTIC_LINE_FRACTION:
            exempt = "exempt-diagnostic"
        elif moved_frac >= MOVED_FRACTION:
            exempt = "exempt-moved"

        # An exemption says "no collapse happened here", i.e. it speaks about
        # the base->head RELATION: it therefore arbitrates only the
        # comparative signals. `orphan-output` claims something about the head
        # CELL alone (an asserted result no statement can produce) and is true
        # whatever happened to the code, so it is never suppressed.
        if exempt:
            signals = [s for s in signals if s == "orphan-output"]

        finding = {
            "cell": key, "base": b_chars, "head": h_chars,
            "loss": b_chars - h_chars if b_cell is not None else None,
            "ratio": (round((b_chars - h_chars) / b_chars, 3)
                      if b_cell is not None and b_chars else None),
            "diagnostic_fraction": round(diag_frac, 2),
            "moved_fraction": round(moved_frac, 2),
            "signals": signals,
            "base_body": b_body, "head_body": h_body,
        }
        finding["kind"] = exempt if not signals else (
            "structure" if any(s in ("emptied", "orphan-output")
                               for s in signals) else "magnitude")
        findings.append(finding)

    regressed = (not added) and any(
        not f["kind"].startswith("exempt-") for f in findings)
    return {
        "added": added,
        "base_total": b_total,
        "head_total": h_total,
        "cells": findings,
        "regressed": regressed,
    }


def compare(base_ref, head_ref, paths, cwd=None):
    """Per-notebook source collapse between two refs.

    ``head_ref`` is None for the working tree (same contract as the siblings).
    """
    rows = []
    for path in paths:
        base_nb = read_notebook_at(base_ref, path, cwd=cwd)
        head_nb = read_notebook_at(head_ref, path, cwd=cwd)
        if head_nb is None:
            continue
        row = analyze(base_nb, head_nb)
        row["notebook"] = path
        rows.append(row)
    return rows


def self_test(cwd=None):
    """Positive and negative control, then the founding-case replay.

    A detector that cannot be shown to fire is indistinguishable from one
    that is unplugged -- the same contract that keeps the siblings honest.
    """
    failures = []

    def _nb(cells):
        """Build a synthetic notebook from [(id, source[, outputs])].

        The metadata names a Python kernel: the structural criteria are
        Python-only (the statement is a Python notion), so a fixture without
        a kernel would silently exercise the volume half alone.
        """
        out = []
        for item in cells:
            cell = {"cell_type": "code", "id": item[0], "source": item[1]}
            if len(item) > 2:
                cell["outputs"] = item[2]
            out.append(cell)
        return {"cells": out,
                "metadata": {"kernelspec": {"name": "python3",
                                            "language": "python"}}}

    def _analyze(base_cells, head_cells, added=False):
        return analyze(None if added else _nb(base_cells), _nb(head_cells))

    big = "\n".join("ligne_de_code_%d = %d" % (i, i) for i in range(400))
    if len(big) < 8000:
        failures.append("fixture too small (%d chars): controls vacuous"
                        % len(big))

    # 1. magnitude fires: substantial base, an order-of-magnitude-free but
    #    large absolute loss with a real ratio (mirrors the founding case).
    r = _analyze([("a", big)], [("a", big[:5000])])
    if not (r["cells"] and r["cells"][0]["kind"] == "magnitude"):
        failures.append("magnitude (8000 -> 5000) not flagged")
    # 2. benign churn stays silent: the loss clears the absolute floor but
    #    not the ratio floor, so this control pins the RATIO rule (fixture
    #    sized to sit clear of the boundary, not on it).
    r = _analyze([("a", big)], [("a", big[:7600])])
    if r["cells"]:
        failures.append("benign churn (9379 -> 7600) flagged")
    # 3. a small absolute loss stays silent even at a large ratio
    small = "\n".join("x_%d = %d" % (i, i) for i in range(60))
    r = _analyze([("a", small)], [("a", small[:300])])
    if r["cells"]:
        failures.append("sub-floor loss (%d -> 300) flagged" % len(small))
    # 4. a sub-floor base stays silent even if it collapses entirely
    r = _analyze([("a", small[:400])], [("a", "")])
    if r["cells"]:
        failures.append("sub-floor base (400 -> 0) flagged")
    # 5. growth stays silent
    if _analyze([("a", big)], [("a", big + big)])["cells"]:
        failures.append("growth flagged")
    # 6. deleted cell loses volume legitimately: no head key, no finding
    if _analyze([("a", big), ("b", big)], [("a", big)])["cells"]:
        failures.append("deleted cell produced a finding")
    # 7. added notebook is never judged
    if _analyze([], [("a", big)], added=True)["regressed"]:
        failures.append("added notebook judged instead of skipped")
    # 8. index-shift is not misattributed
    if any(f["cell"] == "a" for f in
           _analyze([("a", big)], [("zz", "short"), ("a", big)])["cells"]):
        failures.append("unchanged cell flagged after benign insert")
    # 9. moved content is exempt: the removed block reappears in cell "b"
    moved_block = "\n".join("bloc_deplace_%d = %d" % (i, i)
                            for i in range(120))
    base_head = moved_block + "\n" + big[:2000]
    r = _analyze([("a", base_head), ("b", "court = 1")],
                 [("a", big[:2000]), ("b", moved_block + "\ncourt = 1")])
    if not (r["cells"] and r["cells"][0]["kind"] == "exempt-moved"):
        failures.append("moved content not exempted")
    if r["regressed"]:
        failures.append("moved content exempted but still regressed")
    # 10. diagnostic purge is exempt: base is mostly commented warnings
    warnings = "\n".join(
        "# warning CS8632: reference nullable requise %d" % i
        for i in range(60))
    r = _analyze([("a", warnings + "\n" + big[:1500])],
                 [("a", big[:1500])])
    if not (r["cells"] and r["cells"][0]["kind"] == "exempt-diagnostic"):
        failures.append("diagnostic purge not exempted")
    if r["regressed"]:
        failures.append("diagnostic purge exempted but still regressed")
    # 11. a purge that ALSO swallows real code is not exempt
    mixed = warnings + "\n" + big[:2500]
    r = _analyze([("a", mixed)], [("a", big[:300])])
    if not (r["cells"] and r["cells"][0]["kind"] == "magnitude"):
        failures.append("purge swallowing real code exempted (should flag)")

    # 12. STRUCTURE fires where volume cannot: the head is LONGER than the
    #     base (the fold is followed by a note), so the magnitude gate stops
    #     before any floor -- exactly the #16110 incident. EMPTIED and
    #     ORPHAN-OUTPUT both fire on the same cell.
    out_stream = [{"output_type": "stream", "name": "stdout",
                   "text": "@Sendov.sendov : axioms [propext, ...]"}]
    folded = "# " + big.replace("\n", "")
    r = _analyze([("a", big)], [("a", folded, out_stream)])
    kinds = [f["kind"] for f in r["cells"]]
    if kinds != ["structure"]:
        failures.append("folded cell not flagged as structure (%r)" % kinds)
    else:
        sig = r["cells"][0]["signals"]
        if "emptied" not in sig or "orphan-output" not in sig:
            failures.append("folded cell signals incomplete (%r)" % sig)
        if r["cells"][0]["loss"] <= 0:
            failures.append("fixture must GROW to mirror the incident")
    if not r["regressed"]:
        failures.append("structural finding did not regress")

    # 13. a magic line IS a producer: `# comment` + `!python ...` keeps its
    #     output legitimately, and `ast` sees 0 statements because the
    #     stripper removed the line. Measured necessity: without this guard
    #     the sweep of `main` flags 6 healthy cells, all of this shape. (The
    #     cell also SHRINKS, so the volume signal fires and may fire -- this
    #     control pins the STRUCTURAL half alone.)
    r = _analyze([("a", big)],
                 [("a", "# Telecharger\n!python x.py --symbols SPY",
                   out_stream)])
    if any(f["kind"] == "structure" or "orphan-output" in f["signals"]
           or "emptied" in f["signals"] for f in r["cells"]):
        failures.append("magic cell reached a structural signal (%r)"
                        % [f["signals"] for f in r["cells"]])
    # 14. same, untouched: a magic-only cell carries no structure claim
    magic = "# Installer\n%pip install -q rdflib"
    if _analyze([("a", magic)], [("a", magic, out_stream)])["cells"]:
        failures.append("unchanged magic cell flagged")

    # 15. criterion 1 of #16110 REFUTED: an unterminated-item count is a
    #     serialization granularity, not a defect. A cell whose source is
    #     split CHARACTER BY CHARACTER (as `21_LoRA_FineTuning.ipynb` cell
    #     `69b296cb` is on `main`) reports one unterminated item per
    #     character, parses to a full module, and must stay silent.
    perchar = list(big)
    unterminated = sum(1 for x in perchar[:-1] if not x.endswith("\n"))
    if unterminated < 800:
        failures.append("per-char fixture too small to be a witness")
    if _analyze([("a", perchar)], [("a", perchar)])["cells"]:
        failures.append("per-char serialization flagged (%d unterminated)"
                        % unterminated)

    # 16. the moved exemption does NOT silence ORPHAN-OUTPUT: the block
    #     reappears in cell "b", so EMPTIED is exempted, but cell "a" still
    #     asserts a result no statement of its own can produce.
    r = _analyze(
        [("a", moved_block), ("b", "court = 1")],
        [("a", "# " + moved_block.replace("\n", ""), out_stream),
         ("b", moved_block)])
    if not (r["cells"] and r["cells"][0]["kind"] == "structure"):
        failures.append("orphan output silenced by the moved exemption")
    elif r["cells"][0]["signals"] != ["orphan-output"]:
        failures.append("emptied survived the moved exemption (%r)"
                        % r["cells"][0]["signals"])

    # 17. an added notebook is still never judged, structural criteria
    #     included: the boundary is the notebook, not the signal.
    if _analyze([], [("a", "# rien\n", out_stream)], added=True)["cells"]:
        failures.append("added notebook judged by the structural pass")

    # Replay the founding case (#15901 / #15862): the organ MUST fire on the
    # cell that motivated it.
    from check_output_failure_text import git
    if (git("cat-file", "-e", SELF_TEST_HEAD, cwd=cwd) is None
            or git("cat-file", "-e", SELF_TEST_BASE, cwd=cwd) is None):
        print("SKIP replay: founding-case commits not in this clone")
    else:
        rrows = compare(SELF_TEST_BASE, SELF_TEST_HEAD,
                        [SELF_TEST_NOTEBOOK], cwd=cwd)
        r0 = rrows[0] if rrows else {}
        hits = [f for f in r0.get("cells", []) if f["cell"] == SELF_TEST_CELL]
        print("replay " + SELF_TEST_HEAD[:12] + " on "
              + SELF_TEST_NOTEBOOK.split("/")[-1] + ": total "
              + str(r0.get("base_total")) + " -> " + str(r0.get("head_total"))
              + ", findings " + str([(f["cell"], f["kind"], f["base"],
                                      f["head"], f["ratio"])
                                     for f in r0.get("cells", [])]))
        if not hits:
            failures.append("founding case: cell " + SELF_TEST_CELL
                            + " not flagged")
        elif hits[0]["kind"] != "magnitude":
            failures.append("founding case: cell " + SELF_TEST_CELL
                            + " exempted as " + hits[0]["kind"])

    # Replay the STRUCTURAL founding case (#16110): the volume gate must stay
    # silent on it AND the structural pass must fire -- a replay that only
    # checked the latter would not show that the two mechanisms are disjoint.
    from check_output_failure_text import git as _git
    if (_git("cat-file", "-e", SELF_TEST_16110_HEAD, cwd=cwd) is None
            or _git("cat-file", "-e", SELF_TEST_16110_BASE, cwd=cwd) is None):
        print("SKIP replay #16110: founding commits not in this clone")
    else:
        srows = compare(SELF_TEST_16110_BASE, SELF_TEST_16110_HEAD,
                        [SELF_TEST_16110_NOTEBOOK], cwd=cwd)
        s0 = srows[0] if srows else {}
        shits = [f for f in s0.get("cells", [])
                 if f["cell"] == SELF_TEST_16110_CELL]
        print("replay #16110 " + SELF_TEST_16110_HEAD[:12]
              + ": findings " + str([(f["cell"], f["kind"], f["signals"],
                                      f["base_body"], f["head_body"],
                                      f["loss"]) for f in s0.get("cells", [])]))
        if not shits:
            failures.append("#16110: cell " + SELF_TEST_16110_CELL
                            + " not flagged")
        else:
            f0 = shits[0]
            if f0["kind"] != "structure":
                failures.append("#16110: kind " + str(f0["kind"])
                                + " (expected structure)")
            if f0["base_body"] != 10 or f0["head_body"] != 0:
                failures.append("#16110: statements %r -> %r (expected 10 -> 0)"
                                % (f0["base_body"], f0["head_body"]))
            if "emptied" not in f0["signals"]:
                failures.append("#16110: emptied missing from signals")
            if "orphan-output" not in f0["signals"]:
                failures.append("#16110: orphan-output missing from signals")
            if f0["loss"] >= 0:
                failures.append("#16110: expected GROWTH (negative loss),"
                                " measured %r" % f0["loss"])

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: witnesses fired, benign churn silent, exemptions "
          "hold, both founding cases fire (volume #15901, structure #16110)")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Advisory ratchet: no silent collapse of notebook SOURCE"
                    " volume between the merge base and HEAD (mirror of"
                    " check_output_collapse.py, source side).")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--self-test", action="store_true",
                    help="Positive + negative control, then replay the"
                         " founding case (#15901 / #15862)")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if not args.base:
        ap.error("base ref required (or --self-test)")

    base = resolve_base(args.base)
    paths = changed_notebooks(base)
    rows = compare(base, None, paths)
    bad = [r for r in rows if r["regressed"]]

    if args.as_json:
        print(json.dumps({"base_ref": args.base, "merge_base": base,
                          "changed": len(paths), "flagged": len(bad),
                          "rows": rows}, indent=2, ensure_ascii=False))
    else:
        print("base " + str(args.base) + " -> merge-base " + base[:12]
              + " | " + str(len(paths)) + " changed notebooks | "
              + str(len(bad)) + " flagged (advisory)")
        for r in rows:
            for f in r["cells"]:
                if f["kind"].startswith("exempt-"):
                    print("  EXEMPT (" + f["kind"][7:] + ") "
                          + r["notebook"] + " cell " + str(f["cell"]) + " "
                          + str(f["base"]) + " -> " + str(f["head"])
                          + " " + _format_delta(f)
                          + " signals=" + ",".join(f["signals"]))
        for r in bad:
            print("\nFLAGGED (advisory) " + r["notebook"] + "  total "
                  + str(r["base_total"]) + " -> " + str(r["head_total"]))
            for f in r["cells"]:
                if f["kind"] == "magnitude":
                    print("  MAGNITUDE: cell " + str(f["cell"]) + " "
                          + str(f["base"]) + " -> " + str(f["head"])
                          + " " + _format_delta(f))
                elif f["kind"] == "structure":
                    print("  STRUCTURE: cell " + str(f["cell"]) + " signals "
                          + ",".join(f["signals"]) + " -- statements "
                          + str(f["base_body"]) + " -> " + str(f["head_body"])
                          + ", " + str(f["base"]) + " -> " + str(f["head"])
                          + " chars (" + _format_delta(f) + ")")
        if bad:
            print("\nAdvisory, not a gate. MAGNITUDE: a cell lost at least "
                  + str(LOSS_FLOOR) + " characters and "
                  + str(int(LOSS_FRACTION * 100)) + "% of its source. If the"
                  " material moved to another cell or was a diagnostic purge"
                  " the organ exempts it mechanically -- otherwise justify"
                  " the removal in the PR body or restore it. Removing a"
                  " declarative reference table or a verifier is exactly what"
                  " the output-side ratchets cannot see (#15901).")
            print("STRUCTURE (#16110) is the other end of the same family: the"
                  " source survives in volume and loses its shape. EMPTIED ="
                  " the cell had statements and has none; ORPHAN-OUTPUT = it"
                  " carries a result no statement can have produced (a cell"
                  " folded into a comment parses clean, so the BLOCKING"
                  " notebook-cell-source-parses guard cannot see it). Either"
                  " way the committed output is no longer backed by code:"
                  " restore the source or drop the output.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
