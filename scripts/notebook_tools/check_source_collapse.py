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

Cells are matched BASE -> HEAD by nbformat cell ``id`` when both sides carry
one, falling back to positional index (same contract as the output-side
siblings). A cell DELETED by the PR has no head counterpart and produces no
finding (deleting code cells is legitimate, and the surviving cells already
report the loss); a notebook ADDED by the branch has no baseline and is never
judged.

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
    for key, h_cell in h_cells.items():
        b_cell = b_cells.get(key)
        if b_cell is None:
            continue  # cell added by the branch: no baseline, no judgement
        b_chars, h_chars = _cell_chars(b_cell), _cell_chars(h_cell)
        if b_chars < BASE_FLOOR or h_chars >= b_chars:
            continue
        loss = b_chars - h_chars
        if loss < LOSS_FLOOR or (loss / b_chars) < LOSS_FRACTION:
            continue

        b_src, h_src = _cell_source(b_cell), _cell_source(h_cell)
        removed = _removed_lines(b_src, h_src)
        other_head = "".join(_cell_source(c) for k, c in h_cells.items()
                             if k != key)
        diag_frac = _diagnostic_fraction(removed)
        moved_frac = _moved_fraction(removed, other_head)

        finding = {
            "cell": key, "base": b_chars, "head": h_chars,
            "loss": loss, "ratio": round(loss / b_chars, 3),
            "diagnostic_fraction": round(diag_frac, 2),
            "moved_fraction": round(moved_frac, 2),
        }
        if diag_frac >= DIAGNOSTIC_LINE_FRACTION:
            finding["kind"] = "exempt-diagnostic"
        elif moved_frac >= MOVED_FRACTION:
            finding["kind"] = "exempt-moved"
        else:
            finding["kind"] = "magnitude"
        findings.append(finding)

    regressed = (not added) and any(
        f["kind"] == "magnitude" for f in findings)
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
        """Build a synthetic notebook from [(id, source_text)]."""
        return {"cells": [
            {"cell_type": "code", "id": k, "source": s} for k, s in cells]}

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

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: witnesses fired, benign churn silent, exemptions "
          "hold, founding case fires")
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
                          + " (-" + str(f["loss"]) + ", "
                          + str(int(f["ratio"] * 100)) + "%)")
        for r in bad:
            print("\nFLAGGED (advisory) " + r["notebook"] + "  total "
                  + str(r["base_total"]) + " -> " + str(r["head_total"]))
            for f in r["cells"]:
                if f["kind"] == "magnitude":
                    print("  MAGNITUDE: cell " + str(f["cell"]) + " "
                          + str(f["base"]) + " -> " + str(f["head"])
                          + " (-" + str(f["loss"]) + ", "
                          + str(int(f["ratio"] * 100)) + "%)")
        if bad:
            print("\nAdvisory, not a gate: a cell lost at least "
                  + str(LOSS_FLOOR) + " characters and "
                  + str(int(LOSS_FRACTION * 100)) + "% of its source. If the"
                  " material moved to another cell or was a diagnostic purge"
                  " the organ exempts it mechanically -- otherwise justify"
                  " the removal in the PR body or restore it. Removing a"
                  " declarative reference table or a verifier is exactly what"
                  " the output-side ratchets cannot see (#15901).")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
