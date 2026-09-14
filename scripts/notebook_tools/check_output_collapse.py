"""Advisory ratchet: a re-execution must not silently collapse a notebook's
OUTPUT VOLUME -- the mirror image of check_output_flood.py.

Issue #15327 / user reserve on #15209 (2026-09-08: « Il n'est pas normal que
ni le CI ni la review l'ait detecte. Gros rouge et investigation necessaire ! »).
Measured firsthand on the reference case (Lean-7b-Examples.ipynb,
6b327a9bf -> 56d98429a): 11 -> 11 code cells, 0 error cells, real
execution_counts everywhere, and output_chars 10637 -> 2985 (-71.9 %). The
graceful-degradation guards (``if api_ok:``) did their job: three cells ran
"successfully" and printed ``Execution sautee (API non configuree)`` instead
of their real output (2195 -> 147, 2568 -> 38, 2074 -> 42 chars).

Every existing surface stayed green on that diff: H.1 (no ``error`` output),
H.3/pre-commit (cells executed with outputs), the failure-text ratchet (a
skip notice is not a failure banner), the output-flood ratchet (asymmetric:
it catches INFLATION, not contraction), markdown-content-loss (it measures
markdown, and the markdown GREW). The repo had a ratchet against output
inflation and none against output collapse. This file closes that hole.

Design constraint (ai-01 measurement on #15327, 2026-09-09): the AGGREGATE
notebook contraction ratio alone is a ~100 % false-positive signal -- over
14 days / 162 commits, every contraction > 50 % (3 of them) was a legitimate
PR (declared lightening, content split into a notebook created in the same
commit, compiler-warning purge), and the one real degradation (#15209) never
crossed a 50 % aggregate threshold that would have separated it from noise
anyway. A useful instrument therefore needs a CAUSE DISCRIMINANT, not a
finer aggregate threshold. Two signals, two mechanical exemptions:

  SIGNATURE  a cell whose base output is substantial and whose head output
             matches a graceful-degradation motif (``execution sautee``,
             ``non configure``, ``mode simulation``, ``skipped``,
             ``not available``) while contracting at all -- catches the
             whole "re-executed without the keys" class, not just #15209.
             Narrow by construction; not subject to the exemptions below
             (a split or a warning purge does not leave skip notices behind).
  MAGNITUDE  a cell whose output loses an ORDER OF MAGNITUDE (factor >= 10
             over a noise floor), subject to the two legitimate causes that
             are mechanically detectable:
               - MOVED CONTENT: a notebook CREATED by the same diff gains a
                 comparable output volume (>= MOVED_GAIN_FRACTION of the
                 loss) -- compare at diff scale, not file scale.
               - DIAGNOSTIC PURGE: the removed text is predominantly
                 diagnostic-shaped (CS#### / warning / DeprecationWarning
                 lines) -- classify the removed lines, not just count them.
             The third legitimate cause (declared lightening) is
             human-side: the advisory label appears and the PR body
             justifies it, same contract as the other ratchets.

Placement (issue point 3): ADVISORY first, blocking later once the threshold
is calibrated on history. Wired as ``blocking=False`` in the fast lane: the
verdict is published under a neutral conclusion, never gate.

Cells are matched BASE -> HEAD by nbformat cell ``id`` when both sides carry
one, falling back to positional index (same contract as the flood sibling).
A cell DELETED by the PR has no head counterpart and produces no finding (a
notebook that deletes code cells loses volume legitimately); a notebook
ADDED by the branch has no baseline and is never judged, though its output
volume counts toward the moved-content exemption of the same diff.

Usage:
    python check_output_collapse.py <base-ref> [--json]
    python check_output_collapse.py --self-test

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

# Reuse the siblings' git plumbing so all three ratchets share one
# implementation of "what changed between the merge base and HEAD".
from check_output_failure_text import (
    EXCLUDE_MARKERS,
    changed_notebooks,
    resolve_base,
    read_notebook_at,
)
from check_output_flood import _cell_key

# A base output below this many chars is noise (a shorter tqdm bar, a
# different seed): never judged. The reference case's guilty cells sit at
# 2074-2568 chars; ai-01's calibration puts the p99 per-cell output object
# count at 1, so 500 chars of text is already a substantial cell.
BASE_FLOOR = 500

# Order-of-magnitude contraction (reference case: factors 14.9 / 67.6 / 49.4).
MAGNITUDE_FACTOR = 10

# The signature signal needs SOME real contraction, not sub-noise jitter, but
# deliberately far below the magnitude factor: the motif itself is the
# discriminator, the ratio only rules out a coincidental substring.
SIGNATURE_FACTOR = 2

# Moved-content exemption: an added notebook's output volume counts against
# the magnitude losses of the same diff from this fraction up ("un volume
# comparable", ai-01 on #14795's split).
MOVED_GAIN_FRACTION = 0.5

# Diagnostic-purge exemption: this fraction of the REMOVED lines must be
# diagnostic-shaped for the cell to be exempt (Sudoku-06 #15144 purged 21
# CS8632 warnings -- the warnings WERE the output).
DIAGNOSTIC_LINE_FRACTION = 0.8

# Graceful-degradation motifs, matched on accent-stripped lowercase text
# (the reference notebook prints "configuree" without its accent; other
# notebooks print "configuré"). List from the issue's design point 2 plus
# the English twins of the observed forms.
DEGRADATION_RE = re.compile(
    r"execution sautee"
    r"|comparaison sautee"
    r"|non configure"
    r"|not configured"
    r"|mode simulation"
    r"|\bskipped\b"
    r"|not available"
)

# Diagnostic-shaped lines (removed-text classification). CS#### is the C#
# compiler; the warning family covers Python (DeprecationWarning and
# friends) and both spellings of the French "warning : CS####".
DIAGNOSTIC_RE = re.compile(
    r"\bCS\d{4}\b"
    r"|warning"
    r"|deprecationwarning"
    r"|futurewarning"
    r"|userwarning"
    r"|runtimewarning"
    r"|pendingdeprecationwarning"
)

# Reference case (#15209), replayed by --self-test. 56d98429a is the
# measured PR head; its parent-side base is the main commit 6b327a9bf.
SELF_TEST_BASE = "6b327a9bf"
SELF_TEST_HEAD = "56d98429a"
SELF_TEST_NOTEBOOK = "MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-7b-Examples.ipynb"
SELF_TEST_MIN_FINDINGS = 3


def _normalize(text):
    """Lowercase, accents stripped: motif matching is accent-blind."""
    decomposed = unicodedata.normalize("NFD", text)
    stripped = "".join(c for c in decomposed
                       if unicodedata.category(c) != "Mn")
    return stripped.lower()


def _text_of(value):
    """nbformat stores output text as str or list[str]; flatten both."""
    if isinstance(value, list):
        return "".join(str(x) for x in value)
    return str(value or "")


def _cell_output_text(cell):
    """Concatenated `text` + `data["text/plain"]` of a cell's outputs.

    This is the exact quantity the issue defines as the output volume.
    """
    parts = []
    for o in cell.get("outputs", []) or []:
        parts.append(_text_of(o.get("text")))
        data = o.get("data") or {}
        parts.append(_text_of(data.get("text/plain")))
    return "".join(parts)


def _cell_chars(cell):
    return len(_cell_output_text(cell))


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


def _diagnostic_fraction(base_text, head_text):
    """Fraction (in chars) of the REMOVED text that is diagnostic-shaped.

    Removed lines are a multiset difference (duplicate warnings count), so a
    purge of 21 identical CS8632 lines is fully accounted. The fraction is
    weighted by CHARS, not lines: the ratchet guards output VOLUME, so a
    purge that also swallows a large real output line must not ride along a
    handful of short warnings.
    """
    removed = Counter(base_text.splitlines()) - Counter(head_text.splitlines())
    total = sum(len(line) * n for line, n in removed.items())
    if total == 0:
        return 0.0
    diag = sum(len(line) * n for line, n in removed.items()
               if DIAGNOSTIC_RE.search(_normalize(line)))
    return diag / total


def analyze(base_nb, head_nb):
    """Pure per-notebook collapse analysis on two parsed notebooks.

    ``base_nb`` is None for a notebook ADDED by the branch (never judged).
    Returns one row dict; the moved-content exemption is applied later, at
    diff scale, by ``compare`` (it needs the other rows of the same diff).
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
        factor = b_chars / max(h_chars, 1)
        h_text = _cell_output_text(h_cell)
        if factor >= SIGNATURE_FACTOR and DEGRADATION_RE.search(
                _normalize(h_text)):
            findings.append({
                "cell": key, "kind": "signature",
                "base": b_chars, "head": h_chars,
                "factor": round(factor, 1),
            })
            continue
        if factor >= MAGNITUDE_FACTOR:
            b_text = _cell_output_text(b_cell)
            diag_frac = _diagnostic_fraction(b_text, h_text)
            if diag_frac >= DIAGNOSTIC_LINE_FRACTION:
                findings.append({
                    "cell": key, "kind": "exempt-diagnostic",
                    "base": b_chars, "head": h_chars,
                    "factor": round(factor, 1),
                    "diagnostic_fraction": round(diag_frac, 2),
                })
            else:
                findings.append({
                    "cell": key, "kind": "magnitude",
                    "base": b_chars, "head": h_chars,
                    "factor": round(factor, 1),
                })

    regressed = (not added) and any(
        f["kind"] in ("signature", "magnitude") for f in findings)
    return {
        "added": added,
        "base_total": b_total,
        "head_total": h_total,
        "cells": findings,
        "regressed": regressed,
    }


def _apply_moved_content(rows):
    """Diff-scale exemption: volume that reappears in an ADDED notebook of
    the same diff is content that moved, not content that vanished."""
    moved_gain = sum(r["head_total"] for r in rows if r["added"])
    magnitude_loss = sum(f["base"] - f["head"] for r in rows
                         for f in r["cells"] if f["kind"] == "magnitude")
    if magnitude_loss <= 0 or moved_gain < MOVED_GAIN_FRACTION * magnitude_loss:
        return rows
    for r in rows:
        for f in r["cells"]:
            if f["kind"] == "magnitude":
                f["kind"] = "exempt-moved"
                f["moved_gain"] = moved_gain
        r["regressed"] = any(f["kind"] == "signature" for f in r["cells"])
    return rows


def compare(base_ref, head_ref, paths, cwd=None):
    """Per-notebook collapse between two refs, then the diff-scale exemption.

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
    return _apply_moved_content(rows)


def self_test(cwd=None):
    """Positive and negative control, then the reference-case replay.

    A detector that cannot be shown to fire is indistinguishable from one
    that is unplugged -- the same contract that keeps the siblings honest.
    """
    failures = []

    def _nb(cells):
        """Build a synthetic notebook from [(id, output_text)]."""
        return {"cells": [
            {"cell_type": "code", "id": k, "outputs": [
                {"output_type": "stream", "text": t}]}
            for k, t in cells]}

    def _analyze(base_cells, head_cells, added=False):
        return analyze(None if added else _nb(base_cells), _nb(head_cells))

    long_text = "x" * 1000
    skip_notice = ("[INFO] API non configuree - execution sautee\n"
                   "Configurez OPENAI_API_KEY pour executer les exemples\n")

    # 1. signature fires: substantial base, skip-notice head, real contraction
    r = _analyze([("a", long_text)], [("a", skip_notice)])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("signature (1000 -> skip notice) not flagged")
    # 2. magnitude fires: order-of-magnitude contraction without a motif
    r = _analyze([("a", long_text)], [("a", "y" * 40)])
    if not (r["cells"] and r["cells"][0]["kind"] == "magnitude"):
        failures.append("magnitude (1000 -> 40) not flagged")
    # 3. benign variance stays silent (30 % churn is not a collapse)
    if _analyze([("a", long_text)], [("a", "x" * 700)])["cells"]:
        failures.append("benign contraction (1000 -> 700) flagged")
    # 4. small base stays silent (below the noise floor, even x1000)
    if _analyze([("a", "x" * 400)], [("a", "y")])["cells"]:
        failures.append("sub-floor base (400 -> 1) flagged")
    # 5. growth stays silent
    if _analyze([("a", long_text)], [("a", "x" * 5000)])["cells"]:
        failures.append("growth (1000 -> 5000) flagged")
    # 6. diagnostic purge is exempt: base is 30 warning lines, head is clean
    warnings = "".join(
        "warning CS8632: Une reference nullable est requise %d\n" % i
        for i in range(30))
    r = _analyze([("a", warnings)], [("a", "Build succeeded.\n")])
    if not (r["cells"] and r["cells"][0]["kind"] == "exempt-diagnostic"):
        failures.append("diagnostic purge not exempted")
    if r["regressed"]:
        failures.append("diagnostic purge exempted but still regressed")
    # 7. mixed cell is NOT exempt: the purge swallowed a large real output
    #    line together with the warnings (char-weighted fraction ~0.65)
    mixed = warnings + "real result: " + "z" * 900 + "\n"
    r = _analyze([("a", mixed)], [("a", "real result: " + "z" * 50 + "\n")])
    if not (r["cells"] and r["cells"][0]["kind"] == "magnitude"):
        failures.append("purge swallowing real output exempted (should flag)")
    # 8. accent-blind motif: "configuré" with accent still matches
    r = _analyze([("a", long_text)],
                 [("a", "Execution sautée (API non configurée)\n")])
    if not (r["cells"] and r["cells"][0]["kind"] == "signature"):
        failures.append("accented motif (sautée/configurée) not matched")
    # 9. added notebook is never judged
    if _analyze([], [("a", skip_notice)], added=True)["regressed"]:
        failures.append("added notebook judged instead of skipped")
    # 10. deleted cell loses volume legitimately: no head key, no finding
    if _analyze([("a", long_text), ("b", long_text)], [("a", long_text)])["cells"]:
        failures.append("deleted cell produced a finding")
    # 11. index-shift is not misattributed (same contract as the flood)
    if any(f["cell"] == "a" for f in
           _analyze([("a", long_text)],
                    [("zz", "y"), ("a", long_text)])["cells"]):
        failures.append("unchanged cell flagged after benign insert")

    # 12. moved-content exemption at diff scale: notebook A collapses a cell,
    #     notebook B is CREATED by the same diff with comparable volume.
    rows = [
        analyze(_nb([("a", long_text * 3)]), _nb([("a", "y" * 30)])),
        analyze(None, _nb([("b", "z" * 1500)])),
    ]
    _apply_moved_content(rows)
    if rows[0]["cells"] and rows[0]["cells"][0]["kind"] != "exempt-moved":
        failures.append("moved content not exempted at diff scale")
    if rows[0]["regressed"]:
        failures.append("moved content exempted but still regressed")
    # 13. ...but a moved gain BELOW the fraction does not exempt
    rows = [
        analyze(_nb([("a", long_text * 3)]), _nb([("a", "y" * 30)])),
        analyze(None, _nb([("b", "z" * 300)])),
    ]
    _apply_moved_content(rows)
    if not rows[0]["regressed"]:
        failures.append("insufficient moved gain exempted the collapse")

    # Replay the reference case (#15209).
    from check_output_failure_text import git
    if (git("cat-file", "-e", SELF_TEST_HEAD, cwd=cwd) is None
            or git("cat-file", "-e", SELF_TEST_BASE, cwd=cwd) is None):
        print("SKIP replay: reference commits not in this clone")
    else:
        rrows = compare(SELF_TEST_BASE, SELF_TEST_HEAD,
                        [SELF_TEST_NOTEBOOK], cwd=cwd)
        r0 = rrows[0] if rrows else {}
        n_sig = sum(1 for f in r0.get("cells", [])
                    if f["kind"] == "signature")
        print("replay " + SELF_TEST_HEAD[:12] + " on "
              + SELF_TEST_NOTEBOOK.split("/")[-1] + ": total "
              + str(r0.get("base_total")) + " -> " + str(r0.get("head_total"))
              + ", signature findings " + str(n_sig)
              + " " + str([f["cell"] + " x" + str(f["factor"])
                           for f in r0.get("cells", [])]))
        if n_sig < SELF_TEST_MIN_FINDINGS:
            failures.append("replay signature findings " + str(n_sig)
                            + " < " + str(SELF_TEST_MIN_FINDINGS) + " expected")

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: witnesses fired, benign churn silent, exemptions "
          "hold, reference replay fires")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Advisory ratchet: no silent per-cell collapse of output"
                    " volume between the merge base and HEAD (mirror of"
                    " check_output_flood.py).")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--self-test", action="store_true",
                    help="Positive + negative control, then replay the"
                         " reference case (#15209)")
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
                          + " (x" + str(f["factor"]) + ")")
        for r in bad:
            print("\nFLAGGED (advisory) " + r["notebook"] + "  total "
                  + str(r["base_total"]) + " -> " + str(r["head_total"]))
            for f in r["cells"]:
                if f["kind"] in ("signature", "magnitude"):
                    print("  " + f["kind"].upper() + ": cell "
                          + str(f["cell"]) + " " + str(f["base"]) + " -> "
                          + str(f["head"]) + " (x" + str(f["factor"]) + ")")
        if bad:
            print("\nAdvisory, not a gate: justify the contraction in the PR"
                  " body (declared lightening, moved content, warning purge)"
                  " or fix the cause and RE-EXECUTE. The signature signal"
                  " usually means a re-execution without API keys --"
                  " re-execute with the keys configured (Stop & Repair).")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
