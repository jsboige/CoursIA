"""Ratchet gate: a re-execution must not let a notebook's output-object count
explode per cell or in totality.

Issue: user report 2026-09-06 (Sudoku-15-Infer-Csharp.ipynb, then 45 434 lines).
A re-execution of the notebook on a machine where ``InferenceEngine.ShowProgress``
defaults to true made every Infer.NET run emit one dot PER ITERATION, and the
``.net-csharp`` kernel turns each ``Console.Write(".")`` into a separate
``stream`` output object. Measured on the committed artifact (cells 27/25/34/9/14/19
carrying 3018 / 2243 / 376 / 112 / 111 / 55 output objects -- 5 992 objects for the
whole notebook, 2 900 of them single dot characters).

The three surfaces consulted at merge time all returned CLEAN:

  1. ``output_type == "error"``: 0. The flood is stdout, not an exception.
  2. The failure-text / machine-path ratchet (check_output_failure_text.py): 0.
     A dot character is neither a tool-failure banner nor a path.
  3. The exec-count check: every cell carries a real ``execution_count``.

Surface 3 is what this file exists to close: nothing counted OUTPUT OBJECTS, so a
notebook could grow from ~29k to ~45k lines (26k -> 45k bytes of dot output
multiplied into 5 300+ objects) while every existing gate stayed green.

Two axes, both ratcheted 0 -> N against the merge base and capped with an
absolute floor:

  CELL    a code cell whose output-object count GREW beyond ``CELL_CAP``, or a
          cell ADDED by the branch already above ``CELL_CAP``.
  TOTAL   the notebook's summed output-object count GREW beyond ``TOTAL_CAP``.

Cap calibration (measured on origin/main 2026-09-06): median per-cell output
count is 1, p99 is 40. The flood family starts at 55; the clear outliers above
CELL_CAP are the named degeneration and a few other legacy notebooks which the
ratchet leaves untouched unless they grow -- this is a ratchet, not a repo-wide
scold. Pre-existing debt is surfaced by ``--all`` (advisory sweep), never by the
gate.

Cells are matched BASE -> HEAD by nbformat cell ``id`` when both sides carry one,
falling back to positional index (the capability axis of the sibling does the
same thing); an id-aligned match survives cell insertions, so a PR that inserts a
benign cell before a legacy-flood cell is not misattributed. A notebook ADDED by
the branch has no baseline and is reported ADVISORY, never gated.

Usage:
    python check_output_flood.py <base-ref> [--json]
    python check_output_flood.py --all [--json]
    python check_output_flood.py --self-test

Base ref is resolved to merge-base(base-ref, HEAD), same as the sibling.

Exit 1 iff at least one changed notebook grew either axis.
"""

import argparse
import json
import sys

# Reuse the sibling's git plumbing and notebook resolution so the two ratchets
# share one implementation of "what changed between the merge base and HEAD".
from check_output_failure_text import (
    EXCLUDE_MARKERS,
    changed_notebooks,
    resolve_base,
    read_notebook_at,
)

CELL_CAP = 50
TOTAL_CAP = 400

# Founding commit, replayed by --self-test. 954d1cd7fef5 (v3 solver, PR #11828)
# grew Sudoku-15 from 29 665 to 44 173 lines by ADDING a v3-test cell carrying 376
# output objects (the parent already carried the 2243/3018 cells at 5 583 total).
SELF_TEST_COMMIT = "954d1cd7fef5"
SELF_TEST_MIN_CELL = 1
SELF_TEST_MIN_TOTAL = 100  # head total - base total on that commit (measured +372)

_MIN_NOTEBOOK_SAMPLES = 0


def _cell_key(cell, index):
    """nbformat v4.5 cell id when present, else a positional key."""
    cid = cell.get("id")
    return cid if cid else "@%d" % index


def _cell_counts(nb):
    """{(id-or-positional-key): output-object-count} for every code cell."""
    if not nb:
        return {}
    counts = {}
    for i, c in enumerate(nb.get("cells", []) or []):
        if c.get("cell_type") != "code":
            continue
        counts[_cell_key(c, i)] = len(c.get("outputs", []) or [])
    return counts


def analyze(base_nb, head_nb):
    """Pure per-notebook growth on two parsed notebooks.

    ``base_nb`` is None for a notebook ADDED by the branch (advisory, never
    gated). Returns one row dict (the shape ``compare`` aggregates).
    """
    added = base_nb is None
    bm, hm = _cell_counts(base_nb), _cell_counts(head_nb)

    b_total = sum(bm.values())
    h_total = sum(hm.values())

    cell_findings = []
    for key, count in hm.items():
        bc = bm.get(key)
        if bc is None:
            if count > CELL_CAP:
                cell_findings.append({"cell": key, "kind": "added",
                                      "head": count})
        elif count > bc and count > CELL_CAP:
            cell_findings.append({"cell": key, "kind": "grew",
                                  "base": bc, "head": count})

    total_finding = None
    if h_total > b_total and h_total > TOTAL_CAP:
        total_finding = {"base": b_total, "head": h_total,
                         "delta": h_total - b_total}

    # Regress only on non-adopted notebooks (a fresh notebook is advisory).
    regressed = (not added) and (bool(cell_findings) or total_finding is not None)
    return {
        "added": added,
        "base_total": b_total,
        "head_total": h_total,
        "cells": cell_findings,
        "total": total_finding,
        "regressed": regressed,
    }


def compare(base_ref, head_ref, paths, cwd=None):
    """Per-notebook growth of each axis between two refs.

    ``head_ref`` is None for the working tree (same contract as the sibling).
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


def all_notebooks(cwd=None):
    """Every tracked deliverable notebook (advisory sweep)."""
    import subprocess
    out = subprocess.run(["git", "ls-files", "*.ipynb"], cwd=cwd,
                         capture_output=True, encoding="utf-8", errors="replace")
    if out.returncode != 0:
        return []
    paths = []
    for line in out.stdout.splitlines():
        posix = line.strip().replace("\\", "/")
        if posix and not any(m in "/" + posix for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def self_test(cwd=None):
    """Positive and negative control, then the founding-commit replay.

    A detector that cannot be shown to fire is indistinguishable from one that
    is unplugged -- the same contract that keeps the sibling honest.
    """
    failures = []

    def _nb(cells):
        return {"cells": [{"cell_type": "code", "id": kid,
                           "outputs": [{"output_type": "stream", "text": "."}
                                       for _ in range(n)]}
                          for kid, n in cells]}

    def _nb(code_cells, added=False):
        """Build a synthetic notebook from [(id, outputs)]; None base = added."""
        return None if added else {
            "cells": [{"cell_type": "code", "id": k, "outputs": [{}] * n}
                      for k, n in code_cells]}

    def _analyze(base_cells, head_cells, added=False):
        return analyze(_nb(base_cells, added), _nb(head_cells))

    # 1. existing cell floods
    if not _analyze([("a", 3)], [("a", 3018)])["cells"]:
        failures.append("existing-cell flood (3 -> 3018) not flagged")
    # 2. added cell above cap
    if not any(c["cell"] == "b" for c in _analyze([("a", 3)], [("a", 3), ("b", 80)])["cells"]):
        failures.append("added flooding cell (80) not flagged")
    # 3. benign growth stays silent
    if _analyze([("a", 5)], [("a", 12)])["cells"]:
        failures.append("benign growth (5 -> 12) flagged")
    # 4. improvement stays silent (3018 -> 500)
    if _analyze([("a", 3018)], [("a", 500)])["cells"]:
        failures.append("flood reduction (3018 -> 500) flagged")
    # 5. new benign cell stays silent
    if _analyze([("a", 3)], [("a", 3), ("b", 40)])["cells"]:
        failures.append("benign new cell (40) flagged")
    # 6. index-shift is not misattributed: insert benign cell before a legacy
    #    flooded (but unchanged) cell. Id-alignment must NOT flag the legacy one.
    if any(c["cell"] == "a" for c in _analyze([("a", 3000)], [("zz", 10), ("a", 3000)])["cells"]):
        failures.append("legacy flooded cell flagged after benign insert")
    # 7. diffuse flood across many cells catches TOTAL (40 cells 5 -> 30)
    if not _analyze([(f"c{i}", 5) for i in range(40)],
                    [(f"c{i}", 30) for i in range(40)])["total"]:
        failures.append("diffuse flood (40 cells 5->30) not flagged on TOTAL")
    # 8. added notebook is advisory, not gated
    if _analyze([], [("a", 800)], added=True)["regressed"]:
        failures.append("added notebook gated instead of advisory")

    # Replay the founding commit against its parent.
    from check_output_failure_text import git
    if git("cat-file", "-e", SELF_TEST_COMMIT, cwd=cwd) is None:
        print("SKIP replay: " + SELF_TEST_COMMIT[:12] + " not in this clone")
    else:
        parent = SELF_TEST_COMMIT + "^"
        paths = changed_notebooks(parent, SELF_TEST_COMMIT, cwd=cwd)
        rows = compare(parent, SELF_TEST_COMMIT, paths, cwd=cwd)
        n_cell = sum(len(r["cells"]) for r in rows)
        n_total = sum(1 for r in rows if r["total"] is not None)
        d_total = sum((r["total"] or {}).get("delta", 0) for r in rows)
        print("replay " + SELF_TEST_COMMIT[:12] + ": " + str(len(paths))
              + " notebooks, CELL flood " + str(n_cell)
              + ", TOTAL delta +" + str(d_total))
        if n_cell < SELF_TEST_MIN_CELL:
            failures.append("replay CELL flood " + str(n_cell) + " < "
                            + str(SELF_TEST_MIN_CELL) + " expected")
        if d_total < SELF_TEST_MIN_TOTAL:
            failures.append("replay TOTAL delta +" + str(d_total) + " < +"
                            + str(SELF_TEST_MIN_TOTAL) + " expected")

    for f in failures:
        print("SELF-TEST FAIL: " + f)
    if failures:
        return 1
    print("SELF-TEST OK: witnesses matched, benign growth silent, replay fires")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Ratchet: no NEW output-object explosion in a notebook."
                    " Counts output objects per code cell and per notebook, "
                    "against the merge base.")
    ap.add_argument("base", nargs="?",
                    help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--all", action="store_true",
                    help="Advisory sweep of every tracked notebook (no gate)")
    ap.add_argument("--self-test", action="store_true",
                    help="Positive + negative control, then replay the founding"
                         " commit")
    ap.add_argument("--json", action="store_true", dest="as_json")
    args = ap.parse_args(argv)

    if args.self_test:
        return self_test()

    if args.all:
        head = None
        rows = []
        for path in all_notebooks():
            H = read_notebook_at(None, path)
            if H is None:
                continue
            cm = _cell_counts(H)
            tot = sum(cm.values())
            # Absolute floor for the sweep: report cells above CELL_CAP.
            big = [(k, n) for k, n in cm.items() if n > CELL_CAP]
            if big or tot > TOTAL_CAP:
                rows.append({"notebook": path, "cells_above_cap": big,
                             "total": tot})
        if args.as_json:
            print(json.dumps({"mode": "sweep", "notebooks": len(rows),
                              "rows": rows}, indent=2, ensure_ascii=False))
        else:
            print("ADVISORY sweep (" + str(len(rows))
                  + " notebook(s) with a cell above " + str(CELL_CAP)
                  + " objects or a total above " + str(TOTAL_CAP) + ")")
            for r in rows:
                print("  " + r["notebook"] + "  total=" + str(r["total"])
                      + "  cells=" + str([c for c, n in r["cells_above_cap"]]))
        return 0

    if not args.base:
        ap.error("base ref required (or --all / --self-test)")

    base = resolve_base(args.base)
    paths = changed_notebooks(base)
    rows = compare(base, None, paths)
    bad = [r for r in rows if r["regressed"]]

    if args.as_json:
        print(json.dumps({"base_ref": args.base, "merge_base": base,
                          "changed": len(paths), "regressions": len(bad),
                          "rows": rows}, indent=2, ensure_ascii=False))
    else:
        print("base " + str(args.base) + " -> merge-base " + base[:12]
              + " | " + str(len(paths)) + " changed notebooks | "
              + str(len(bad)) + " regressed")
        for r in rows:
            if r.get("added") and (r["cells"] or r["total"]):
                print("  ADVISORY (added by this branch, no baseline) "
                      + r["notebook"])
        for r in bad:
            print("\nFAIL " + r["notebook"])
            for cf in r["cells"]:
                if cf["kind"] == "grew":
                    print("  CELL: " + cf["cell"] + " " + str(cf["base"]) + " -> "
                          + str(cf["head"]) + " outputs (+"
                          + str(cf["head"] - cf["base"]) + ")")
                else:
                    print("  CELL (added): " + cf["cell"] + " "
                          + str(cf["head"]) + " outputs at birth")
            if r["total"]:
                t = r["total"]
                print("  TOTAL: " + str(t["base"]) + " -> " + str(t["head"])
                      + " (+" + str(t["delta"]) + ")")
        if bad:
            print("\nCause is in the notebook code, not the environment: an "
                  "Infer.NET / solver loop is printing one output object per "
                  "iteration (ShowProgress, per-line Console.Write in a loop, "
                  "one display per table row). Fix the source and RE-EXECUTE; "
                  "never hand-edit a committed output (Stop & Repair).")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
