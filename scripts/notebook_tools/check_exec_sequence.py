"""Check execution_count sequence coherence of notebooks.

A notebook really executed end-to-end on a fresh kernel necessarily carries
execution_count 1, 2, 3, ..., N on its code cells: the kernel increments the
counter at each execution, so two cells cannot share a number within one
session and a cell cannot carry a smaller number than its predecessor. A
sequence violating this is the trace of a disordered interactive session
(cells re-run by hand, order edited after the fact, kernel restarted midway)
-- the committed outputs, taken together, describe no single run.

All existing gates (H.3 pre-commit, validate_pr_notebooks.py) only check that
execution_count EXISTS. This organ measures sequence coherence (issue #11112,
tier 1).

Usage:
    python check_exec_sequence.py [path] [--tracked-only] [--json]
                                  [--check] [--fail-on DIRTY] [--verbose]

    path          notebook file, directory, or family root
                  (default: MyIA.AI.Notebooks)
    --tracked-only  restrict the scan to git-TRACKED files. Reference
                  measurements MUST use this: working trees hold ignored
                  artifacts (checkpoints, audit copies) that differ per
                  machine -- see "measurement basis" below.
    --json        machine-readable output (one record per notebook)
    --check       gate mode: exit 1 if any notebook is neither CLEAN nor
                  covered by a declared exemption (issue #19930). The named
                  exit-in-error mode; equivalent to failing on NONCLEAN minus
                  the declared exemptions below.
    --fail-on VERDICT[,VERDICT...]  exit 1 if any notebook carries one of
                  these verdicts (default: never fail; tier-2 gate will
                  pass FAIL_ON here). Accepts DIRTY (= any of DUPLICATE,
                  UNORDERED, NOT_FROM_1, GAP) and NONCLEAN (= any verdict other
                  than CLEAN). Unlike --check, --fail-on does NOT honour the
                  declared exemptions.
    --verbose     also list CLEAN notebooks

Declared exemptions (issue #19930 criterion 3). A non-CLEAN verdict whose
cause is legitimate carries a WRITTEN justification in the organ rather than
being silently ignored:
    qc-cloud     QuantConnect books run on QuantConnect Cloud (rule F): no
                 local kernel, so their unexecuted cells (PARTIAL) are
                 expected. Matched by path root, not by a dated file list.
    pii-empty    GradeBook.ipynb carries student PII; its outputs are
                 deliberately empty (its own first cell declares it, cf
                 code-style). Matched by exact path.
Only PARTIAL is exemptable: a carnet whose counters CAN be continuous is a
defect (DIRTY) and must be re-executed, never declared away.

Verdicts (per notebook):
    CLEAN        sequence is exactly 1..N
    DUPLICATE    some value appears twice
    UNORDERED    some value is smaller than its predecessor
    NOT_FROM_1   first value is not 1
    GAP          deviates from 1..N with no repeat and no decrease
                 (e.g. a cell deleted after the run)
    PARTIAL      at least one code cell has execution_count null (never
                 executed) -- excluded from coherence statistics, reported
                 for visibility
    EMPTY        no non-empty code cells
    PARSE_ERROR  invalid notebook JSON

The summary counts DUPLICATE / UNORDERED / NOT_FROM_1 / GAP INDEPENDENTLY
(a sequence can violate several), so the bucket sum exceeds the
dirty-notebook count.

Measurement basis. Numbers are only comparable when the scanned corpus is.
On a dirty working tree, rglob picks up ignored artifacts -- e.g. 217 ignored
.ipynb on one cluster machine vs 0 on another -- silently shifting every
count. Reference runs therefore use --tracked-only, which intersects the
scan with `git ls-files`; corpus identity is then the commit, which the
script prints.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

DIRTY_VERDICTS = {"DUPLICATE", "UNORDERED", "NOT_FROM_1", "GAP"}

# Declared exemptions (issue #19930, criterion 3). A notebook whose counters
# cannot legitimately be continuous carries a WRITTEN justification here; --check
# then reports it as exempt instead of failing on it. The rules are path-based
# (a family root, an exact path), never a dated list of files that would rot as
# notebooks are added or renamed.
QC_CLOUD_ROOT = "MyIA.AI.Notebooks/QuantConnect/"
EXEMPT_PII_PATHS = frozenset({"MyIA.AI.Notebooks/GradeBook.ipynb"})
# Only partiality is exemptable. A carnet whose counters CAN be continuous is a
# defect (DIRTY): it is re-executed, never declared away.
EXEMPTABLE_VERDICTS = frozenset({"PARTIAL"})


def exemption_reason(notebook_posix, verdict):
    """Written justification that lifts a verdict from the --check gate, or None.

    Returns a non-empty reason string only for an EXEMPTABLE verdict whose path
    matches a declared rule; every other case returns None and stays gated."""
    if verdict not in EXEMPTABLE_VERDICTS:
        return None
    if notebook_posix.startswith(QC_CLOUD_ROOT):
        return "qc-cloud (rule F: run on QuantConnect Cloud, no local kernel)"
    if notebook_posix in EXEMPT_PII_PATHS:
        return "pii-empty (declared in the notebook's own first cell)"
    return None


def check_offenders(records):
    """Records the --check gate fails on: non-CLEAN and not covered by a rule."""
    return [r for r in records if r["verdict"] != "CLEAN" and not r.get("exempt")]


def sequence_verdict(exec_counts):
    """Verdict of one notebook's execution_count sequence.

    CLEAN means EXACTLY 1..N (the reference definition: any deviation
    from range(1, N+1) is dirty). Priority for the single label: NOT_FROM_1,
    then DUPLICATE, then UNORDERED, then GAP (a hole with no repeat and no
    decrease -- e.g. a cell deleted after the run). The buckets themselves
    are counted independently in the summary."""
    if not exec_counts:
        return "EMPTY"
    if any(e is None for e in exec_counts):
        return "PARTIAL"
    if exec_counts == list(range(1, len(exec_counts) + 1)):
        return "CLEAN"
    if exec_counts[0] != 1:
        return "NOT_FROM_1"
    if len(set(exec_counts)) != len(exec_counts):
        return "DUPLICATE"
    if any(cur < prev for prev, cur in zip(exec_counts, exec_counts[1:])):
        return "UNORDERED"
    return "GAP"


def buckets_of(exec_counts):
    """Independent violation buckets of a fully-executed sequence.

    GAP is the residual bucket: the sequence deviates from 1..N without any
    of the three named violations."""
    buckets = set()
    if exec_counts[0] != 1:
        buckets.add("NOT_FROM_1")
    if len(set(exec_counts)) != len(exec_counts):
        buckets.add("DUPLICATE")
    if any(cur < prev for prev, cur in zip(exec_counts, exec_counts[1:])):
        buckets.add("UNORDERED")
    if not buckets and exec_counts != list(range(1, len(exec_counts) + 1)):
        buckets.add("GAP")
    return buckets


def self_test():
    """Prove the detector gates the gate (issue #14676 lesson).

    A gate that cannot be shown to fire is indistinguishable from one that is
    unplugged -- which is exactly how the Exec-sequence ratchet was misread as
    advisory and its CLEAN -> non-CLEAN regressions let through for several
    cycles. Assert a clean sequence stays CLEAN (negative control), every
    dirty class fires (positive control), and the #14676 option-(c) scenario
    -- a DUPLICATE-producing code cell converted to markdown leaves the
    sequence 1..N CLEAN. Also exercises the #19930 declared exemptions and the
    --check predicate: an exempt PARTIAL passes the gate, an undeclared PARTIAL
    fails it, and a DIRTY under the QC root still fails (partiality is
    exemptable, a real counter defect never is). Exit 0 iff every control
    holds."""
    controls = [
        ("negative: clean 1..N stays CLEAN", [1, 2, 3], "CLEAN"),
        ("negative: single clean cell stays CLEAN", [1], "CLEAN"),
        ("positive: not-from-1 fires", [2, 3, 4], "NOT_FROM_1"),
        ("positive: duplicate fires", [1, 2, 2, 3], "DUPLICATE"),
        ("positive: unordered fires", [1, 2, 4, 3], "UNORDERED"),
        ("positive: gap fires (cell deleted after run)", [1, 2, 3, 5], "GAP"),
        ("#14676 option-(c): markdown cell drops, clean 1..12 stays CLEAN",
         list(range(1, 13)), "CLEAN"),
    ]
    failures = []
    for label, seq, expected in controls:
        got = sequence_verdict(seq)
        status = "ok" if got == expected else "FAIL"
        if got != expected:
            failures.append((label, expected, got))
        print(f"  [{status}] {label}: {got}")

    # Declared-exemption controls (issue #19930): the rule must lift an exempt
    # PARTIAL and leave everything else gated.
    exempt_controls = [
        ("qc-cloud PARTIAL is exempt",
         "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-02-Platform-Fundamentals.ipynb",
         "PARTIAL", True),
        ("pii-empty PARTIAL is exempt",
         "MyIA.AI.Notebooks/GradeBook.ipynb", "PARTIAL", True),
        ("undeclared PARTIAL is NOT exempt",
         "MyIA.AI.Notebooks/ML/foo.ipynb", "PARTIAL", False),
        ("DIRTY under the QC root is NOT exempt",
         "MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-02-Platform-Fundamentals.ipynb",
         "DIRTY", False),
        ("CLEAN is never exempt", "MyIA.AI.Notebooks/GradeBook.ipynb", "CLEAN", False),
    ]
    for label, path, verdict, expect_exempt in exempt_controls:
        got = bool(exemption_reason(path, verdict))
        status = "ok" if got == expect_exempt else "FAIL"
        if got != expect_exempt:
            failures.append((label, expect_exempt, got))
        print(f"  [{status}] {label}: exempt={got}")

    # --check predicate controls: only non-CLEAN, non-exempt records are offenders.
    gate_controls = [
        ("gate passes when only CLEAN + exempt PARTIAL present",
         [{"verdict": "CLEAN", "exempt": False},
          {"verdict": "PARTIAL", "exempt": True}], 0),
        ("gate fails on an undeclared PARTIAL",
         [{"verdict": "PARTIAL", "exempt": False}], 1),
        ("gate fails on a DIRTY even beside an exempt PARTIAL",
         [{"verdict": "DIRTY", "exempt": False},
          {"verdict": "PARTIAL", "exempt": True}], 1),
    ]
    for label, recs, expected_n in gate_controls:
        got = len(check_offenders(recs))
        status = "ok" if got == expected_n else "FAIL"
        if got != expected_n:
            failures.append((label, expected_n, got))
        print(f"  [{status}] {label}: offenders={got}")

    if failures:
        print("SELF-TEST FAIL:")
        for label, expected, got in failures:
            print(f"  - {label}: expected {expected}, got {got}")
        return 1
    print("all detector self-test controls passed")
    return 0


def family_of(path, root):
    try:
        rel = path.resolve().relative_to(root.resolve())
    except ValueError:
        return "(outside-root)"
    parts = rel.parts
    return parts[0] if len(parts) > 1 else "(root)"


def tracked_files(root):
    """Set of tracked file paths under root, as posix strings relative to CWD."""
    try:
        out = subprocess.run(
            ["git", "ls-files", "--", str(root)],
            capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
        ).stdout
    except (subprocess.CalledProcessError, OSError) as err:
        print(f"[!] git ls-files failed ({err}); scanning everything.",
              file=sys.stderr)
        return None
    return {Path(line).as_posix() for line in out.splitlines() if line}


def head_commit():
    try:
        return subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            capture_output=True, text=True, encoding="utf-8", errors="replace", check=True,
        ).stdout.strip()
    except (subprocess.CalledProcessError, OSError):
        return "?"


def code_exec_counts(nb):
    """execution_count list of the notebook's non-empty code cells.

    Shared definition of "the sequence" between the tier-1 scanner and the
    tier-2 ratchet gate (check_exec_ratchet.py): a code cell whose source is
    blank does not occupy a kernel counter slot."""
    cells = [c for c in nb.get("cells", [])
             if c.get("cell_type") == "code"
             and "".join(c.get("source", [])).strip()]
    return [c.get("execution_count") for c in cells]


def scan(target, tracked_only, verbose):
    root = target if target.is_dir() else target.parent
    tracked = tracked_files(root) if tracked_only else None

    files = sorted(target.rglob("*.ipynb") if target.is_dir() else [target])
    records = []
    for path in files:
        posix = path.as_posix()
        if ".ipynb_checkpoints" in posix:
            continue
        if tracked is not None and posix not in tracked:
            continue
        rec = {"notebook": posix, "family": family_of(path, root),
               "verdict": "PARSE_ERROR", "sequence": [], "sequence_head": [],
               "exempt": False, "exempt_reason": None}
        try:
            nb = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            records.append(rec)
            continue
        ec = code_exec_counts(nb)
        rec["verdict"] = sequence_verdict(ec)
        rec["sequence"] = ec
        rec["sequence_head"] = ec[:12]
        rec["exempt_reason"] = exemption_reason(posix, rec["verdict"])
        rec["exempt"] = bool(rec["exempt_reason"])
        records.append(rec)
    return records


def main():
    ap = argparse.ArgumentParser(
        description="Check execution_count sequence coherence (issue #11112 tier 1)")
    ap.add_argument("path", nargs="?", default="MyIA.AI.Notebooks",
                    help="Notebook file, directory or family root")
    ap.add_argument("--tracked-only", action="store_true",
                    help="Restrict scan to git-tracked files (reference mode)")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="One JSON record per notebook")
    ap.add_argument("--check", action="store_true",
                    help="Gate mode: exit 1 if any notebook is neither CLEAN "
                         "nor covered by a declared exemption (issue #19930)")
    ap.add_argument("--fail-on", default="",
                    help="Comma-separated verdicts that make the run exit 1 "
                         "(DIRTY = DUPLICATE|UNORDERED|NOT_FROM_1|GAP)")
    ap.add_argument("--verbose", action="store_true",
                    help="Also list CLEAN notebooks")
    ap.add_argument("--self-test", action="store_true",
                    help="Run the detector self-test (positive + negative "
                         "control) and exit")
    args = ap.parse_args()

    if args.self_test:
        sys.exit(self_test())

    target = Path(args.path)
    if not target.exists():
        ap.error(f"path not found: {target}")

    records = scan(target, args.tracked_only, args.verbose)

    # Summary: buckets are counted independently over fully-executed seqs.
    bucket_counts = {"DUPLICATE": 0, "UNORDERED": 0, "NOT_FROM_1": 0,
                     "GAP": 0}
    for r in records:
        if r["verdict"] not in DIRTY_VERDICTS and r["verdict"] != "CLEAN":
            continue
        for b in buckets_of(r["sequence"]):
            bucket_counts[b] += 1

    by_verdict = {}
    for r in records:
        by_verdict[r["verdict"]] = by_verdict.get(r["verdict"], 0) + 1
    clean = by_verdict.get("CLEAN", 0)
    dirty = sum(by_verdict.get(v, 0) for v in DIRTY_VERDICTS)

    fam_dirty = {}
    for r in records:
        if r["verdict"] in DIRTY_VERDICTS:
            fam_dirty[r["family"]] = fam_dirty.get(r["family"], 0) + 1

    if args.as_json:
        print(json.dumps({
            "basis": {"tracked_only": args.tracked_only,
                      "commit": head_commit(), "root": str(target)},
            "summary": {"scanned": len(records),
                        "fully_executed": clean + dirty,
                        "clean": clean, "dirty": dirty,
                        "exempt": sum(1 for r in records if r.get("exempt")),
                        "gate_offenders": len(check_offenders(records)),
                        "buckets": bucket_counts,
                        "other": {k: v for k, v in by_verdict.items()
                                  if k not in DIRTY_VERDICTS | {"CLEAN"}}},
            "records": records}, ensure_ascii=False, indent=1))
        return

    basis = (f"tracked-only @ {head_commit()}" if args.tracked_only
             else f"working tree @ {head_commit()}")
    print(f"execution_count sequence check -- {basis}")
    print(f"scanned            : {len(records)}")
    print(f"fully executed     : {clean + dirty}")
    print(f"  CLEAN (1..N)     : {clean}"
          + (f"  ({100.0 * clean / (clean + dirty):.1f}%)" if clean + dirty else ""))
    print(f"  DIRTY notebooks  : {dirty}"
          + (f"  ({100.0 * dirty / (clean + dirty):.1f}%)" if clean + dirty else ""))
    print(f"buckets (independent, sum >= dirty):")
    for b in ("DUPLICATE", "UNORDERED", "NOT_FROM_1", "GAP"):
        print(f"  {b:<12}: {bucket_counts[b]}")
    exempt_n = sum(1 for r in records if r.get("exempt"))
    others = {k: v for k, v in by_verdict.items()
              if k not in DIRTY_VERDICTS | {"CLEAN"}}
    if others:
        print(f"excluded from coherence stats: {others}")
    if exempt_n:
        print(f"declared exempt (issue #19930): {exempt_n}")
    if fam_dirty:
        print("dirty by family:")
        for fam, n in sorted(fam_dirty.items(), key=lambda kv: -kv[1]):
            print(f"  {fam:<14} {n}")
    for r in records:
        if r["verdict"] == "CLEAN" and not args.verbose:
            continue
        head = r["sequence_head"]
        seq = "[" + ", ".join("None" if e is None else str(e) for e in head) \
            + (", ..." if len(head) == 12 else "") + "]"
        tag = " [exempt]" if r.get("exempt") else ""
        print(f"{r['verdict']:<12}{tag} {r['notebook']:<70} {seq}")

    if args.check:
        offenders = check_offenders(records)
        if offenders:
            print(f"\nFAIL (--check): {len(offenders)} notebook(s) non-CLEAN "
                  f"and not covered by a declared exemption:")
            for r in offenders[:40]:
                print(f"  {r['verdict']:<12} {r['notebook']}")
            if len(offenders) > 40:
                print(f"  ... and {len(offenders) - 40} more")
            print("Admissible outcomes (issue #19930): re-execute the notebook "
                  "on a fresh kernel (counters become real), or declare it with "
                  "a written justification in exemption_reason().")
            sys.exit(1)
        print(f"\nOK (--check): no non-CLEAN notebook is left undeclared "
              f"({exempt_n} declared exempt).")

    if args.fail_on:
        wanted = set()
        for tok in args.fail_on.split(","):
            tok = tok.strip().upper()
            if not tok:
                continue
            if tok == "DIRTY":
                wanted |= DIRTY_VERDICTS
            elif tok == "NONCLEAN":
                wanted |= set(by_verdict) - {"CLEAN"}
            else:
                wanted.add(tok)
        hits = [r for r in records if r["verdict"] in wanted]
        if hits:
            print(f"\nFAIL: {len(hits)} notebook(s) match --fail-on "
                  f"{sorted(wanted & set(by_verdict))}")
            sys.exit(1)


if __name__ == "__main__":
    main()
