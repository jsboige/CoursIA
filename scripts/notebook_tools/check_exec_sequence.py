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
                                  [--fail-on DIRTY] [--verbose]

    path          notebook file, directory, or family root
                  (default: MyIA.AI.Notebooks)
    --tracked-only  restrict the scan to git-TRACKED files. Reference
                  measurements MUST use this: working trees hold ignored
                  artifacts (checkpoints, audit copies) that differ per
                  machine -- see "measurement basis" below.
    --json        machine-readable output (one record per notebook)
    --fail-on VERDICT[,VERDICT...]  exit 1 if any notebook carries one of
                  these verdicts (default: never fail; tier-2 gate will
                  pass FAIL_ON here). Accepts DIRTY (= any of DUPLICATE,
                  UNORDERED, NOT_FROM_1, GAP) and NONCLEAN (= any verdict other
                  than CLEAN).
    --verbose     also list CLEAN notebooks

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
            capture_output=True, text=True, check=True,
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
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    except (subprocess.CalledProcessError, OSError):
        return "?"


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
               "verdict": "PARSE_ERROR", "sequence": [], "sequence_head": []}
        try:
            nb = json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            records.append(rec)
            continue
        cells = [c for c in nb.get("cells", [])
                 if c.get("cell_type") == "code"
                 and "".join(c.get("source", [])).strip()]
        ec = [c.get("execution_count") for c in cells]
        rec["verdict"] = sequence_verdict(ec)
        rec["sequence"] = ec
        rec["sequence_head"] = ec[:12]
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
    ap.add_argument("--fail-on", default="",
                    help="Comma-separated verdicts that make the run exit 1 "
                         "(DIRTY = DUPLICATE|UNORDERED|NOT_FROM_1|GAP)")
    ap.add_argument("--verbose", action="store_true",
                    help="Also list CLEAN notebooks")
    args = ap.parse_args()

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
    others = {k: v for k, v in by_verdict.items()
              if k not in DIRTY_VERDICTS | {"CLEAN"}}
    if others:
        print(f"excluded from coherence stats: {others}")
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
        print(f"{r['verdict']:<12} {r['notebook']:<70} {seq}")

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
