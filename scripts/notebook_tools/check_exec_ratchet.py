"""Ratchet gate: a PR must not soil a notebook whose sequence was clean.

Issue #11112 tier 2. The tier-1 organ (check_exec_sequence.py) measures the
corpus; this gate enforces only the non-regression half: for every .ipynb
changed between BASE and HEAD, a verdict that was CLEAN at BASE must still be
CLEAN at HEAD. A notebook already dirty at BASE is free to stay dirty (no
retroactive catch-up), so the gate is green on main from day one despite the
legacy dirty notebooks that the tier-3 rollout is re-executing family by
family. Improvements (DIRTY -> CLEAN) are reported but never required.

Added notebooks (no base blob) carry no ratchet: their execution evidence is
already enforced by notebook-execution-required.yml (H.3). They are reported
for visibility only.

Usage:
    python check_exec_ratchet.py <base-ref> [--json]

    base-ref      git ref of the merge base (CI: origin/<base branch>)

Head verdicts read the working tree (in CI the checkout IS the head), base
verdicts read the blob via `git show`. Exit code 1 iff at least one
CLEAN -> non-CLEAN regression exists.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_exec_sequence import code_exec_counts, sequence_verdict

# Same exclusions as notebook-execution-required.yml's detect step plus the
# checkpoints rule of the tier-1 scanner: archived, papermill-output and
# research copies are not deliverable notebooks.
EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")


def git(*args, cwd=None):
    """Run a git command, returning stdout (utf-8) or None on failure."""
    try:
        out = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                             encoding="utf-8", errors="replace", check=False)
    except OSError:
        return None
    return out.stdout if out.returncode == 0 else None


def changed_notebooks(base, cwd=None):
    """Notebooks added/copied/modified/renamed between base and HEAD."""
    out = git("diff", "--name-only", "--diff-filter=ACMR",
              base, "HEAD", "--", "*.ipynb", cwd=cwd)
    if out is None:
        return []
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace("\\", "/")
        if posix and not any(m in f"/{posix}" for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def verdict_at_base(base, path, cwd=None):
    """Verdict of the notebook blob at base ref.

    ABSENT: the file does not exist at base (added by the PR).
    PARSE_ERROR: not valid JSON."""
    content = git("show", f"{base}:{path}", cwd=cwd)
    if content is None:
        return "ABSENT", []
    try:
        ec = code_exec_counts(json.loads(content))
    except Exception:
        return "PARSE_ERROR", []
    return sequence_verdict(ec), ec


def verdict_at_head(path, cwd=None):
    """Verdict of the working-tree notebook."""
    try:
        ec = code_exec_counts(json.loads(
            (Path(cwd or ".") / path).read_text(encoding="utf-8")))
    except Exception:
        return "PARSE_ERROR", []
    return sequence_verdict(ec), ec


def ratchet(base, cwd=None):
    """One record per changed notebook; regression = CLEAN soiled."""
    records = []
    for path in changed_notebooks(base, cwd=cwd):
        base_verdict, _ = verdict_at_base(base, path, cwd=cwd)
        head_verdict, _ = verdict_at_head(path, cwd=cwd)
        records.append({
            "notebook": path,
            "base": base_verdict,
            "head": head_verdict,
            "regression": base_verdict == "CLEAN" and head_verdict != "CLEAN",
        })
    return records


def main():
    ap = argparse.ArgumentParser(
        description="Ratchet gate: PR must not soil a clean sequence "
                    "(issue #11112 tier 2)")
    ap.add_argument("base", help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="Machine-readable output")
    args = ap.parse_args()

    records = ratchet(args.base)
    regressions = [r for r in records if r["regression"]]

    if args.as_json:
        print(json.dumps({
            "base": args.base,
            "changed": len(records),
            "regressions": len(regressions),
            "records": records}, ensure_ascii=False, indent=1))
    else:
        print(f"execution_count ratchet -- base {args.base}")
        print(f"changed notebooks : {len(records)}")
        print(f"regressions       : {len(regressions)}")
        for r in records:
            mark = "REGRESSION" if r["regression"] else ""
            print(f"  {r['base']}->{r['head']} {r['notebook']} {mark}")

    if regressions:
        for r in regressions:
            print(f"::error file={r['notebook']}::sequence was CLEAN at "
                  f"{args.base}, is {r['head']} in this PR — re-execute the "
                  f"notebook end-to-end on a fresh kernel before commit",
                  file=sys.stderr)
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
