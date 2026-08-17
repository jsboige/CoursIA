"""Ratchet gate: changed outputs must not ride an identical papermill block.

Issue #11155 (tier 2 of #11146). The tier-1 measure (published in #11146,
PR #11153) counted 631/1015 tracked notebooks carrying a
``metadata.papermill`` block and 576 stale candidates - a retroactive sweep
would be massive and mostly wrong (a later markdown-only commit does not
make a block false). This gate enforces the ratchet half only: for every
.ipynb changed between BASE and HEAD, if the execution evidence (outputs /
execution_count of the code cells) changed while the ``metadata.papermill``
block stayed identical, the run that produced the new outputs did not write
the block - the block describes a previous run that no longer matches the
committed outputs. FAIL.

Everything else is clean, by design of the issue body:
- outputs untouched (a markdown-only edit rides an unchanged block legally)
- block absent at head (removed - explicitly allowed)
- block changed or newly added (the executor rewrote it alongside outputs)
- notebook added by the PR (no base blob; execution evidence itself is
  enforced by notebook-execution-required.yml, H.3)

Usage:
    python check_papermill_ratchet.py <base-ref> [--json]

    base-ref      git ref of the merge base (CI: origin/<base branch>)

Head state reads the working tree (in CI the checkout IS the head), base
state reads the blob via `git show`. Exit code 1 iff at least one
changed-outputs + identical-block regression exists.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

# Same exclusions as check_exec_ratchet.py / notebook-execution-required.yml:
# archived, papermill-output and research copies are not deliverable notebooks.
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


def exec_evidence(nb):
    """Canonical signature of the execution evidence of a notebook.

    (execution_count, canonical outputs) of every code cell, in cell order.
    Two notebooks with equal signatures were not re-executed differently.
    """
    parts = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        parts.append(json.dumps(
            [cell.get("execution_count"), cell.get("outputs")],
            sort_keys=True, ensure_ascii=False))
    return "\n".join(parts)


def papermill_block(nb):
    """Canonical serialization of the metadata.papermill block, or None."""
    block = (nb.get("metadata") or {}).get("papermill")
    if block is None:
        return None
    return json.dumps(block, sort_keys=True, ensure_ascii=False)


def state_at_base(base, path, cwd=None):
    """(evidence, block) of the notebook blob at base ref.

    Returns ("ABSENT", None, None) when the file does not exist at base and
    ("PARSE_ERROR", None, None) on invalid JSON.
    """
    content = git("show", f"{base}:{path}", cwd=cwd)
    if content is None:
        return "ABSENT", None, None
    try:
        nb = json.loads(content)
    except Exception:
        return "PARSE_ERROR", None, None
    return "OK", exec_evidence(nb), papermill_block(nb)


def state_at_head(path, cwd=None):
    """(status, evidence, block) of the working-tree notebook."""
    try:
        nb = json.loads((Path(cwd or ".") / path).read_text(encoding="utf-8"))
    except Exception:
        return "PARSE_ERROR", None, None
    return "OK", exec_evidence(nb), papermill_block(nb)


def classify(base_state, head_state):
    """Verdict of one changed notebook. Regression iff stale block ridden."""
    b_status, b_ev, b_block = base_state
    h_status, h_ev, h_block = head_state
    if b_status == "ABSENT":
        return "ADDED", False
    if b_status == "PARSE_ERROR" or h_status == "PARSE_ERROR":
        return "PARSE_ERROR", False
    if h_block is None:
        # Block removed at head - explicitly allowed by the issue.
        return "BLOCK_REMOVED", False
    if h_ev == b_ev:
        # Outputs untouched: a markdown-only edit rides the block legally.
        return "OUTPUTS_UNCHANGED", False
    if h_block == b_block:
        # Outputs changed but the block is byte-identical: it describes the
        # previous run, not the one that produced the committed outputs.
        return "STALE_BLOCK", True
    # Block changed or newly written alongside the new outputs.
    return "BLOCK_MOVED" if b_block is not None else "BLOCK_ADDED", False


def ratchet(base, cwd=None):
    """One record per changed notebook; regression = stale block ridden."""
    records = []
    for path in changed_notebooks(base, cwd=cwd):
        verdict, regression = classify(
            state_at_base(base, path, cwd=cwd),
            state_at_head(path, cwd=cwd))
        records.append({
            "notebook": path,
            "verdict": verdict,
            "regression": regression,
        })
    return records


def main():
    ap = argparse.ArgumentParser(
        description="Ratchet gate: changed outputs must not ride an "
                    "identical papermill block (issue #11155)")
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
        print(f"papermill ratchet -- base {args.base}")
        print(f"changed notebooks : {len(records)}")
        print(f"regressions       : {len(regressions)}")
        for r in records:
            mark = "REGRESSION" if r["regression"] else ""
            print(f"  {r['verdict']:18s} {r['notebook']} {mark}")

    if regressions:
        for r in regressions:
            print(f"::error file={r['notebook']}::outputs/execution_count "
                  f"changed but the metadata.papermill block is identical to "
                  f"{args.base} - the block describes the previous run. "
                  f"Re-execute the notebook via an executor that rewrites the "
                  f"block, or remove the block", file=sys.stderr)
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
