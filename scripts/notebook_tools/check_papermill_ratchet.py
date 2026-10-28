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
- outputs rewritten by a sanctioned output-strip pre-commit hook
  (OUTPUTS_STRIPPED, #12366)
- outputs that are exactly the cp1252 reversion of the base ones
  (OUTPUTS_ENCODING_REPAIRED, #23021) - the file-wide double-encoding
  repair of a notebook whose outputs carry the same corrupted text as its
  sources; no run happened, so the block is not stale

Usage:
    python check_papermill_ratchet.py <base-ref> [--json]

    base-ref      base branch ref (CI: origin/<base branch>). Resolved
                  internally to merge-base(base-ref, HEAD), so a branch
                  behind its base is judged on its own diff only.

Head state reads the working tree (in CI the checkout IS the head), base
state reads the blob via `git show`. Exit code 1 iff at least one
changed-outputs + identical-block regression exists.
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

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


def resolve_base(base, cwd=None):
    """Resolve `base` to merge-base(base, HEAD).

    The gate must judge what the branch CHANGED, not how far behind it is.
    Comparing a stale branch tree-to-tree against the tip of its base branch
    reports every notebook the base advanced meanwhile -- with the sign
    reversed, since the branch still holds the older blob -- and attributes
    those to the PR.  Measured on #11528 (a one-line markdown fix, 21 commits
    behind main): 15 changed notebooks / 9 regressions against origin/main,
    1 / 0 against the merge base.  The false verdict is the dangerous kind:
    it sends an author to "repair" notebooks they never touched.

    Falls back to the ref as given when no merge base exists (shallow clone,
    unrelated histories), i.e. the previous behaviour.
    """
    out = git("merge-base", base, "HEAD", cwd=cwd)
    return out.strip() if out and out.strip() else base


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


def cell_papermill_signature(nb):
    """Canonical hash of the per-cell ``metadata.papermill`` blocks.

    papermill rewrites the top-level ``metadata.papermill`` AND the per-cell
    block of every cell it executed. A branch that hand-rewrites the
    top-level block alone -- the FORGED_BLOCK pattern of #21229/#21230/#21232
    -- leaves the per-cell blocks identical to the base. Comparing the
    signature is therefore a positive test: same signature + different
    top-level block = hand-rewrite, regression. Same signature + same
    top-level block = STALE_BLOCK (the original regression class). Different
    signature + different top-level block = a real re-execution, the
    legitimate BLOCK_MOVED path.

    The signature hashes only the ``metadata.papermill`` field of each cell
    (when present), in cell order. Cells without a ``metadata.papermill``
    field contribute nothing -- both legs of a comparison share the same
    empty-list contribution, so the signature stays stable across a
    block-removal operation that targets only the top-level field.
    """
    parts = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        cell_pm = (cell.get("metadata") or {}).get("papermill")
        if cell_pm is None:
            continue
        parts.append(json.dumps(cell_pm, sort_keys=True, ensure_ascii=False))
    return "\n".join(parts)


def cell_papermill_blocks(nb):
    """Per-cell papermill block serializations, in code-cell order.

    Returns a list of ``json.dumps(...)`` strings, one per code cell that
    carries a ``metadata.papermill`` block. Cells without a per-cell block
    are skipped (the indices do NOT align with code-cell positions; a
    parallel walk with ``exec_evidence`` is required to align them). A
    re-execution rewrites every entry together with the top-level block;
    a hand-rewrite of the top-level block alone leaves the list identical
    to the base. The FORGED_BLOCK partial case (c2187-ask, refine #21299)
    is one entry differing on outputs but identical to base. The function
    is paired with ``_per_cell_forged`` in ``classify``.
    """
    parts = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        cell_pm = (cell.get("metadata") or {}).get("papermill")
        if cell_pm is None:
            continue
        parts.append(json.dumps(cell_pm, sort_keys=True, ensure_ascii=False))
    return parts


# --- sanctioned output strips -------------------------------------------
# Three pre-commit hooks in .pre-commit-config.yaml rewrite committed cell
# outputs without any re-execution. Two of them touch the code-cell outputs
# this gate hashes:
#
#   strip-probeaddresses-banner -> strip_probe_banner.py --apply
#   strip-dotnet-nuget-ext      -> strip_machine_paths.py --apply
#
# (The third, scrub-papermill-paths, rewrites metadata.papermill and is
# therefore already visible to the block comparison, not to exec_evidence.)
#
# Both hooks exist precisely BECAUSE re-execution does not fix what they
# remove: the strip-dotnet-nuget-ext description says the message "is
# re-injected at every kernel re-execution ... so the durable fix is this
# output-only pre-commit strip - no source change, execution_count
# preserved". A branch that merely touches a markdown cell of a notebook
# still carrying such a leak therefore gets its OUTPUTS rewritten at commit
# time, by an organ of this very repository - and would be judged as riding
# a stale block, which it is not.
#
# The test is exact, not heuristic: the base blob is passed through the same
# tools, and the result must equal the head evidence BYTE FOR BYTE. A
# hand-edited output does not survive it, because no strip tool produces a
# hand-edit.
STRIP_TOOLS = ("strip_machine_paths", "strip_probe_banner")


def stripped_evidence(content):
    """exec_evidence of `content` after the output-touching strip hooks.

    Returns None when the tools cannot run, so a failure here can only leave
    the caller on its previous (stricter) verdict - never turn a FAIL into a
    PASS by accident.
    """
    handle, tmp = tempfile.mkstemp(suffix=".ipynb")
    os.close(handle)
    try:
        Path(tmp).write_text(content, encoding="utf-8")
        import strip_machine_paths
        import strip_probe_banner
        strip_machine_paths.strip_in_place(tmp)
        strip_probe_banner.strip_banner_in_place(tmp)
        return exec_evidence(json.loads(Path(tmp).read_text(encoding="utf-8")))
    except Exception:
        return None
    finally:
        try:
            os.unlink(tmp)
        except OSError:
            pass


# --- sanctioned text repair: UTF-8/cp1252 double encoding (#23021) ------
# A notebook can be written after being read back as cp1252 and re-encoded
# as UTF-8: every accented character and every em dash becomes a visible
# artefact ('e' acute -> 'A-tilde copyright', em dash -> 'a-circumflex
# euro right-double-quote'). The corruption is FILE-WIDE - it reaches the
# committed outputs as well as the sources. The issue's repair is the
# deterministic reversion `s.encode("cp1252").decode("utf-8")`, applied per
# source element and per output string, with execution_count preserved.
#
# That repair changes exec_evidence while leaving metadata.papermill
# untouched, which is exactly the signature of a fabricated output: the run
# that produced the outputs did happen, it simply wrote them corrupted. The
# exemption below separates the two cases the way OUTPUTS_STRIPPED does:
# the base blob's output strings are passed through the SAME reversion, and
# the result must equal the head evidence byte for byte. A fabricated
# output cannot survive it, because the reversion of a base string never
# changes a digit or a floating-point value.
ENCODING_REPAIR = "OUTPUTS_ENCODING_REPAIRED"


def revert_cp1252(text):
    """cp1252 reversion of one decoded string, or the string itself.

    Raising is the honesty guard, not an accident: a string carrying a real
    accented character encodes to a byte that is not a UTF-8 start byte, so
    `decode("utf-8")` fails and the string is returned untouched. Mixed and
    partially corrupted strings are therefore left alone rather than
    approximated.
    """
    try:
        return text.encode("cp1252").decode("utf-8")
    except (UnicodeEncodeError, UnicodeDecodeError):
        return text


def revert_strings(node):
    """Apply revert_cp1252 to every string nested in `node`."""
    if isinstance(node, str):
        return revert_cp1252(node)
    if isinstance(node, list):
        return [revert_strings(item) for item in node]
    if isinstance(node, dict):
        return {key: revert_strings(value) for key, value in node.items()}
    return node


def encoding_repaired_evidence(content):
    """exec_evidence of `content` after the sanctioned cp1252 reversion.

    Only the outputs are rewritten; execution_count and cell sources are out
    of the evidence this gate hashes. Returns None when the blob cannot be
    parsed, so a failure here can only leave the caller on its previous
    (stricter) verdict - never turn a FAIL into a PASS by accident.
    """
    try:
        nb = json.loads(content)
        repaired = []
        for cell in nb.get("cells", []):
            if cell.get("cell_type") != "code":
                continue
            repaired.append({**cell,
                             "outputs": revert_strings(cell.get("outputs"))})
        return exec_evidence({"cells": repaired})
    except Exception:
        return None


def state_at_base(base, path, cwd=None):
    """(status, evidence, block, ev_stripped, cell_sig, cell_pms, ev_enc) at base.

    Returns ("ABSENT", None, None, None, None, None, None) when the file does
    not exist at base and ("PARSE_ERROR", None, None, None, None, None, None)
    on invalid JSON.
    """
    content = git("show", f"{base}:{path}", cwd=cwd)
    if content is None:
        return "ABSENT", None, None, None, None, None, None
    try:
        nb = json.loads(content)
    except Exception:
        return "PARSE_ERROR", None, None, None, None, None, None
    # Lazy: the strip tools cost ~150 ms per notebook and are only ever
    # consulted on the STALE_BLOCK branch, which is the rare one. A thunk
    # keeps a 200-notebook PR at the cost it had before this exemption.
    return ("OK", exec_evidence(nb), papermill_block(nb),
            lambda: stripped_evidence(content), cell_papermill_signature(nb),
            cell_papermill_blocks(nb),
            lambda: encoding_repaired_evidence(content))


def state_at_head(path, cwd=None):
    """(status, evidence, block, ev_stripped, cell_sig, cell_pms, ev_enc) at head."""
    try:
        nb = json.loads((Path(cwd or ".") / path).read_text(encoding="utf-8"))
    except Exception:
        return "PARSE_ERROR", None, None, None, None, None, None
    return "OK", exec_evidence(nb), papermill_block(nb), None, \
        cell_papermill_signature(nb), cell_papermill_blocks(nb), None


def classify(base_state, head_state):
    """Verdict of one changed notebook. Regression iff stale or forged block ridden."""
    b_status, b_ev, b_block, b_ev_stripped, b_cell_sig, b_cell_pms, b_ev_enc = \
        base_state
    h_status, h_ev, h_block, _, h_cell_sig, h_cell_pms, _ = head_state
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
    if b_ev_stripped is not None and h_ev == b_ev_stripped():
        # The whole delta is what the sanctioned output-strip hooks produce.
        # No run happened, so the block is not stale - it still describes the
        # execution that produced these outputs, minus a machine-path leak
        # that no re-execution could have removed.
        return "OUTPUTS_STRIPPED", False
    if b_ev_enc is not None and h_ev == b_ev_enc():
        # The whole delta is the sanctioned cp1252 reversion of #23021: the
        # base outputs were the corrupted rendering of the very strings the
        # head carries. No run happened, so the block is not stale - it still
        # describes the execution that produced these outputs, minus the
        # file-wide encoding corruption no re-execution could have repaired
        # (a fresh run would rewrite the numbers too, which is why the issue
        # mandates the reversion instead).
        return ENCODING_REPAIR, False
    if h_block == b_block:
        # Outputs changed but the block is byte-identical: it describes the
        # previous run, not the one that produced the committed outputs.
        return "STALE_BLOCK", True
    # h_block != b_block at this point (top-level block changed). A real
    # papermill re-execution also rewrites every per-cell papermill block;
    # a hand-rewrite of the top-level block alone leaves the per-cell
    # signature identical to the base. #21229/#21230/#21232 measured on
    # 18/10 all rode that path. #21232: 16.0 s exactly, microsecond-identical
    # end_time, no cell-level block touched - the FORGED_BLOCK class.
    # The guard requires b_cell_pms to be non-empty: a notebook with a
    # top-level metadata.papermill but NO per-cell blocks (legacy papermill
    # versions, or papermill run that pre-dates the per-cell block write)
    # cannot be a hand-rewrite of the top-level -- the per-cell layer is
    # simply absent. Falling through to BLOCK_MOVED preserves the legacy
    # green path for such notebooks (issue #11155 contract). #11155
    # regression reproduced on test_block_moved_passes without this guard
    # (Hermes review c2190, run 39179203301).
    if (h_cell_sig == b_cell_sig and b_block is not None
            and b_cell_pms):
        return "FORGED_BLOCK", True
    # Per-cell check (c2187-ask, refine #21299): the global signature above
    # is the all-identical case. Mixed cases -- a hand-rewriter that touched
    # the top-level AND some per-cell blocks but left at least one changed-
    # output cell's per-cell block byte-identical to the base -- are
    # FORGED_BLOCK too. A real re-execution rewrites every per-cell block
    # together with the top-level one. #21345.
    if (b_block is not None and b_cell_pms is not None
            and h_cell_pms is not None
            and _per_cell_forged(b_ev, h_ev, b_cell_pms, h_cell_pms)):
        return "FORGED_BLOCK", True
    return "BLOCK_MOVED" if b_block is not None else "BLOCK_ADDED", False


def _per_cell_forged(b_ev, h_ev, b_cell_pms, h_cell_pms):
    """True iff a cell with changed output carries an identical per-cell block.

    ``b_ev`` and ``h_ev`` are the exec_evidence strings (one line per code
    cell). ``b_cell_pms`` and ``h_cell_pms`` are parallel lists of
    serialized per-cell ``metadata.papermill`` blocks, where the i-th entry
    is the block of the i-th code cell that carries one (cells without a
    per-cell block are skipped). A real papermill re-execution rewrites
    every such block together with the top-level one; a hand-rewrite of
    the top-level block alone leaves them identical. The global signature
    check is the special case where every entry is identical; this helper
    catches the partial case.
    """
    b_lines = (b_ev or "").split("\n")
    h_lines = (h_ev or "").split("\n")
    b_idx = 0
    h_idx = 0
    # Walk code cells in order. b_lines[i] / h_lines[i] are the per-cell
    # signatures; b_cell_pms[b_idx] / h_cell_pms[h_idx] are the per-cell
    # papermill blocks of those code cells that carry one (advancing
    # independently on each side).
    for i in range(max(len(b_lines), len(h_lines))):
        b_line = b_lines[i] if i < len(b_lines) else None
        h_line = h_lines[i] if i < len(h_lines) else None
        b_pm = b_cell_pms[b_idx] if b_idx < len(b_cell_pms) else None
        h_pm = h_cell_pms[h_idx] if h_idx < len(h_cell_pms) else None
        # If the cell has a per-cell papermill block in BOTH sides AND
        # those blocks are byte-identical AND the cell's outputs changed,
        # it's the FORGED_BLOCK signal. We require a per-cell block on
        # both sides because a cell newly given a per-cell block by a
        # legitimate re-execution is the BLOCK_MOVED path.
        if (b_pm is not None and h_pm is not None
                and b_line != h_line and b_pm == h_pm):
            return True
        if b_pm is not None:
            b_idx += 1
        if h_pm is not None:
            h_idx += 1
    return False


def ratchet(base, cwd=None):
    """One record per changed notebook; regression = stale block ridden."""
    # Resolved once: the file list and the base-side blobs must be read at
    # the SAME point, or a notebook the branch AND the base both touched is
    # compared against the base's newer version.
    base = resolve_base(base, cwd=cwd)
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
            verdict = r["verdict"]
            if verdict == "FORGED_BLOCK":
                print(f"::error file={r['notebook']}::top-level "
                      f"metadata.papermill block changed but the per-cell "
                      f"papermill blocks are identical to {args.base} - a "
                      f"real papermill run rewrites both layers. The "
                      f"top-level block was hand-rewritten. Re-execute the "
                      f"notebook via an executor that rewrites both, or "
                      f"revert the hand-rewrite", file=sys.stderr)
            else:
                print(f"::error file={r['notebook']}::outputs/execution_count "
                      f"changed but the metadata.papermill block is identical to "
                      f"{args.base} - the block describes the previous run. "
                      f"Re-execute the notebook via an executor that rewrites the "
                      f"block, or remove the block", file=sys.stderr)
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
