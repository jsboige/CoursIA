"""Source-output ratchet: changed code must not ride unchanged outputs.

Issue #13562. Mirror image of check_papermill_ratchet.py: that gate catches
new outputs riding an old ``metadata.papermill`` block; this one catches a
changed code SOURCE riding byte-identical outputs. It is literally rule C.2
of CLAUDE.md - "modify a code cell = re-execute before commit" - which had
no organ: check_exec_sequence and check_exec_ratchet only look at
execution_count (untouched here), and check_papermill_ratchet's
precondition (outputs changed) is false in exactly this case.

Founding measurement (issue #13562, PR #13550): three cells with modified
source and byte-identical outputs on a PR that was green end to end. The
committed outputs had been produced by a source that no longer existed.

Verdict per CODE cell of every .ipynb changed between BASE and HEAD
(cells are indexed over ALL cells, the convention the issue's evidence
uses):

    source changed AND outputs byte-identical AND outputs non-empty
        -> STALE_OUTPUT (regression: the output describes a source
           that no longer exists)
    everything else -> clean

Deliberate design choices from the issue body:
- outputs empty (``[]``) never fails: that is H.3's turf (never-executed),
  there is nothing to go stale.
- a comment-only edit FAILS all the same: statically indistinguishable
  from a semantic change, and a re-execution is cheap; the escape door
  below is the relief valve, not a heuristic.
- notebooks added by the PR (no base blob) are skipped: their execution
  evidence is notebook-execution-required.yml's job (H.3).
- cells not executable on any worker machine reuse validate_pr_notebooks'
  exemption predicates - Lean kernels and QuantBook/QC-Cloud notebooks -
  never a second parallel list. .NET Interactive is NOT exempt: it runs
  on every worker machine (same rationale as ALLOW_NULL_EXEC_COUNT_KERNELS
  excluding .NET in validate_pr_notebooks.py).

Escape door (case "cannot change the output" and GPU notebooks whose
re-exec is routed to another machine): a written sentence in the PR body,
per cell, same mechanics as the repo's other lifts - a sentence, an
author, an hour; not a label, not a global skip:

    Source-output ratchet: [12] exempte -- comment-only edit, unchanged
    output expected.

An optional notebook qualifier disambiguates multi-notebook PRs:

    Source-output ratchet: MyIA.AI.Notebooks/Foo.ipynb: [12] exempte -- ...

A bare ``[12]`` matches any notebook of the PR.

Cell pairing: code cells pair by their nbformat ``id`` when the base
notebook carries ids, so inserted cells (fresh ids, unpaired) or shifted
cells (stable ids, paired to their real base partner) no longer
fabricate source-changed/outputs-identical pairs on enrichment PRs
(#14297). Legacy notebooks whose base carries no id pair by CONTENT:
exact source matches first (a moved-unmodified cell pairs with its own
base copy), then a difflib fuzzy pass (ratio >= 0.75, greedy) so a
moved-AND-modified cell still confronts its own base version; a head
cell matching nothing stays UNPAIRED - never a fabricated stale pair.

Usage:
    python check_source_output_ratchet.py <base-ref> [--json] [--body-file F]

    base-ref    base branch ref (CI: origin/<base branch>). Resolved
                internally to merge-base(base-ref, HEAD) like the
                papermill ratchet, so a branch behind its base is judged
                on its own diff only.
    --body-file PR body text carrying per-cell exemptions (optional).

Head state reads the working tree (in CI the checkout IS the head), base
state reads the blob via ``git show``. Exit code 1 iff at least one
stale-output regression survives the exemptions.
"""

import argparse
import difflib
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from validate_pr_notebooks import (  # noqa: E402
    ALLOW_NULL_EXEC_COUNT_KERNELS,
    QC_CLOUD_PATHS,
    QUANTBOOK_PATTERN,
)

# Same exclusions as check_papermill_ratchet.py / check_exec_ratchet.py:
# archived, papermill-output and research copies are not deliverable
# notebooks.
EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")

# Kernels no worker machine can execute (Lean via lean4_jupyter/alectryon
# is advisory everywhere else in the repo). .NET Interactive is
# deliberately absent - see module docstring.
NON_EXECUTABLE_KERNELS = set(ALLOW_NULL_EXEC_COUNT_KERNELS) | {"lean"}

# Fuzzy-pairing floor for legacy bases without ids (#14297): below it a
# head code cell stays UNPAIRED rather than confronting a base cell it
# merely resembles. High on purpose - two distinct C.1 stubs share enough
# boilerplate that a lax floor would re-fabricate the exact stale pair
# the content pairing exists to kill.
FUZZY_PAIR_RATIO = 0.75

# "Source-output ratchet: [12] exempte" / "Source-output ratchet:
# Path/To.ipynb: [12] exempte"
_EXEMPT_RE = re.compile(
    r"Source-output ratchet:\s*(?:(?P<path>[^:\[\n]+?):\s*)?"
    r"\[(?P<idx>\d+)\]\s*exempte",
    re.IGNORECASE,
)


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

    The gate must judge what the branch CHANGED, not how far behind it is
    (measured on #11528: 15 phantom changed notebooks against origin/main
    vs 1 against the merge base). Same rationale as the papermill ratchet.
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


def canonical_source(cell):
    """Canonical serialization of a cell's source lines."""
    return "".join(cell.get("source") or [])


def canonical_outputs(cell):
    """Canonical serialization of a cell's outputs."""
    return json.dumps(cell.get("outputs") or [], sort_keys=True,
                      ensure_ascii=False)


def notebook_kernel(nb):
    """kernelspec.name of a notebook, or None."""
    return ((nb.get("metadata") or {}).get("kernelspec") or {}).get("name")


def notebook_exempt_reason(path, nb):
    """Why a whole notebook is out of the ratchet's reach, or None.

    Predicates are validate_pr_notebooks' own (no second list): Lean
    kernels cannot run on a worker, QuantBook notebooks only execute in
    QC Cloud. The QuantBook check tests the SOURCE, not the path - the
    path fast-path alone left 16 notebooks out (see #8056).
    """
    kernel = notebook_kernel(nb)
    if kernel in NON_EXECUTABLE_KERNELS:
        return "kernel"
    posix = path.replace("\\", "/")
    if any(posix.startswith(p) or f"/{p}" in f"/{posix}"
           for p in QC_CLOUD_PATHS):
        return "qc_path"
    if QUANTBOOK_PATTERN.search(json.dumps(nb, ensure_ascii=False)):
        return "quantbook"
    return None


def parse_body_exemptions(body_text):
    """Set of (path-or-None, cell-index) lifted by the PR body."""
    lifted = set()
    if not body_text:
        return lifted
    for m in _EXEMPT_RE.finditer(body_text):
        path = m.group("path")
        if path:
            path = path.strip().replace("\\", "/").rstrip(":").strip()
        lifted.add((path, int(m.group("idx"))))
    return lifted


def _pair_by_content(base_cells, head_cells):
    """Content-based code-cell pairing for legacy bases without ids.

    Two passes over canonical sources. Exact pass first: a cell that only
    MOVED pairs with its own byte-identical base copy (the #14297 FP class
    - enrichment insertions shift indices, positional pairing then
    confronted unrelated C.1 stubs whose uniform outputs are identical).
    Fuzzy pass second (difflib ratio, descending, greedy): a MOVED AND
    MODIFIED cell still confronts its own base version - without it, the
    fallback would disarm the guard on the very PRs it polices. A head
    cell with no partner in either pass stays unpaired.
    """
    base_code = [(j, canonical_source(c))
                 for j, c in enumerate(base_cells)
                 if c.get("cell_type") == "code"]
    head_code = [(i, canonical_source(c))
                 for i, c in enumerate(head_cells)
                 if c.get("cell_type") == "code"]
    pairs = {}
    free_base = dict(base_code)
    for i, src in head_code:
        for j, bsrc in free_base.items():
            if src == bsrc:
                pairs[i] = j
                del free_base[j]
                break
    candidates = []
    for i, src in head_code:
        if i in pairs:
            continue
        for j, bsrc in free_base.items():
            ratio = difflib.SequenceMatcher(
                None, bsrc, src, autojunk=False).ratio()
            if ratio >= FUZZY_PAIR_RATIO:
                candidates.append((ratio, i, j))
    for _, i, j in sorted(candidates, key=lambda t: (-t[0], t[1], t[2])):
        if i not in pairs and j in free_base:
            pairs[i] = j
            del free_base[j]
    return pairs


def classify_cells(base_nb, head_nb):
    """Per-code-cell records of one notebook pair, indexed over ALL cells.

    Pure function over parsed notebooks: the tests build fixtures, the CLI
    feeds git blobs. No exemption logic here - the caller applies
    notebook-level and body-level lifts so the classification stays
    reusable for the tier-1 sweep.
    """
    base_cells = base_nb.get("cells", [])
    head_cells = head_nb.get("cells", [])
    # nbformat 4.5+ stamps every cell with a stable `id`: pair by id so an
    # insertion shifts indices but never the pairing itself (#14297 - the
    # positional pairing fabricated 3/3 STALE_OUTPUT on enrichment PRs).
    # A head cell with a fresh id (inserted) has no partner. Legacy
    # notebooks whose base carries no id pair by CONTENT (#14297 fallback:
    # exact then fuzzy) - positional pairing there re-fabricated stale
    # pairs on every enrichment insertion.
    base_by_id = {c.get("id"): c for c in base_cells if c.get("id")}
    use_ids = bool(base_by_id)
    content_pairs = (None if use_ids
                     else _pair_by_content(base_cells, head_cells))
    records = []
    for i, hcell in enumerate(head_cells):
        if hcell.get("cell_type") != "code":
            continue
        bcell = None
        if use_ids:
            hid = hcell.get("id")
            if hid and hid in base_by_id:
                bcell = base_by_id[hid]
            elif not hid:
                bcell = base_cells[i] if i < len(base_cells) else None
        elif content_pairs and i in content_pairs:
            bcell = base_cells[content_pairs[i]]
        if bcell is None or bcell.get("cell_type") != "code":
            records.append({"index": i, "verdict": "UNPAIRED",
                            "regression": False})
            continue
        if canonical_source(bcell) == canonical_source(hcell):
            records.append({"index": i, "verdict": "UNCHANGED",
                            "regression": False})
            continue
        outs_nonempty = bool(hcell.get("outputs"))
        if not outs_nonempty:
            # Nothing to go stale; H.3 owns the never-executed case.
            records.append({"index": i, "verdict": "NO_OUTPUTS",
                            "regression": False})
            continue
        if canonical_outputs(bcell) == canonical_outputs(hcell):
            records.append({"index": i, "verdict": "STALE_OUTPUT",
                            "regression": True})
        else:
            records.append({"index": i, "verdict": "EXECUTED",
                            "regression": False})
    return records


def _parse_notebook(text):
    try:
        return json.loads(text), "OK"
    except Exception:
        return None, "PARSE_ERROR"


def classify_notebook(path, base_nb, head_nb, body_exemptions):
    """Apply notebook-level and body-level lifts to classify_cells."""
    exempt = notebook_exempt_reason(path, head_nb)
    if exempt:
        return [{"verdict": f"EXEMPT_{exempt.upper()}", "regression": False}]
    lifted = {idx for (p, idx) in body_exemptions
              if p is None or p == path.replace("\\", "/")}
    records = []
    for rec in classify_cells(base_nb, head_nb):
        if rec["regression"] and rec["index"] in lifted:
            rec = {"index": rec["index"], "verdict": "EXEMPT_BODY",
                   "regression": False}
        records.append(rec)
    return records


def ratchet(base, cwd=None, body_text=""):
    """One record per changed notebook; regression = stale output ridden."""
    base = resolve_base(base, cwd=cwd)
    body_exemptions = parse_body_exemptions(body_text)
    records = []
    for path in changed_notebooks(base, cwd=cwd):
        content = git("show", f"{base}:{path}", cwd=cwd)
        if content is None:
            records.append({"notebook": path, "verdict": "ADDED",
                            "cells": [], "regressions": 0})
            continue
        base_nb, b_status = _parse_notebook(content)
        try:
            head_nb = json.loads((Path(cwd or ".") / path).read_text(
                encoding="utf-8"))
            h_status = "OK"
        except Exception:
            head_nb, h_status = None, "PARSE_ERROR"
        if b_status != "OK" or h_status != "OK":
            records.append({"notebook": path, "verdict": "PARSE_ERROR",
                            "cells": [], "regressions": 0})
            continue
        cells = classify_notebook(path, base_nb, head_nb, body_exemptions)
        records.append({
            "notebook": path,
            "verdict": "CHANGED",
            "cells": [{"index": c.get("index"), "verdict": c["verdict"],
                       "regression": c["regression"]} for c in cells],
            "regressions": sum(1 for c in cells if c["regression"]),
        })
    return records


def main():
    ap = argparse.ArgumentParser(
        description="Source-output ratchet: changed code must not ride "
                    "unchanged outputs (issue #13562)")
    ap.add_argument("base", help="Base git ref (CI: origin/<base branch>)")
    ap.add_argument("--json", action="store_true", dest="as_json",
                    help="Machine-readable output")
    ap.add_argument("--body-file", dest="body_file", default=None,
                    help="PR body text carrying per-cell exemptions")
    args = ap.parse_args()

    body_text = ""
    if args.body_file:
        try:
            body_text = Path(args.body_file).read_text(encoding="utf-8")
        except OSError as exc:
            print(f"cannot read body file: {exc}", file=sys.stderr)
            sys.exit(2)

    records = ratchet(args.base, body_text=body_text)
    total_reg = sum(r["regressions"] for r in records)
    failing = [r for r in records if r["regressions"]]

    if args.as_json:
        print(json.dumps({
            "base": args.base,
            "changed": len(records),
            "regressions": total_reg,
            "records": records}, ensure_ascii=False, indent=1))
    else:
        print(f"source-output ratchet -- base {args.base}")
        print(f"changed notebooks : {len(records)}")
        print(f"stale cells       : {total_reg}")
        for r in records:
            mark = (f" REGRESSION x{r['regressions']}"
                    if r["regressions"] else "")
            print(f"  {r['verdict']:12s} {r['notebook']}{mark}")
            for c in r["cells"]:
                if c["regression"]:
                    print(f"    [{c['index']}] STALE_OUTPUT")

    if failing:
        for r in failing:
            for c in r["cells"]:
                if c["regression"]:
                    print(f"::error file={r['notebook']}::cell [{c['index']}] "
                          f"source changed but outputs are byte-identical to "
                          f"{args.base} - the committed output was produced "
                          f"by a source that no longer exists. Re-execute, "
                          f"or lift with 'Source-output ratchet: "
                          f"[{c['index']}] exempte -- <reason>' in the PR "
                          f"body", file=sys.stderr)
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
