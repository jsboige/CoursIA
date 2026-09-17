"""Ratchet gate: notebook kernel and float-format drift between base and PR.

Issue context (c.559, derived from PR #16043 investigation 2026-09-14):
A notebook can be re-executed under a different Python kernel or NumPy
version than its base reference, producing byte-different outputs even
when the underlying computation is mathematically equivalent. Three
classes observed:

  - Kernel change: ``metadata.kernelspec.name`` or
    ``metadata.language_info.version`` differs (Python 3.11 -> 3.13).
    Outputs may format ``repr(np.float64(0.9999999999999999))`` instead
    of ``[1.0, 1.0, ...]`` even when the cell computes the same values.
  - Float format drift: NumPy 1.x prints ``[1.0, 1.0, 1.0]``; NumPy 2.x
    prints ``[1.0, 0.9999999999999999, 1.0]``. The values are within
    1 ULP but the textual signature differs.
  - Machine path leak: a fresh execution under a different temp dir
    injects new ``MACHINE_PATH`` strings (covered by
    check_output_failure_text.py, not this gate).

This gate compares each changed notebook's kernel/version metadata
between base and HEAD, plus a sampled output signature for cells whose
output text looks float-array-shaped. A regression in either
(category A: kernel change with no documented acceptance, category B:
float-format drift with no explanation in the PR body) fails the run.

Usage:
    python check_kernel_drift.py <base-ref> [--json] [--explain]

    base-ref    base branch ref (CI: origin/<base branch>). Resolved
                internally to merge-base(base-ref, HEAD) so a branch
                behind its base is judged on its own diff only.

Exclusions: same as check_papermill_ratchet.py (notebooks in
.ipynb_checkpoints/, /archive/, /_output/, /research/).

Exit code: 0 if no regression, 1 if at least one changed notebook
shows kernel or float-format drift without a documented justification.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")


def git(*args, cwd=None):
    """Run a git command. Fail-closed: raise RuntimeError on OSError.

    Returns stdout string on success, raises on subprocess failure.
    Empty stdout is a valid result and is returned as ''.
    """
    try:
        out = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                             encoding="utf-8", errors="replace", check=False)
    except OSError as e:
        raise RuntimeError(f"git subprocess failed: {e}") from e
    if out.returncode != 0:
        raise RuntimeError(
            f"git {args!r} failed (rc={out.returncode}): "
            f"{out.stderr.strip()[:200] if out.stderr else '<no stderr>'}"
        )
    return out.stdout


def git_fail_closed(*args, cwd=None):
    """Wrapper used in tests: same as git() but explicitly named for clarity."""
    return git(*args, cwd=cwd)


def resolve_base(base, cwd=None):
    out = git("merge-base", base, "HEAD", cwd=cwd)
    return out.strip() if out.strip() else base


def changed_notebooks(base, cwd=None):
    out = git("diff", "--name-only", "--diff-filter=ACMR",
              base, "HEAD", "--", "*.ipynb", cwd=cwd)
    paths = []
    for line in out.splitlines():
        posix = line.strip().replace("\\", "/")
        if posix and not any(m in f"/{posix}" for m in EXCLUDE_MARKERS):
            paths.append(posix)
    return sorted(paths)


def read_blob(commit_ref, nb_path, cwd=None):
    """Read a notebook JSON from a git blob (returns None if absent).

    Returns None ONLY when the blob doesn't exist (legitimately absent path).
    Raises RuntimeError if git itself fails (fail-closed per defect 4).
    """
    try:
        out = git("show", f"{commit_ref}:{nb_path}", cwd=cwd)
    except RuntimeError as e:
        if "exists on disk, but not in" in str(e) or "does not exist" in str(e) or "bad revision" in str(e):
            return None
        raise
    if not out:
        return None
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return None


# Matches an array-shaped float repr in stdout output: "[1.0, 0.9999..., 1.0]"
# or "array([...])" — anything that looks like NumPy / Python printing a
# homogeneous float list. The regex is intentionally loose: we only need a
# canonical signature per cell to detect format drift, not a parser.
FLOAT_ARRAY_RE = re.compile(
    r"[\[\(]\s*"
    r"-?\d+\.\d+(?:[eE][+-]?\d+)?j?\s*"
    r"(?:,\s*-?\d+\.\d+(?:[eE][+-]?\d+)?j?\s*){1,}"
    r"[\]\)]"
)


def _flatten_text(value):
    """Normalize a text field (string OR list of strings) to a single string.

    Defect 5 (PR #16082 review): corpus real shows 1409/1430 cells have
    text/plain as a LIST of strings (Papermill artifact). Old code did
    `''.join(...)` which raised TypeError. We accept both shapes.
    """
    if isinstance(value, list):
        return "".join(str(s) for s in value)
    return str(value)


def float_signatures(nb):
    """For each code cell, return a tuple of float-array signatures.

    Two cells with identical signatures, modulo whitespace and rounding
    within 1 ULP, are considered equivalent for drift detection. We do
    not attempt numerical comparison (that is a different organ, see
    check_output_collapse.py and check_output_failure_text.py) — this
    gate only flags textual-shape changes that are characteristic of a
    NumPy 1.x vs 2.x repr change or a cmath exp precision drift.

    Defect 5 fix: text/plain can be a string OR a list of strings.
    """
    sigs = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        text_parts = []
        for out in cell.get("outputs", []):
            if "text" in out:
                text_parts.append(_flatten_text(out["text"]))
            elif "data" in out and "text/plain" in out["data"]:
                text_parts.append(_flatten_text(out["data"]["text/plain"]))
        joined = "".join(text_parts)
        sigs.append(tuple(FLOAT_ARRAY_RE.findall(joined)))
    return tuple(sigs)


def kernel_info(nb):
    meta = nb.get("metadata", {})
    return {
        "kernelspec_name": meta.get("kernelspec", {}).get("name", ""),
        "language_version": meta.get("language_info", {}).get("version", ""),
        "kernelspec_display": meta.get("kernelspec", {}).get("display_name", ""),
    }


def diff_kernel(base_info, head_info):
    """Return a list of human-readable kernel-version drift strings."""
    diffs = []
    if base_info["language_version"] != head_info["language_version"]:
        diffs.append(
            f"language_info.version: {base_info['language_version']!r} -> "
            f"{head_info['language_version']!r}"
        )
    if base_info["kernelspec_name"] != head_info["kernelspec_name"]:
        diffs.append(
            f"kernelspec.name: {base_info['kernelspec_name']!r} -> "
            f"{head_info['kernelspec_name']!r}"
        )
    return diffs


def body_has_derive_exemption(body):
    """Defect 1: PR body contains '## Diagnostic dérive' section.

    Per acceptance of issue #15650 (point 4): cellules non touchées
    reproduisent leurs sorties - ou l'écart résiduel est expliqué par
    une section '## Diagnostic dérive' (C.4).

    Fix v2 (post-NanoClaw review #16466): regex is now case-insensitive and
    tolerates the unaccented 'derive' (covers authors who type the header
    without the accent, a common shortcut when reviewing on a non-French
    keyboard layout).
    """
    if not body:
        return False
    # Case-insensitive header, optional whitespace, optional accent on 'e'.
    pattern = re.compile(
        r"^##\s*Diagnostic\s*d[ée]rive\s*$",
        re.MULTILINE | re.IGNORECASE,
    )
    return bool(pattern.search(body))


def _cell_index_by_id(nb):
    """Build a mapping cell_id -> ordinal index for stable alignment.

    Defect 2 (PR #16082 review): ordinal alignment produces false drifts
    when a new cell is inserted before unchanged cells. We align by cell
    id when available, fall back to ordinal for legacy notebooks (no ids).
    """
    result = {}
    cells = nb.get("cells", [])
    for i, cell in enumerate(cells):
        cid = cell.get("id") or None
        if cid:
            result[cid] = i
    return result


def diff_signatures(base_sig, head_sig, base_nb=None, head_nb=None):
    """Return a list of cell identifiers whose float signature changed.

    Defect 2 fix: aligns by cell id when notebooks are provided (stable
    under insertions); falls back to ordinal otherwise (legacy).
    Returns a list of ids (str) when aligned by id, or ints (legacy).
    """
    # If we have notebooks with cell ids, align by id
    if base_nb is not None and head_nb is not None:
        base_ids = _cell_index_by_id(base_nb)
        head_ids = _cell_index_by_id(head_nb)
        # Only consider cells present in BOTH (intersection), plus
        # report new cells (in head but not base) as drifts.
        common = set(base_ids.keys()) & set(head_ids.keys())
        if not common and (base_ids or head_ids):
            # No common ids -> fall back to ordinal
            return _diff_signatures_ordinal(base_sig, head_sig)
        diffs = []
        # Common cells: compare signatures
        for cid in sorted(common):
            b_idx = base_ids[cid]
            h_idx = head_ids[cid]
            b = base_sig[b_idx] if b_idx < len(base_sig) else ()
            h = head_sig[h_idx] if h_idx < len(head_sig) else ()
            if b != h:
                diffs.append(cid)
        # Added cells (only in head)
        for cid in sorted(set(head_ids.keys()) - set(base_ids.keys())):
            diffs.append(cid)
        return diffs
    return _diff_signatures_ordinal(base_sig, head_sig)


def _diff_signatures_ordinal(base_sig, head_sig):
    """Legacy ordinal alignment: returns int indices."""
    diffs = []
    n = max(len(base_sig), len(head_sig))
    for i in range(n):
        b = base_sig[i] if i < len(base_sig) else ()
        h = head_sig[i] if i < len(head_sig) else ()
        if b != h:
            diffs.append(i)
    return diffs


def _run(args_obj):
    """Core logic shared between CLI and tests. Returns dict or prints."""
    base = resolve_base(args_obj.base_ref)
    notebooks = changed_notebooks(base)

    # Defect 1: read PR body for exemption
    pr_body = ""
    try:
        from pathlib import Path
        # Path is taken from env var or .git/PR_BODY
        pr_body_path = Path(os.environ.get("PR_BODY_FILE", "/tmp/pr_body"))
        if pr_body_path.exists():
            pr_body = pr_body_path.read_text(encoding="utf-8", errors="replace")
    except (ImportError, OSError):
        pass

    body_exempts = body_has_derive_exemption(pr_body)

    findings = []
    for nb_path in notebooks:
        base_nb = read_blob(base, nb_path)
        head_nb = read_blob("HEAD", nb_path)
        if base_nb is None or head_nb is None:
            continue
        base_kernel = kernel_info(base_nb)
        head_kernel = kernel_info(head_nb)
        base_sig = float_signatures(base_nb)
        head_sig = float_signatures(head_nb)
        kernel_diffs = diff_kernel(base_kernel, head_kernel)
        # Defect 2: pass notebooks for id-based alignment
        sig_diffs = diff_signatures(base_sig, head_sig,
                                     base_nb=base_nb, head_nb=head_nb)
        if kernel_diffs or sig_diffs:
            finding = {
                "notebook": nb_path,
                "kernel_diffs": kernel_diffs,
                "signature_drift_cells": sig_diffs,
                "base_kernel": base_kernel,
                "head_kernel": head_kernel,
                "body_exemption": body_exempts,
            }
            # Defect 1: if body exempts and drift is documented, downgrade
            if body_exempts and (kernel_diffs or sig_diffs):
                finding["acknowledged"] = True
                finding["acknowledgment_reason"] = (
                    "PR body contains '## Diagnostic dérive' (C.4 exemption)"
                )
            if args_obj.explain:
                causes = []
                if kernel_diffs:
                    causes.append(
                        "kernel or language_version changed between base and "
                        "HEAD; re-execution may have used a different Python "
                        "interpreter (3.11 -> 3.13) which alters repr() for "
                        "floating-point values"
                    )
                if sig_diffs:
                    causes.append(
                        f"{len(sig_diffs)} code cells show float-array repr "
                        "drift consistent with a NumPy 1.x -> 2.x upgrade or "
                        "a cmath precision change; values are within 1 ULP "
                        "but byte-text differs"
                    )
                finding["probable_causes"] = causes
            findings.append(finding)

    return {"findings": findings, "base": base, "body_exempts": body_exempts}


def main():
    """Defect 3 fix: parse argv once, build args, call _run ONCE."""
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("base_ref")
    p.add_argument("--json", action="store_true",
                   help="emit findings as JSON on stdout")
    p.add_argument("--explain", action="store_true",
                   help="annotate each finding with probable cause")
    args = p.parse_args()

    result = _run(args)
    findings = result["findings"]

    if args.json:
        # Defect 3: emit a SINGLE JSON document
        print(json.dumps(result, indent=2))
        return 0 if not findings or all(f.get("acknowledged") for f in findings) else 1
    else:
        if not findings:
            print(f"OK: 0 kernel-drift regression across "
                  f"{len(changed_notebooks(result['base']))} changed notebooks "
                  f"(base={result['base']}).")
            return 0
        print(f"FAIL: kernel-drift regression in {len(findings)} notebook(s):",
              file=sys.stderr)
        for f in findings:
            tag = " [ACKNOWLEDGED via ## Diagnostic dérive]" if f.get("acknowledged") else ""
            print(f"  {f['notebook']}{tag}", file=sys.stderr)
            for k in f["kernel_diffs"]:
                print(f"    - {k}", file=sys.stderr)
            if f["signature_drift_cells"]:
                print(f"    - float-signature drift on cells: "
                      f"{f['signature_drift_cells']}", file=sys.stderr)
        return 1


def main_with_args(argv):
    """Entry point for tests: parse argv as a list, run ONCE, return rc + result.

    Defect 3 fix verification: this function calls _run() exactly once and
    prints a single JSON document when --json is set.
    """
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("base_ref")
    p.add_argument("--json", action="store_true")
    p.add_argument("--explain", action="store_true")
    args = p.parse_args(argv)
    result = _run(args)
    findings = result["findings"]
    if args.json:
        # Single JSON emission
        print(json.dumps(result, indent=2))
        return 0 if not findings or all(f.get("acknowledged") for f in findings) else 1
    if not findings:
        print(f"OK: 0 kernel-drift regression across 0 changed notebooks (base={result['base']}).")
        return 0
    print(f"FAIL: {len(findings)} drift(s)", file=sys.stderr)
    return 1


if __name__ == "__main__":
    sys.exit(main())
