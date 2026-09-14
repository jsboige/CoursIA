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
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

EXCLUDE_MARKERS = ("/.ipynb_checkpoints/", "/archive/", "/_output/",
                   "/research/")


def git(*args, cwd=None):
    try:
        out = subprocess.run(["git", *args], cwd=cwd, capture_output=True,
                             encoding="utf-8", errors="replace", check=False)
    except OSError:
        return None
    return out.stdout if out.returncode == 0 else None


def resolve_base(base, cwd=None):
    out = git("merge-base", base, "HEAD", cwd=cwd)
    return out.strip() if out and out.strip() else base


def changed_notebooks(base, cwd=None):
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


def read_blob(commit_ref, nb_path, cwd=None):
    """Read a notebook JSON from a git blob (returns None if absent)."""
    out = git("show", f"{commit_ref}:{nb_path}", cwd=cwd)
    if out is None:
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


def float_signatures(nb):
    """For each code cell, return a tuple of float-array signatures.

    Two cells with identical signatures, modulo whitespace and rounding
    within 1 ULP, are considered equivalent for drift detection. We do
    not attempt numerical comparison (that is a different organ, see
    check_output_collapse.py and check_output_failure_text.py) — this
    gate only flags textual-shape changes that are characteristic of a
    NumPy 1.x vs 2.x repr change or a cmath exp precision drift.
    """
    sigs = []
    for cell in nb.get("cells", []):
        if cell.get("cell_type") != "code":
            continue
        text_parts = []
        for out in cell.get("outputs", []):
            if "text" in out and isinstance(out["text"], list):
                text_parts.extend(out["text"])
            elif "data" in out and "text/plain" in out["data"]:
                text_parts.append(out["data"]["text/plain"])
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


def diff_signatures(base_sig, head_sig):
    """Return a list of cell indices whose float signature changed."""
    diffs = []
    n = max(len(base_sig), len(head_sig))
    for i in range(n):
        b = base_sig[i] if i < len(base_sig) else ()
        h = head_sig[i] if i < len(head_sig) else ()
        if b != h:
            diffs.append(i)
    return diffs


def main():
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("base_ref")
    p.add_argument("--json", action="store_true",
                   help="emit findings as JSON on stdout")
    p.add_argument("--explain", action="store_true",
                   help="annotate each finding with probable cause")
    args = p.parse_args()

    base = resolve_base(args.base_ref)
    notebooks = changed_notebooks(base)
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
        sig_diffs = diff_signatures(base_sig, head_sig)
        if kernel_diffs or sig_diffs:
            finding = {
                "notebook": nb_path,
                "kernel_diffs": kernel_diffs,
                "signature_drift_cells": sig_diffs,
                "base_kernel": base_kernel,
                "head_kernel": head_kernel,
            }
            if args.explain:
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

    if args.json:
        print(json.dumps({"findings": findings, "base": base}, indent=2))
    else:
        if not findings:
            print(f"OK: 0 kernel-drift regression across "
                  f"{len(notebooks)} changed notebooks (base={base}).")
            return 0
        print(f"FAIL: kernel-drift regression in {len(findings)} notebook(s):",
              file=sys.stderr)
        for f in findings:
            print(f"  {f['notebook']}", file=sys.stderr)
            for k in f["kernel_diffs"]:
                print(f"    - {k}", file=sys.stderr)
            if f["signature_drift_cells"]:
                print(f"    - float-signature drift on cells: "
                      f"{f['signature_drift_cells']}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(0 if main() == 0 or main() == None else 1)
