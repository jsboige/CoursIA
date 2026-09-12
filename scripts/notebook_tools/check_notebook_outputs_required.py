#!/usr/bin/env python3
"""Check every code cell of a Jupyter notebook carries a well-typed `outputs` key.

Cause (c.1084): PR #15631 shipped GameTheory-06g-Bounded-Agents-Lean.ipynb whose
9 code cells were MISSING the `outputs` key entirely (not `outputs: []` empty -
the key was absent from the cell dict). `nbformat` 5.10.4 strict schema
validator rejects this as a hard error:

    Invalid Notebook
    'outputs' is a required property
    Using nbformat v5.10.4 and nbconvert v7.17.1

(Papermill accepted the input with its permissive validator, then ran the
kernel without producing output because of an unrelated kernel-resolution
failure -- the c.1082 fabrication omitted the key from the cell-dict template,
so Papermill never wrote it back. Subsequent checks downstream saw a notebook
that opens in Jupyter, parses as JSON, passes `execution_count is not None`,
and yet is invalid against the schema.)

This guard closes the gap: it walks every notebook, opens the JSON, finds
every code cell, and verifies the `outputs` key is PRESENT and a `list`. Empty
list `[]` is the expected value for a non-executed / stub cell (`execution_count`
null or zero -- the canonical nbformat shape of a not-yet-rendered cell).

Detection discriminants (3, without which the detector lies):

  1. `cell_type == "code"` only -- markdown / raw cells are not in scope;
     their `outputs` absence is structurally correct;
  2. the key MUST be present and a list -- `outputs: []` is PASS (empty is
     valid), `outputs: null` is FAIL (explicit null violates the schema);
  3. non-empty outputs are also PASS: this guard enforces PRESENCE+TYPE, not
     CONTENT. Existing `notebook-execution-required.yml` covers the deeper
     `execution_count != null` / zero-error / C.1 invariants; we complement
     without duplicating.

Exit codes:
    0 -- every code cell carries an `outputs: list` key (PASS)
    1 -- at least one code cell is missing or mis-typed `outputs` (FAIL)
    2 -- error (unreadable notebook, bad arguments)

Usage:
    python check_notebook_outputs_required.py                    # whole repo
    python check_notebook_outputs_required.py --path FILE        # single notebook
    python check_notebook_outputs_required.py --pr-diff BASE HEAD  # PR diff scope
    python check_notebook_outputs_required.py --json             # JSON output
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Mirrored with check_latex_control_chars.py EXCLUDED_DIRS / SUFFIX.
# The probe-archive + papermill output dirs hold notebooks that are not part
# of the corpus a PR is changing; scanning them makes the guard noisy and
# extends CI time without ever producing a PR-relevant finding.
EXCLUDED_DIRS = ("/.ipynb_checkpoints/", "/archive/", "/_output/", "/research/")
EXCLUDED_SUFFIX = "_output.ipynb"


def scan_notebook(path: Path) -> list[dict]:
    """Defects for one notebook: [{cell_index, cell_id, reason}]."""
    nb = json.loads(path.read_text(encoding="utf-8"))
    out = []
    for idx, cell in enumerate(nb.get("cells", [])):
        if cell.get("cell_type") != "code":
            continue
        if "outputs" not in cell:
            out.append({
                "cell_index": idx,
                "cell_id": cell.get("id", "?"),
                "reason": "missing 'outputs' key",
            })
            continue
        outs = cell["outputs"]
        if not isinstance(outs, list):
            out.append({
                "cell_index": idx,
                "cell_id": cell.get("id", "?"),
                "reason": f"'outputs' is {type(outs).__name__}, expected list",
            })
    return out


def iter_repo_notebooks():
    for p in sorted(REPO_ROOT.glob("MyIA.AI.Notebooks/**/*.ipynb")):
        s = str(p).replace("\\", "/")
        if any(x in s for x in EXCLUDED_DIRS) or s.endswith(EXCLUDED_SUFFIX):
            continue
        yield p


def pr_diff_files(base: str, head: str) -> list[Path]:
    proc = subprocess.run(
        ["git", "diff", "--name-only", base, head],
        cwd=REPO_ROOT, capture_output=True, text=True, check=True,
        encoding="utf-8", errors="replace",
    )
    # A path the diff names but the working tree lacks (renamed or deleted
    # since base -- e.g. a rename landed on main after the branch point) has
    # nothing to scan at HEAD; scanning it crashed an earlier guard with
    # UNREADABLE (#14901). Same lesson, same shape -- keep the existence
    # filter.
    return [REPO_ROOT / f for f in proc.stdout.splitlines()
            if f.endswith(".ipynb") and (REPO_ROOT / f).exists()]


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    scope = p.add_mutually_exclusive_group()
    scope.add_argument("--path", metavar="FILE", help="single notebook")
    scope.add_argument("--pr-diff", nargs=2, metavar=("BASE", "HEAD"),
                       help="notebooks changed in BASE..HEAD")
    p.add_argument("--json", action="store_true", help="JSON output")
    args = p.parse_args(argv)

    if args.path:
        targets = [Path(args.path)]
    elif args.pr_diff:
        targets = pr_diff_files(*args.pr_diff)
    else:
        targets = list(iter_repo_notebooks())

    results, errors = [], []
    for path in targets:
        try:
            defects = scan_notebook(path)
        except Exception as e:
            errors.append({"notebook": str(path), "error": str(e)})
            continue
        if defects:
            results.append({"notebook": str(path), "defects": defects})

    if args.json:
        print(json.dumps({
            "occurrences": sum(len(r["defects"]) for r in results),
            "notebooks": results,
            "errors": errors,
        }, indent=1))
    else:
        for r in results:
            try:
                rel = str(Path(r["notebook"]).relative_to(REPO_ROOT))
            except ValueError:
                rel = r["notebook"]
            for d in r["defects"]:
                print(f"{rel} cell#{d['cell_index']} id={d['cell_id']}: {d['reason']}")
        for e in errors:
            print(f"UNREADABLE {e['notebook']} :: {e['error']}")
        total = sum(len(r["defects"]) for r in results)
        print(f"=== {total} defective code-cell(s) in {len(results)} notebook(s), "
              f"{len(errors)} unreadable ===")

    return 2 if errors and not results else (1 if results else 0)


if __name__ == "__main__":
    sys.exit(main())
