"""
Forensic scan of all notebooks: categorize execution state via JSON parsing only.

Categories:
  A = ALL_EXEC_OK     : every code cell has execution_count != null AND no error outputs
  B = PARTIAL_EXEC    : some code cells executed, others not (mix of null and int execution_count)
  C = NEVER_EXECUTED  : every code cell has execution_count == null
  D = HAS_ERRORS      : at least one cell with output_type == 'error'
  E = STALE_PRE_RULE  : last commit before 2026-04-26 (pre-C.2 enforcement) — overlay flag

Output: JSON to stdout + summary table. Use --json-out <path> to also write to file.
Run: python scripts/notebook_tools/forensic_scan.py [--root MyIA.AI.Notebooks] [--json-out path]

Pure parsing + git log. Zero notebook execution. Compatible CPU/thermal-constrained machines.
"""
import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

RULE_C2_DATE = datetime(2026, 4, 26, tzinfo=timezone.utc)

EXCLUDE_DIRS = {
    "_archive_obsoletes",
    "_archives",
    "_old",
    "TrashBin",
    "trashbin",
    ".ipynb_checkpoints",
    "node_modules",
}


def categorize_notebook(path: Path) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            nb = json.load(f)
    except (json.JSONDecodeError, UnicodeDecodeError, OSError) as e:
        return {"path": str(path), "category": "PARSE_ERROR", "error": str(e)}

    cells = nb.get("cells", [])
    code_cells = [c for c in cells if c.get("cell_type") == "code"]
    n_code = len(code_cells)

    if n_code == 0:
        return {"path": str(path), "category": "NO_CODE", "n_code": 0}

    n_exec = sum(1 for c in code_cells if c.get("execution_count") is not None)
    n_err = sum(
        1
        for c in code_cells
        if any(o.get("output_type") == "error" for o in c.get("outputs", []))
    )
    n_outputs = sum(1 for c in code_cells if c.get("outputs"))

    if n_err > 0:
        category = "D_HAS_ERRORS"
    elif n_exec == 0:
        category = "C_NEVER_EXECUTED"
    elif n_exec == n_code:
        category = "A_ALL_EXEC_OK"
    else:
        category = "B_PARTIAL_EXEC"

    return {
        "path": str(path),
        "category": category,
        "n_code": n_code,
        "n_exec": n_exec,
        "n_err": n_err,
        "n_outputs": n_outputs,
    }


def get_last_commit_date(path: Path, repo_root: Path) -> str | None:
    rel = path.relative_to(repo_root).as_posix()
    try:
        out = subprocess.run(
            ["git", "-C", str(repo_root), "log", "-1", "--format=%cI", "--", rel],
            check=True,
            capture_output=True,
            text=True,
        )
        return out.stdout.strip() or None
    except subprocess.CalledProcessError:
        return None


def is_excluded(path: Path) -> bool:
    return any(part in EXCLUDE_DIRS for part in path.parts)


def get_series(path: Path, root: Path) -> str:
    rel = path.relative_to(root).parts
    if not rel:
        return "ROOT"
    return rel[0] if len(rel) > 1 else "TOP"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="MyIA.AI.Notebooks", help="Notebook root")
    parser.add_argument("--repo-root", default=".", help="Git repo root")
    parser.add_argument("--json-out", default=None, help="JSON output file")
    parser.add_argument("--with-git", action="store_true", help="Include git last-commit (slow)")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    repo_root = Path(args.repo_root).resolve()

    if not root.exists():
        print(f"ERROR: root {root} does not exist", file=sys.stderr)
        return 1

    notebooks = sorted(p for p in root.rglob("*.ipynb") if not is_excluded(p))
    print(f"Scanning {len(notebooks)} notebooks under {root}", file=sys.stderr)

    results = []
    for i, nb_path in enumerate(notebooks, 1):
        if i % 100 == 0:
            print(f"  {i}/{len(notebooks)}...", file=sys.stderr)
        info = categorize_notebook(nb_path)
        info["series"] = get_series(nb_path, root)
        if args.with_git:
            commit_date = get_last_commit_date(nb_path, repo_root)
            info["last_commit"] = commit_date
            if commit_date:
                try:
                    dt = datetime.fromisoformat(commit_date.replace("Z", "+00:00"))
                    info["pre_rule_c2"] = dt < RULE_C2_DATE
                except ValueError:
                    info["pre_rule_c2"] = None
        results.append(info)

    by_cat: dict[str, list] = {}
    for r in results:
        by_cat.setdefault(r["category"], []).append(r)

    by_series_cat: dict[str, dict[str, int]] = {}
    for r in results:
        s = r["series"]
        by_series_cat.setdefault(s, {})
        by_series_cat[s][r["category"]] = by_series_cat[s].get(r["category"], 0) + 1

    summary = {
        "total": len(results),
        "by_category": {k: len(v) for k, v in by_cat.items()},
        "by_series_category": by_series_cat,
        "d_has_errors": sorted(
            (r for r in by_cat.get("D_HAS_ERRORS", [])),
            key=lambda r: r.get("n_err", 0),
            reverse=True,
        ),
        "c_never_executed": sorted(
            r["path"] for r in by_cat.get("C_NEVER_EXECUTED", [])
        ),
        "b_partial_exec": sorted(
            (r for r in by_cat.get("B_PARTIAL_EXEC", [])),
            key=lambda r: r.get("n_exec", 0) / max(r.get("n_code", 1), 1),
        ),
    }

    print("\n=== SUMMARY ===")
    print(f"Total notebooks: {summary['total']}")
    for cat, n in sorted(summary["by_category"].items()):
        pct = 100.0 * n / summary["total"]
        print(f"  {cat:25s} {n:5d}  ({pct:.1f}%)")

    print("\n=== BY SERIES ===")
    cats = ["A_ALL_EXEC_OK", "B_PARTIAL_EXEC", "C_NEVER_EXECUTED", "D_HAS_ERRORS"]
    print(f"{'Series':25s}" + "".join(f"{c[:8]:>10s}" for c in cats) + "    Total")
    for s in sorted(by_series_cat):
        row = by_series_cat[s]
        total = sum(row.values())
        print(
            f"{s:25s}"
            + "".join(f"{row.get(c, 0):10d}" for c in cats)
            + f"{total:10d}"
        )

    print("\n=== D HAS_ERRORS (priority MAX) ===")
    for r in summary["d_has_errors"]:
        print(f"  {r['n_err']}/{r['n_code']} errors  {r['path']}")

    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as f:
            json.dump({"summary": summary, "results": results}, f, indent=2)
        print(f"\nJSON output: {args.json_out}", file=sys.stderr)

    return 0


if __name__ == "__main__":
    sys.exit(main())
