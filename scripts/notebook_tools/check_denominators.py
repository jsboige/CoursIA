#!/usr/bin/env python3
"""Reconciliation check for notebook denominators (forensic vs catalogue).

Issue #8050 — the forensic scan (~943 notebooks) and the curated catalogue (~830)
measure DIFFERENT things, so raw counts must never be compared. This check:

  1. Builds the forensic set with the SAME exclusion logic as forensic_scan
     (imports is_excluded -> zero logic drift).
  2. Reads the catalogue entry set (COURSE_CATALOG.generated.json).
  3. Detects PHANTOM catalogue entries (catalogue references a notebook that the
     forensic set does not contain AND that does not exist on disk). A phantom is
     the ONLY kind of gap that signals a real bug (catalogue drift); the structural
     gap (forensic > catalogue, due to research/twins/examples) is healthy and
     non-blocking.
  4. Categorizes the forensic-only gap so an unexpected new source of divergence
     is visible in the report.
  5. Exits 1 iff phantoms are found. Exits 0 otherwise (structural gap is reported
     but tolerated).

Run: python scripts/notebook_tools/check_denominators.py [--root MyIA.AI.Notebooks]
"""
import argparse
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO_DEFAULT = HERE.parents[1]  # HERE = .../scripts/notebook_tools ; parents[1] = repo root


def _load_forensic_module():
    """Import forensic_scan.is_excluded without requiring a package."""
    spec = importlib.util.spec_from_file_location(
        "forensic_scan", HERE / "forensic_scan.py"
    )
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def build_forensic_set(root: Path, is_excluded) -> set[str]:
    """Notebook paths (relative to root, forward-slash) under root, forensic-excluded."""
    out = set()
    for p in root.rglob("*.ipynb"):
        if is_excluded(p):
            continue
        out.add(p.relative_to(root).as_posix())
    return out


def read_catalogue(repo_root: Path) -> set[str]:
    cat_path = repo_root / "COURSE_CATALOG.generated.json"
    if not cat_path.exists():
        raise FileNotFoundError(f"catalogue not found: {cat_path}")
    data = json.loads(cat_path.read_text(encoding="utf-8"))
    return {e["path"] for e in data}


def categorize_forensic_only(paths: list[str]) -> dict[str, int]:
    """Bucket forensic-only notebooks by why they are not catalogued."""
    buckets: Counter = Counter()
    for p in paths:
        top = p.split("/")[0]
        pl = p.lower()
        if p.endswith("GradeBook.ipynb") or top == "GradeBook.ipynb":
            buckets["tool (GradeBook)"] += 1
        elif "/examples/" in pl or pl.startswith("examples/"):
            buckets["examples"] += 1
        elif "/_archives/" in pl or "/archive/" in pl or "/_old/" in pl:
            buckets["archive"] += 1
        elif top == "QuantConnect" and (
            "/research/" in pl or "/projects/" in pl or "/ml-training-pipeline/" in pl
        ):
            buckets["qc research/project"] += 1
        elif "-csharp" in pl or "-lean" in pl or "-python" in pl:
            buckets["twin (C#/Lean/Python variant)"] += 1
        else:
            buckets[f"other ({top})"] += 1
    return dict(buckets)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default="MyIA.AI.Notebooks")
    parser.add_argument("--repo-root", default=str(REPO_DEFAULT))
    args = parser.parse_args()

    root = Path(args.root).resolve()
    repo_root = Path(args.repo_root).resolve()
    if not root.exists():
        print(f"ERROR: root {root} does not exist", file=sys.stderr)
        return 2

    forensic_mod = _load_forensic_module()
    forensic = build_forensic_set(root, forensic_mod.is_excluded)
    catalogue = read_catalogue(repo_root)

    forensic_only = sorted(forensic - catalogue)
    catalogue_only = sorted(catalogue - forensic)

    # A catalogue-only entry is a PHANTOM iff the file does not exist on disk.
    # (catalogue paths are relative to MyIA.AI.Notebooks.)
    phantoms = [p for p in catalogue_only if not (root / p).exists()]
    catalogue_only_known = [p for p in catalogue_only if (root / p).exists()]

    print("=== Denominator reconciliation ===")
    print(f"forensic (under {root.name}, forensic-excluded): {len(forensic)}")
    print(f"catalogue entries:                                {len(catalogue)}")
    print(f"  intersection:                                   {len(forensic & catalogue)}")
    print(f"  forensic-only (structural, healthy):            {len(forensic_only)}")
    print(f"  catalogue-only:                                 {len(catalogue_only)}")
    print(f"    of which phantom (file missing on disk):      {len(phantoms)}")
    print(f"    of which known to forensic-scan set:          {len(catalogue_only_known)}")

    if forensic_only:
        print("\n=== forensic-only by category (informational, non-blocking) ===")
        for bucket, n in sorted(
            categorize_forensic_only(forensic_only).items(), key=lambda kv: -kv[1]
        ):
            print(f"  {n:4d}  {bucket}")

    if phantoms:
        print("\n=== PHANTOM catalogue entries (BLOCKING — catalogue drift) ===")
        for p in phantoms:
            print(f"  {p}")
        print(
            "\nFAIL: catalogue references notebooks absent from disk. "
            "The catalogue is regenerated by catalog-cron/catalog-drift CI; "
            "this should self-heal on the next regen. See "
            "docs/reference/notebook-denominators.md and "
            ".claude/rules/catalog-pr-hygiene.md.",
            file=sys.stderr,
        )
        return 1

    print("\nOK: no phantom catalogue entries. Structural forensic/catalogue gap is healthy.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
