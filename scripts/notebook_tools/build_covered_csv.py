#!/usr/bin/env python3
"""Concatener les résultats de scan_pr_arxiv_diff + scan repo-wide -> delta.

Lit le JSON de scan_pr_arxiv_diff, fait l'union des IDs couverts par toutes
les PRs, lit le JSON de scan_arxiv_citations, et sort :
- IDs totaux
- IDs couverts par au moins une PR
- IDs non couverts (= delta)
"""
import argparse
import json
import sys
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--pr-diff", required=True,
                    help="JSON produit par scan_pr_arxiv_diff.py")
    ap.add_argument("--scan", required=True,
                    help="JSON produit par scan_arxiv_citations.py")
    ap.add_argument("--out-csv", default=None,
                    help="CSV de sortie des IDs couverts (un par ligne)")
    ap.add_argument("--out-delta", default=None,
                    help="JSON de sortie du delta (par ID, fichiers, etc.)")
    args = ap.parse_args()

    with open(args.pr_diff, encoding="utf-8") as f:
        pr_data = json.load(f)
    with open(args.scan, encoding="utf-8") as f:
        scan_data = json.load(f)

    # Union des IDs couverts
    covered = set()
    by_pr = {}
    for entry in pr_data:
        pr_id = entry["pr"]
        ids = entry.get("ids_covered", [])
        by_pr[pr_id] = sorted(set(ids))
        covered.update(ids)

    # Tous les IDs du scan repo-wide
    all_ids = set(scan_data["occurrences"].keys())

    delta = sorted(all_ids - covered)
    total = len(all_ids)
    n_covered = len(covered)
    n_delta = len(delta)

    summary = {
        "total_unique_ids": total,
        "covered_unique_ids": n_covered,
        "delta_unique_ids": n_delta,
        "covered_by_pr_count": {str(k): len(v) for k, v in by_pr.items()},
        "delta": delta,
    }
    print(json.dumps(summary, indent=2))

    if args.out_csv:
        Path(args.out_csv).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out_csv).write_text(
            "\n".join(sorted(covered)) + "\n",
            encoding="utf-8",
        )
        print(f"-> CSV couvert: {args.out_csv} ({n_covered} IDs)")
    if args.out_delta:
        delta_records = []
        for aid in delta:
            occs = scan_data["occurrences"].get(aid, [])
            delta_records.append({
                "arxiv_id": aid,
                "occurrences": len(occs),
                "notebooks": sorted({o["notebook"] for o in occs}),
            })
        Path(args.out_delta).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out_delta).write_text(
            json.dumps(delta_records, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        print(f"-> delta JSON: {args.out_delta}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
