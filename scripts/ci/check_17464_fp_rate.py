#!/usr/bin/env python3
"""Mesure du taux de faux positifs de l'organe mode DIFF (#17464).

Le ticket exige un taux de FP publie sur les 30 dernieres PR notebook
mergees hors campagne densite. Ce script fait le run, imprime le verdict
par PR, et conclut avec un compteur global.

Usage :
    python scripts/ci/check_17464_fp_rate.py [LIMIT]
    LIMIT defaut : 30
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/notebook_tools/check_split_reading_cells.py"


def first_parent(merge_sha):
    proc = subprocess.run(
        ["git", "rev-parse", f"{merge_sha}^1"],
        cwd=str(ROOT), capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def show_file(sha, path):
    proc = subprocess.run(
        ["git", "show", f"{sha}:{path}"],
        cwd=str(ROOT), capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    return proc.stdout if proc.returncode == 0 else None


def run_diff(head_text, base_text, label):
    scratch = Path("/tmp")
    base_p = scratch / f"fp_base_{label}.ipynb"
    head_p = scratch / f"fp_head_{label}.ipynb"
    base_p.write_text(base_text, encoding="utf-8")
    head_p.write_text(head_text, encoding="utf-8")
    proc = subprocess.run(
        ["python", str(SCRIPT), str(head_p), "--base", str(base_p), "--json"],
        cwd=str(ROOT), capture_output=True, text=True, encoding="utf-8", errors="replace",
        env={"PYTHONIOENCODING": "utf-8", "PYTHONUTF8": "1", "PATH": "C:\\Program Files\\Python313"},
    )
    if proc.returncode not in (0, 2):
        return ["ERROR", proc.stderr[:200]]
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return ["non-json", proc.stdout[:200]]


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--limit", type=int, default=30)
    args = ap.parse_args(argv)

    prs_text = subprocess.check_output(
        ["gh", "pr", "list", "--state", "merged", "--limit", "300",
         "--json", "number,title,files,mergedAt,mergeCommit"],
        cwd=str(ROOT), text=True, encoding="utf-8", errors="replace",
    )
    data = json.loads(prs_text)

    seen = set()
    nb_prs = []
    for pr in data:
        if pr["number"] in seen:
            continue
        files = [f["path"] for f in pr.get("files", [])]
        nb_files = [f for f in files if f.endswith(".ipynb")]
        if not nb_files:
            continue
        title = pr["title"].lower()
        if "density" in title or "#17021" in title or "#17040" in title:
            continue
        seen.add(pr["number"])
        merge_sha = pr.get("mergeCommit", {}).get("oid") if pr.get("mergeCommit") else None
        nb_prs.append((pr["number"], pr["title"], nb_files, merge_sha))

    nb_prs = nb_prs[:args.limit]

    print(f"{'#PR':>5} {'files':>5} {'findings':>9}  kinds")
    fp_count = 0  # PRs ayant au moins 1 finding -- ici le script ne tranche pas FP/TP,
                  # il les LISTE pour audit manuel. Le verdict vient de la lecture body.
    for pr_num, title, nb_files, merge_sha in nb_prs:
        if not merge_sha:
            continue
        parent_sha = first_parent(merge_sha)
        if not parent_sha:
            continue
        n_findings = 0
        kinds = {}
        for f in nb_files[:1]:
            base_text = show_file(parent_sha, f)
            head_text = show_file(merge_sha, f)
            if base_text is None or head_text is None:
                continue
            label = f"{pr_num}_{f.replace('/', '_').replace('.ipynb', '')[:30]}"
            findings = run_diff(head_text, base_text, label)
            n_findings += len(findings)
            for fi in findings:
                kinds[fi.get("type", "?")] = kinds.get(fi.get("type", "?"), 0) + 1
        if n_findings > 0:
            fp_count += 1
        print(f"#{pr_num:5d} {len(nb_files[0:1]):5d} {n_findings:9d}  {kinds}  {title[:50]}")

    print()
    print(f"PRs scanned: {len(nb_prs)}")
    print(f"PRs with at least 1 finding: {fp_count}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
