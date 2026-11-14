#!/usr/bin/env python3
"""Rejeu local et deterministe du lot check_issues_batch (#24824).

Usage depuis la racine du depot :
  python scripts/benchmarks/bench_check_lane_claim_snapshot.py \
    --snapshot-dir /workspace/coursia-batch20 --limit 300

Le snapshot d'issues/commentaires et la liste de PR ouvertes sont lus tels
quels. Les snapshots ne portent ni l'activite des PR ni l'etat des PR fermees:
ces champs restent inconnus, ce qui reproduit le repli hors ligne; aucun `gh`
ne peut etre execute. Le temps mesure le batch en processus, avec `git
ls-files` local, et n'est pas une mesure de la flotte ni du tapis de production.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot-dir", type=Path, required=True)
    parser.add_argument("--limit", type=int, default=300)
    parser.add_argument("--lane", default="myia-ai-01:CoursIA-2")
    parser.add_argument("--module-dir", type=Path,
                        help="scripts/ alternatif, pour comparer un ancien SHA")
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit doit etre positif")
    module_dir = (args.module_dir or Path(__file__).resolve().parents[1])
    sys.path.insert(0, str(module_dir.resolve()))
    import check_lane_claim as clc  # noqa: PLC0415

    issues = json.loads((args.snapshot_dir / "all-issues.json").read_text())
    comments = json.loads((args.snapshot_dir / "all-comments.json").read_text())
    open_prs = json.loads((args.snapshot_dir / "open-prs.json").read_text())
    chosen = issues[:args.limit]
    issue_map = {str(item["number"]): item for item in issues}
    comment_map = {
        str(key).removeprefix("i"): value.get("comments", {}).get("nodes", [])
        for key, value in comments.items()
    }
    chosen_numbers = [str(item["number"]) for item in chosen]
    clc.set_snapshot({
        "issues": issue_map,
        "comments": comment_map,
        "prs": {str(pr["number"]): "OPEN" for pr in open_prs},
    })
    clc._OPEN_PRS_MEMO = open_prs
    clc._PR_STATE_CACHE.update(
        {int(pr["number"]): ("OPEN", None) for pr in open_prs})
    clc._PR_ACTIVITY_CACHE.update(
        {int(pr["number"]): None for pr in open_prs})
    refs = clc._collect_delivered_pr_refs(chosen_numbers)
    for ref in refs:
        clc._PR_STATE_CACHE.setdefault(
            ref, (None, "PR state absent from supplied open-PR snapshot"))
    # The snapshot contains no closed-PR states. Keep the grouped prefetch
    # offline, and let the reader's normal unknown-state path consume misses.
    clc._prefetch_pr_states = lambda _refs: {}

    original_extract_lane = clc.extract_lane
    extract_lane_calls = 0

    def counted_extract_lane(*positional, **keywords):
        nonlocal extract_lane_calls
        extract_lane_calls += 1
        return original_extract_lane(*positional, **keywords)

    clc.extract_lane = counted_extract_lane

    original_run = subprocess.run
    gh_calls = 0

    def no_gh(command, *positional, **keywords):
        nonlocal gh_calls
        if command and str(command[0]) == "gh":
            gh_calls += 1
            raise RuntimeError("gh disabled by local snapshot benchmark")
        return original_run(command, *positional, **keywords)

    subprocess.run = no_gh
    captured_err = io.StringIO()
    start = time.perf_counter()
    try:
        with contextlib.redirect_stderr(captured_err):
            result = clc.check_issues_batch(
                chosen_numbers, args.lane, stale_threshold=48.0, my_paths=None)
    finally:
        subprocess.run = original_run
    elapsed = time.perf_counter() - start
    verdicts = {
        number: {key: result["results"][number].get(key)
                 for key in ("code", "exit", "human", "blocker_named")}
        for number in chosen_numbers
    }
    digest = hashlib.sha256(
        json.dumps(verdicts, ensure_ascii=False, sort_keys=True).encode()
    ).hexdigest()
    print(json.dumps({
        "seconds": round(elapsed, 4),
        "issues": len(chosen_numbers),
        "first_issue": chosen_numbers[0],
        "last_issue": chosen_numbers[-1],
        "gh_calls": gh_calls,
        "extract_lane_calls": extract_lane_calls,
        "verdicts_sha256": digest,
        "code_counts": {
            code: sum(v["code"] == code for v in verdicts.values())
            for code in sorted({v["code"] for v in verdicts.values()})
        },
    }, ensure_ascii=False, sort_keys=True))
    return 0 if gh_calls == 0 else 2


if __name__ == "__main__":
    raise SystemExit(main())
