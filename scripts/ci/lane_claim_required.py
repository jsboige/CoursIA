#!/usr/bin/env python3
r"""lane_claim_required.py -- BLOCKING gate: a closing-keyword reference must
not close an issue another lane actively claims (#10223).

## Why this exists

Two collisions the same day (2026-08-09, #10169 then #10161): in both, the
doubled lane (po-2025) held the SOLE issue-level claim, was protocol-conforme,
and got doubled anyway -- because ``scripts/check_lane_claim.py`` (the tool
that would have caught it, shipped in #9775 with both legs: issue-claim check +
``--paths`` PR collision) was never wired into CI. Nothing called it
mechanically. This gate is the mandatory consumer: it compares the
``Grain: lane`` of a PR body to the ``[CLAIMED]`` comments on the issue(s) its
closing keywords reference, and blocks the merge if a different lane holds a
fresh, unreleased claim.

The gate cannot prevent the collision (once the PR exists the work is written):
it makes it impossible to MERGE without a written adjudication. That
adjudication is the ``[OVERRIDE]`` marker (Task 2 of #10223) -- without it, a
coordinator cannot merge against a held claim.

## Discriminant -- closing keywords only

Only CLOSING references (``Closes|Fixes|Resolves #N``, via the shared
``grain_tag.find_close_keyword_pr_refs`` scanner -- NOT a new regex) block. A
``See #N`` / ``Part of #N`` on an EPIC is multi-lane by construction (#1454,
#1027, #3801 carry legitimate concurrent claims) and blocking on it would
redden half the repo. Non-closing references get an advisory LABEL only (Task
4), never a block.

## Single-reader / single-reducer discipline (#9485)

The lane is read by ``grain_tag.extract_lane`` -- the SAME reader the Grain tag
and check_lane_claim use -- so a PR body and a claim comment never disagree on
what a lane is. The claim state is reduced by ``check_lane_claim.compute_active
_claims`` -- the SAME reducer check_lane_claim uses, now extended with the
``[OVERRIDE]`` event (Task 2). No competing regex for ``machine:workspace`` or
``[CLAIMED]`` lives in this file.

## Falsifiable verdict

The decisive test (criterion 6 of #10223): replaying PR #10176's body against
issue #10169's comments yields ``block`` with ``blocking_lane =
myia-po-2025:CoursIA-2`` (the lane that held the claim and was doubled), and
``pass`` once the coordinator's adjudication is converted to ``[OVERRIDE]
lane myia-po-2026:CoursIA``.

## Run locally

    python scripts/ci/lane_claim_required.py --body-file body.txt
    python scripts/ci/lane_claim_required.py --body-file body.txt --stale-threshold 48

Exit codes: 0 pass / 1 block / 2 caller error (unreadable body file).

The default issue fetcher calls ``gh issue view`` (``GH_TOKEN``/``GITHUB_REPO``
present in CI); it is injectable so unit tests never touch the network.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

# Make the shared modules importable from anywhere in the repo.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402
import grain_tag as gt  # noqa: E402

IssueFetcher = Callable[[int], "dict | None"]


def gh_issue_fetcher(number: int) -> "dict | None":
    r"""Fetch issue ``{number, title, comments}`` via ``gh``.

    Returns None on any failure (missing issue, auth/rate-limit, network) -- the
    gate fails OPEN on it: a fetch failure must not block a legitimate merge,
    and the verdict carries a warning so the gap is visible. Reads ``GH_TOKEN``
    from the environment (set by the workflow).
    """
    try:
        out = subprocess.run(
            [
                "gh", "issue", "view", str(number),
                "--json", "number,title,comments",
            ],
            capture_output=True, text=True, timeout=20,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    try:
        return json.loads(out.stdout)
    except json.JSONDecodeError:
        return None


def check(
    pr_body: str | None,
    issue_fetcher: IssueFetcher,
    stale_threshold: float = 48.0,
    now: datetime | None = None,
) -> dict:
    r"""Pure decision function: blocking verdict for a PR body (#10223).

    Args:
        pr_body: the PR body text (carries the ``Grain: lane`` tag).
        issue_fetcher: ``int -> {number,title,comments} | None``. Injected in
            tests (dict-based); defaults to ``gh_issue_fetcher`` in the CLI.
        stale_threshold: hours. Other lanes' claims older than this do NOT
            block (the protocol re-arbitrates claims held by a dead lane after
            48 h). Age is from the server ``createdAt``, never the body.
        now: injected for testability (defaults to UTC now).

    Returns a one-line JSON verdict on stdout (the YAML reads exit code):

        {
          "guard_pass": True|False,
          "reason": str,
          "pr_lane": str|None,
          "blocking_lane": str|None,        # set on block
          "blocking_issue": int|None,       # set on block
          "blocking_claim_at": str|None,    # set on block (server ISO UTC)
          "closing_issues": [int, ...],
          "warnings": [str, ...],
        }

    Block logic (criterion c of #10223): a DIFFERENT lane holds an active,
    unreleased, non-stale claim on an issue this PR closes via a closing
    keyword. Lane-unreadable (criterion: lane illisible) defers to
    ``check-variation-tag-required`` and never blocks here -- a second red on
    the same cause only duplicates. ``See #N`` / ``Part of #N`` (non-closing)
    do not reach this function as blocking (advisory label only, Task 4).
    """
    pr_lane = gt.extract_lane(pr_body)
    if pr_lane is None:
        # Lane unreadable -> the tag gate (check-variation-tag-required) owns
        # this defect. Do not duplicate the red.
        return {
            "guard_pass": True,
            "reason": "PR lane unreadable -- deferred to check-variation-tag-required",
            "pr_lane": None,
            "blocking_lane": None,
            "blocking_issue": None,
            "blocking_claim_at": None,
            "closing_issues": [],
            "warnings": [],
        }

    # Closing references ONLY (Closes|Fixes|Resolves). See/Part of are excluded
    # by construction by find_close_keyword_pr_refs -- that is the discriminant.
    closing = gt.find_close_keyword_pr_refs(pr_body)
    issue_nums = sorted({h["number"] for h in closing})
    if not issue_nums:
        return {
            "guard_pass": True,
            "reason": "no closing-keyword reference -> advisory only (See/Part of do not block)",
            "pr_lane": pr_lane,
            "blocking_lane": None,
            "blocking_issue": None,
            "blocking_claim_at": None,
            "closing_issues": [],
            "warnings": [],
        }

    now = now or datetime.now(timezone.utc)
    warnings: list[str] = []

    for num in issue_nums:
        payload = issue_fetcher(num)
        if payload is None:
            # Fail-open: a fetch failure (network, missing issue) must not
            # block. Surface it so the gap is visible.
            warnings.append(
                f"could not fetch #{num} -- fail-open (network/missing)"
            )
            continue
        events = clc._sort_events(payload)
        active, _unattrib = clc.compute_active_claims(events)
        others = {ln: ev for ln, ev in active.items() if ln != pr_lane}

        # Stale filter (#10223 Task 1.5): a claim older than stale_threshold
        # (server createdAt age) does not block -- the protocol re-arbitrates
        # claims held by a dead lane. Fresh ones do.
        fresh_others: dict = {}
        for ln, ev in others.items():
            age = clc._claim_age_hours(ev.created_at, now)
            if age is not None and age >= stale_threshold:
                warnings.append(
                    f"#{num}: lane {ln} claim stale ({age:.1f}h >= "
                    f"{stale_threshold:g}h) -- not blocking"
                )
            else:
                fresh_others[ln] = ev

        if fresh_others:
            blocking = sorted(fresh_others)[0]
            ev = fresh_others[blocking]
            return {
                "guard_pass": False,
                "reason": (
                    f"#{num}: lane {blocking} holds an active claim "
                    f"(since {ev.created_at}). Release with `[RELEASED]`, have "
                    f"the coordinator post `[OVERRIDE] lane {pr_lane}`, or "
                    f"wait {stale_threshold:g}h for staleness. See #10223."
                ),
                "pr_lane": pr_lane,
                "blocking_lane": blocking,
                "blocking_issue": num,
                "blocking_claim_at": ev.created_at,
                "closing_issues": issue_nums,
                "warnings": warnings,
            }

    return {
        "guard_pass": True,
        "reason": "no other lane holds a fresh active claim on the closing issue(s)",
        "pr_lane": pr_lane,
        "blocking_lane": None,
        "blocking_issue": None,
        "blocking_claim_at": None,
        "closing_issues": issue_nums,
        "warnings": warnings,
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--body-file", metavar="FILE", required=True,
                   help="path to the PR body")
    p.add_argument("--stale-threshold", type=float, metavar="HOURS",
                   default=48.0,
                   help="other lanes' claims older than HOURS do not block "
                        "(default 48; age from server createdAt).")
    args = p.parse_args(argv)

    try:
        with open(args.body_file, encoding="utf-8") as f:
            body = f.read()
    except OSError as e:
        print(json.dumps(
            {"guard_pass": False, "reason": f"caller error: {e}"},
            ensure_ascii=False,
        ), file=sys.stderr)
        return 2

    verdict = check(body, gh_issue_fetcher, stale_threshold=args.stale_threshold)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
