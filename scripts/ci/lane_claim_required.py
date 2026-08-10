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


def _compute_advisory_labels(
    pr_body: str | None,
    issue_fetcher: IssueFetcher,
    pr_lane: str,
    pr_closing_refs: set[int] | None = None,
) -> list[str]:
    r"""Advisory labels for adoption telemetry (#10223 Task 4) -- never block.

    Two labels, surfaced so the coordinator can read the adoption curve at the
    merge-gate without the gate reddening:

      - ``lane-claim-absent``  -- a CLOSING-referenced issue carries NO active
        claim at all. The protocol wants a claim before editing; measuring it
        without blocking gives the curve (most of the historical backlog was
        taken without a claim, and a hard gate here would redden massively and
        teach nothing).
      - ``lane-claim-conflict`` -- a NON-closing reference (See/Part of #N)
        points to an issue another lane actively claims. Multi-lane by
        construction on an EPIC, so advisory only (the closing variant blocks).

    Reuses the SAME reducer (``check_lane_claim.compute_active_claims``) and the
    SAME scanners (``grain_tag.find_close_keyword_pr_refs`` /
    ``find_non_closing_refs``) -- no competing logic. Fetch failures are
    skipped: an advisory label must not crash the job on a network blip.

    ``pr_closing_refs`` (#10323): the issue numbers GitHub resolved as closing
    refs for this PR (``closingIssuesReferences``). A closing keyword inside a
    code span / negation is matched by the regex finder but IGNORED by GitHub --
    it must not fire ``lane-claim-absent`` either, since GitHub will not close
    it. ``None`` = cross-check unavailable -> keep the regex-only behaviour
    (backward compatible).
    """
    labels: set[str] = set()
    # lane-claim-absent: a closing-referenced issue with no active claim at all.
    for h in gt.find_close_keyword_pr_refs(pr_body):
        # #10323: skip closing keywords GitHub ignores (code span / negation).
        if pr_closing_refs is not None and h["number"] not in pr_closing_refs:
            continue
        payload = issue_fetcher(h["number"])
        if payload is None:
            continue
        events = clc._sort_events(payload)
        active, _unattrib = clc.compute_active_claims(events)
        if not active:
            labels.add("lane-claim-absent")
    # lane-claim-conflict: a non-closing ref whose issue another lane claims.
    for h in gt.find_non_closing_refs(pr_body):
        payload = issue_fetcher(h["number"])
        if payload is None:
            continue
        events = clc._sort_events(payload)
        active, _unattrib = clc.compute_active_claims(events)
        if any(ln != pr_lane for ln in active):
            labels.add("lane-claim-conflict")
    return sorted(labels)


def check(
    pr_body: str | None,
    issue_fetcher: IssueFetcher,
    stale_threshold: float = 48.0,
    now: datetime | None = None,
    pr_closing_refs: set[int] | None = None,
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
          "advisory_labels": [str, ...],    # #10223 Task 4 (never blocks)
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
        # this defect. Do not duplicate the red. Advisory labels are skipped:
        # without a pr_lane, a conflict/absent reading is meaningless.
        return {
            "guard_pass": True,
            "reason": "PR lane unreadable -- deferred to check-variation-tag-required",
            "pr_lane": None,
            "blocking_lane": None,
            "blocking_issue": None,
            "blocking_claim_at": None,
            "closing_issues": [],
            "advisory_labels": [],
            "warnings": [],
        }

    # Advisory labels (#10223 Task 4): computed across BOTH closing and
    # non-closing refs -- the blocking path below only looks at closing refs,
    # but a `See #N` conflict or a no-claim closing issue is still worth a
    # label. Never blocks. The same closingIssuesReferences cross-check (#10323)
    # applies so a code-span/negated closing keyword does not fire lane-claim-absent.
    advisory = _compute_advisory_labels(pr_body, issue_fetcher, pr_lane, pr_closing_refs)

    now = now or datetime.now(timezone.utc)
    warnings: list[str] = []

    # Closing references ONLY (Closes|Fixes|Resolves). See/Part of are excluded
    # by construction by find_close_keyword_pr_refs -- that is the discriminant.
    closing = gt.find_close_keyword_pr_refs(pr_body)
    regex_nums = sorted({h["number"] for h in closing})

    # #10323: for a PR BODY, GitHub's closingIssuesReferences is authoritative.
    # The regex finder matches closing keywords even inside code spans, fenced
    # blocks, or negations ("NOT closing #N") that GitHub's parser ignores. Only
    # numbers GitHub actually resolved as closing refs can block; regex-only
    # matches are logged IGNORED_BY_GITHUB and do not block. The regex stays the
    # source of truth for COMMIT messages (scanned by pr_close_keyword_guard.py),
    # which GitHub does not pre-resolve and where the squash trap is real.
    if pr_closing_refs is None:
        # Cross-check unavailable (fetch failed / older caller) -> fall back to
        # the regex finder. Do NOT disarm the gate on a network blip: a real
        # closing ref still blocks; only the code-span FP resurfaces, and it is
        # warned so the gap is visible.
        warnings.append(
            "closingIssuesReferences unavailable -- using regex finder only; a "
            "closing keyword in a code span/negation may false-positive (#10323)"
        )
        confirmed_nums = regex_nums
    else:
        confirmed_nums = sorted(n for n in regex_nums if n in pr_closing_refs)
        for n in regex_nums:
            if n not in pr_closing_refs:
                warnings.append(
                    f"#{n}: closing-keyword matched by regex but IGNORED_BY_GITHUB "
                    f"(code span or negation) -- not treated as a closing ref (#10323)"
                )

    if not confirmed_nums:
        return {
            "guard_pass": True,
            "reason": "no GitHub-confirmed closing-keyword reference -> advisory only (See/Part of do not block)",
            "pr_lane": pr_lane,
            "blocking_lane": None,
            "blocking_issue": None,
            "blocking_claim_at": None,
            "closing_issues": confirmed_nums,
            "advisory_labels": advisory,
            "warnings": warnings,
        }

    for num in confirmed_nums:
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
                "closing_issues": confirmed_nums,
                "advisory_labels": advisory,
                "warnings": warnings,
            }

    return {
        "guard_pass": True,
        "reason": "no other lane holds a fresh active claim on the closing issue(s)",
        "pr_lane": pr_lane,
        "blocking_lane": None,
        "blocking_issue": None,
        "blocking_claim_at": None,
        "closing_issues": confirmed_nums,
        "advisory_labels": advisory,
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
    p.add_argument("--pr-closing-refs", metavar="NUMS", default=None,
                   help="comma-separated issue numbers GitHub resolved as closing "
                        "refs for this PR (from `gh pr view --json "
                        "closingIssuesReferences`). The PR BODY is cross-checked "
                        "against this set so a closing keyword in a code span/"
                        "negation cannot block alone (#10323). Omit to fall back "
                        "to the regex finder (used when the fetch failed).")
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

    pr_closing_refs = _parse_closing_refs(args.pr_closing_refs)
    verdict = check(
        body, gh_issue_fetcher,
        stale_threshold=args.stale_threshold,
        pr_closing_refs=pr_closing_refs,
    )
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


def _parse_closing_refs(spec: str | None) -> set[int] | None:
    """Parse the ``--pr-closing-refs`` CLI value into a set, or ``None``.

    ``None`` (arg omitted) signals "cross-check unavailable" -> the gate falls
    back to the regex finder. An empty string means "GitHub fetched, the PR
    closes nothing" -> an empty set (every regex hit is IGNORED_BY_GITHUB).
    Non-numeric tokens are skipped rather than crashing the job.
    """
    if spec is None:
        return None
    spec = spec.strip()
    if spec == "":
        return set()
    return {int(t) for t in spec.split(",") if t.strip().isdigit()}


if __name__ == "__main__":
    sys.exit(main())
