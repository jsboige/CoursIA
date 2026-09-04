#!/usr/bin/env python3
"""Candidate-delivered labeler -- the missing ORGAN for issue #10466.

#10466 diagnosed why the pool ``gh issue list --state open`` is saturated with
work that is already delivered but not closed: delivery PRs write ``See #N``
(semantics "partial contribution") even when they fully resolve the issue, so
GitHub does not close it. The issue stays in the pool, the next worker reads it
as available, and re-picks it in duplicate. The cost is paid -- measured
firsthand on #9568 (delivered 2026-08-06 by #9589, then TWO post-delivery
``[CLAIMED]`` landed on it, one +4 days after the merge, dispatching a sister
lane to redo work that no longer existed).

This tool operationalises the fix described in #10466 acceptance: a scheduled
sweep that, for each OPEN non-EPIC issue, looks for a MERGED PR referencing it
(GitHub cross-referenced timeline event with ``pull_request.merged_at`` set),
checks that the issue has had NO comment activity after that merge, and -- if
both hold -- poses the label ``candidate-delivered``. The pool scan then becomes
a filter::

    gh issue list --state open --search '-label:candidate-delivered'

rather than a judgement every worker re-derives in isolation.

ADVISORY, never auto-close (#10466 "Ce que l'organe ne doit pas faire"):

  - Closing an issue requires reading the body + confronting the verdict (G.9);
    an auto-close on a reference heuristic would produce the inverse fault. The
    label SIGNALS, a human (or ai-01) DECIDES.
  - Only a PR whose state is ``MERGED`` counts. A ``Closes #N`` on an unmerged
    PR is worth nothing.
  - EPICs are excluded: a living EPIC referenced by a merged PR stays open
    correctly (``See #N`` is right for a partial delivery). EPIC detection is
    by **title or label containing "EPIC"** (case-insensitive). The
    checkbox-based heuristic suggested in #10466 was measured firsthand and is
    UNRELIABLE: EPIC #1454 carries no task checkboxes at all, while the
    delivered leaf #10143 carries 4 unchecked acceptance boxes -- so
    "unchecked checkbox => EPIC" is wrong in both directions. Title/label is the
    robust signal (covers #1454 "[EPIC]", #3801 "EPIC:", #10355/#4362 label
    EPIC). This exclusion rule is written here per acceptance #3 (the motif is
    in the workflow, not patched by hand).
  - An OPEN PR referencing the issue means work in flight -- excluded as
    ``in_flight`` (#11100): the correct `See #N` syntax for a partial delivery
    must not produce the "probably delivered" label. Measured on #10984
    (open #10986 + six merged PRs = a multi-phase rollout the old heuristic
    mislabeled). An open *issue* mention does NOT trigger this: only PR refs.
  - A **human retraction of the label is a verdict, and it sticks** (#14307).
    Removing the label after a firsthand check is a decision about *this*
    issue ("acceptance not satisfied", "engine on user hold"); a later merge
    that merely *mentions* the issue does not overturn it. Without this
    memory the sweep re-posed the label over 30 human retractions on 16
    issues, measured 2026-09-02 -- #11601 and #10475 had been round the loop
    five times each, and #10038 came back top of the picker's ``delivered``
    urn two days after a 15-line measured verdict said it was not delivered.
    The bot's OWN retractions (``active`` / ``in_flight``) are hysteresis,
    not verdicts, and do NOT stick; a human who re-poses the label by hand
    hands control back to the sweep.

The classification core (``classify``) is a PURE function -- no network -- so it
is unit-tested with fixtures in ``scripts/tests/test_candidate_delivered.py``.
The ``main`` driver wires it to ``gh`` (timeline + issue view) and applies or
removes the label idempotently.

Usage::

    python scripts/candidate_delivered.py --dry-run        # log only, no labels
    python scripts/candidate_delivered.py                  # apply labels (CI)
    python scripts/candidate_delivered.py --label NAME     # override label name

Exit code is always 0 (advisory). The actionable payload is the set of labeled
issues, NEVER the green conclusion.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from typing import Iterable

LABEL_DEFAULT = "candidate-delivered"
LABEL_COLOR = "5319e7"  # purple -- "delivered, awaiting close triage"
LABEL_DESC = "Referenced by a merged PR with no post-merge activity -- candidate for close triage (#10466)"

# EPIC detection: title OR any label contains "epic" as a word (case-insensitive).
# Measured firsthand: #1454 "[EPIC] ...", #3801 "EPIC: ...", #10355/#4362 label EPIC.
# Word boundaries avoid false positives like "Epictetus" / "epicycle".
_EPIC_RE = re.compile(r"\bepic\b", re.IGNORECASE)


def is_epic(title: str, labels: Iterable[str]) -> bool:
    """True if the issue is an EPIC by title or label (case-insensitive 'epic')."""
    if _EPIC_RE.search(title or ""):
        return True
    return any(_EPIC_RE.search(lab or "") for lab in labels)


def _is_bot(actor: str) -> bool:
    """True if ``actor`` is a GitHub App/bot login (``...[bot]``).

    An empty or unknown actor is treated as HUMAN. The asymmetry is
    deliberate: the fault this guards against is *discarding a human
    verdict*, so an unreadable actor errs towards preserving the verdict
    rather than towards re-posing the label.
    """
    return (actor or "").endswith("[bot]")


def human_retraction(label_events: list[dict] | None) -> dict | None:
    """The latest label event by a non-bot actor, iff it is a removal.

    Returns the event dict, or ``None`` when the label has never been touched
    by a human, or when a human's latest action was to *pose* the label --
    which hands control back to the sweep (the documented escape hatch).

    Bot events are ignored entirely: the sweep's own ``active`` /
    ``in_flight`` retractions are hysteresis, not verdicts, and must stay
    revisable on the next run.
    """
    human = [e for e in (label_events or []) if not _is_bot(e.get("actor", ""))]
    if not human:
        return None
    latest = max(human, key=lambda e: e.get("created_at") or "")
    return latest if latest.get("event") == "unlabeled" else None


def classify(
    issue: dict,
    cross_refs: list[dict],
    label_events: list[dict] | None = None,
) -> tuple[str, str]:
    """Classify one open issue against its cross-referenced PRs.

    Args:
        issue: ``{"number", "title", "labels": [str], "created_at": ISO,
               "comments": [{"created_at": ISO}, ...]}``
        cross_refs: ``[{"pr_number": int, "merged_at": ISO|None}, ...]`` --
                    GitHub cross-referenced timeline events.
        label_events: ``[{"event": "labeled"|"unlabeled", "actor": str,
                      "created_at": ISO}, ...]`` for THIS label. ``None``
                      (the default) means "not consulted" and preserves the
                      pre-#14307 behaviour, so existing callers are unaffected.

    Returns:
        ``(verdict, detail)`` where verdict is one of:
        ``"epic"``         -- excluded (EPIC by title/label)
        ``"retracted"``    -- a human removed the label: verdict stands (#14307)
        ``"no_delivery"``  -- no merged PR references it
        ``"in_flight"``    -- an OPEN PR references it: work in progress (#11100)
        ``"active"``       -- a comment landed after the latest merge
        ``"candidate"``    -- delivered + silent: pose the label
    """
    title = issue.get("title", "")
    labels = issue.get("labels", []) or []
    if is_epic(title, labels):
        return ("epic", f"EPIC by title/label: {title!r}")

    # #14307: a human retraction pre-empts the reference heuristic entirely.
    # It sits before in_flight/active/candidate because it is not evidence
    # about delivery -- it is a decision about this label on this issue, and
    # a heuristic over references has no standing to overturn it.
    retraction = human_retraction(label_events)
    if retraction is not None:
        who = retraction.get("actor") or "unknown"
        when = retraction.get("created_at") or "?"
        return ("retracted", f"label removed by {who} on {when}; verdict stands")

    # #11100: an OPEN PR referencing the issue is work in flight -- the
    # multi-phase rollout shape (e.g. #10984, referenced by open #10986 plus
    # six merged PRs). Partial deliveries write `See #N` correctly, so the
    # "merged + silent" heuristic alone mislabels the rollout as delivered.
    open_prs = [r for r in cross_refs if r.get("is_pr") and r.get("state") == "open"]
    if open_prs:
        prs = ", ".join(f"#{r['pr_number']}" for r in open_prs)
        return ("in_flight", f"open PR(s) {prs} reference this issue")

    merged = [r for r in cross_refs if r.get("merged_at")]
    if not merged:
        return ("no_delivery", "no merged PR references the issue")

    # ISO 8601 timestamps sort lexicographically; string max is correct.
    latest_merge = max(r["merged_at"] for r in merged)

    comment_dates = [c["created_at"] for c in (issue.get("comments") or []) if c.get("created_at")]
    last_activity = max(comment_dates + [issue.get("created_at", "")])

    if last_activity and last_activity > latest_merge:
        return ("active", f"issue active after merge ({last_activity} > {latest_merge})")
    return ("candidate", f"delivered {latest_merge}, no post-merge activity")


# ---------------------------------------------------------------------------
# gh wiring
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
    """Run a gh command, return parsed JSON (or None if empty). Raise on failure."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def list_open_issues(repo: str) -> list[dict]:
    """Open issues (excludes PRs) with the fields classify() needs."""
    return list(_gh_json([  # type: ignore[return-value]
        "issue", "list", "--repo", repo, "--state", "open", "--limit", "200",
        "--json", "number,title,labels",
    ]))


def issue_detail(repo: str, number: int) -> dict:
    """Comments + createdAt for one issue."""
    raw = _gh_json([
        "issue", "view", str(number), "--repo", repo,
        "--json", "createdAt,comments",
    ])
    d = raw or {}
    return {
        "created_at": d.get("createdAt", ""),
        "comments": [{"created_at": c.get("createdAt", "")} for c in (d.get("comments") or [])],
    }


def _parse_cross_ref_events(events: list[dict]) -> list[dict]:
    """Extract ``(pr_number, merged_at)`` refs from raw cross-referenced events.

    Pure (network-free) -- factored out of :func:`cross_refs_via_timeline` so the
    GitHub payload-shape handling is unit-tested independently of the network.
    Each event's ``source.issue`` carries a ``pull_request`` sub-object iff the
    referrer is a PR; ``merged_at`` on that sub-object is set iff the PR merged.
    ``state`` ("open"/"closed") distinguishes an unmerged-but-OPEN PR (work in
    flight, #11100) from a closed-unmerged one (abandoned lane) -- both carry
    ``merged_at: None``. Non-PR refs (an *issue* citing this one) yield
    ``merged_at: None`` and are ignored downstream by :func:`classify`, which
    counts only refs with a merge. Events missing a source issue number are
    dropped.
    """
    refs = []
    for ev in events or []:
        src = (ev.get("source") or {}).get("issue") or {}
        if src.get("number") is None:
            continue
        is_pr = "pull_request" in src  # presence, not truthiness: {} is a PR
        pr = src.get("pull_request") or {}
        refs.append({
            "pr_number": src["number"],
            "merged_at": pr.get("merged_at"),
            "is_pr": is_pr,
            "state": src.get("state"),
        })
    return refs


def _parse_label_events(events: list[dict], label: str) -> list[dict]:
    """Extract this label's ``labeled``/``unlabeled`` events from a timeline.

    Pure (network-free), same contract as :func:`_parse_cross_ref_events`:
    the events come from the timeline fetch :func:`classify` already needs,
    so the #14307 retraction memory costs **no extra API call**. Events for
    other labels, and events with no ``label.name``, are dropped.
    """
    out = []
    for ev in events or []:
        if ev.get("event") not in ("labeled", "unlabeled"):
            continue
        if ((ev.get("label") or {}).get("name")) != label:
            continue
        out.append({
            "event": ev["event"],
            "actor": ((ev.get("actor") or {}).get("login")) or "",
            "created_at": ev.get("created_at") or "",
        })
    return out


def timeline_facts(
    repo: str, number: int, label: str,
) -> tuple[list[dict], list[dict]]:
    """``(cross_refs, label_events)`` from ONE paginated timeline fetch.

    Both signals live in the same payload, so the #14307 retraction memory
    adds no request to the sweep's rate-limited budget. See
    :func:`cross_refs_via_timeline` for why the timeline endpoint is used
    rather than ``search/issues``, and why ``-q`` is not passed alongside
    ``--paginate``.
    """
    events = _gh_json([
        "api", f"repos/{repo}/issues/{number}/timeline", "--paginate",
    ]) or []
    xrefs = [ev for ev in events if ev.get("event") == "cross-referenced"]
    return _parse_cross_ref_events(xrefs), _parse_label_events(events, label)


def cross_refs_via_timeline(repo: str, number: int) -> list[dict]:
    """Cross-referenced PRs with merged_at, via the issue **timeline** endpoint.

    The timeline endpoint (``repos/{owner}/{repo}/issues/{n}/timeline``) is
    **repo-scoped**, so it answers reliably to the ``GITHUB_TOKEN`` that the CI
    cron carries. The ``search/issues`` endpoint used in the first cut is a
    *global* search and silently returns an empty result set (HTTP 200,
    ``total_count: 0``) under the soft rate-limit / scoped-token states the
    daily cron hits -- causing the **64 -> 0 candidate regression** measured
    2026-08-12 (CI run 31568734417 returned ``candidate: 0`` where the manual
    dry-run with a full-scope token found 64). The timeline endpoint does not
    have that failure mode: it is the same auth path as ``issue view``.

    ``gh api --paginate`` walks the Link headers and merges the raw timeline
    into ONE clean JSON array. A ``-q`` filter is deliberately NOT used here:
    with ``--paginate``, gh applies the query **per page** and prints each
    page's result separately (e.g. ``[page1 events][page2 events]``), which is
    invalid JSON and made ``json.loads`` raise ``Extra data`` on the largest
    timelines (#10488, 102 events) -- silently SKIPping them as no_delivery.
    The event-type filter is applied in Python instead. :func:`_parse_cross_ref_events`
    then extracts the PR number and merge timestamp from each event's
    ``source.issue`` payload.
    """
    return timeline_facts(repo, number, LABEL_DEFAULT)[0]


def ensure_label(repo: str, name: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "label", "create", name, "--repo", repo,
         "--color", LABEL_COLOR, "--description", LABEL_DESC, "--force"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def apply_label(repo: str, number: int, name: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "issue", "edit", str(number), "--repo", repo, "--add-label", name],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def remove_label(repo: str, number: int, name: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "issue", "edit", str(number), "--repo", repo, "--remove-label", name],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def has_label(issue: dict, name: str) -> bool:
    return any((lab.get("name") == name) for lab in (issue.get("labels") or []))


# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dry-run", action="store_true", help="log classifications, apply no labels")
    ap.add_argument("--repo", default=None, help="repo (default: gh default / GITHUB_REPOSITORY)")
    ap.add_argument("--label", default=LABEL_DEFAULT, help=f"label name (default: {LABEL_DEFAULT})")
    ap.add_argument("--limit", type=int, default=0, help="cap issues processed (0 = all)")
    ap.add_argument("--sleep", type=float, default=1.5,
                    help="seconds between issues (timeline API is REST-rate-limited)")
    args = ap.parse_args(argv)

    repo = args.repo or (subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True, encoding="utf-8").stdout.strip()
        or "jsboige/CoursIA")

    ensure_label(repo, args.label, args.dry_run)

    issues = list_open_issues(repo)
    if args.limit:
        issues = issues[: args.limit]

    counts = {"candidate": 0, "active": 0, "in_flight": 0, "no_delivery": 0,
              "epic": 0, "retracted": 0}
    print(f"[candidate-delivered] repo={repo} mode={'dry-run' if args.dry_run else 'apply'} "
          f"open_issues={len(issues)} label={args.label}")

    for issue in issues:
        number = issue["number"]
        try:
            refs, label_events = timeline_facts(repo, number, args.label)
            detail = issue_detail(repo, number)
        except Exception as exc:  # network/gh hiccup -- skip, do not crash the sweep
            print(f"  #{number:<6} SKIP  ({exc})")
            continue

        enriched = {
            "number": number,
            "title": issue.get("title", ""),
            "labels": [lab.get("name", "") for lab in (issue.get("labels") or [])],
            "created_at": detail["created_at"],
            "comments": detail["comments"],
        }
        verdict, why = classify(enriched, refs, label_events)
        counts[verdict] = counts.get(verdict, 0) + 1

        labeled = has_label(issue, args.label)
        if verdict == "candidate":
            if not labeled:
                apply_label(repo, number, args.label, args.dry_run)
            print(f"  #{number:<6} CANDIDATE  {why}")
        elif verdict == "active":
            if labeled:  # became active again -- retract the label (idempotent)
                remove_label(repo, number, args.label, args.dry_run)
                print(f"  #{number:<6} active     {why}  (label retracted)")
            else:
                print(f"  #{number:<6} active     {why}")
        elif verdict == "in_flight":
            if labeled:  # an open PR appeared since the label was posed -- retract
                remove_label(repo, number, args.label, args.dry_run)
                print(f"  #{number:<6} in_flight  {why}  (label retracted)")
            else:
                print(f"  #{number:<6} in_flight  {why}")
        elif verdict == "retracted":
            if labeled:  # re-posed over a human verdict -- restore the verdict
                remove_label(repo, number, args.label, args.dry_run)
                print(f"  #{number:<6} retracted  {why}  (label retracted)")
            else:
                print(f"  #{number:<6} retracted  {why}")
        elif verdict == "epic":
            print(f"  #{number:<6} EPIC       excluded  ({enriched['title'][:50]})")
        else:  # no_delivery
            pass  # quiet -- the common case, no merged PR references it

        if args.sleep:
            time.sleep(args.sleep)

    print(f"[candidate-delivered] done: {counts}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
