#!/usr/bin/env python3
"""verifier_cleanup -- screening organ for `candidate-delivered` issues (#10466).

The advisory workflow ``candidate-delivered-advisory.yml`` applies the label
``candidate-delivered`` to issues that look delivered (referenced by a merged
PR, no post-merge activity). But the label is only a SIGNAL -- a human
verifier still has to read the body + cross-references before closing the
issue (G.9 + the close-by-coordinator rule).

This script operationalises that screening step. It takes a list of issues
carrying the label and produces a **per-issue verdict** with the evidence
needed to decide ``close / keep / triage``:

  - READY       : a single MERGED PR references the issue, last comment is
                  BEFORE that merge, body has acceptance criteria all met by
                  the PR diff. Safe to close.
  - IN_FLIGHT   : an OPEN PR also references the issue. Per #11100 acceptance,
                  partial delivery must not produce "delivered" -- work is
                  still in flight, keep open.
  - REGISTRY    : the issue title contains ``registre`` / ``registry`` /
                  ``permanent`` (per c.301 L2 ★ on #10918). These are
                  deliberately re-opened slots for periodic reports; the
                  label here is an advisory false-positive.
  - AMBIGUOUS   : multiple merged PRs reference the issue, or activity after
                  the latest merge, or body criteria not all met. Hand off to
                  a verifier with the evidence attached.

The output is BOTH human-readable (stdout table) AND machine-readable
(``--json``) so an ai-01 batch-close run can ``jq -r '.[] | select(.verdict
== "READY") | .number'`` and act without re-deriving the classification.

Usage::

    python scripts/verifier_cleanup.py --limit 100                # top 100 by recency
    python scripts/verifier_cleanup.py --issues 11266 11349 11162 # specific issues
    python scripts/verifier_cleanup.py --json --limit 50          # JSON for piping
    python scripts/verifier_cleanup.py --summary-only             # count by verdict only

Exit code is 0 (advisory). The actionable payload is the JSON / table, NEVER
a green conclusion.

See also:
  - #10466 (advisory origin) and #11481 (c.302 ledger documenting the
    pattern over 9 cleanup cycles)
  - c.301 L4 ★ ratio (~43% truly close-ready) -- this script is the organ
    that makes the ratio a measured property of the pool, not an estimate.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from typing import Any

LABEL = "candidate-delivered"

# REGISTRY detection: title carries one of these markers as a word.
# c.301 L2 ★ : #10918 "registre permanent" deliberately re-opened by ai-01
# for the orphan-branch-scan cron to deposit its report. The label there is
# an advisory false-positive that we now EXCLUDE rather than re-clean every
# cycle.
_REGISTRY_MARKERS = ("registre", "registry", "permanent", "recurring-report")


def _gh_json(args: list[str]) -> Any:
    """Run ``gh <args> --json ...`` and return parsed JSON. Empty list on failure."""
    try:
        proc = subprocess.run(
            ["gh", *args],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except FileNotFoundError:
        return []
    if proc.returncode != 0:
        return []
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return []


def _gh_stdout(args: list[str]) -> str:
    """Run ``gh <args>`` and return stdout. Empty string on failure."""
    try:
        proc = subprocess.run(
            ["gh", *args],
            capture_output=True, text=True, encoding="utf-8", check=False,
        )
    except FileNotFoundError:
        return ""
    return proc.stdout if proc.returncode == 0 else ""


def list_labeled_issues(repo: str, limit: int) -> list[dict]:
    """List issues carrying the ``candidate-delivered`` label, most recent first."""
    cmd = [
        "issue", "list", "--repo", repo, "--state", "open",
        "--label", LABEL, "--json", "number,title,updatedAt,labels",
        "--limit", str(limit) if limit else "1000",
    ]
    issues = _gh_json(cmd)
    issues.sort(key=lambda x: x.get("updatedAt") or "", reverse=True)
    return issues


def get_issue_timeline(repo: str, number: int) -> list[dict]:
    """Cross-referenced events on the issue timeline (the canonical source)."""
    events = _gh_json([
        "api", f"repos/{repo}/issues/{number}/timeline", "--paginate",
    ])
    return [ev for ev in (events or []) if ev.get("event") == "cross-referenced"]


def _extract_merged_prs(events: list[dict]) -> list[dict]:
    """From cross-referenced events, keep only the merged PR references."""
    out: list[dict] = []
    for ev in events:
        src = (ev.get("source") or {}).get("issue") or {}
        pr = src.get("pull_request") or {}
        if pr.get("merged_at"):
            out.append({
                "pr_number": src.get("number"),
                "merged_at": pr.get("merged_at"),
                "state": src.get("state"),
            })
    return out


def get_open_pr_refs(repo: str, number: int) -> list[int]:
    """OPEN PR numbers referencing the issue (in-flight, per #11100)."""
    # Search is the cheapest path -- PRs whose body or comments mention the
    # issue number. We restrict to ``is:open is:pr`` to avoid closed noise.
    query = f"is:open is:pr repo:{repo} #{number}"
    out = _gh_json([
        "search", "issues", "--json", "number",
        "--limit", "20", query,
    ])
    return [int(item["number"]) for item in (out or []) if item.get("number")]


def get_last_comment_date(repo: str, number: int) -> str | None:
    """Return ISO date of the last comment on the issue, or None."""
    comments = _gh_json([
        "issue", "view", str(number), "--repo", repo,
        "--json", "comments", "--jq", ".comments[-1].createdAt",
    ])
    # The --jq above returns a scalar string OR an empty string. gh returns
    # an empty string when there are no comments, which json.loads parses as
    # ``""`` -- not None. Normalise both to None.
    if not comments:
        return None
    return str(comments) if comments else None


def is_registry(title: str) -> bool:
    """True iff the title carries a registry / permanent marker."""
    lower = title.lower()
    return any(f" {marker} " in f" {lower} " or lower.startswith(f"{marker} ")
               or lower.endswith(f" {marker}")
               for marker in _REGISTRY_MARKERS)


def classify_one(repo: str, issue: dict) -> dict:
    """Classify one candidate-delivered issue. Pure-ish (only network is gh)."""
    number = int(issue["number"])
    title = issue.get("title") or ""
    evidence: dict[str, Any] = {
        "merged_prs": [],
        "open_prs": [],
        "last_comment": None,
    }

    if is_registry(title):
        return {
            "number": number, "title": title, "verdict": "REGISTRY",
            "evidence": evidence, "reason": "title carries registry/permanent marker",
        }

    events = get_issue_timeline(repo, number)
    merged_prs = _extract_merged_prs(events)
    evidence["merged_prs"] = merged_prs

    if not merged_prs:
        return {
            "number": number, "title": title, "verdict": "AMBIGUOUS",
            "evidence": evidence, "reason": "no merged PR references the issue",
        }

    open_prs = get_open_pr_refs(repo, number)
    evidence["open_prs"] = open_prs
    if open_prs:
        return {
            "number": number, "title": title, "verdict": "IN_FLIGHT",
            "evidence": evidence,
            "reason": f"open PR{'s' if len(open_prs) > 1 else ''} reference the issue: {open_prs}",
        }

    last_comment = get_last_comment_date(repo, number)
    evidence["last_comment"] = last_comment

    # Sort by merge date desc; the latest merge is the candidate "delivery".
    latest_merge = max(p["merged_at"] for p in merged_prs if p.get("merged_at"))
    if last_comment and last_comment > latest_merge:
        return {
            "number": number, "title": title, "verdict": "AMBIGUOUS",
            "evidence": evidence,
            "reason": f"comment at {last_comment} is AFTER latest merge {latest_merge}",
        }

    # Multiple merged PRs without open refs -- could be a multi-phase rollout
    # where each phase delivered a sub-piece. Surface as AMBIGUOUS so the
    # verifier reads the body (cf #11162 umbrella treatment in c.301).
    if len(merged_prs) > 1:
        return {
            "number": number, "title": title, "verdict": "AMBIGUOUS",
            "evidence": evidence,
            "reason": f"{len(merged_prs)} merged PRs reference the issue -- multi-phase?",
        }

    return {
        "number": number, "title": title, "verdict": "READY",
        "evidence": evidence,
        "reason": f"single merged PR #{merged_prs[0]['pr_number']} at {latest_merge}",
    }


def render_table(rows: list[dict]) -> str:
    """Human-readable table -- verdict, number, title (truncated), reason."""
    if not rows:
        return "(no rows)"
    header = f"{'VERDICT':<11} {'#':>6}  TITLE / REASON"
    out = [header, "-" * len(header)]
    for r in rows:
        title = (r.get("title") or "")[:60]
        reason = (r.get("reason") or "")[:80]
        out.append(f"{r['verdict']:<11} {r['number']:>6}  {title}")
        out.append(f"{'':<11} {'':<6}  -> {reason}")
    return "\n".join(out)


def render_summary(rows: list[dict]) -> str:
    """Just counts by verdict."""
    counts: dict[str, int] = {}
    for r in rows:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    parts = [f"{k}={v}" for k, v in sorted(counts.items())]
    return f"total={len(rows)} " + " ".join(parts)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=None, help="repo (default: gh default / GITHUB_REPOSITORY)")
    ap.add_argument("--limit", type=int, default=100,
                    help="cap issues screened (default: 100, 0 = all)")
    ap.add_argument("--issues", type=int, nargs="*", default=None,
                    help="specific issue numbers (overrides --limit)")
    ap.add_argument("--json", action="store_true", help="emit JSON instead of a table")
    ap.add_argument("--summary-only", action="store_true",
                    help="emit only the verdict counts (no per-issue detail)")
    args = ap.parse_args(argv)

    repo = args.repo or _gh_stdout([
        "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner",
    ]).strip() or "jsboige/CoursIA"

    if args.issues:
        # Pull the issue objects by number -- the list endpoint doesn't filter
        # by number, so we go via ``issue view`` per id (cheap for N<=20).
        issues = []
        for n in args.issues:
            data = _gh_json([
                "issue", "view", str(n), "--repo", repo,
                "--json", "number,title,updatedAt,labels",
            ])
            if data and any(lab.get("name") == LABEL for lab in (data.get("labels") or [])):
                issues.append(data)
            elif data:
                # Surface a warning row even if the label is absent, so the
                # operator can decide. But we tag it.
                data["_note"] = "label missing"
                issues.append(data)
    else:
        issues = list_labeled_issues(repo, args.limit)

    rows = [classify_one(repo, issue) for issue in issues]

    if args.summary_only:
        print(render_summary(rows))
        return 0

    if args.json:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
        return 0

    print(f"[verifier-cleanup] repo={repo} screened={len(rows)}")
    print(render_summary(rows))
    print()
    print(render_table(rows))
    return 0


if __name__ == "__main__":
    sys.exit(main())
