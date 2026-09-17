#!/usr/bin/env python3
"""Fail-closed gate for the coordinator's adjoint prevalidation dossier.

The gate answers one narrow question: does this pull request have a complete,
exact-head, machine-readable READY dossier from the canonical adjoint lane?
It does not approve the pull request, replace B.0, or authorize a merge.

Canonical comment body (the marker must be the first line):

    [ADJOINT PREFLIGHT]
    schema: 1
    lane: myia-po-2025:CoursIA-2
    pr: 123
    head: 0123456789abcdef0123456789abcdef01234567
    complete: true
    body: read
    comments-reviewed: 4
    reviews-reviewed: 2
    threads-reviewed: 1
    threads-unresolved: 0
    surfaces-sha256: <printed by --fingerprint>
    diff-files: 3
    diff-additions: 42
    diff-deletions: 7
    checks: latest-wins-green
    b0: clear
    scope: pass
    domain: pass
    verdict: READY
    [/ADJOINT PREFLIGHT]

The comment count excludes the dossier comment itself. Any observable later
issue comment, review, inline-thread, PR-metadata, check, or head change
invalidates the dossier and requires a fresh one. GitHub does not expose a
stateless audit trail for an event that is later deleted or reverted; this gate
therefore certifies the current surfaces, not erased history.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import asdict, dataclass
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Callable, Sequence

REPO = "jsboige/CoursIA"
ADJOINT_LANE = "myia-po-2025:CoursIA-2"
SHARED_GITHUB_LOGIN = "jsboige"
START = "[ADJOINT PREFLIGHT]"
END = "[/ADJOINT PREFLIGHT]"
SHA_RE = re.compile(r"[0-9a-f]{40}")
READY = "READY"
BLOCKED = "BLOCKED"
DWELL_PENDING = "DWELL_PENDING"
STALE = "STALE"
DEFAULT_DWELL_MINUTES = 120.0
DEFAULT_STALE_AFTER_MINUTES = 24 * 60.0
DWELL_WAIVER_LABEL = "merge-dwell-waived"
CHECK_OK = frozenset({"SUCCESS", "NEUTRAL", "SKIPPED"})
CHECK_PENDING = frozenset({"EXPECTED", "PENDING", "QUEUED", "IN_PROGRESS", "WAITING"})

REQUIRED_FIELDS = {
    "schema",
    "lane",
    "pr",
    "head",
    "complete",
    "body",
    "comments-reviewed",
    "reviews-reviewed",
    "threads-reviewed",
    "threads-unresolved",
    "surfaces-sha256",
    "diff-files",
    "diff-additions",
    "diff-deletions",
    "checks",
    "b0",
    "scope",
    "domain",
    "verdict",
}
INTEGER_FIELDS = {
    "pr",
    "comments-reviewed",
    "reviews-reviewed",
    "threads-reviewed",
    "threads-unresolved",
    "diff-files",
    "diff-additions",
    "diff-deletions",
}


@dataclass(frozen=True)
class Dossier:
    fields: dict[str, str]
    comment_index: int
    author: str


@dataclass(frozen=True)
class QueueEntry:
    pr: int
    verdict: str
    created_at: str
    head: str
    dossier_comment_id: str | None
    dossier_created_at: str | None
    surfaces_sha256: str
    b0_rc: int | None
    checks: str
    review_qualifying: bool
    grain_tag: str | None
    last_comment_is_dossier: bool
    tail_to_read: list[dict[str, Any]]
    dossier_age_minutes: float | None
    dwell_until: str | None
    reject_cause: list[str]

    @property
    def status(self) -> str:
        """Compatibility alias for callers using the initial queue prototype."""
        return self.verdict

    def to_json(self) -> dict[str, Any]:
        return asdict(self)


def gh_json(args: list[str]) -> Any:
    proc = subprocess.run(
        ["gh", *args], capture_output=True, text=True, encoding="utf-8"
    )
    if proc.returncode != 0:
        raise RuntimeError(proc.stderr.strip() or "gh command failed")
    return json.loads(proc.stdout)


def parse_dossier(body: str, comment_index: int, author: str) -> tuple[Dossier | None, list[str]]:
    """Parse one strictly delimited dossier comment without interpreting prose."""
    lines = body.strip().splitlines()
    if not lines or lines[0].strip() != START:
        return None, []
    errors: list[str] = []
    closing = next(
        (index for index, line in enumerate(lines[1:], 1) if line.strip() == END),
        None,
    )
    if closing is None:
        errors.append("missing closing marker")
        content = lines[1:]
    else:
        content = lines[1:closing]
        if closing != len(lines) - 1:
            errors.append("content after closing marker")

    fields: dict[str, str] = {}
    for raw in content:
        if not raw.strip():
            continue
        if ":" not in raw:
            errors.append(f"malformed line: {raw.strip()}")
            continue
        key, value = (part.strip() for part in raw.split(":", 1))
        if key in fields:
            errors.append(f"duplicate field: {key}")
        fields[key] = value

    missing = sorted(REQUIRED_FIELDS - fields.keys())
    unknown = sorted(fields.keys() - REQUIRED_FIELDS)
    if missing:
        errors.append("missing fields: " + ", ".join(missing))
    if unknown:
        errors.append("unknown fields: " + ", ".join(unknown))
    return Dossier(fields, comment_index, author), errors


def _integer(fields: dict[str, str], key: str, errors: list[str]) -> int | None:
    value = fields.get(key, "")
    if not re.fullmatch(r"0|[1-9][0-9]*", value):
        errors.append(f"{key} must be a canonical non-negative integer")
        return None
    return int(value)


def surfaces_fingerprint(snapshot: dict[str, Any], comment_limit: int | None = None) -> str:
    """Hash stable content from every discussion surface plus the PR body."""
    comments = snapshot.get("comments") or []
    if comment_limit is not None:
        comments = comments[:comment_limit]

    def author(row: dict[str, Any]) -> str:
        return (row.get("author") or {}).get("login", "")

    payload = {
        "pr": {
            "number": snapshot.get("number"),
            "state": snapshot.get("state"),
            "title": snapshot.get("title"),
            "isDraft": snapshot.get("isDraft"),
            "baseRefName": snapshot.get("baseRefName"),
            "body": snapshot.get("body") or "",
        },
        "comments": [
            {
                "id": row.get("id"),
                "author": author(row),
                "createdAt": row.get("createdAt"),
                "body": row.get("body") or "",
            }
            for row in comments
        ],
        "reviews": [
            {
                "id": row.get("id"),
                "author": author(row),
                "submittedAt": row.get("submittedAt"),
                "state": row.get("state"),
                "commit": (row.get("commit") or {}).get("oid"),
                "body": row.get("body") or "",
            }
            for row in snapshot.get("reviews") or []
        ],
        "threads": snapshot.get("threads") or [],
        "checks": sorted(
            snapshot.get("statusCheckRollup") or [],
            key=lambda row: json.dumps(
                row, sort_keys=True, separators=(",", ":")
            ),
        ),
    }
    encoded = json.dumps(
        payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def validate_dossier(dossier: Dossier, snapshot: dict[str, Any]) -> list[str]:
    """Validate a parsed dossier against one live PR snapshot."""
    f = dossier.fields
    errors: list[str] = []
    integers = {key: _integer(f, key, errors) for key in INTEGER_FIELDS}

    expected = {
        "schema": "1",
        "lane": ADJOINT_LANE,
        "complete": "true",
        "body": "read",
        "checks": "latest-wins-green",
        "b0": "clear",
        "scope": "pass",
        "verdict": "READY",
    }
    for key, value in expected.items():
        if f.get(key) != value:
            errors.append(f"{key} must be {value!r}")
    if f.get("domain") not in {"pass", "not-applicable"}:
        errors.append("domain must be 'pass' or 'not-applicable'")
    if dossier.author != SHARED_GITHUB_LOGIN:
        errors.append(f"comment author must be {SHARED_GITHUB_LOGIN!r}")
    if not SHA_RE.fullmatch(f.get("head", "")):
        errors.append("head must be a full lowercase 40-character SHA")
    if not re.fullmatch(r"[0-9a-f]{64}", f.get("surfaces-sha256", "")):
        errors.append("surfaces-sha256 must be a lowercase SHA-256")
    live_fingerprint = surfaces_fingerprint(snapshot, dossier.comment_index)
    if f.get("surfaces-sha256") != live_fingerprint:
        errors.append(
            "discussion surfaces changed or were not fully attested: "
            f"dossier={f.get('surfaces-sha256', '?')}, live={live_fingerprint}"
        )

    comparisons = {
        "pr": snapshot["number"],
        "comments-reviewed": dossier.comment_index,
        "reviews-reviewed": len(snapshot.get("reviews") or []),
        "threads-reviewed": len(snapshot.get("threads") or []),
        "threads-unresolved": sum(
            not thread.get("isResolved", False)
            for thread in snapshot.get("threads") or []
        ),
        "diff-files": snapshot["changedFiles"],
        "diff-additions": snapshot["additions"],
        "diff-deletions": snapshot["deletions"],
    }
    for key, live_value in comparisons.items():
        if integers.get(key) is not None and integers[key] != live_value:
            errors.append(f"{key} is stale: dossier={integers[key]}, live={live_value}")

    if f.get("head") != snapshot["headRefOid"]:
        errors.append(
            f"head is stale: dossier={f.get('head', '?')}, live={snapshot['headRefOid']}"
        )
    if snapshot.get("state") != "OPEN":
        errors.append(f"pull request state must be OPEN, live={snapshot.get('state')}")
    if snapshot.get("isDraft"):
        errors.append("draft pull request cannot be READY")
    if integers.get("threads-unresolved") not in {None, 0}:
        errors.append("READY requires zero unresolved threads")
    return errors


def evaluate(snapshot: dict[str, Any]) -> tuple[bool, list[str]]:
    """Select the newest candidate and return a fail-closed verdict."""
    comments = snapshot.get("comments") or []
    candidates: list[tuple[Dossier, list[str]]] = []
    for index, comment in enumerate(comments):
        author = (comment.get("author") or {}).get("login", "")
        dossier, parse_errors = parse_dossier(comment.get("body") or "", index, author)
        if dossier is not None:
            candidates.append((dossier, parse_errors))

    if not candidates:
        return False, ["no [ADJOINT PREFLIGHT] dossier comment found"]

    dossier, errors = candidates[-1]
    errors = [*errors, *validate_dossier(dossier, snapshot)]
    # A dossier is a snapshot. Any later comment invalidates it, including a
    # reply that claims the PR is still ready.
    if dossier.comment_index != len(comments) - 1:
        errors.append(
            "discussion changed after dossier: a fresh adjoint preflight is required"
        )
    return not errors, errors


def run_b0(pr: int) -> tuple[int, str]:
    """Run the canonical B.0 organ; its output remains evidence, not approval."""
    checker = Path(__file__).with_name("check_unaddressed_nits.py")
    proc = subprocess.run(
        [sys.executable, str(checker), str(pr)],
        capture_output=True,
        text=True,
        encoding="utf-8",
        timeout=120,
    )
    output = "\n".join(part.strip() for part in (proc.stdout, proc.stderr) if part.strip())
    return proc.returncode, output


def _utc(value: str) -> datetime:
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def _iso(value: datetime) -> str:
    return value.astimezone(timezone.utc).isoformat().replace("+00:00", "Z")


def _dossiers(snapshot: dict[str, Any]) -> list[tuple[Dossier, list[str]]]:
    dossiers: list[tuple[Dossier, list[str]]] = []
    for index, comment in enumerate(snapshot.get("comments") or []):
        author = (comment.get("author") or {}).get("login", "")
        dossier, errors = parse_dossier(comment.get("body") or "", index, author)
        if dossier is not None:
            dossiers.append((dossier, errors))
    return dossiers


def _check_name(check: dict[str, Any]) -> str:
    return str(check.get("name") or check.get("context") or "<unnamed>")


def _check_verdict(check: dict[str, Any]) -> str:
    return str(check.get("conclusion") or check.get("state") or check.get("status") or "").upper()


def _latest_checks(snapshot: dict[str, Any]) -> dict[str, dict[str, Any]]:
    latest: dict[str, dict[str, Any]] = {}
    for index, check in enumerate(snapshot.get("statusCheckRollup") or []):
        name = _check_name(check)
        stamp = str(
            check.get("startedAt")
            or check.get("createdAt")
            or check.get("completedAt")
            or ""
        )
        candidate = (stamp, str(check.get("id") or index))
        current = latest.get(name)
        if current is None or candidate > current["_order"]:
            latest[name] = {**check, "_order": candidate}
    return latest


def _checks_summary(snapshot: dict[str, Any]) -> tuple[str, list[str]]:
    latest = _latest_checks(snapshot)
    if not latest:
        return "missing", ["no live checks found"]
    pending: list[str] = []
    failed: list[str] = []
    for name, check in latest.items():
        verdict = _check_verdict(check)
        if verdict in CHECK_PENDING or not verdict:
            pending.append(name)
        elif verdict not in CHECK_OK:
            failed.append(f"{name}={verdict}")
    reasons = []
    if pending:
        reasons.append("checks in-flight: " + ", ".join(sorted(pending)))
    if failed:
        reasons.append("checks not green: " + ", ".join(sorted(failed)))
    if pending:
        return "in-flight", reasons
    if failed:
        return "not-green", reasons
    return "latest-wins-green", []


def _qualifying_review(snapshot: dict[str, Any]) -> bool:
    head = snapshot.get("headRefOid")
    latest_by_author: dict[str, tuple[tuple[str, str], dict[str, Any]]] = {}
    for index, review in enumerate(snapshot.get("reviews") or []):
        author = (review.get("author") or {}).get("login", "") or f"unknown-{index}"
        order = (str(review.get("submittedAt") or ""), str(review.get("id") or index))
        current = latest_by_author.get(author)
        if current is None or order > current[0]:
            latest_by_author[author] = (order, review)
    latest = [item[1] for item in latest_by_author.values()]
    if any(review.get("state") == "CHANGES_REQUESTED" for review in latest):
        return False
    return any(
        review.get("state") == "APPROVED"
        and (review.get("commit") or {}).get("oid") == head
        for review in latest
    )


def _grain_tag(snapshot: dict[str, Any]) -> str | None:
    texts = [snapshot.get("body") or ""]
    texts.extend(comment.get("body") or "" for comment in snapshot.get("comments") or [])
    pattern = re.compile(r"(?im)^\s*Grain:\s*(.+?)\s*$")
    for text in reversed(texts):
        match = pattern.search(text)
        if match:
            return match.group(1)
    return None


def _head_committed_at(snapshot: dict[str, Any]) -> datetime | None:
    head = snapshot.get("headRefOid")
    for commit in snapshot.get("commits") or []:
        if commit.get("oid") == head and commit.get("committedDate"):
            return _utc(commit["committedDate"])
    return None


def _comment_tail(snapshot: dict[str, Any], dossier_index: int) -> list[dict[str, Any]]:
    return [
        {
            "id": comment.get("id"),
            "author": (comment.get("author") or {}).get("login", ""),
            "createdAt": comment.get("createdAt"),
            "body": comment.get("body") or "",
        }
        for comment in (snapshot.get("comments") or [])[dossier_index + 1 :]
    ]


def classify_snapshot(
    snapshot: dict[str, Any],
    *,
    now: datetime | None = None,
    dwell_minutes: float = DEFAULT_DWELL_MINUTES,
    stale_after_minutes: float = DEFAULT_STALE_AFTER_MINUTES,
    b0_result: tuple[int, str] | None = None,
) -> QueueEntry:
    """Derive one queue entry from current surfaces without stored queue state."""
    now = (now or datetime.now(timezone.utc)).astimezone(timezone.utc)
    dossiers = _dossiers(snapshot)
    created_at = str(snapshot.get("createdAt") or "")
    head = str(snapshot.get("headRefOid") or "")
    live_fingerprint = surfaces_fingerprint(snapshot)
    checks, check_errors = _checks_summary(snapshot)
    review_qualifying = _qualifying_review(snapshot)

    if not dossiers:
        return QueueEntry(
            pr=snapshot["number"], verdict=BLOCKED, created_at=created_at,
            head=head, dossier_comment_id=None, dossier_created_at=None,
            surfaces_sha256=live_fingerprint,
            b0_rc=b0_result[0] if b0_result is not None else None,
            checks=checks, review_qualifying=review_qualifying,
            grain_tag=_grain_tag(snapshot), last_comment_is_dossier=False,
            tail_to_read=[], dossier_age_minutes=None, dwell_until=None,
            reject_cause=["no [ADJOINT PREFLIGHT] dossier comment found"],
        )

    dossier, parse_errors = dossiers[-1]
    comments = snapshot.get("comments") or []
    dossier_comment = comments[dossier.comment_index]
    dossier_created_at = dossier_comment.get("createdAt")
    dossier_age = None
    if dossier_created_at:
        dossier_age = max(0.0, (now - _utc(dossier_created_at)).total_seconds() / 60.0)
    tail = _comment_tail(snapshot, dossier.comment_index)
    validation_errors = [*parse_errors, *validate_dossier(dossier, snapshot)]
    reasons = [*validation_errors, *check_errors]
    b0_rc = b0_result[0] if b0_result is not None else None
    if b0_rc is not None and b0_rc != 0:
        detail = b0_result[1].splitlines()[0] if b0_result[1] else "no detail"
        reasons.append(f"B.0 organ blocked (rc={b0_rc}): {detail}")
    if not review_qualifying:
        reasons.append("no qualifying APPROVED review on exact head")

    stale_reasons: list[str] = []
    stale_markers = (
        "head is stale",
        "discussion surfaces changed",
        "discussion changed after dossier",
    )
    dossier_head_is_canonical = bool(SHA_RE.fullmatch(dossier.fields.get("head", "")))
    for reason in validation_errors:
        if reason.startswith("head is stale") and not dossier_head_is_canonical:
            continue
        if any(marker in reason for marker in stale_markers):
            stale_reasons.append(reason)
    if dossier.comment_index != len(comments) - 1:
        reason = "discussion changed after dossier: a fresh adjoint preflight is required"
        if reason not in reasons:
            reasons.append(reason)
        stale_reasons.append(reason)
    if (
        dossier_age is not None
        and stale_after_minutes > 0
        and dossier_age > stale_after_minutes
    ):
        reason = (
            "dossier stale by age: "
            f"age={dossier_age:.1f}m, limit={stale_after_minutes:.1f}m"
        )
        reasons.append(reason)
        stale_reasons.append(reason)

    dwell_until = None
    head_time = _head_committed_at(snapshot)
    labels = {
        str((label or {}).get("name") or "")
        for label in snapshot.get("labels") or []
    }
    dwell_waived = DWELL_WAIVER_LABEL in labels
    dwell_pending = False
    if head_time is None:
        reasons.append("head commit timestamp unavailable; dwell cannot be verified")
    else:
        floor = head_time + timedelta(minutes=dwell_minutes)
        dwell_until = _iso(floor)
        dwell_pending = not dwell_waived and now < floor

    if stale_reasons:
        status = STALE
    elif reasons:
        status = BLOCKED
    elif dwell_pending:
        status = DWELL_PENDING
        reasons = [f"dwell pending until {dwell_until}"]
    else:
        status = READY

    return QueueEntry(
        pr=snapshot["number"], verdict=status, created_at=created_at, head=head,
        dossier_comment_id=str(dossier_comment.get("id") or "") or None,
        dossier_created_at=str(dossier_created_at) if dossier_created_at else None,
        surfaces_sha256=dossier.fields.get("surfaces-sha256", ""),
        b0_rc=b0_rc,
        checks=checks, review_qualifying=review_qualifying,
        grain_tag=_grain_tag(snapshot),
        last_comment_is_dossier=dossier.comment_index == len(comments) - 1,
        tail_to_read=tail, dossier_age_minutes=dossier_age,
        dwell_until=dwell_until, reject_cause=reasons,
    )


def build_queue(
    prs: Sequence[int],
    *,
    now: datetime | None = None,
    dwell_minutes: float = DEFAULT_DWELL_MINUTES,
    stale_after_minutes: float = DEFAULT_STALE_AFTER_MINUTES,
    loader: Callable[[int], dict[str, Any]] | None = None,
    b0_runner: Callable[[int], tuple[int, str]] | None = None,
) -> tuple[dict[str, Any], bool]:
    """Load each PR independently and derive an oldest-first queue."""
    loader = loader or load_snapshot
    b0_runner = b0_runner or run_b0
    generated = (now or datetime.now(timezone.utc)).astimezone(timezone.utc)
    entries: list[QueueEntry] = []
    unknown: list[dict[str, Any]] = []
    for pr in dict.fromkeys(prs):
        try:
            b0_result = b0_runner(pr)
            snapshot = loader(pr)
            entries.append(classify_snapshot(
                snapshot, now=generated, dwell_minutes=dwell_minutes,
                stale_after_minutes=stale_after_minutes,
                b0_result=b0_result,
            ))
        except (
            RuntimeError, KeyError, TypeError, ValueError, OSError, UnicodeError,
            json.JSONDecodeError,
        ) as exc:
            unknown.append({"pr": pr, "error": f"UNKNOWN: {exc}"})
    entries.sort(key=lambda entry: (entry.created_at, entry.pr))
    counts = {status: 0 for status in (READY, BLOCKED, DWELL_PENDING, STALE)}
    for entry in entries:
        counts[entry.status] += 1
    result = {
        "schema": 1,
        "generated_at": _iso(generated),
        "queue": [entry.to_json() for entry in entries],
        "unknown": unknown,
        "metrics": {
            "received": len(set(prs)),
            "classified": len(entries),
            "unknown": len(unknown),
            **counts,
        },
    }
    return result, not unknown


def consume_pr(
    pr: int,
    *,
    now: datetime | None = None,
    dwell_minutes: float = DEFAULT_DWELL_MINUTES,
    stale_after_minutes: float = DEFAULT_STALE_AFTER_MINUTES,
    loader: Callable[[int], dict[str, Any]] | None = None,
    b0_runner: Callable[[int], tuple[int, str]] | None = None,
) -> QueueEntry:
    """Re-read every live surface immediately before an exact-head merge."""
    loader = loader or load_snapshot
    b0_runner = b0_runner or run_b0
    b0_result = b0_runner(pr)
    snapshot = loader(pr)
    return classify_snapshot(
        snapshot, now=now, dwell_minutes=dwell_minutes,
        stale_after_minutes=stale_after_minutes, b0_result=b0_result,
    )


def review_threads(pr: int) -> list[dict[str, Any]]:
    query = """
    query($owner:String!,$repo:String!,$number:Int!,$cursor:String){
      repository(owner:$owner,name:$repo){
        pullRequest(number:$number){
          reviewThreads(first:100,after:$cursor){
            nodes{
              id isResolved isOutdated path line
              comments(first:100){
                totalCount
                nodes{id body createdAt author{login}}
              }
            }
            pageInfo{hasNextPage endCursor}
          }
        }
      }
    }"""
    owner, repo = REPO.split("/", 1)
    cursor: str | None = None
    threads: list[dict[str, Any]] = []
    while True:
        args = [
            "api", "graphql", "-f", f"query={query}",
            "-F", f"owner={owner}", "-F", f"repo={repo}",
            "-F", f"number={pr}",
        ]
        if cursor is not None:
            args.extend(["-f", f"cursor={cursor}"])
        data = gh_json(args)
        connection = data["data"]["repository"]["pullRequest"]["reviewThreads"]
        nodes = connection.get("nodes") or []
        for thread in nodes:
            inline = thread.get("comments") or {}
            if inline.get("totalCount", 0) > len(inline.get("nodes") or []):
                raise RuntimeError(
                    "inline thread has more than 100 comments; complete pagination required"
                )
        threads.extend(nodes)
        page = connection["pageInfo"]
        if not page["hasNextPage"]:
            return threads
        cursor = page["endCursor"]


def _issue_comments(pr: int) -> list[dict[str, Any]]:
    rows = gh_json([
        "api", f"repos/{REPO}/issues/{pr}/comments", "--paginate",
    ])
    if not isinstance(rows, list):
        raise RuntimeError("issue comments response is not a list")
    return [
        {
            "id": row.get("node_id") or row.get("id"),
            "author": {"login": (row.get("user") or {}).get("login", "")},
            "createdAt": row.get("created_at"),
            "body": row.get("body") or "",
        }
        for row in rows
    ]


def _reviews(pr: int) -> list[dict[str, Any]]:
    rows = gh_json([
        "api", f"repos/{REPO}/pulls/{pr}/reviews", "--paginate",
    ])
    if not isinstance(rows, list):
        raise RuntimeError("reviews response is not a list")
    return [
        {
            "id": row.get("node_id") or row.get("id"),
            "author": {"login": (row.get("user") or {}).get("login", "")},
            "submittedAt": row.get("submitted_at"),
            "state": row.get("state"),
            "commit": {"oid": row.get("commit_id")},
            "body": row.get("body") or "",
        }
        for row in rows
    ]


def _pr_metadata(pr: int) -> dict[str, Any]:
    fields = (
        "number,title,body,state,isDraft,baseRefName,headRefOid,createdAt,updatedAt,"
        "changedFiles,additions,deletions,statusCheckRollup,commits,labels"
    )
    data = gh_json([
        "pr", "view", str(pr), "--repo", REPO, "--json", fields,
    ])
    if not isinstance(data, dict):
        raise RuntimeError("pull request response is not an object")
    return data


def _metadata_identity(data: dict[str, Any]) -> str:
    normalized = dict(data)
    normalized["statusCheckRollup"] = sorted(
        data.get("statusCheckRollup") or [],
        key=lambda row: json.dumps(row, sort_keys=True, separators=(",", ":")),
    )
    return json.dumps(
        normalized, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    )


def load_snapshot(pr: int) -> dict[str, Any]:
    before = _pr_metadata(pr)
    snapshot = dict(before)
    snapshot["comments"] = _issue_comments(pr)
    snapshot["reviews"] = _reviews(pr)
    snapshot["threads"] = review_threads(pr)
    after = _pr_metadata(pr)
    if _metadata_identity(before) != _metadata_identity(after):
        raise RuntimeError("pull request changed while prevalidation snapshot was read")
    return snapshot


def render_template(snapshot: dict[str, Any]) -> str:
    """Render the mechanical fields; the adjoint sets the four verdict fields."""
    fields = (
        ("schema", "1"),
        ("lane", ADJOINT_LANE),
        ("pr", str(snapshot["number"])),
        ("head", snapshot["headRefOid"]),
        ("complete", "REPLACE_WITH_true"),
        ("body", "REPLACE_WITH_read"),
        ("comments-reviewed", str(len(snapshot.get("comments") or []))),
        ("reviews-reviewed", str(len(snapshot.get("reviews") or []))),
        ("threads-reviewed", str(len(snapshot.get("threads") or []))),
        (
            "threads-unresolved",
            str(sum(
                not thread.get("isResolved", False)
                for thread in snapshot.get("threads") or []
            )),
        ),
        ("surfaces-sha256", surfaces_fingerprint(snapshot)),
        ("diff-files", str(snapshot["changedFiles"])),
        ("diff-additions", str(snapshot["additions"])),
        ("diff-deletions", str(snapshot["deletions"])),
        ("checks", "REPLACE_WITH_latest-wins-green_OR_BLOCKED"),
        ("b0", "REPLACE_WITH_clear_OR_blocked"),
        ("scope", "REPLACE_WITH_pass_OR_fail"),
        ("domain", "REPLACE_WITH_pass_OR_not-applicable_OR_fail"),
        ("verdict", "REPLACE_WITH_READY_OR_BLOCKED"),
    )
    return "\n".join([START, *(f"{key}: {value}" for key, value in fields), END])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("pr", type=int, nargs="?", help="pull request number")
    parser.add_argument(
        "--queue", type=int, nargs="+", metavar="PR",
        help="derive the oldest-first queue for the listed pull requests",
    )
    parser.add_argument(
        "--consume", type=int, metavar="PR",
        help="re-read one candidate immediately before exact-head merge",
    )
    parser.add_argument("--json", action="store_true", help="emit machine-readable output")
    parser.add_argument(
        "--dwell-minutes", type=float, default=DEFAULT_DWELL_MINUTES,
        help=f"minimum head age (default: {DEFAULT_DWELL_MINUTES:g})",
    )
    parser.add_argument(
        "--stale-after-minutes", type=float,
        default=DEFAULT_STALE_AFTER_MINUTES,
        help=f"maximum dossier age; 0 disables (default: {DEFAULT_STALE_AFTER_MINUTES:g})",
    )
    parser.add_argument(
        "--fingerprint",
        action="store_true",
        help="print the live discussion fingerprint for a new dossier",
    )
    parser.add_argument(
        "--template",
        action="store_true",
        help="render a complete dossier template from the live snapshot",
    )
    args = parser.parse_args()
    modes = sum((args.pr is not None, args.queue is not None, args.consume is not None))
    if modes != 1:
        parser.error("choose exactly one of PR, --queue, or --consume")
    if (args.queue is not None or args.consume is not None) and (
        args.template or args.fingerprint
    ):
        parser.error("--template and --fingerprint require the positional PR mode")
    if args.dwell_minutes < 0 or args.stale_after_minutes < 0:
        parser.error("age thresholds must be non-negative")

    if args.queue is not None:
        result, complete = build_queue(
            args.queue, dwell_minutes=args.dwell_minutes,
            stale_after_minutes=args.stale_after_minutes,
        )
        print(json.dumps(result, ensure_ascii=False))
        return 0 if complete else 2

    target = args.consume if args.consume is not None else args.pr
    assert target is not None
    try:
        if args.consume is not None:
            entry = consume_pr(
                target, dwell_minutes=args.dwell_minutes,
                stale_after_minutes=args.stale_after_minutes,
            )
            print(json.dumps({"schema": 1, **entry.to_json()}, ensure_ascii=False))
            return 0 if entry.status == READY else 1

        snapshot = load_snapshot(target)
        if args.template:
            print(render_template(snapshot))
            return 0
        if args.fingerprint:
            print(surfaces_fingerprint(snapshot))
            return 0
        ready, errors = evaluate(snapshot)
    except (
        RuntimeError,
        KeyError,
        TypeError,
        ValueError,
        OSError,
        UnicodeError,
        json.JSONDecodeError,
    ) as exc:
        result = {"pr": target, "ready": False, "errors": [f"UNKNOWN: {exc}"]}
        print(json.dumps(result, ensure_ascii=False) if args.json or args.consume is not None else f"UNKNOWN -- {exc}")
        return 2

    result = {
        "pr": target,
        "head": snapshot["headRefOid"],
        "ready": ready,
        "errors": errors,
    }
    if args.json:
        print(json.dumps(result, ensure_ascii=False))
    elif ready:
        print(f"READY -- PR #{target} prevalidated by adjoint at {snapshot['headRefOid']}")
    else:
        print(f"BLOCKED -- PR #{target} is not adjoint-prevalidated")
        for error in errors:
            print(f"  - {error}")
    return 0 if ready else 1


if __name__ == "__main__":
    sys.exit(main())
