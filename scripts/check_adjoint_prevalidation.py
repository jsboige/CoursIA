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
from dataclasses import dataclass
from typing import Any

REPO = "jsboige/CoursIA"
ADJOINT_LANE = "myia-po-2025:CoursIA-2"
SHARED_GITHUB_LOGIN = "jsboige"
START = "[ADJOINT PREFLIGHT]"
END = "[/ADJOINT PREFLIGHT]"
SHA_RE = re.compile(r"[0-9a-f]{40}")

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
        "number,title,body,state,isDraft,baseRefName,headRefOid,updatedAt,"
        "changedFiles,additions,deletions,statusCheckRollup"
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
    parser.add_argument("pr", type=int, help="pull request number")
    parser.add_argument("--json", action="store_true", help="emit machine-readable output")
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
    try:
        snapshot = load_snapshot(args.pr)
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
        result = {"pr": args.pr, "ready": False, "errors": [f"UNKNOWN: {exc}"]}
        print(json.dumps(result, ensure_ascii=False) if args.json else f"UNKNOWN -- {exc}")
        return 2

    result = {
        "pr": args.pr,
        "head": snapshot["headRefOid"],
        "ready": ready,
        "errors": errors,
    }
    if args.json:
        print(json.dumps(result, ensure_ascii=False))
    elif ready:
        print(f"READY -- PR #{args.pr} prevalidated by adjoint at {snapshot['headRefOid']}")
    else:
        print(f"BLOCKED -- PR #{args.pr} is not adjoint-prevalidated")
        for error in errors:
            print(f"  - {error}")
    return 0 if ready else 1


if __name__ == "__main__":
    sys.exit(main())
