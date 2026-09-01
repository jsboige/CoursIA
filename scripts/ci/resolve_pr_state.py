#!/usr/bin/env python3
r"""resolve_pr_state.py -- single-PR merge lookup via REST, no search lag.

## Why

GitHub's search API does NOT index newly-merged PRs immediately. Measured on
jsboige/CoursIA (2026-08-31): a PR that landed minutes ago is invisible to
``gh pr list --search "merged:>=..."`` until the index catches up -- often 5-10
minutes, sometimes longer. Downstream guards that rely on the search window
(G-VAR-3 predecessor resolution, G-LIVRE-1 deliverable detection, etc.) get a
hole in their merged sequence at exactly the wrong time: right after a merge,
when the lane is most active.

The REST endpoint ``repos/$REPO/pulls/<N>`` reads straight from the merge
table and has no lag. This helper is the no-lag primitive that closes the
hole: given a PR number, it returns the merge metadata (or ``None`` if the
PR is not merged / absent / the call fails).

## Why this lives next to ``fetch_merged_prs_since.py``

Both modules talk to GitHub's PR surface, and the G-VAR-3 guard consumes
both. Co-location keeps the import surface small for callers that already
import the sibling module.

## Output

Single JSON object on stdout:

    {"number": 123, "body": "...", "mergedAt": "2026-08-31T23:55:03Z"}

Exit code 0 if merged, 1 if not merged / absent / error. Stderr carries the
reason on non-zero exit. This mirrors the exit-code contract of
``check_already_delivered.py`` (0=NO, 1=YES, 2=AMBIGU -> here collapsed to 0/1
because a single PR cannot be ambiguous).

## Usage

    python3 scripts/ci/resolve_pr_state.py 13877
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys

# Repo is fixed in this organisation; env override exists for forks.
DEFAULT_REPO = os.environ.get("GH_REPO", "jsboige/CoursIA")


def run_gh(pr_number: int, repo: str = DEFAULT_REPO) -> tuple[int, str, str]:
    """Invoke ``gh api repos/$REPO/pulls/<N>`` with a strict JSON jq template.

    The template emits one JSON object on a single line (jq's compact
    default), with field rename ``merged_at`` -> ``mergedAt`` baked in so
    downstream callers see the same shape as ``gh pr list --json mergedAt``.

    We avoid the line-based template (``.number, .body, .merged_at, .state``)
    because real PR bodies contain embedded newlines -- including CRLF from
    GitHub's web editor -- which shift a 4-line parser's alignment. JSON
    parsing is line-agnostic and unambiguous.

    Returns ``(returncode, stdout, stderr)`` to mirror ``_run`` in sibling
    modules so test injection follows the same shape.
    """
    cmd = [
        "gh", "api", f"repos/{repo}/pulls/{pr_number}",
        "--jq", '{number: .number, body: .body, mergedAt: .merged_at, state: .state}',
    ]
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True, text=True, encoding="utf-8", errors="replace",
            timeout=30, check=False,
        )
        return proc.returncode, proc.stdout, proc.stderr
    except (subprocess.TimeoutExpired, OSError) as e:
        return 124, "", str(e)


def parse_pr(stdout: str) -> dict | None:
    """Parse the single-line JSON output into a normalized PR dict.

    Field rename happens server-side via the ``--jq`` template (``merged_at``
    snake_case -> ``mergedAt`` camelCase) so callers see the same shape as
    ``gh pr list --json mergedAt``.

    Returns ``None`` if:
      - stdout is empty or not valid JSON (gh errored to stderr instead),
      - ``mergedAt`` is null or empty (PR is open or closed-unmerged), or
      - ``state`` is not ``closed`` (a merged PR transitions to state=closed
        atomically with the merge commit; any other state = not merged).
    """
    if not stdout or not stdout.strip():
        return None
    try:
        data = json.loads(stdout)
    except json.JSONDecodeError:
        return None
    merged_at = data.get("mergedAt") or ""
    state = data.get("state") or ""
    if not merged_at or state != "closed":
        return None
    return {
        "number": data.get("number"),
        "body": data.get("body", "") or "",
        "mergedAt": merged_at,
    }


def resolve(pr_number: int, repo: str = DEFAULT_REPO, run=run_gh) -> dict | None:
    """Fetch and parse. Returns the normalized PR dict or ``None``.

    ``run`` is dependency-injected for tests. Production callers omit it
    and get the real ``gh api`` invocation.
    """
    rc, out, err = run(pr_number, repo)
    if rc != 0:
        return None
    return parse_pr(out)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("pr_number", type=int, help="PR number to resolve")
    p.add_argument("--repo", default=DEFAULT_REPO,
                   help=f"OWNER/REPO (default {DEFAULT_REPO}, env GH_REPO honoured)")
    args = p.parse_args(argv)

    pr = resolve(args.pr_number, args.repo)
    if pr is None:
        # On not-merged / not-found / error, exit 1 with a short stderr note.
        # The CLI consumer (a guard script) treats exit=1 as "no merge evidence
        # for this PR via REST" and falls through to its other sources.
        print(f"resolve_pr_state: PR #{args.pr_number} not merged / not found",
              file=sys.stderr)
        return 1

    json.dump(pr, sys.stdout, ensure_ascii=False)
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
