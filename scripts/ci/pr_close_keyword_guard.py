#!/usr/bin/env python3
r"""pr_close_keyword_guard.py -- BLOCKING gate against ``<closing-keyword> #N``
that closes a PR (#10101).

## Why this exists

The #10093 gate (``variation_prev_guard.py``) blocks a closing keyword in the
*genre slot of a ``prev:`` field* -- structurally always wrong. But the same
auto-close danger lives in **free prose followed by a PR number**. Issue #10101
measures it firsthand: PR #10094's own commit message carried a line saying it
had CLOSED a PR (the translation core deliverable) without merging it. A naive
squash of #10094 would have re-closed that PR -- the exact victim #10093
protects -- because GitHub parses ``<closing-keyword> #N`` in a commit message
as an auto-close instruction whenever N resolves to a PR.

## The discriminator -- the NUMBER's nature, not the keyword's context

Closing an **issue** by keyword is intended (catalog-pr-hygiene HARD 4 --
``Closes #N`` is what makes the backlog shrink on its own). Closing a **PR** by
keyword never is: one does not "resolve" a PR -- one merges it or closes it
explicitly. So the gate resolves each referenced N:

  - N is an ISSUE -> silence (intended close)
  - N is a PR      -> BLOCKING failure
  - N missing / API error -> fail-open (warn, do not crash the job)

The resolver is **injectable** so unit tests never touch the network: the
caller passes a callable ``int -> "pr"|"issue"|"missing"|"error"``, or leaves
it None for the default ``gh``-based resolver (used by CI).

## What it scans

The PR body AND every commit message on the branch (the offending text in
#10101 was a COMMIT, and the squash message is what GitHub parses -- the same
reason ``variation_prev_guard.py`` scans commits).

## Why BLOCKING (not advisory)

Same reason as #10093: the failure is DESTRUCTIVE and happens AT MERGE TIME.
An advisory label does not stop the squash. Only a required check turning
``PR gate`` red before merge prevents the auto-close.

## Run locally

    python scripts/ci/pr_close_keyword_guard.py --body-file body.txt
    # with commit messages (JSON array of strings):
    python scripts/ci/pr_close_keyword_guard.py --body-file body.txt --commits-file commits.json

The GH-based resolver needs ``GH_REPO`` and ``GH_TOKEN`` in the environment
(both are present in CI).
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Callable

# Make the shared extractor importable from anywhere in the repo.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402

# The four kinds a referenced number can resolve to.
#   "pr"      -> N is a Pull Request  -> BLOCKING (closing a PR by keyword is never intended)
#   "issue"   -> N is an Issue        -> silence (catalog-pr-hygiene HARD 4 intended close)
#   "missing" -> N does not exist     -> fail-open warn (stale ref, not a crash)
#   "error"   -> the API call failed  -> fail-open warn (do not fail-closed on a network blip)
NumberKind = str
Resolver = Callable[[int], NumberKind]


def gh_resolver(number: int) -> NumberKind:
    """Resolve ``number`` to "pr"/"issue"/"missing"/"error" via the ``gh`` CLI.

    Uses ``gh api repos/:owner/:repo/issues/<n>``: a response with a non-null
    ``pull_request`` field is a PR; null is an issue; a 404 is "missing".
    Any other failure (auth, rate limit, network) is "error" -- the gate
    fails OPEN on it (a network blip must not block legitimate merges).
    Reads ``GH_REPO``/``GH_TOKEN`` from the environment (set by the workflow).
    """
    repo = os.environ.get("GH_REPO") or os.environ.get("GITHUB_REPOSITORY")
    if not repo:
        return "error"
    try:
        # ``gh api`` prints the JSON object; we only need whether
        # ``.pull_request`` is null. ``--jq`` exits non-zero on a 404, which
        # we catch as "missing".
        out = subprocess.run(
            ["gh", "api", f"repos/{repo}/issues/{number}", "--jq", ".pull_request"],
            capture_output=True, text=True, timeout=20,
        )
    except (OSError, subprocess.SubprocessError):
        return "error"
    if out.returncode != 0:
        # gh exits non-zero on 404 (and on auth/rate-limit). Distinguish by
        # the stderr: a "not found"/404 line -> "missing"; anything else ->
        # "error" (fail-open). The body of the 404 response carries no PR.
        stderr = (out.stderr or "").lower()
        if "not found" in stderr or "404" in stderr:
            return "missing"
        return "error"
    # ``.pull_request`` is a dict for a PR, null/empty for an issue.
    body = (out.stdout or "").strip()
    return "pr" if body and body != "null" else "issue"


def check(body: str | None, commits: list[str] | None = None,
          resolver: Resolver | None = None) -> dict:
    """Return the blocking verdict for a PR body + commit messages (#10101).

    Pure function: ``resolver`` is injected (default ``gh_resolver``), so unit
    tests pass a table-based resolver and never touch the network. Finds every
    ``<closing-keyword> #N`` in the body and each commit, resolves N, and
    BLOCKS iff any resolved N is a PR. Issues pass (intended close); missing /
    error numbers pass with a warning (fail-open).
    """
    resolve: Resolver = resolver or gh_resolver
    warnings: list[str] = []
    pr_hits: list[dict] = []

    def _resolve_hits(text: str, location: str) -> None:
        for h in gt.find_close_keyword_pr_refs(text):
            kind = resolve(h["number"])
            entry = {**h, "kind": kind, "location": location}
            if kind == "pr":
                pr_hits.append(entry)
            elif kind == "issue":
                pass  # intended close (catalog-pr-hygiene HARD 4) -> silence
            else:  # missing / error
                warnings.append(
                    f"referenced #{h['number']} resolved as '{kind}' at {location} "
                    f"-- fail-open (not blocking), but the ref may be stale."
                )

    _resolve_hits(body or "", "body")
    for i, msg in enumerate(commits or []):
        _resolve_hits(msg, f"commit[{i}]")

    if not pr_hits:
        return {
            "guard_pass": True,
            "reason": "no closing-keyword + PR-number reference found",
            "hits": [],
            "warnings": warnings,
        }

    # Cite each offending line + tell the author what to do (acceptance #5):
    # drop the keyword, or write the number without the `#`.
    cite = [
        f"`{h['keyword']} #{h['number']}` ({h['location']}, resolves to a PR)"
        for h in pr_hits
    ]
    reason = (
        f"closing-keyword + PR-number reference(s) that would auto-close a PR on "
        f"squash: {cite}. Remove the closing keyword, or write the number "
        f"WITHOUT the leading `#` (a bare number is not an auto-close). See #10101."
    )
    return {
        "guard_pass": False,
        "reason": reason,
        "hits": pr_hits,
        "warnings": warnings,
    }


def _read_commits_file(path: str) -> list[str]:
    """Read a commits file as a JSON array of message strings (same shape as
    ``variation_prev_guard.py``: ``gh pr view --json commits --jq '[.[].messageBody]'``).
    Empty/missing -> no commits to scan.
    """
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    if isinstance(data, list):
        return [str(m) for m in data if isinstance(m, str)]
    return []


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--body-file", metavar="FILE", required=True,
                   help="path to the PR body")
    p.add_argument("--commits-file", metavar="FILE",
                   help="path to a JSON array of commit message strings")
    args = p.parse_args(argv)

    try:
        with open(args.body_file, encoding="utf-8") as f:
            body = f.read()
    except OSError as e:
        print(json.dumps({"guard_pass": False, "reason": f"caller error: {e}",
                          "hits": [], "warnings": []}), file=sys.stderr)
        return 2

    commits = _read_commits_file(args.commits_file) if args.commits_file else []
    verdict = check(body, commits)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
