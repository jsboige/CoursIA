#!/usr/bin/env python3
r"""variation_prev_guard.py -- BLOCKING gate against `prev:` close-keyword genres (#10093).

## Why this exists

Issue #10093 measures a silent, destructive failure: merging PR #10063 via
squash created a commit whose message carried the line

    Grain: MED/fix -- lane myia-po-2024:CoursIA-2 -- prev: MED/fix #10067 (c.1331+50)

GitHub parsed `fix #10067` as an auto-close instruction and CLOSED PR #10067
(the core translation deliverable) without merging it -- no intention, no
keyword in the PR body of #10063 (its body tag was `MED/tooling`, sane), no
notification to its author. A closed PR reads exactly like an abandoned one.

The `prev:` field (variation-protocol.md §1) is mandatory for tracing genre
adjacency. Its genre slot reuses the same enumeration as the leading tag. The
15 canonical genres contain NO GitHub closing keyword, so a `prev:` whose genre
is `fix`/`close`/`resolve` (or inflections) is ALWAYS a misuse -- the worker
meant `refactor`, `guard`, or `tooling`. The danger is that the `genre #N`
tail is a valid auto-close instruction when the text lands in a commit
message.

## What it does

Scans the PR body AND every commit message on the branch for a `prev:` field
whose genre is a closing keyword (`grain_tag.CLOSING_KEYWORDS`). Emits a
single verdict on stdout:

    {"guard_pass": true|false, "reason": "<one line>", "hits": [...]}

Exit codes:
  0  -- no `prev:` close-keyword genre in body or commits
  1  -- at least one hit (the PR is non-mergeable until the offending tag is
        rewritten with a non-closing genre)
  2  -- caller error (unreadable file)

## Why BLOCKING (not advisory)

The existing `check-variation-tag` job is advisory (exit 0): it posts labels
and lets the coordinator decide. That is correct for cosmetic tag defects
(offlist genre). It is WRONG here because the failure is DESTRUCTIVE and
happens AT MERGE TIME: the squash commit message is what GitHub parses,
and an advisory label does not stop the merge. Only a required check that
turns `PR gate` red before merge prevents the auto-close -- the same shape
as `check-variation-tag-required` (#10045).

## Why it scans commit messages (not just the body)

The #10093 incident: the offending tag was in a COMMIT message, not the PR
body. A body-only gate would have seen nothing (the body tag was `MED/tooling`
-- perfectly sane). The point dur (#10093) is precisely that the gate must
read the commit messages that will become the squash message.

## What it does NOT flag

A standalone ``Fixes #123`` / ``Closes #456`` in a commit message is an
INTENDED close (catalog-pr-hygiene HARD 4 -- `Closes #N` when the PR fully
resolves the issue). This gate leaves those alone: it only flags the genre
slot of a `prev:` field, where a closing keyword is structurally wrong. The
discriminator is the `prev:` prefix, not the keyword alone.

## Run locally

    python scripts/ci/variation_prev_guard.py --body-file body.txt
    # with commit messages (JSON array of strings):
    python scripts/ci/variation_prev_guard.py --body-file body.txt --commits-file commits.json
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Make the shared extractor importable from anywhere in the repo (CI runs
# from the repo root; local devs may run from the script directory).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402


def check(body: str | None, commits: list[str] | None = None) -> dict:
    """Return the blocking verdict for a PR body + its commit messages.

    Pure function so unit tests pin each branch without going through the
    CLI. ``commits`` is the list of commit message strings on the branch
    (the workflow fetches them via ``gh pr view --json commits``); each is
    scanned independently so the verdict can name which commit offended.
    """
    hits_body = gt.find_prev_close_keywords(body)
    hits_commits: list[dict] = []
    for i, msg in enumerate(commits or []):
        for h in gt.find_prev_close_keywords(msg):
            hits_commits.append({"commit_index": i, **h})

    if not hits_body and not hits_commits:
        return {"guard_pass": True, "reason": "no prev: close-keyword genre", "hits": []}

    locs = []
    if hits_body:
        locs.append(f"body ({len(hits_body)})")
    if hits_commits:
        locs.append(f"commit messages ({len(hits_commits)})")
    # The one-line fix: map the closing-keyword genre to its canonical
    # non-closing equivalent. `fix` -> `refactor` (can-be-rouging work) or
    # `guard`; the worker picks. The reason must name the offending genres
    # so the failure is debuggable from the job log alone.
    genres = sorted({h["genre"] for h in (hits_body + hits_commits)})
    reason = (
        f"`prev:` genre(s) {genres} in {' + '.join(locs)} are GitHub closing "
        f"keywords -> rewrite the `prev:` genre as refactor/guard/tooling "
        f"(never a closing word). See #10093."
    )
    return {
        "guard_pass": False,
        "reason": reason,
        "hits": {"body": hits_body, "commits": hits_commits},
    }


def _read_commits_file(path: str) -> list[str]:
    """Read a commits file as a JSON array of message strings.

    The workflow writes ``gh pr view --json commits --jq '[.[].messageBody]'``
    to the file. A plain JSON array of strings is the robust shape: commit
    messages are multi-line, so a line-oriented format would be ambiguous.
    An empty/missing file yields an empty list (no commits to scan).
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
        print(json.dumps({"guard_pass": False, "reason": f"caller error: {e}", "hits": []}),
              file=sys.stderr)
        return 2

    commits = _read_commits_file(args.commits_file) if args.commits_file else []

    verdict = check(body, commits)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
