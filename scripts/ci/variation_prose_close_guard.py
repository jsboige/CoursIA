#!/usr/bin/env python3
r"""variation_prose_close_guard.py -- BLOCKING gate against close-keyword
prose that targets a PR (not an issue) (#10101).

## Why this exists

Issue #10101 measures a hole in the #10093 gate (variation_prev_guard.py):
the existing gate only scans the `prev:` field of a `Grain:` tag, so a
close-keyword followed by `#<N>` in free prose is invisible to it.

The spec:
- A standalone `Closes #<issue>` or `Fixes #<issue>` in a commit message or
  PR body is an INTENDED close (catalog-pr-hygiene HARD 4 -- `Closes #N`
  when the PR fully resolves the issue). The discipline **wants** it.
- A standalone `Closes #<PR>` or `Fixes #<PR>` is NEVER intended: PRs are
  not "resolved" by another PR (they are merged or explicitly closed). The
  #10093 incident started from `prev: MED/fix #10067` (genre-slot misuse),
  but the wider hazard is the same shape in prose: the message body or
  commit message of #10094 itself contained a `Closes #10067`-shaped
  fragment when the worker transcribed the incident for the audit, and a
  naive squash of #10094 would have re-closed #10067. The discriminator
  that catches both shapes is **the nature of the N**, not the surface
  syntax.

## What it does

Scans the PR body AND every commit message on the branch for the GitHub
auto-close keywords (`grain_tag.CLOSING_KEYWORDS`) followed by `#<N>`. For
each hit, resolves N via the injectable `resolver(n) -> "pr" | "issue" |
"unknown"`. A hit whose N is a PR is a hard failure (exit 1). A hit whose
N is an issue is silence (the gate leaves intended closes alone). A hit
whose N cannot be resolved fails OPEN with an audit warning (the worker
already pushed the prose, so the gate's job is not to invent a
disambiguation that is not there -- but it must NOT block on a transient
API failure, which would be a DoS on its own).

Emits a single verdict on stdout:

    {"guard_pass": true|false, "reason": "<one line>", "hits": [...]}

Exit codes:
  0  -- no offending prose (issues are allowed, PRs are absent, unknowns
        are absent)
  1  -- at least one close-keyword + PR hit (the PR is non-mergeable until
        the offending line is rewritten -- remove the keyword, or drop the
        `#` so GitHub does not parse it as a reference)
  2  -- caller error (unreadable file)

## Why BLOCKING (not advisory)

The failure mode is identical to #10093: a destructive auto-close at merge
time. The existing `check-prev-close-keyword-required` job is the same
shape. This gate lives next to it.

## Run locally

    python scripts/ci/variation_prose_close_guard.py --body-file body.txt \
        --commits-file commits.json --resolver-table '{"10067": "pr", "10093": "issue"}'

Without `--resolver-table`, the gate runs an INERT resolver that classifies
every N as `issue` (i.e. PASS everywhere). This is the safe default for
offline local runs: no real-world PR is auto-closed, and tests inject their
own resolver. The CI workflow supplies a resolver populated by
`gh api repos/:owner/:repo/issues/N --jq '.pull_request'` for the Ns the
scan produced.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# Make the shared extractor importable from anywhere in the repo (CI runs
# from the repo root; local devs may run from the script directory).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402


# A close-keyword word boundary that does not match when the keyword is part
# of an identifier (e.g. `prefix` should not match `fix`). GitHub's own
# keyword matcher is whitespace-and-punctuation sensitive; we mirror it
# loosely with `\b` so we catch the headline `Closes #N` form and the
# `CLOSED #N` form (the #10101 spec specimen) without false positives on
# words that contain a keyword as a substring.
_CLOSE_KW_RE = re.compile(
    r"\b(" + "|".join(re.escape(k) for k in sorted(gt.CLOSING_KEYWORDS, key=len, reverse=True)) + r")\b",
    re.IGNORECASE,
)

# `#<N>` reference -- only what GitHub parses as an issue/PR link. Strips
# the hash, captures the digits. A trailing `,` / `.` / `)` is NOT in the
# capture because GitHub's parser is permissive there but the prose scan
# wants the integer for the resolver.
_HASH_REF_RE = re.compile(r"#(\d+)\b")


# --- resolver --------------------------------------------------------------

# Default resolver: inert. Classifies every N as `issue` so the gate is
# PASS-by-default offline. Tests inject their own resolver. CI replaces it
# with one populated by `gh api` for the Ns the scan produced. The inert
# default is a deliberate safety choice: a misconfigured offline run must
# NOT block every PR (it would be a DoS); the worker can also use it to
# dry-run the scan and see the hits without resolving them.
def inert_resolver(n: int) -> str:
    """Default resolver: every N is treated as an issue (gate stays silent)."""
    return "issue"


def gh_resolver_factory(repo: str):
    """Build a resolver backed by `gh api repos/<repo>/issues/<N>`.

    Caches per-N to bound the network budget. The CI workflow passes this
    resolver only when GITHUB_TOKEN + GH_REPO are available. A failing call
    yields `"unknown"` -- the gate fails OPEN on unknown, never blocks on
    an API blip.
    """
    cache: dict[int, str] = {}

    def resolve(n: int) -> str:
        if n in cache:
            return cache[n]
        try:
            import subprocess  # local import: the gh-resolver is CI-only
            r = subprocess.run(
                ["gh", "api", f"repos/{repo}/issues/{n}", "--jq", ".pull_request"],
                capture_output=True, text=True, timeout=10,
            )
            if r.returncode != 0:
                cache[n] = "unknown"
                return "unknown"
            # `gh api --jq .pull_request` prints `null` for issues (no
            # `pull_request` key) and an object `{url: ...}` for PRs.
            v = r.stdout.strip()
            if v == "null" or v == "":
                cache[n] = "issue"
                return "issue"
            if v.startswith("{"):
                cache[n] = "pr"
                return "pr"
            cache[n] = "unknown"
            return "unknown"
        except Exception:
            cache[n] = "unknown"
            return "unknown"

    return resolve


# --- scan ------------------------------------------------------------------

def find_prose_close_refs(text: str | None) -> list[dict]:
    """Return all `<keyword> #N` occurrences in `text` (body or commit).

    Each hit is a `{"keyword": "close", "number": 10067, "span": (start, end)}`
    dict -- the `span` is the slice of the input that contains the keyword,
    so the failure message can quote the offending fragment. The order
    matches the input (the gate does not deduplicate; the same `Closes #100`
    twice is two hits).
    """
    if not text:
        return []
    hits: list[dict] = []
    for kw_m in _CLOSE_KW_RE.finditer(text):
        # Look ahead from the keyword's END for a `#N` reference within a
        # reasonable window (a closing paragraph can run hundreds of chars
        # before the `#N`; we cap at 200 to avoid matching a much later
        # `#N` that is not associated with this keyword -- e.g. a body that
        # mentions `Closes #100` then later `See #200` should NOT pair the
        # two). The cap is generous: GitHub's auto-close parser pairs them
        # on the same paragraph / commit message anyway, and 200 chars
        # covers the realistic shapes seen in the corpus.
        start = kw_m.end()
        window = text[start:start + 200]
        ref_m = _HASH_REF_RE.search(window)
        if not ref_m:
            continue
        hits.append({
            "keyword": kw_m.group(1).lower(),
            "number": int(ref_m.group(1)),
            "span_start": kw_m.start(),
            "span_end": start + ref_m.end(),
        })
    return hits


def classify_hits(hits: list[dict], resolver) -> tuple[list[dict], list[dict], list[dict]]:
    """Partition hits into (pr_hits, issue_hits, unknown_hits) by resolver.

    `resolver` is a callable `int -> "pr"|"issue"|"unknown"`. Same N twice
    hits the resolver twice (no caching at this layer -- the gh resolver
    caches internally, and the offline resolver is free). The verdict is
    the PR bucket that matters; the others are reported for transparency.
    """
    pr, issue, unknown = [], [], []
    for h in hits:
        kind = resolver(h["number"])
        if kind == "pr":
            pr.append(h)
        elif kind == "issue":
            issue.append(h)
        else:
            unknown.append(h)
    return pr, issue, unknown


def check(
    body: str | None,
    commits: list[str] | None = None,
    *,
    resolver=None,
) -> dict:
    """Return the blocking verdict for a PR body + its commit messages.

    `resolver` is injectable so tests can pin PR vs issue without going
    through the network. The default is the inert resolver -- see
    `inert_resolver` docstring.
    """
    if resolver is None:
        resolver = inert_resolver

    hits_body = find_prose_close_refs(body)
    hits_commits: list[dict] = []
    for i, msg in enumerate(commits or []):
        for h in find_prose_close_refs(msg):
            hits_commits.append({"commit_index": i, **h})

    pr_body, issue_body, unk_body = classify_hits(hits_body, resolver)
    pr_commits, issue_commits, unk_commits = classify_hits(hits_commits, resolver)

    pr_total = pr_body + pr_commits
    if not pr_total:
        # No PR-targeted close-keyword prose: pass. Issues + unknowns are
        # reported in the verdict for transparency but never block.
        return {
            "guard_pass": True,
            "reason": "no close-keyword prose targets a PR",
            "hits": {
                "pr": [],
                "issues_allowed": issue_body + issue_commits,
                "unknowns": unk_body + unk_commits,
            },
        }

    locs = []
    if pr_body:
        locs.append(f"body ({len(pr_body)})")
    if pr_commits:
        locs.append(f"commit messages ({len(pr_commits)})")
    numbers = sorted({h["number"] for h in pr_total})
    reason = (
        f"close-keyword prose targets a PR (#{', #'.join(str(n) for n in numbers)}) "
        f"in {' + '.join(locs)} -- PRs are not 'resolved' by prose. Remove the "
        f"keyword (or drop the `#`) so GitHub does not auto-close. See #10101."
    )
    return {
        "guard_pass": False,
        "reason": reason,
        "hits": {
            "pr": pr_body + pr_commits,
            "issues_allowed": issue_body + issue_commits,
            "unknowns": unk_body + unk_commits,
        },
    }


# --- I/O helpers ------------------------------------------------------------

def _read_commits_file(path: str) -> list[str]:
    """Read a commits file as a JSON array of message strings.

    The workflow writes `gh pr view --json commits --jq '[.[].messageBody]'`
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


def _resolver_from_table(table_json: str | None):
    """Build a resolver from a JSON `{"<N>": "pr"|"issue"}` table.

    Tests use this to pin classification without mocking. Unknown Ns in
    the table fall through to the inert_resolver default (issue).
    """
    if not table_json:
        return inert_resolver
    try:
        table = json.loads(table_json)
    except json.JSONDecodeError:
        return inert_resolver
    if not isinstance(table, dict):
        return inert_resolver

    def from_table(n: int) -> str:
        v = table.get(str(n))
        if v in ("pr", "issue"):
            return v
        return "issue"  # default safe

    return from_table


# --- CLI --------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--body-file", metavar="FILE", required=True,
                   help="path to the PR body")
    p.add_argument("--commits-file", metavar="FILE",
                   help="path to a JSON array of commit message strings")
    p.add_argument("--resolver-table", metavar="JSON",
                   help='JSON object {"<N>": "pr"|"issue"} for offline resolution; '
                        'unknown Ns default to "issue". Without this flag the gate '
                        'uses the inert resolver and always passes.')
    p.add_argument("--resolver-gh-repo", metavar="OWNER/REPO",
                   help="if set, resolve via `gh api repos/<repo>/issues/<N>` "
                        "(CI workflow mode). Takes precedence over --resolver-table.")
    args = p.parse_args(argv)

    try:
        with open(args.body_file, encoding="utf-8") as f:
            body = f.read()
    except OSError as e:
        print(json.dumps({"guard_pass": False, "reason": f"caller error: {e}", "hits": []}),
              file=sys.stderr)
        return 2

    commits = _read_commits_file(args.commits_file) if args.commits_file else []

    if args.resolver_gh_repo:
        resolver = gh_resolver_factory(args.resolver_gh_repo)
    elif args.resolver_table:
        resolver = _resolver_from_table(args.resolver_table)
    else:
        resolver = inert_resolver

    verdict = check(body, commits, resolver=resolver)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())