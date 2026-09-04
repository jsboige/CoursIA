#!/usr/bin/env python3
r"""variation_prev_guard.py -- BLOCKING gate against `prev:` close-keyword genres (#10093)
and against `prev:` references that violate the predecessor invariant (#13475).

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

## Why a second scope was added (#13475)

Issue #13475 extended the original gate with three additional invariants on
the `prev:` PR reference (the `genre #N` tail), each of which silently breaks
the genre-adjacency measurement G-VAR-3 enforces:

  1. **PREV-SELF** -- the `prev:` points at the PR it lives in. The
     adjacency becomes vacuous: a grain compared to itself is trivially
     "different from its predecessor" (or trivially identical, depending on
     the comparator direction), so the cap never measures anything. Real
     witness: #12875.

  2. **PREV-NOT-MERGED** -- the `prev:` points at a PR that has NOT been
     merged yet. The predecessor is a moving target: the author believed
     their work flowed from a closed-but-still-editable PR, and the cap
     silently compares against a genre that may still change. Real witness:
     #13473.

  3. **PREV-NOT-PR** -- the `prev:` points at an ISSUE (not a PR). The
     predecessor is never mergeable, so genre adjacency is structurally
     unevaluable; the gate's response is the same as for an absent `prev:`,
     but the silent acceptance masked the bug. Real witness: #13439.

All three pass the original #10093 gate (the genre is canonical, the
keyword isn't a closing keyword). The defect is silent because the gate
read the surface form and never compared the cited `#N` against the
target's existence and state -- exactly the class of bug #10093 warned
about, only at the PR-reference slot rather than the genre slot.

## What it does

Scans the PR body AND every commit message on the branch for:

  (a) `prev:` whose genre is a closing keyword (`grain_tag.CLOSING_KEYWORDS`)
      -- the #10093 invariant;
  (b) `prev:` whose PR reference violates one of the three #13475 invariants
      (PREV-SELF / PREV-NOT-MERGED / PREV-NOT-PR).

A single verdict is emitted on stdout:

    {
      "guard_pass": true|false,
      "reason": "<one line>",
      "hits": {
        "body": [...],                # (a) hits in body, list of {tier, genre}
        "commits": [...],             # (a) hits in commits, list of {commit_index, tier, genre}
        "prev_invalid": [...]         # (b) hits, list of {location, kind, prev_pr, ...}
      }
    }

Exit codes:
  0  -- no `prev:` defect (close-keyword or invalid reference) anywhere
  1  -- at least one hit (the PR is non-mergeable until the offending tag is
        rewritten or the bad `prev:` reference is replaced)
  2  -- caller error (unreadable file)

## Why BLOCKING (not advisory)

The existing `check-variation-tag` job is advisory (exit 0): it posts labels
and lets the coordinator decide. That is correct for cosmetic tag defects
(offlist genre). It is WRONG here because both failure modes are silent and
cumulative:

  * (a) is DESTRUCTIVE at merge time (the squash commit message is what
    GitHub parses; an advisory label does not stop the merge);
  * (b) silently defeats the genre-adjacency cap G-VAR-3 (a grain that
    trivially satisfies the cap because its `prev:` is unresolvable is
    exactly the monoculture the cap is supposed to detect, only invisible).

Only a required check that turns `PR gate` red before merge prevents
both. The shape is the same as `check-variation-tag-required` (#10045).

## Why it scans commit messages (not just the body)

The #10093 incident: the offending tag was in a COMMIT message, not the PR
body. A body-only gate would have seen nothing (the body tag was `MED/tooling`
-- perfectly sane). The point dur (#10093) is precisely that the gate must
read the commit messages that will become the squash message. The same
discipline extends to (b): a body tag may say `prev: MED/refactor #1234`
but a commit message on the branch may carry `prev: MED/refactor #5678`,
and the commit-message reference is what the squash-merge publishes.

## What it does NOT flag

A standalone ``Fixes #123`` / ``Closes #456`` in a commit message is an
INTENDED close (catalog-pr-hygiene HARD 4 -- `Closes #N` when the PR fully
resolves the issue). This gate leaves those alone: it only flags the genre
slot of a `prev:` field, where a closing keyword is structurally wrong. The
discriminator is the `prev:` prefix, not the keyword alone.

For (b), `prev: none (premier grain)` (the first-grain exemption parsed by
`grain_tag.parse_prev`) is NEVER flagged -- a lane with no predecessor to
cite is a documented exemption, not a defect.

## How the caller passes target metadata

(b) requires knowing whether each cited `#N` resolves to a PR, and whether
that PR is merged. The workflow fetches this with `gh` and writes it as a
JSON dict:

    {"1234": {"kind": "pr", "merged": true},
     "5678": {"kind": "pr", "merged": false},
     "9012": {"kind": "issue"}}

The shape is the smallest information needed to evaluate the three
invariants; the gate does not call `gh` itself (that would couple the
test surface to a network round-trip and break the pure-function tests).
A missing/empty file yields an empty target map; only invariant (1)
(PREV-SELF) can then be evaluated, since it only needs the current PR's
number -- which the caller passes via `--current-pr`.

## Run locally

    python scripts/ci/variation_prev_guard.py --body-file body.txt --current-pr 13918
    # with commit messages (JSON array of strings):
    python scripts/ci/variation_prev_guard.py --body-file body.txt --commits-file commits.json \\
        --current-pr 13918
    # with target metadata (JSON dict of pr_number -> {kind, merged}):
    python scripts/ci/variation_prev_guard.py --body-file body.txt --current-pr 13918 \\
        --prev-targets-file targets.json
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


# Match the `#N` tail of a `prev: <TIER>/<genre> #N` clause. We re-use the
# structure of `grain_tag._PREV_RE` but anchor on the trailing `#N` because
# that's the part (b) needs to evaluate. The match is non-overlapping
# against the same body text (no global state).
_PREV_PR_REF_RE = re.compile(
    r"prev\s*:?\s*[A-Za-z]+\s*/\s*[A-Za-z0-9_-]+\s*#(\d+)\b",
    re.IGNORECASE,
)


def find_prev_self_references(text: str | None, current_pr: int | None) -> list[dict]:
    r"""Return every `prev:` whose PR reference equals `current_pr` (#13475 invariant 1).

    A grain that points `prev:` at itself is the structural false negative
    the G-VAR-3 cap was built to catch: a grain compared to itself is
    trivially "different from its predecessor" by most comparators, so the
    cap never trips. The fix is to require the reference to be DISTINCT
    from the PR that carries the tag.

    Returns a list of `{"prev_pr": int, "match": str}` -- one entry per
    offending `prev:` clause found in the text. Empty list when no
    self-reference is present, or when `current_pr` is None (the caller
    didn't tell us who we are; we can't evaluate identity).
    """
    if not text or current_pr is None:
        return []
    out: list[dict] = []
    for m in _PREV_PR_REF_RE.finditer(text):
        n = int(m.group(1))
        if n == current_pr:
            out.append({"prev_pr": n, "match": m.group(0)})
    return out


def find_prev_target_pr_numbers(text: str | None) -> list[int]:
    r"""Return the deduplicated list of PR numbers cited in any `prev:` clause.

    Used to ask the caller which targets we need metadata for. A `#N` that
    appears OUTSIDE a `prev:` clause (e.g. `Refs #13439`) is NOT a target
    here -- those citations are the body-as-context, not the adjacency
    reference. Only the `prev: ... #N` form is in scope.
    """
    if not text:
        return []
    seen: set[int] = set()
    out: list[int] = []
    for m in _PREV_PR_REF_RE.finditer(text):
        n = int(m.group(1))
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def validate_prev_targets(
    target_prs: list[int],
    targets_meta: dict[str, dict] | None,
    location: str,
) -> list[dict]:
    r"""Evaluate invariants (2) and (3) of #13475 against a target list.

    ``targets_meta`` is a dict `{str(pr_number): {"kind": "pr"|"issue",
    "merged": bool}}` -- the JSON the workflow writes. ``location`` is
    `"body"` or `"commits[<index>]"` so the verdict can name the slot.

    Returns a list of `{"location", "kind", "prev_pr"}` hits:

      * `kind="prev-not-merged"` -- the target is a PR but its `merged` flag
        is false (invariant 2).
      * `kind="prev-not-pr"` -- the target is an issue (invariant 3).

    A target missing from `targets_meta` (the workflow couldn't resolve it)
    is NOT flagged: the FN-safety contract is "unresolved -> abstain",
    matching `check_unaddressed_nits.py`'s posture on the same class of
    problem. The silent-acceptance defect that #13475 measures is at the
    SUFFICIIENT-information end (the metadata is right there in the file,
    we just didn't read it), not at the unresolvable end.
    """
    if not target_prs or not targets_meta:
        return []
    out: list[dict] = []
    for n in target_prs:
        meta = targets_meta.get(str(n))
        if meta is None:
            continue  # unresolved -> abstain (see docstring)
        kind = meta.get("kind")
        if kind == "issue":
            out.append({"location": location, "kind": "prev-not-pr",
                        "prev_pr": n})
        elif kind == "pr" and not meta.get("merged", False):
            out.append({"location": location, "kind": "prev-not-merged",
                        "prev_pr": n})
        # kind == "pr" and merged -> clean, no entry
    return out


def check(
    body: str | None,
    commits: list[str] | None = None,
    *,
    current_pr: int | None = None,
    prev_targets: dict[str, dict] | None = None,
) -> dict:
    """Return the blocking verdict for a PR body + its commit messages.

    Pure function so unit tests pin each branch without going through the
    CLI. ``commits`` is the list of commit message strings on the branch
    (the workflow fetches them via ``gh pr view --json commits``); each is
    scanned independently so the verdict can name which commit offended.

    ``current_pr`` is the number of the PR carrying the tag -- required to
    evaluate PREV-SELF (invariant 1). ``prev_targets`` is the JSON the
    workflow fetches for the cited `#N` references; required for invariants
    2 and 3. Either is optional: a caller that doesn't pass them gets only
    invariant (a) evaluated, and (b) is silently left at the original
    behaviour -- which is the safe backstop because the original gate
    didn't surface (b) at all, and broadening the silent zone is worse than
    partial coverage.
    """
    # (a) close-keyword genre (the #10093 invariant, unchanged).
    hits_body = gt.find_prev_close_keywords(body)
    hits_commits: list[dict] = []
    for i, msg in enumerate(commits or []):
        for h in gt.find_prev_close_keywords(msg):
            hits_commits.append({"commit_index": i, **h})

    # (b) invalid `prev:` PR reference (#13475 invariants 1-3).
    hits_prev_invalid: list[dict] = []
    # PREV-SELF -- body + every commit. The current_pr is constant across
    # all locations; a self-reference in a commit message is the same defect
    # as one in the body, and we name the slot so the failure is debuggable.
    hits_prev_invalid.extend(
        {"location": "body", "kind": "prev-self", "prev_pr": h["prev_pr"]}
        for h in find_prev_self_references(body, current_pr)
    )
    for i, msg in enumerate(commits or []):
        hits_prev_invalid.extend(
            {"location": f"commits[{i}]", "kind": "prev-self",
             "prev_pr": h["prev_pr"]}
            for h in find_prev_self_references(msg, current_pr)
        )
    # PREV-NOT-MERGED + PREV-NOT-PR -- body + every commit. Each location
    # gets its own target list because the body and each commit carry
    # independent `prev:` clauses; aggregating them would mix concerns.
    body_targets = find_prev_target_pr_numbers(body)
    hits_prev_invalid.extend(validate_prev_targets(
        body_targets, prev_targets, location="body"))
    for i, msg in enumerate(commits or []):
        commit_targets = find_prev_target_pr_numbers(msg)
        hits_prev_invalid.extend(validate_prev_targets(
            commit_targets, prev_targets, location=f"commits[{i}]"))

    if not hits_body and not hits_commits and not hits_prev_invalid:
        return {"guard_pass": True,
                "reason": "no prev: defect (close-keyword or invalid ref)",
                "hits": {"body": [], "commits": [], "prev_invalid": []}}

    # Compose the verdict. The reason names the worst offender first so
    # the worker reads the most actionable hint at the top of the failure
    # log; the full hit list is in the JSON for the workflow's machine
    # reader.
    reasons: list[str] = []
    if hits_body or hits_commits:
        locs = []
        if hits_body:
            locs.append(f"body ({len(hits_body)})")
        if hits_commits:
            locs.append(f"commit messages ({len(hits_commits)})")
        genres = sorted({h["genre"]
                         for h in (hits_body + hits_commits)})
        reasons.append(
            f"`prev:` genre(s) {genres} in {' + '.join(locs)} are GitHub "
            "closing keywords -> rewrite the `prev:` genre as "
            "refactor/guard/tooling (never a closing word). See #10093."
        )
    if hits_prev_invalid:
        kinds: dict[str, list[int]] = {}
        for h in hits_prev_invalid:
            kinds.setdefault(h["kind"], []).append(h["prev_pr"])
        kind_summary = ", ".join(
            f"{k} -> {sorted(set(v))}" for k, v in sorted(kinds.items())
        )
        reasons.append(
            f"`prev:` reference(s) fail invariant(s) ({kind_summary}) -> "
            "point `prev:` at a MERGED PR of the same lane, distinct from "
            "the current PR. See #13475."
        )

    return {
        "guard_pass": False,
        "reason": " | ".join(reasons),
        "hits": {
            "body": hits_body,
            "commits": hits_commits,
            "prev_invalid": hits_prev_invalid,
        },
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


def _read_prev_targets_file(path: str) -> dict[str, dict]:
    """Read a prev-targets file as a JSON dict of metadata.

    The workflow writes a dict ``{str(pr_number): {"kind", "merged"}}``
    built from ``gh pr view`` / ``gh issue view`` lookups for each
    `prev:` reference. An empty/missing file yields an empty dict -- the
    gate then abstains on invariants 2/3 (FN-safety contract; see
    ``validate_prev_targets``).

    The keys are coerced to strings (JSON object keys are always strings,
    but the gate is forgiving if the caller hands us ints).
    """
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(data, dict):
        return {}
    out: dict[str, dict] = {}
    for k, v in data.items():
        if isinstance(v, dict):
            out[str(k)] = v
    return out


def resolve_prev_targets(
    target_prs: "list[int]",
    runner=None,
    timeout: int = 15,
) -> "dict[str, dict]":
    r"""Resolve each `prev:` target to ``{"kind": "pr"|"issue", "merged": bool}``.

    This is the half of #13475 that used to live in a heredoc inside
    ``always-on-guards.yml``, where no test could reach it -- and it was
    wrong. The heredoc asked for ``gh pr view N --json state,merged``;
    ``merged`` is **not a field this `gh` exposes**, so the call exited
    non-zero for *every* target, fell through to ``gh issue view``, and
    classified **every PR as an issue**. `prev-not-pr` therefore fired on
    100 % of PRs, including the one shipping the guard: #13922 was blocked
    on ``prev-not-pr -> [14225]`` while #14225 is a PR merged at
    2026-09-03T10:28:59Z.

    The discriminant is the **exit status of `gh pr view`**, not a field of
    its payload. Measured on this repo (2026-09-03), which is also what
    ``test_resolve_prev_targets_*`` replays:

    ==========  ==========================  ==========================
    number      ``gh pr view --json state``  ``gh issue view --json state``
    ==========  ==========================  ==========================
    #14225 PR   rc=0, ``MERGED``             rc=0, ``MERGED``
    #13922 PR   rc=0, ``OPEN``               rc=0, ``OPEN``
    #14513 iss  rc!=0, *Could not resolve*   rc=0, ``OPEN``
    ==========  ==========================  ==========================

    Note the middle column is the only one that separates the classes:
    ``gh issue view`` answers for pull requests too, so it can never be the
    test. Any future rewrite must keep PR-first ordering.

    ``runner`` defaults to ``subprocess.run`` and exists so a test can
    inject the table above without a network. A target that neither call
    resolves is **omitted** from the result -- ``validate_prev_targets``
    then abstains on it (FN-safety).
    """
    if runner is None:  # pragma: no cover - trivial default
        import subprocess
        runner = subprocess.run

    out: "dict[str, dict]" = {}
    for n in sorted(set(target_prs)):
        pr = runner(["gh", "pr", "view", str(n), "--json", "state"],
                    capture_output=True, text=True, timeout=timeout)
        if getattr(pr, "returncode", 1) == 0:
            state = _json_field(pr.stdout, "state")
            if state:
                out[str(n)] = {"kind": "pr",
                               "merged": state.upper() == "MERGED"}
                continue
        issue = runner(["gh", "issue", "view", str(n), "--json", "state"],
                       capture_output=True, text=True, timeout=timeout)
        if getattr(issue, "returncode", 1) == 0:
            if _json_field(issue.stdout, "state"):
                out[str(n)] = {"kind": "issue"}
                continue
        # neither resolved -> omitted -> the gate abstains on this target
    return out


def _json_field(raw: "str | None", field: str) -> "str | None":
    """Return ``field`` from a JSON object payload, or None if unreadable."""
    try:
        data = json.loads(raw or "")
    except (json.JSONDecodeError, TypeError):
        return None
    if not isinstance(data, dict):
        return None
    value = data.get(field)
    return value if isinstance(value, str) else None


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--body-file", metavar="FILE", required=True,
                   help="path to the PR body")
    p.add_argument("--commits-file", metavar="FILE",
                   help="path to a JSON array of commit message strings")
    p.add_argument("--current-pr", metavar="N", type=int, default=None,
                   help="number of the PR carrying the Grain tag "
                        "(required to evaluate PREV-SELF)")
    p.add_argument("--prev-targets-file", metavar="FILE",
                   help="path to a JSON dict of "
                        "{str(pr_number): {kind, merged}} for each cited "
                        "`prev:` reference (required for PREV-NOT-MERGED "
                        "and PREV-NOT-PR)")
    p.add_argument("--resolve-targets", action="store_true",
                   help="resolve each cited `prev:` reference with `gh` "
                        "instead of (or in addition to) --prev-targets-file; "
                        "entries already present in the file win")
    args = p.parse_args(argv)

    try:
        with open(args.body_file, encoding="utf-8") as f:
            body = f.read()
    except OSError as e:
        print(json.dumps({"guard_pass": False, "reason": f"caller error: {e}",
                          "hits": {"body": [], "commits": [],
                                   "prev_invalid": []}}),
              file=sys.stderr)
        return 2

    commits = _read_commits_file(args.commits_file) if args.commits_file else []
    prev_targets = (_read_prev_targets_file(args.prev_targets_file)
                    if args.prev_targets_file else {})

    if args.resolve_targets:
        cited = set(find_prev_target_pr_numbers(body))
        for msg in commits:
            cited.update(find_prev_target_pr_numbers(msg))
        missing = [n for n in sorted(cited) if str(n) not in prev_targets]
        if missing:
            try:
                prev_targets = {**resolve_prev_targets(missing),
                                **prev_targets}
            except Exception as e:  # network, gh absent, timeout
                # Unresolved -> absent from the dict -> the gate abstains on
                # those targets (FN-safety). Never turn a lookup failure into
                # an accusation: that is the defect this flag repairs.
                print(f"prev-target resolution failed ({e}); "
                      "abstaining on invariants 2/3", file=sys.stderr)

    verdict = check(body, commits,
                    current_pr=args.current_pr,
                    prev_targets=prev_targets)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
