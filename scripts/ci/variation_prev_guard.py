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

  2. **PREV-ABANDONED** -- the `prev:` points at a PR that was **closed
     without merging**. The declared lineage was given up: nothing it
     carries will ever reach `main`, so the adjacency is measured against
     a grain that does not exist there.

     This invariant used to read "not merged", i.e. it fired on OPEN PRs
     too, and that was wrong -- see ``validate_prev_targets`` for the
     measurement (five PRs blocked on 2026-09-08 whose four cited
     predecessors were all merely in flight) and for why an OPEN
     predecessor is the *mandated* state of a lane holding R1's floor.
     The witness the original invariant cited, #13473, merged on
     2026-08-29 without anyone touching it.

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
      (PREV-SELF / PREV-ABANDONED / PREV-NOT-PR).

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

(b) requires knowing whether each cited `#N` resolves to a PR, and in
which state. The workflow fetches this with `gh` and writes it as a JSON
dict:

    {"1234": {"kind": "pr", "state": "MERGED", "merged": true},
     "5678": {"kind": "pr", "state": "OPEN",   "merged": false},
     "3456": {"kind": "pr", "state": "CLOSED", "merged": false},
     "9012": {"kind": "issue", "state": "OPEN"}}

``state`` is the field invariant (2) tests; the three PR states are three
different verdicts (clean / clean / blocked) and the `merged` boolean
cannot express that.

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
    # with target metadata (JSON dict of pr_number -> {kind, state}):
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


# Citation masking is shared with the close-keyword finder since #14780: the
# citation/declaration split a `prev:` clause needs (#14550, multi-line #14700)
# is the same split a ``fixes #N`` citation needs. The canonical surface lives
# in grain_tag (``gt.mask_code_spans``) so both guards mask identically.


def _first_grain_line(text: str | None) -> str | None:
    r"""Return the first line of `text` that carries a `Grain:` declaration.

    The canonical tag line is the ONLY line where a `Grain:` mention is a
    DECLARATION -- anywhere else (`the \`Grain:\` field is mandatory`,
    section "How the Grain: tag is parsed"), `Grain:` is a citation of the
    concept, never a declaration of THIS grain's tag. c.966 measured the
    cost of conflating the two on PR #14592: a commit's message body
    documented `` `prev: MED/training #14592` was self-rouge`` in its prose,
    and the line-search naively fed the whole body to `parse_prev`, which
    matched the prose citation and reported `prev: #14592` as the
    declaration. The fix is to bound the search to the line that carries
    the actual `Grain:` declaration, leaving `parse_prev` to handle the
    backticks / noise stripping it already knows.

    A line that contains `Grain:` somewhere (the substring match) but is
    NOT itself a tag declaration (e.g. ``the ``Grain:`` field is mandatory``)
    still gets returned, but `parse_prev` will return
    ``pr_number: None`` on it -- a line without a `<TIER>/<genre> #N` slot
    is structurally not a declaration, and returning `None` preserves the
    safety property.

    Fenced blocks are masked BEFORE the line search (#15932), and with the
    NARROW mask (`gt.mask_fenced_blocks`, inline spans kept): a reproduction
    block that quotes a defective tag line verbatim is a citation, and when
    it sits ABOVE the real tag line it used to win the "first line" race --
    the guard then validated the quote's target as if it were the author's
    `prev:` and red-lit the PR on a predecessor it never pointed at (#15925).
    Masking inline spans here instead would break the backtick-wrapped tag
    line that `parse_prev` relies on, hence the split surface.
    """
    if not text:
        return None
    for line in gt.mask_fenced_blocks(text).splitlines():
        if "Grain:" in line:
            return line
    return None


def _declared_prev_pr(text: str | None) -> int | None:
    r"""The single `prev:` PR the canonical tag reader sees (#14550, c.966).

    The canonical tag line is the ONLY line where a `prev:` mention is a
    DECLARATION -- the BLIND-SPOT CONTROL the gate owes to lanes that wrap
    their entire tag line in backticks is preserved by `parse_prev`, which
    strips them. But the search must be BOUNDED to the tag line: a prose
    documentation line (`` `prev: MED/training #14592` was self-rouge``)
    is a citation of another grain's tag, never a declaration of THIS
    grain's `prev:`. Without the bound, `parse_prev` matches the prose
    citation and reports it as the declaration, which is exactly what
    blocked PR #14592 (`commits[2]` = `b974f2721`, the c.957 REPAIR P0
    commit, restored by the GitHub `pulls/{id}/commits` REST endpoint
    despite being an orphan in the local branch graph -- c.966 ★★★
    fondateur).

    Bounded to the first `Grain:` line, the function is safe across all
    four shapes:

      (a) commit message WITHOUT a tag line + `prev:` in prose (c.966
          bug) -> no `Grain:` line -> returns None.
      (b) tag line wrapped in backticks (BLIND-SPOT CONTROL) -> first
          `Grain:` line starts with `` ` `` and carries the tag ->
          `parse_prev` strips backticks -> returns the declared PR.
      (c) PR body normal with a tag line -> first `Grain:` line is the
          tag -> returns the declared PR.
      (d) PR body with a tag line + a prose citation of another grain's
          `prev:` -> first `Grain:` line is the tag, not the citation ->
          returns the declared PR, not the citation.
    """
    if not text:
        return None
    line = _first_grain_line(text)
    if line is None:
        return None
    try:
        return gt.parse_prev(line).get("pr_number")
    except Exception:
        return None


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
    for m in _PREV_PR_REF_RE.finditer(gt.mask_code_spans(text)):
        n = int(m.group(1))
        if n == current_pr:
            out.append({"prev_pr": n, "match": m.group(0)})
    if not out and _declared_prev_pr(text) == current_pr:
        out.append({"prev_pr": current_pr, "match": "prev: (tag)"})
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
    for m in _PREV_PR_REF_RE.finditer(gt.mask_code_spans(text)):
        n = int(m.group(1))
        if n not in seen:
            seen.add(n)
            out.append(n)
    declared = _declared_prev_pr(text)
    if declared is not None and declared not in seen:
        seen.add(declared)
        out.append(declared)
    return out


def validate_prev_targets(
    target_prs: list[int],
    targets_meta: dict[str, dict] | None,
    location: str,
) -> list[dict]:
    r"""Evaluate invariants (2) and (3) of #13475 against a target list.

    ``targets_meta`` is a dict `{str(pr_number): {"kind": "pr"|"issue",
    "state": "OPEN"|"CLOSED"|"MERGED"}}` -- the JSON ``resolve_prev_targets``
    writes. ``location`` is `"body"` or `"commits[<index>]"` so the verdict
    can name the slot.

    Returns a list of `{"location", "kind", "prev_pr"}` hits:

      * `kind="prev-abandoned"` -- the target is a PR **closed without
        merging**: the lineage the tag declares was given up, so the
        `prev:` points at nothing that will ever reach `main` (invariant 2).
      * `kind="prev-not-pr"` -- the target is an issue (invariant 3).

    **An OPEN target is NOT a hit.** Invariant 2 used to fire on any
    non-merged PR, which conflated two states that are not remotely the
    same defect:

    ==========  =====================================================
    target      what it says about the lineage
    ==========  =====================================================
    ``MERGED``  the predecessor landed -- clean
    ``OPEN``    the predecessor is **still in flight** -- clean too
    ``CLOSED``  the predecessor was abandoned -- the real defect
    ==========  =====================================================

    Flagging ``OPEN`` punished the exact behaviour R1 of
    `proactive-coordination.md` *mandates*: "1 PR entre 2 wakeups =
    PLANCHER, jamais plafond -- une PR livree ne clot pas la session,
    re-pioche IMMEDIATEMENT". A lane that opens its next PR before the
    previous one merges is working as instructed, and this gate rejected
    it for that. Measured on 2026-09-08 at 13:20Z, by replaying this
    organ against the real bodies and commit messages: **five** open PRs
    blocked (#15156, #15190, #15207, #15209, #15210), citing **four**
    distinct predecessors (#15129, #15175, #15199, #15203) -- **all four
    OPEN, not one abandoned**. #15175 was blocked too, but on its own
    ``prev-self``; the ``prev-not-merged`` it also carried was this
    invariant firing a second time on the same self-reference, and the
    repair removes that duplicate without touching the real defect.

    An earlier count of this same set said *six*, including #15200. That
    reading was correct when taken and is no longer reproducible: #15200's
    body was replaced by ``...`` at 2026-09-08T13:11:52Z, which removed
    its ``Grain:`` line and with it every ``prev:`` clause. It is recorded
    here rather than quietly corrected, because a body that moves under a
    content measurement is exactly what makes such a measurement look
    wrong afterwards. (#15200 is now a grain-orphan -- a separate defect,
    invisible to every lane guard, tracked by GRAIN-ORPHANS-SWEEP #13086.)

    It is also the doctrine `variation_adjacency_guard.py` already holds
    since #11963: "the `prev:` field is frozen at PR-open time, so a lane
    that merges grains while the PR sits open made the gate block PRs the
    rule never aimed at". The two organs read the same field; they now
    read it the same way.

    The witness #13475 recorded for invariant 2 -- #13473, tagged
    ``prev: ... #13465`` while #13465 was OPEN -- **merged on 2026-08-29**.
    The "defect" resolved itself the moment its predecessor landed, which
    is what a transient state does and what a broken lineage does not.

    Two abstentions, both deliberate:

      * a target missing from ``targets_meta`` (the workflow couldn't
        resolve it) is NOT flagged -- FN-safety contract "unresolved ->
        abstain", matching `check_unaddressed_nits.py` on the same class of
        problem. The silent-acceptance defect #13475 measures is at the
        SUFFICIENT-information end (the metadata is right there in the
        file, we just didn't read it), not at the unresolvable end;
      * a PR-kind meta carrying **no ``state``** (a hand-written or legacy
        ``--prev-targets-file`` from before this field existed) cannot
        separate OPEN from CLOSED, so it is unresolved *for this predicate*
        and abstains for the same reason. ``resolve_prev_targets`` always
        emits ``state``; ``test_resolver_always_emits_state_for_a_pr`` is
        the control that keeps this path an edge case rather than the norm.

    ``merged`` is still emitted by the resolver for backward compatibility
    with readers of the JSON, but it is **not** what this predicate tests.
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
        elif kind == "pr":
            state = str(meta.get("state") or "").upper()
            if state == "CLOSED":
                out.append({"location": location, "kind": "prev-abandoned",
                            "prev_pr": n})
            # MERGED -> landed, clean.
            # OPEN   -> still in flight, clean (see docstring).
            # ""     -> legacy meta without `state`: abstain, we cannot
            #           tell OPEN from CLOSED and must not guess.
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
    scanned independently so the verdict can name which commit offended --
    **for close-keywords only**. Les invariants ``prev:`` lisent le body
    seul (#15309 4e axe : le message de commit n'est pas une surface
    declarative, et le corriger exige une reecriture d'historique).

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

    # (b) invalid `prev:` PR reference (#13475 invariants 1-3) -- body ONLY.
    # #15309 4e axe : un message de commit n'est pas une surface declarative
    # -- variation-protocol.md §1 place la declaration dans le [CLAIMED] et
    # le body de PR. Un `prev:` errone dans un commit ne se repare par aucun
    # geste que le protocole autorise par defaut : il faut reecrire
    # l'historique, que git-workflow.md presente comme le dernier recours.
    # Un garde n'exige pas, pour etre satisfait, un geste que la regle
    # voisine decourage. La surface commits garde son role pour les
    # close-keywords ci-dessus : la, la surface EST le mecanisme (#10093).
    hits_prev_invalid: list[dict] = []
    # PREV-SELF -- body seul.
    hits_prev_invalid.extend(
        {"location": "body", "kind": "prev-self", "prev_pr": h["prev_pr"]}
        for h in find_prev_self_references(body, current_pr)
    )
    # PREV-ABANDONED + PREV-NOT-PR -- body seul.
    body_targets = find_prev_target_pr_numbers(body)
    hits_prev_invalid.extend(validate_prev_targets(
        body_targets, prev_targets, location="body"))

    if not hits_body and not hits_commits and not hits_prev_invalid:
        return {"guard_pass": True,
                "reason": "no prev: defect (close-keyword or invalid ref)",
                "hits": {"body": [], "commits": [], "prev_invalid": []},
                # Cibles `prev:` declarees et acceptees par ce run vert :
                # la levee de commentaire #15372 les nomme, pour que le
                # remplacement du mur affiche ce qui fait tenir le vert.
                "prev_targets_accepted": sorted(set(body_targets))}

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
            "point `prev:` at a PR of the same lane, distinct from the "
            "current PR, that is merged or still open -- never at an "
            "abandoned (closed-unmerged) PR nor at an issue. See #13475."
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

    The workflow writes a dict ``{str(pr_number): {"kind", "state"}}``
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
    r"""Resolve each `prev:` target to ``{"kind", "state", "merged"}``.

    ``state`` is the verbatim ``gh`` state -- ``OPEN`` / ``CLOSED`` /
    ``MERGED`` -- and it is the field ``validate_prev_targets`` tests.
    ``merged`` is kept as a derived convenience for readers of the JSON,
    but collapsing the three states into that boolean is precisely what
    made invariant 2 unable to tell "still in flight" from "abandoned"
    (see that function's docstring).

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
                               "state": state.upper(),
                               "merged": state.upper() == "MERGED"}
                continue
        issue = runner(["gh", "issue", "view", str(n), "--json", "state"],
                       capture_output=True, text=True, timeout=timeout)
        if getattr(issue, "returncode", 1) == 0:
            istate = _json_field(issue.stdout, "state")
            if istate:
                out[str(n)] = {"kind": "issue", "state": istate.upper()}
                continue
        # neither resolved -> omitted -> the gate abstains on this target
    return out


def unresolved_prev_targets(
    cited: "set[int] | list[int]", prev_targets: dict[str, dict]
) -> list[int]:
    """Cited ``prev:`` numbers the gate could NOT resolve (#14550, 2nd defect).

    After the resolution phase, a cited number absent from ``prev_targets``
    is an ABSTENTION, not an attestation: the guard did not evaluate
    invariants 2/3 for it. Left silent, a lookup failure and a measured pass
    reach the merge-gate under the same green (#14515 was CLEAN and
    mergeable with a `prev:` at an OPEN PR, purely because the `gh`
    resolution happened to fail during its run).
    """
    return sorted(n for n in cited if str(n) not in prev_targets)


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
                        "{str(pr_number): {kind, state}} for each cited "
                        "`prev:` reference (required for PREV-ABANDONED "
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

    resolution_failed: list[int] = []
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
        # An abstention must be READABLE as one (#14550): the gate stays
        # green (FN-safety unchanged) but the verdict names what it could
        # not measure, and the ::warning:: becomes a run annotation through
        # the workflow's existing `cat /tmp/verdict.err`.
        resolution_failed = unresolved_prev_targets(cited, prev_targets)

    verdict = check(body, commits,
                    current_pr=args.current_pr,
                    prev_targets=prev_targets)
    if resolution_failed:
        verdict["resolution_failed"] = resolution_failed
        targets = ", ".join(f"#{n}" for n in resolution_failed)
        print(f"::warning::prev_guard abstention -- unresolvable target(s) "
              f"{targets} (FN-safety): this green is an abstention, not an "
              f"attestation (#14550)", file=sys.stderr)
    print(json.dumps(verdict, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
