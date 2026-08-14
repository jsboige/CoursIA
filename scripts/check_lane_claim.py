#!/usr/bin/env python3
"""Lane-claim guard -- the "one command before you edit" of issue #9774.

#9774 (mandat user 2026-08-06) diagnosed why two lanes delivered #9764 twice:
the `[CLAIMED]` signal lived on the per-lane dashboard, which (a) does not cross
lanes, (b) is garbage-collected by auto-condensation, and (c) mixed local and
UTC timestamps -- a stamp `2026-08-07T00:52Z` that was actually 00:52 CEST
inverted the cross-lane claim order and nearly got the coordinator to entrench
the wrong priority. None of it was a discipline failure: both workers passed
their `gh pr list` guard, which only sees PUSHED work. The collision is born in
the "I decided to work on X" -> "I pushed" window, where the only signal is the
claim, and the claim was in a silo.

This tool operationalises the worker-side of the fix (the rule change itself
needs user sign-off; this is the mechanism that the rule will call):

  - **check** (default): before editing a file for a grain on issue #N, run
        check_lane_claim.py N --lane myia-po-2024:CoursIA
    It reads the issue comments, reconstructs the claim state per lane, and
    exits 1 if ANOTHER lane holds an active (unreleased) claim -- do not start,
    pick elsewhere. Exit 0 means the way is clear (optionally: your own lane
    already claimed, you are resuming).

  - **--stale-threshold HOURS** (check mode): treat OTHER lanes' claims older
    than HOURS as STALE -- the guard no longer blocks on them, it prints a
    `STALE_CLAIM <lane> <age>h` warning instead. This unblocks a lane when a
    prior claimer died (killed session, re-image, exhausted credit) without a
    release. Age is the server `createdAt`, never the body. The new claimant
    MUST still post its own `[CLAIMED]`; the stale claim is not a silent bypass.

  - **--claim "<intention>"**: post a `[CLAIMED] lane <machine:workspace>`
    comment. GitHub server-stamps it UTC -- the body carries NO timestamp, so
    Defaut 2 (local time wearing a `Z` suffix) is impossible by construction.

  - **--release [--note "..."]**: post a `[RELEASED]` comment, closing the
    active claim of this lane on the issue.

  - **--paths PATH [PATH ...]** (path mode, #9959): given one or more file
    paths/globs, list the OPEN PRs whose `files[]` intersect any of them and
    whose Grain tag names a DIFFERENT lane. Exit 2 with the colliding PRs
    printed by number + lane + intersection paths; exit 0 if the path is
    clear; exit 1 if `gh` itself fails. `--paths` complements -- it does not
    replace -- the issue-claim check above: the issue comment is still the
    authoritative claim record (single locus, server-stamped), `--paths`
    only adds the missing "is there already an OPEN PR on the same file?"
    leg of L898. The motivating incident (2026-08-08 R3D, #9955 / #8696) was
    two lanes of the SAME machine, only minutes apart, each having passed
    the issue-claim check -- there was no other-lane issue claim to trip on.

The authoritative timestamp is the comment's server `createdAt`, NEVER a stamp
written in the body. That is the whole of the Defaut-2 fix.

The lane token is read by `grain_tag.extract_lane` -- the SAME reader the Grain
tag and the G-VAR-2 organ use (#9485, single reader), so a claim comment and a
PR body never disagree on what a lane is.

Limitation (documented): claim state is comment-based. A merged PR that
references the issue is not auto-detected as a release -- the lane should
`--release` (or post `[DONE]`) when its PR lands. Detecting merges is a future
flag; the comment contract is the MVP.

Exit codes: 0 ok / 1 blocked (other lane holds active issue claim) /
2 io-or-gh error (issue mode) OR cross-lane OPEN-PR collision (--paths mode).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

# Shared lane reader (#9485) -- see scripts/grain_tag.py.
from grain_tag import extract_lane

# --- markers -----------------------------------------------------------------

# A comment is a claim EVENT only if it carries one of these bracketed markers.
# `[DONE]`/`[RELEASED]`/`[CANCELLED]`/`[ABANDONED]` close a claim; `[CLAIMED]`
# opens one. Read on ISSUE comments (the claim registry per #9774), not on the
# dashboard. Case-insensitive, tolerates inner spaces.
# Line-anchored (`(?m)^...`): a marker only enacts a state change when it
# STARTS a line -- the convention of every `--claim`/`--release` post and every
# coordinator dispatch. A marker MENTIONED mid-sentence in prose is not an event.
# Closes the #10228 false-negative: ai-01's claim comment ended with the
# instructional sentence "Release with `[RELEASED]` when your PR lands" -- the
# unanchored regex took that mid-prose `[RELEASED]` as the final-intent close,
# neutralising the real `[CLAIMED]` and reporting the issue CLEAR while another
# lane held an active claim. `findall` still returns markers in order, so the
# legitimate "last marker wins" design (a `[CLAIMED]\n[DONE]` edit sequence on
# separate lines) is preserved -- only mid-line mentions are rejected.
# Decoration tolerance (#10906): issue comments are markdown-rendered, and
# agents legitimately post `**[CLAIMED] ...**`, `## [CLAIMED] ...`, `- [CLAIMED]
# ...`, `> [CLAIMED] ...` etc. The legacy `^[ \t]*\[` anchor voided every such
# marker (8 voided on 70 issues, including po-2024's [CLAIMED] on #10043 and
# po-2025's on #10038). The prefix group eats up to 6 leading `#>*+-` chars
# (headings / bullets / blockquotes / nested lists), then an optional `**`/`__`
# bold pair opener, then whitespace, then the bracket. A `[` NOT immediately at
# a decorator position (e.g. `- Prose with [CLAIMED] mid-line`) still does not
# match -- the mid-prose non-regression property is preserved.
_MARKER_RE = re.compile(
    r"(?m)^[ \t]*(?:[#>*+-]{1,6}[ \t]*)*(?:\*\*|__)?[ \t]*\[\s*(CLAIMED|RELEASED|CANCELLED|ABANDONED|DONE|OVERRIDE)\s*\]",
    re.IGNORECASE,
)
_OPEN = {"CLAIMED"}
_CLOSE = {"RELEASED", "CANCELLED", "ABANDONED", "DONE"}
# `[OVERRIDE] lane <machine:workspace>` (#10223): coordinator adjudication --
# GRANTS the claim to the named lane and CLOSES every other lane's claim in one
# gesture. Distinct from CLAIMED (grants to one) and RELEASED/DONE (closes one):
# override does both at once, which is the only mechanical trace of a
# coordinator merging against a held claim (the gap that let #10169 / #10161 be
# merged without a written adjudication). Additive: the existing markers keep
# their semantics, so no prior test changes.
#
# `paths:` clause (#10342 for [OVERRIDE], extended to [CLAIMED]/[RELEASED] by
# #10419): an optional path scope after the lane token. When present on an
# [OVERRIDE], the "close all others" effect is BOUND to the listed paths
# (fnmatch, comma-separated). When present on a [CLAIMED], the claim is SCOPED
# to those paths -- two lanes whose scoped claims do NOT intersect are free to
# work the same issue in parallel (the nominal pattern for multi-instance
# audits like #10382, one lane per notebook). Other lanes remain FREE on paths
# outside the scope. Syntax: `[CLAIMED] lane <machine:workspace> -- paths: g1, g2`.
# Without the clause, the marker is EPIC-WIDE (legacy semantics, preserved):
# an unscoped [CLAIMED] blocks every other lane, an unscoped [OVERRIDE] closes
# every other lane -- exactly as before #10342/#10419.
_OVERRIDE = {"OVERRIDE"}
# The token is OPTIONAL; the lane stays REQUIRED (an override without a named
# beneficiary is unattributed, per existing semantics). Capture groups:
# 1 = comma-separated path list (already stripped of surrounding spaces).
# Recognised on [CLAIMED], [RELEASED] (attached; the reducer treats release as
# a full lane-close, so the scope is informational there), and [OVERRIDE].
# Same leading-decoration tolerance as `_MARKER_RE` (#10906). In practice the
# reducer feeds this regex the `_line_for_match` output (which starts at the
# `[`), so the legacy `^[ \t]*\[` anchor already worked -- the prefix group is
# defense-in-depth for direct calls on a full decorated marker line. The path
# list capture deliberately does NOT strip a trailing `**`/`__` (closing pair
# of a bold-wrapped claim): `paths: dir/**` is a legitimate recursive glob,
# indistinguishable from a closing decorator by suffix alone. Trailing `*` in
# fnmatch matches empty, so a captured `glob**` still matches `glob`.
_PATHS_CLAUSE_RE = re.compile(
    r"(?im)^[ \t]*(?:[#>*+-]{1,6}[ \t]*)*(?:\*\*|__)?[ \t]*\[\s*(?:CLAIMED|RELEASED|OVERRIDE)\s*\][^\n]*?paths\s*:\s*([^\n]+?)\s*$"
)
# #10958 -- the annotation suffix separator. Fleet claims append a trailing
# annotation after the glob list: `paths: a/** -- 2026-08-11T18:10Z` (body
# timestamp) or `paths: .../** — Phase 2 : ...` (prose rationale). The clause
# regex swallows it into the LAST glob, which then matches no tracked file and
# the claim silently ends up non-blocking (fail-open). The separator must be
# whitespace-delimited on BOTH sides so a `foo--bar.py` (internal dashes, no
# spaces) is never cut. Em/en dashes are included because fleet markers use
# both (` -- ` in timestamps, ` — ` in prose rationales).
_ANNOTATION_SUFFIX_RE = re.compile(r"\s+(?:--|—|–)\s+")


class ClaimEvent(dict):
    """Typed-ish view over a parsed claim event.

    Keys: lane (str|None), action ("open"|"close"|"override"), marker (str upper),
    created_at (str ISO, server UTC), author (str|None), url (str|None),
    intent (str|None). `created_at` comes from the comment's server field, never
    from the body. `intent` is the marker line without the bracket prefix --
    the human-readable scope announcement that turns a BLOCKED verdict
    (otherwise opaque) into an actionable list of disjoint intentions (#10395
    Variante 2).
    """

    @property
    def lane(self) -> str | None:
        return self.get("lane")

    @property
    def is_open(self) -> bool:
        return self.get("action") == "open"

    @property
    def is_override(self) -> bool:
        return self.get("action") == "override"

    @property
    def intent(self) -> str | None:
        """Marker-line body excerpt (#10395 Variante 2).

        The portion of the comment AFTER the bracketed marker, with leading
        punctuation / spaces stripped, capped at ~120 characters. The point
        is to give a BLOCKED message enough context to discriminate "two
        lanes working on disjoint notebooks of the same EPIC" (legitimate
        collision detection) from "two lanes working on the same file"
        (real collision). The marker is stripped so the excerpt reads
        naturally -- `lanes myia-po-2025:CoursIA-2 — taxonomy coverage
        analysis notebook` is the intent that justifies the claim.
        """
        return self.get("intent")

    @property
    def created_at(self) -> str | None:
        return self.get("created_at")

    @property
    def marker(self) -> str | None:
        return self.get("marker")

    @property
    def author(self) -> str | None:
        return self.get("author")

    @property
    def url(self) -> str | None:
        return self.get("url")

    @property
    def paths(self) -> list[str] | None:
        """Optional path scope (#10342 OVERRIDE, #10419 CLAIMED/RELEASED).

        None when the marker is epic-wide (no `paths:` clause). A non-None value
        on an [OVERRIDE] binds its "close all others" effect to the listed globs;
        on a [CLAIMED] it SCOPES the claim, so two lanes whose paths do NOT
        intersect (fnmatch, `_path_matches`) are free to work the same issue in
        parallel. The reducer preserves the full `paths` payload; the check
        filters `others` by scope intersection (`_filter_by_claim_scope`).
        """
        return self.get("paths")

    @property
    def unparseable_scope(self) -> list[str]:
        """Subset of `paths` that survived parse but still contain `{` or `}`.

        #10597 hardener: a lane that writes `paths: foo-{a,b-*.yaml`
        (unclosed brace) yields fnmatch-garbage on expansion. The safe read
        is to treat the claim as EPIC-WIDE (`conservateur: in case of doubt,
        block rather than let through`) -- `_run_check` reads this list and
        lifts the scope back to epic-wide when non-empty.
        """
        return self.get("unparseable_scope") or []

    @property
    def empty_scope(self) -> list[str]:
        """Subset of `paths` matching ZERO tracked files in the repo (#10958).

        Unlike `unparseable_scope` (pure parse residue, computable without
        the repo), this witness requires a `git ls-files` walk, so it is
        attached at the CHECK layer (`_run_check`), not at parse. Empty when
        every glob locks at least one real file, or when the walk failed
        (best-effort: we cannot prove deadness, so we do not lift).
        """
        return self.get("empty_scope") or []


def _line_for_match(body: str, m: re.Match) -> str:
    """Return the verbatim source line carrying a marker match (marker included).

    Walks from the end of the match to the end of its line so the caller sees
    any trailing content (e.g. `[CLAIMED] #9764 - myia-po-2025:CoursIA`). This
    is the per-marker generalisation of the old `_last_marker_line`: the
    #10881 addendum fix reads EACH marker line, not just the last one.
    """
    tail = body[m.end():]
    nl = tail.find("\n")
    return (m.group(0) + (tail if nl == -1 else tail[:nl])).rstrip("\r")


def _intent_from_line(line: str | None) -> str | None:
    """Marker-line excerpt with the bracketed marker stripped (#10395 V2).

    The per-marker variant of the old `_extract_marker_intent`: strips the
    `[MARKER]` from a single line, trims leading punctuation, caps at 120
    chars. Returns None for a bare `[CLAIMED]` (nothing after the bracket).
    """
    if not line:
        return None
    text = _MARKER_RE.sub("", line, count=1)
    text = text.strip().lstrip(":—-•| ").strip()
    if not text:
        return None
    if len(text) > 120:
        text = text[:120].rstrip() + "…"
    return text


def _parse_claim_events(comment: dict) -> list[ClaimEvent]:
    """One ClaimEvent per bracketed marker line -- the #10881 reducer fix.

    A comment can LEGITIMATELY carry markers for several lanes: the natural
    shape of a coordinator arbitration is `[RELEASED] lane A` then
    `[CLAIMED] lane B -- paths: X`. The legacy single-event reader kept only
    the LAST marker (final intent): every marker of the comment was attributed
    to ONE lane (the first `lane <token>` in the whole body) with the LAST
    marker's paths clause, and intermediate `[RELEASED]`s were lost. Measured
    on #10678 2026-08-14 (ai-01's 07:30:08Z comment): po-2024:CoursIA-2 was
    credited with ai-01's gate-file scope while its own two notebooks were
    claimed by no one, and ai-01's epic-wide 07:06:23Z claim stayed active
    against every other lane.

    This function treats each marker line independently, with the lane ITS
    OWN LINE names (marker line first, whole body as fallback), its own
    paths clause, its own intent. `compute_active_claims` walks these events
    in order, so a comment can release one lane and open another, and a
    `[CLAIMED]\n[DONE]` sequence on separate lines still reduces to inactive
    (open then close). Per-marker fields keep the #10342/#10419 scope, the
    #10395 Variante-1 fallback and the #10597 hardener semantics.
    """
    body = comment.get("body") or ""
    author = (comment.get("author") or {}).get("login")
    created_at = comment.get("createdAt")
    url = comment.get("url")
    events: list[ClaimEvent] = []
    for m in _MARKER_RE.finditer(body):
        marker = m.group(1).upper()
        line = _line_for_match(body, m)
        if marker in _OPEN:
            action = "open"
        elif marker in _OVERRIDE:
            action = "override"
        else:
            action = "close"
        paths = _extract_paths_clause(line) if line else None
        # Lane attribution per marker line: the marker's OWN line first, then
        # the whole body as fallback. The line-first order is the fix -- the
        # legacy whole-body search always picked the FIRST `lane <token>` of
        # the comment, mis-attributing every later marker to that lane.
        lane = extract_lane(line, marker_line=line)
        if lane is None:
            lane = extract_lane(body, marker_line=line)
        events.append(ClaimEvent(
            lane=lane,
            action=action,
            marker=marker,
            created_at=created_at,
            author=author,
            url=url,
            paths=paths,
            # #10597 hardener -- preserve the unparseable subset of the scope
            # (residual `{` or `}` after `_expand_brace_groups`). The reducer
            # and check layer use this to lift the claim back to EPIC-WIDE
            # when the scope cannot be matched by fnmatch. Without this field
            # an unclosed-brace scope would silently degrade to "non-blocking
            # accidental empty" -- the exact defect that motivated #10597.
            unparseable_scope=_unparseable_scope_in(paths) if paths else [],
            intent=_intent_from_line(line),
        ))
    return events


def parse_claim_event(comment: dict) -> ClaimEvent | None:
    """Classify one issue comment into a claim event, or None if not a marker.

    Legacy single-event view: the LAST bracketed marker of the comment is the
    final intent (backward-compatible with every existing caller and the
    Defaut-2 / lane / scope semantics). The full reader is `_parse_claim_events`
    -- one event per marker line (#10881 addendum), used by `_sort_events`; for
    a single-marker comment the two views are identical. The lane is read by
    `extract_lane`; None when the body carries no lane token (surfaced as
    "unattributed", never guessed). The timestamp is the comment's server
    `createdAt` -- the Defaut-2 fix: body stamps are not trusted.
    """
    events = _parse_claim_events(comment)
    return events[-1] if events else None


def _split_paths_brace_aware(raw: str) -> list[str]:
    """Split a comma-separated path list on commas OUTSIDE `{...}` groups.

    A scope like `search-{6,8,9}-*.yaml` uses commas as brace alternatives,
    not as list separators. A naive `raw.split(",")` fragments it into
    `["search-{6", "8", "9}-*.yaml"]` -- three invalid globs that `fnmatch`
    will never match, so the claim silently ends up EPIC-WIDE by accident
    (#10597). This splitter tracks brace depth and only splits on depth-0
    commas, keeping each brace group intact. Empty fragments from stray
    commas are dropped (`paths: a, , b` -> `["a", "b"]`).
    """
    parts: list[str] = []
    buf: list[str] = []
    depth = 0
    for ch in raw:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth = max(0, depth - 1)
        if ch == "," and depth == 0:
            parts.append("".join(buf).strip())
            buf = []
        else:
            buf.append(ch)
    parts.append("".join(buf).strip())
    return [p for p in parts if p]


def _expand_brace_groups(pattern: str) -> list[str]:
    """Expand a single `{a,b,c}` group into plain globs.

    fnmatch supports `*`, `?`, `[seq]`, `[!seq]` but NOT `{a,b}`. A pattern
    like `search-{6,8,9}-*.yaml` therefore matches nothing via fnmatch.
    This expands the FIRST brace group into sibling globs
    (`search-6-*.yaml`, `search-8-*.yaml`, `search-9-*.yaml`); nested
    groups would need recursion, but no scope in the fleet uses nesting.
    Patterns without braces are returned unchanged.
    """
    m = re.search(r"\{([^{}]*)\}", pattern)
    if not m:
        return [pattern]
    alts = [a for a in m.group(1).split(",") if a]
    if not alts:
        return [pattern]
    return [
        f"{pattern[:m.start()]}{alt}{pattern[m.end():]}" for alt in alts
    ]


def _extract_paths_clause(text: str | None) -> list[str] | None:
    """Parse the optional `paths: <comma-list>` clause from a marker line.

    Recognised on [CLAIMED], [RELEASED], and [OVERRIDE] marker lines (#10342
    introduced the clause for [OVERRIDE]; #10419 extended it to [CLAIMED] and
    [RELEASED] so disjoint scoped claims no longer false-block each other on a
    multi-instance issue). Returns the trimmed path list, or None when the
    clause is absent -- the marker is then EPIC-WIDE (legacy semantics: an
    unscoped [CLAIMED] blocks every other lane, an unscoped [OVERRIDE] closes
    every other lane). Brace groups are expanded to sibling globs so that
    `paths: search-{6,8,9}-*.yaml` yields three matchable patterns instead of
    one silently-EPIC-WIDE accident (#10597).

    #10597 -- hardener: a scope containing UNCLOSED braces (e.g.
    `paths: foo-{a,b-*.yaml`) cannot be parsed to a matchable glob set.
    After expansion, any pattern still containing `{` or `}` is reported
    via `_unparseable_scope_in`; the caller MUST treat such a claim as
    EPIC-WIDE (conservateur: in case of doubt, block rather than let
    through). See `_run_check` for the integration.

    #10958 -- annotation suffix: a trailing ` -- <rest>` (or ` — <rest>`)
    after the glob list is TRUNCATED before the split. The clause regex
    captures to end of line, so `paths: a/** -- 2026-08-11T18:10Z` used to
    yield the single glob `a/** -- 2026-08-11T18:10Z` -- which matches no
    tracked file, so the scoped claim never blocked anyone (fail-open). The
    separator is whitespace-delimited on both sides, so an INTERNAL unspaced
    dash sequence (`foo--bar.py`) survives untouched; the truncation cuts at
    the FIRST separator, so glob content after it stays out regardless of
    how the annotation is punctuated.
    """
    m = _PATHS_CLAUSE_RE.search(text or "")
    if not m:
        return None
    raw = m.group(1)
    m_suffix = _ANNOTATION_SUFFIX_RE.search(raw)
    if m_suffix:
        raw = raw[:m_suffix.start()]
    parts = _split_paths_brace_aware(raw)
    expanded: list[str] = []
    for p in parts:
        for e in _expand_brace_groups(p):
            expanded.append(e)
    return expanded or None


def _unparseable_scope_in(parts: list[str] | None) -> list[str]:
    """Return the subset of `parts` that still contain literal `{` or `}`.

    After `_extract_paths_clause` and `_expand_brace_groups`, any pattern
    residue containing braces is a SCOPE THAT FNMATCH WILL NEVER MATCH
    (fnmatch knows `*` `?` `[seq]` `[!seq]` -- not `{a,b}`). The safe
    read is to treat the claim as epic-wide (conservateur -- #10597
    acceptance #2). The list returned here is the witness, so the
    reducer and the JSON audit can surface it without re-parsing.
    Empty when the scope is fully parseable.
    """
    if not parts:
        return []
    return [p for p in parts if "{" in p or "}" in p]


def _empty_scope_in(parts: list[str] | None,
                    tracked: list[str] | None) -> list[str]:
    """Return the subset of `parts` matching ZERO tracked files (#10958).

    The dead-glob witness: unlike `_unparseable_scope_in` (a parse residue),
    this requires the `git ls-files` walk, so the caller passes `tracked`
    (fetched once per check). Returns [] when `tracked` is None -- the walk
    failed (not a repo, git missing): we cannot prove deadness, so the
    fail-safe lift does NOT fire (best-effort, mirroring the lint). A
    NON-empty result means the glob locks nothing; `_filter_by_claim_scope`
    treats an ENTIRELY-dead scope as epic-wide (a broken claim is not a
    permissive claim).
    """
    if not parts or tracked is None:
        return []
    return [p for p in parts if not _glob_matches_tracked(p, tracked)]


def compute_active_claims(events: list[ClaimEvent]) -> tuple[dict, list[ClaimEvent]]:
    """Reduce a chronologically-ordered event list to active claims per lane.

    Returns `(active_by_lane, unattributed)`:
      - `active_by_lane`: {lane: ClaimEvent} for lanes whose LATEST event is an
        open (or the lane named by the latest override). Computed by walking
        events in order (caller sorts); later events overwrite earlier ones, a
        close removes the lane, and an **override** (#10223) grants the claim to
        its named lane while closing every other lane -- the only event type
        that touches more than one lane at once.
      - `unattributed`: events whose body carried a marker but no lane token --
        the tool surfaces them for manual verification, it does not guess.
        An override with no lane token is unattributed (an adjudication must
        name its beneficiary).
    """
    state: dict[str, ClaimEvent] = {}
    unattributed: list[ClaimEvent] = []
    for ev in events:
        if ev.lane is None:
            unattributed.append(ev)
            continue
        if ev.is_override:
            # Coordinator adjudication (#10223): grant to this lane. The
            # optional `paths:` clause (#10342, #10505) BOUNDS the "close
            # others" effect to the override's scope instead of closing every
            # other lane unconditionally. An unscoped override keeps the legacy
            # epic-wide semantics (closes all). A scoped override closes only
            # claims that INTERSECT it -- where intersection reuses the same
            # convention as `_filter_by_claim_scope`: a claim with no `paths`
            # clause is epic-wide (claims everything) so it intersects any
            # scope and is closed; a scoped claim is closed iff its paths
            # match the override's (fnmatch via `_path_matches_any`). The
            # symmetry is deliberate: disjointness must require BOTH sides to
            # declare a scope, at the reducer just as at the filter.
            # Later events (open/close) still apply on top in walk order.
            scope = ev.get("paths")
            if not scope:
                state = {ev.lane: ev}
            else:
                state = {
                    ln: e for ln, e in state.items()
                    if ln == ev.lane
                    or (
                        e.get("paths") is not None
                        and not _path_matches_any(scope, e.get("paths") or [])
                    )
                }
                state[ev.lane] = ev
        elif ev.is_open:
            state[ev.lane] = ev
        else:
            state.pop(ev.lane, None)
    return state, unattributed


# --- gh plumbing -------------------------------------------------------------

def _gh_issue_comments(issue: str) -> dict:
    """Fetch issue metadata + comments as JSON via `gh`. Raises on failure."""
    proc = subprocess.run(
        [
            "gh", "issue", "view", str(issue),
            "--json", "number,title,comments",
        ],
        capture_output=True, text=True, shell=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh issue view {issue} failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )
    return json.loads(proc.stdout)


def _sort_events(payload: dict) -> list[ClaimEvent]:
    """Parse + chronologically sort claim events from a `gh issue view` payload.

    Uses `_parse_claim_events` -- one event per marker line (#10881) -- so a
    comment carrying markers for several lanes reduces correctly instead of
    collapsing to a single (mis-attributed) event. Events from the same comment
    share the server `createdAt`; the stable sort preserves their in-comment
    marker order, so the walk-order reducer sees `[CLAIMED] X\n[DONE] X` as
    open-then-close (final state inactive), exactly as before.
    """
    events = [
        ev
        for c in payload.get("comments", [])
        for ev in _parse_claim_events(c)
    ]
    # Server createdAt, ISO 8601 UTC -> lexicographic order == chronological.
    events.sort(key=lambda e: e.created_at or "")
    return events


def _post_comment(issue: str, body: str) -> None:
    """Post an issue comment via `gh issue comment --body-file`.

    A body file (not --body) avoids shell-escaping the marker / em-dash / quotes
    and keeps the posted text byte-exact. Written under the OS temp dir, not the
    worktree, so it never leaks into a commit (cf L677-L4 body-file discipline).
    """
    with tempfile.NamedTemporaryFile(
        "w", suffix=".md", delete=False, encoding="utf-8"
    ) as fh:
        fh.write(body)
        path = fh.name
    proc = subprocess.run(
        ["gh", "issue", "comment", str(issue), "--body-file", path],
        capture_output=True, text=True, shell=False,
    )
    Path(path).unlink(missing_ok=True)
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh issue comment {issue} failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )


def _gh_open_prs_with_files() -> list[dict]:
    """Fetch all open PRs (number, title, headRefName, body, files) via `gh`.

    Used by `--paths` mode to intersect PR file lists with caller-provided
    patterns. Returns a list of dicts; each PR dict is {number, title,
    headRefName, body, files: [{path, ...}, ...], lane: str|None}. The `lane`
    key is filled by the caller -- `_run_check_paths` -- via the shared
    `extract_lane` reader, NOT here, so the lane-detection rule lives in
    exactly one place (#9485 single-reader discipline).

    Raises RuntimeError on `gh` failure so callers surface exit 2.
    """
    proc = subprocess.run(
        [
            "gh", "pr", "list", "--state", "open",
            "--json", "number,title,headRefName,body,files",
            "--limit", "200",
        ],
        capture_output=True, text=True, shell=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh pr list --state open failed (exit {proc.returncode}): "
            f"{proc.stderr.strip()}"
        )
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            f"gh pr list returned non-JSON (exit {proc.returncode}): {exc}"
        )


def _path_matches(path: str, patterns: list[str]) -> bool:
    """Return True if `path` matches any of the caller-provided patterns.

    Each pattern is a glob (fnmatch.fnmatch case-sensitive, `*` / `?` /
    `[abc]`); plain substrings without glob meta are also matched (covers
    the common dispatch form `path/to/file.py`). Symmetric with how GitHub
    UI's PR-files search treats "filter" input -- a worker who filters the
    web UI by filename and pastes the result here gets the same matches.

    Brace groups (`{a,b}`) are expanded first, so `--paths
    'sel/{6,8}-*.yaml'` behaves like the fs-shell glob a worker means
    (#10597) instead of silently matching nothing.

    The fnmatch patterns are anchored to the basename of the path AND to
    the full path, so a pattern like `*.lean` matches `knot_lean/Foo.lean`
    AND `Foo.lean` alone. This is the same convenience offered by the
    existing `grep`/git commands used in the cluster for "where does this
    file live" queries.
    """
    from fnmatch import fnmatch
    basename = path.rsplit("/", 1)[-1]
    for pat in patterns:
        for p in _expand_brace_groups(pat):
            if fnmatch(path, p) or fnmatch(basename, p):
                return True
    return False


# --- formatted output --------------------------------------------------------

_CLAIM_BODY_TMPL = (
    "[CLAIMED] lane {lane} -- {intention}\n\n"
    "(check_lane_claim #9774 -- server-stamped UTC; body timestamps are NOT "
    "authoritative. Release with `[RELEASED]` when your PR lands.)\n"
)
_RELEASE_BODY_TMPL = (
    "[RELEASED] lane {lane} -- {note}\n"
)


def _fmt_utc(iso: str | None) -> str:
    return (iso or "?").replace("T", " ").replace("Z", " UTC")


def _scope_zero_coverage_warning(
    scope: list[str] | None,
    repo_root: str | None = None,
) -> dict | None:
    """Return a warning dict if `scope` matches zero tracked files. None otherwise.

    #10597 bonus -- a lane declaring a scope that matches nothing is
    INDISTINGUISHABLE from a legitimately-empty scope (both read "the
    globs do not cover any file"). Without a positive control the lane
    never learns its lock is empty until the next round of arbitration.
    Walk the tracked files under `repo_root` (default: cwd) and return
    a structured warning when none match. Non-blocking by design: the
    gate is the structured claim, this is a usability hint.

    The walk is best-effort: when not in a git repo, or when the walk
    fails for any reason, return None. The warning is a polite nudge,
    not a structural guarantee.
    """
    if not scope:
        return None  # unscoped -> nothing to warn about
    if repo_root is None:
        repo_root = os.getcwd()
    try:
        proc = subprocess.run(
            ["git", "-C", repo_root, "ls-files"],
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    tracked = [ln for ln in proc.stdout.splitlines() if ln]
    if not tracked:
        return None
    # Apply fnmatch (with brace expansion) per file. The first hit
    # short-circuits -- we only need to know "at least one file matches".
    for path in tracked:
        if _path_matches(path, scope):
            return None
    return {"scope": scope, "tracked_count": len(tracked)}


# --- #10881 lint: malformed paths: clauses -----------------------------------
# 2026-08-14 morning on #10678: four markers, all misread SILENTLY, two lanes
# blocked 1.5h. The lint fires on stderr when a marker is READ -- visible to
# any lane running the check, NEVER changing a verdict. Three checks:
#   1. marker without a `paths:` clause -> INFO naming the epic-wide effect
#      (the information that was missing in all four cases).
#   2. implausible glob (em-dash, colon-space, escaped comma, >120 chars) ->
#      WARN "glob suspect (prose avalée ?)" -- the prose-after-clause trap.
#   3. glob matching zero tracked files -> WARN "glob sans correspondance".
#      A dead glob is almost always a typo or prose. Best-effort: when the
#      git walk fails (not a repo), the no-match check silently skips.
# Selectivity is the acceptance's core ("la moitié qui compte"): a well-formed
# marker (`paths: a/b.lean, a/c.lean`, two existing files) produces NOTHING.

_IMPLAUSIBLE_SUBSTRINGS = ("—", "–", "\\,")


def _glob_implausible(glob: str) -> bool:
    """True when a `paths:` entry cannot plausibly be a repo path (prose)."""
    if len(glob) > 120:
        return True
    if any(s in glob for s in _IMPLAUSIBLE_SUBSTRINGS):
        return True
    if re.search(r":\s", glob):  # colon followed by whitespace = prose
        return True
    return False


def _git_tracked_files(repo_root: str | None = None) -> list[str] | None:
    """Best-effort `git ls-files` under repo_root (cwd default). None on failure.

    Mirrors the walk of `_scope_zero_coverage_warning` -- the one source of
    "which files does the repo track" for both callers.
    """
    if repo_root is None:
        repo_root = os.getcwd()
    try:
        proc = subprocess.run(
            ["git", "-C", repo_root, "ls-files"],
            capture_output=True, text=True, timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    tracked = [ln for ln in proc.stdout.splitlines() if ln]
    return tracked or None


def _glob_matches_tracked(glob: str, tracked: list[str]) -> bool:
    """True when at least one tracked file matches the glob (fnmatch, basename-or-full)."""
    for path in tracked:
        if _path_matches(path, [glob]):
            return True
    return False


def _lint_claim_events(
    events: list[ClaimEvent],
    issue_number: int | None,
    repo_root: str | None = None,
    tracked: list[str] | None = None,
) -> None:
    """Emit WARN/INFO lines for malformed claim markers (#10881). Non-blocking.

    Runs on OPEN and OVERRIDE markers only: a close marker is always a full
    lane-close (its scope is informational, #10419), so an epic-wide release
    is semantically identical to a scoped one -- nothing to warn about. The
    lint only prints to stderr; verdicts are untouched. `tracked` lets a
    caller that already walked the repo (#10958 empty-scope witness) reuse
    the list instead of paying the walk twice.
    """
    if tracked is None:
        tracked = _git_tracked_files(repo_root)
    for ev in events:
        if ev.get("action") not in ("open", "override"):
            continue
        if ev.paths is None:
            print(
                f"INFO: marqueur {ev.marker} epic-wide (pas de clause paths:) "
                f"-- il bloque toutes les autres lanes sur #{issue_number} "
                f"(lane {ev.lane or '?'}).",
                file=sys.stderr,
            )
            continue
        for g in ev.paths:
            if _glob_implausible(g):
                print(
                    f'WARN: glob suspect (prose avalée ?) : "{g}" '
                    f"(lane {ev.lane or '?'})",
                    file=sys.stderr,
                )
            if tracked is not None and not _glob_matches_tracked(g, tracked):
                print(
                    f'WARN: glob sans correspondance : "{g}" '
                    f"(lane {ev.lane or '?'})",
                    file=sys.stderr,
                )


def _warn_bare_integer_paths(paths: list[str]) -> list[str]:
    """Return the `--paths` entries that are bare integers (#10881 trap).

    `--paths` uses `nargs='+'` and swallows a TRAILING positional issue
    number: `--lane X --paths a b 10678` puts `"10678"` into the paths list,
    switches to path mode, and prints a reassuring CLEAR that measured
    nothing. A bare integer in the list is almost always that trap -- the
    correct form is `check_lane_claim.py 10678 --lane X --paths a b`
    (positional FIRST).
    """
    return [p for p in paths if p.isdigit()]


# --- modes -------------------------------------------------------------------

def _claim_age_hours(created_at: str | None, now: datetime) -> float | None:
    """Age of a claim in hours, from the server `createdAt` field.

    Returns None when `created_at` is missing or unparseable -- conservatively
    treated as NOT stale (we cannot prove an age, so we do not silently lift a
    block on a claim we cannot date). `now` is injected for testability.
    """
    if not created_at:
        return None
    parsed = _parse_iso_utc(created_at)
    if parsed is None:
        return None
    return (now - parsed).total_seconds() / 3600.0


def _parse_iso_utc(iso: str) -> datetime | None:
    """Parse a GitHub server `createdAt` (ISO 8601 UTC, trailing 'Z').

    Tolerates a fractional second component and an explicit +00:00 offset.
    Returns None on any parse failure rather than raising.
    """
    try:
        s = iso.strip()
        if s.endswith("Z"):
            s = s[:-1] + "+00:00"
        dt = datetime.fromisoformat(s)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except (ValueError, TypeError):
        return None


def _run_check(payload: dict, my_lane: str, stale_threshold=None,
               now: datetime | None = None,
               my_paths: list[str] | None = None) -> int:
    """Issue-claim check: exit 1 if another lane blocks, 0 if clear.

    Args:
        payload: `gh issue view --json ...` payload (or `from-json`).
        my_lane: caller lane `machine:workspace`.
        stale_threshold: optional hours; claims older than this DO NOT block
            (but a warning is printed, #9812). None = legacy epic-wide block.
        now: injected `datetime` for stale calc (testability).
        my_paths: optional list of files the caller intends to edit (#10342).
            Merged with the caller's OWN active-claim `paths:` clause (#10419)
            to form `my_scope`. An `[OVERRIDE]` or `[CLAIMED]` whose `paths:`
            clause does NOT intersect `my_scope` is treated as if it does not
            exist for the blocker test -- the claim only locks the paths it
            names. Without any declared scope (no `my_paths` AND no `paths:` on
            the caller's own claim), behaviour is unchanged: every other active
            claim blocks, regardless of its scope clause (we cannot prove
            disjointness, so we conservatively over-block).
    """
    events = _sort_events(payload)
    # One shared tracked-files walk feeds BOTH the #10881 lint and the
    # #10958 empty-scope witness (best-effort: None outside a git repo, in
    # which case both features degrade to their pre-#10958 behaviour).
    tracked = _git_tracked_files()
    # #10881 lint -- malformed paths: clauses surface on stderr when the
    # marker is read: visible to every lane running the check, never changing
    # a verdict. The four 2026-08-14 markers on #10678 shared the defect the
    # three checks name (epic-wide by accident / prose swallowed as globs).
    _lint_claim_events(events, payload.get("number"), tracked=tracked)
    # #10958 -- attach the dead-glob witness to every scoped event (own and
    # others): a glob that matches zero tracked files is surfaced in the
    # JSON (`empty_scope`) and, when it covers the WHOLE scope, lifts the
    # claim to epic-wide in `_filter_by_claim_scope` (fail-safe).
    if tracked is not None:
        for ev in events:
            if ev.get("paths"):
                ev["empty_scope"] = _empty_scope_in(ev["paths"], tracked)
    active, unattributed = compute_active_claims(events)
    others = {ln: ev for ln, ev in active.items() if ln != my_lane}
    mine = active.get(my_lane)

    # Override-scope filter (#10342): an `[OVERRIDE]` with a `paths:` clause
    # only locks lanes whose intended files intersect the scope. Without
    # `my_paths`, we conservatively treat every scoped override as blocking
    # (the caller's intent is unknown -- better to over-block than silently
    # merge a write that should have pinged a held lane).
    others = _filter_by_claim_scope(others, my_paths, mine, tracked=tracked)

    # Stale-claim handling (#9812): a claim older than `stale_threshold` hours
    # (age from the server createdAt, NEVER the body) is treated as STALE -- it
    # no longer blocks, but a warning is printed and the new claimant MUST post
    # their own [CLAIMED] (this is not a silent bypass). Without the flag
    # (default None), behaviour is unchanged: every active claim blocks.
    stale_others: dict[str, ClaimEvent] = {}
    if stale_threshold is not None:
        now = now or datetime.now(timezone.utc)
        for ln, ev in others.items():
            age = _claim_age_hours(ev.created_at, now)
            if age is not None and age >= stale_threshold:
                stale_others[ln] = ev
        others = {ln: ev for ln, ev in others.items() if ln not in stale_others}

    summary = {
        "issue": payload.get("number"),
        "title": payload.get("title"),
        "my_lane": my_lane,
        "my_active_claim": bool(mine),
        "blocking_lanes": sorted(others),
        "stale_claims": sorted(stale_others),
        "active_claims": {
            ln: {
                "claimed_at": ev.created_at,
                "by": ev.author,
                "marker": ev.marker,
                "url": ev.url,
                "paths": ev.get("paths"),
                # #10597 hardener -- surface the witness list of residual
                # `{`/`}` so a human reviewer can see WHY an unparseable claim
                # is being treated as epic-wide. The list may be empty (the
                # scope is fully parseable) or non-empty (the claim carries
                # patterns fnmatch cannot match).
                "unparseable_scope": ev.get("unparseable_scope") or [],
                # #10958 -- the dead-glob witness: globs of this claim that
                # match zero tracked files. Empty when every glob locks
                # something (or the walk was impossible). Non-empty means the
                # declaring lane should reissue the claim with valid globs;
                # when it covers the whole scope the claim is lifted to
                # epic-wide (a broken claim is not a permissive claim).
                "empty_scope": ev.get("empty_scope") or [],
            }
            for ln, ev in sorted(active.items())
        },
        "unattributed_markers": len(unattributed),
        "blocked": bool(others),
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2))

    # #10597 bonus -- SCOPE_ZERO_COVERAGE warning. When a lane declares a
    # SCOPED claim whose expanded globs do not match any tracked file in
    # the repo, the declaring lane gets a loud-but-non-blocking warning.
    # The motivation is the same as the positive control: a glob that
    # matches nothing is INDISTINGUISHABLE from a legitimately-empty
    # scope, so the lane learns at the call site that its declared lock
    # is empty and reissues with a valid glob. Best-effort: when the
    # file walk fails (e.g. not in a git repo), we skip silently -- the
    # warning is a usability hint, not a gate.
    if not others and not stale_others and mine is not None:
        warn = _scope_zero_coverage_warning(mine.get("paths"))
        if warn is not None:
            print(
                f"SCOPE_ZERO_COVERAGE: your declared claim scope "
                f"{warn['scope']!r} matches zero tracked files in the "
                f"repo. The claim is recorded, but the lock is empty -- "
                f"reissue with valid globs.",
                file=sys.stderr,
            )

    # Stale warnings -- non-blocking, but loud enough to prompt a fresh claim.
    for ln, ev in sorted(stale_others.items()):
        age = _claim_age_hours(ev.created_at, now)
        age_h = f"{age:.1f}" if age is not None else "?"
        print(
            f"STALE_CLAIM {ln} ({age_h}h >= {stale_threshold:g}h threshold) -- "
            f"reprise autorisee, poster un nouveau [CLAIMED].",
            file=sys.stderr,
        )

    # Human verdict after the JSON.
    if others:
        who = ", ".join(
            f"{ln} (@{_fmt_active(ev)})" for ln, ev in sorted(others.items())
        )
        # #10395 Variante 2: display the intentions side-by-side when the
        # comments carry them. A bare `BLOCKED` is not actionable on a
        # multi-lane EPIC where two lanes might be working on disjoint
        # notebooks -- surfacing the marker-line excerpts lets a coordinator
        # (or the worker themselves) read disjoint intent at a glance and
        # either narrow the claim's scope, post a `[RELEASED]`, or escalate.
        intent_lines: list[str] = []
        for ln, ev in sorted(others.items()):
            tag = f"  - {ln}: "
            excerpt = (ev.get("intent") if hasattr(ev, "get") else None) or "(no intent)"
            intent_lines.append(f"{tag}{excerpt}")
        intent_block = "\n".join(intent_lines)
        print(
            f"\nBLOCKED: another lane holds an active claim on "
            f"#{payload.get('number')}: {who}.\n"
            f"Claimed scopes (marker-line excerpts -- #10395 Variante 2):\n"
            f"{intent_block}\n"
            f"Do not start -- pick another grain, post a scope-narrowing "
            f"`[CLAIMED] paths: ...`, or wait for release.",
            file=sys.stderr,
        )
        return 1
    parts = []
    if mine:
        parts.append("resuming your own active claim")
    if stale_others:
        parts.append(f"{len(stale_others)} stale claim(s) bypassed")
    note = f" ({'; '.join(parts)})" if parts else ""
    print(f"\nCLEAR: no other lane claims #{payload.get('number')}{note}.")
    return 0


def _filter_by_claim_scope(
    others: dict[str, ClaimEvent],
    my_paths: list[str] | None,
    mine: ClaimEvent | None,
    tracked: list[str] | None = None,
) -> dict[str, ClaimEvent]:
    """Drop `others` lanes whose scoped claim does NOT intersect my scope.

    `my_scope` (#10419) = the caller's `--paths` intent MERGED with the
    `paths:` clause of the caller's OWN active claim (`mine`). When `my_scope`
    is empty (the caller declared no path intent at all), every other lane is
    kept -- we cannot prove disjointness, so we conservatively over-block
    (legacy behaviour, preserved).

    Per other lane:
      - No `paths:` clause (plain [CLAIMED], or epic-wide [OVERRIDE]) -> STAYS.
        Its epic-wide semantics predate the scope feature (#10342/#10419).
      - Has a `paths:` clause that INTERSECTS `my_scope` -> STAYS (real overlap).
      - Has a `paths:` clause DISJOINT from `my_scope` -> DROPPED (free). This
        is the #10419 fix: two lanes with disjoint scoped claims on the same
        multi-instance issue no longer false-block each other.
      - #10597 hardener: scope carries an `unparseable_scope` (residual `{` or
        `}` after brace expansion) -> STAYS. The read is conservative: an
        unparseable scope is fnmatch-garbage, so we cannot prove the lane's
        intent; better to over-block than to silently clear. The witness list
        is surfaced in the JSON summary under `unparseable_scopes` so the
        declaring lane sees the defect and reissues the claim with valid
        syntax.
      - #10958 fail-safe: scope is ENTIRELY dead (every glob matches zero
        tracked files, witness under `empty_scope`) -> STAYS, lifted to
        epic-wide. A claim whose scope matches nothing is not a permissive
        claim -- it is a BROKEN one (polluted suffix, typo'd path), and the
        safe hypothesis is that the lane meant something. A PARTIALLY dead
        scope (at least one live glob) stays scoped on its live part: the
        lock is real, the dead globs are surfaced in the JSON for the lane
        to fix. `tracked` None (no repo walk) -> no lift (cannot prove).

    The reducer `compute_active_claims` is untouched; this filter only prunes
    the `others` view. The active_claims summary keeps the full state, so the
    JSON output remains auditable.
    """
    mine_paths = (mine.get("paths") if mine else None) or []
    my_scope = list(dict.fromkeys((my_paths or []) + mine_paths)) or None
    if not my_scope:
        return others  # no declared scope -> cannot prove disjointness
    # #10958 fail-safe, caller side: an entirely-dead MY scope proves nothing
    # either. Dropping an other-lane claim as "disjoint" from globs that lock
    # no real file would be the same fail-open with the roles swapped, so the
    # caller keeps every other lane until its own scope is reissued clean.
    if tracked is not None and _empty_scope_in(my_scope, tracked) == my_scope:
        return others
    filtered: dict[str, ClaimEvent] = {}
    for ln, ev in others.items():
        scope = ev.get("paths")
        if not scope:
            filtered[ln] = ev  # epic-wide (plain CLAIMED or unscoped OVERRIDE)
            continue
        # #10597 hardener -- unparseable scope (residual braces) lifts the
        # claim back to epic-wide BEFORE we attempt the disjointness test.
        # fnmatch on residual `{`/`}` is guaranteed to miss every file, so
        # a "scoped disjoint" read here would silently clear the lane. The
        # witness list is surfaced via `ev.get("unparseable_scope")` for
        # the JSON audit (see _run_check summary).
        if ev.get("unparseable_scope"):
            filtered[ln] = ev  # lifted to epic-wide -- always blocking
            continue
        # #10958 fail-safe -- an ENTIRELY dead scope (every glob matches zero
        # tracked files) is a broken claim, not a permissive one: lifted to
        # epic-wide before the disjointness test, mirroring #10597. The
        # witness is `ev.get("empty_scope")` (attached by `_run_check` when
        # the walk succeeded); a missing/empty witness never lifts.
        empty = ev.get("empty_scope") or []
        if empty and len(empty) >= len(scope):
            filtered[ln] = ev  # lifted to epic-wide -- always blocking
            continue
        if _path_matches_any(my_scope, scope):
            filtered[ln] = ev  # scopes intersect -> real collision
        # else: both scoped, disjoint -> free, drop from others
    return filtered


def _path_matches_any(paths: list[str], patterns: list[str]) -> bool:
    """Return True if any of `paths` matches any of `patterns` (fnmatch glob)."""
    for p in paths:
        if _path_matches(p, patterns):
            return True
    return False


def _fmt_active(ev: ClaimEvent) -> str:
    return f"{ev.author or '?'}, {_fmt_utc(ev.created_at)}"


# --- path-mode (--paths, #9959) -----------------------------------------------
#
# Complements -- not replaces -- the issue-claim check. The motivating
# incident (R3D 2026-08-08) had two lanes of the SAME machine colliding on
# `knot_lean/Knots/Reidemeister.lean` minutes apart, each having passed the
# issue-claim check (the other lane's issue comment was posted AFTER each
# push but BEFORE the dispatch landed). The fix is the missing leg of L898:
# "does an OPEN PR on this machine already touch the same files?"
#
# Two lanes of a SAME machine MUST trip each other. The comparison key is
# the full `machine:workspace` string -- comparing on `machine` alone
# would miss this case by construction, which is exactly the bug.

class PathCollision:
    """One OPEN PR that intersects the caller's paths on a different lane."""

    def __init__(self, pr: dict, lane: str | None, files: list[str]) -> None:
        self.pr = pr
        self.number = pr.get("number")
        self.title = pr.get("title", "")
        self.headRefName = pr.get("headRefName", "")
        self.lane = lane
        self.files = files  # the PR files that intersect the patterns


def _run_check_paths(
    paths: list[str],
    my_lane: str,
    prs: list[dict] | None = None,
) -> int:
    """Path-mode guard: exit 2 on cross-lane OPEN-PR collision, 0 if clear.

    Args:
        paths: file paths/globs from the caller. Each PR file is matched
            against the list (fnmatch, basename-OR-full-path), and a PR
            counts as intersecting when at least one file matches.
        my_lane: caller's full lane token (e.g. "myia-po-2024:CoursIA-2").
        prs: pre-fetched list of OPEN PRs (testability seam); default None
            triggers a real `gh pr list` call via `_gh_open_prs_with_files`.

    Returns:
        0 if no other-lane PR intersects the paths,
        2 if at least one OPEN PR of another lane (or with an unreadable
          lane tag) intersects -- the calling worker MUST pick another
          grain or wait for that PR to merge/close,
        1 only on `gh` plumbing failure (raised RuntimeError is caught in
          `main` and turned into exit 1).

    Lane comparison is on the FULL `machine:workspace` string. Same
    machine + different workspace counts as a different lane (the
    motivating R3D incident). Same lane is reported as a non-issue
    ("your own PR is fine; it lands when it lands") even when the paths
    intersect, because the caller is resuming their own work.
    """
    if not paths:
        print("error: --paths requires at least one path/glob", file=sys.stderr)
        return 1
    if prs is None:
        try:
            prs = _gh_open_prs_with_files()
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 1

    collisions: list[PathCollision] = []
    self_overlap: list[PathCollision] = []
    for pr in prs:
        pr_files = pr.get("files") or []
        if not pr_files:
            continue
        intersecting = [
            f.get("path", "") for f in pr_files
            if f.get("path") and _path_matches(f["path"], paths)
        ]
        if not intersecting:
            continue
        lane = extract_lane(pr.get("body") or "")
        coll = PathCollision(
            pr=pr, lane=lane, files=[p for p in intersecting if p],
        )
        # Three-way classification:
        #  - lane == my_lane             -> self_overlap (resuming own work)
        #  - lane is None (no Grain tag) -> collisions (cannot attribute;
        #                                    author is jsboige on every PR,
        #                                    so the tag is the only signal;
        #                                    absence = uncertainty, treated
        #                                    as a potential collision -- not
        #                                    silently ignored)
        #  - lane != my_lane (tagged)    -> collisions
        if lane == my_lane:
            self_overlap.append(coll)
        else:
            collisions.append(coll)

    def _serialise(c: PathCollision) -> dict:
        return {
            "number": c.number,
            "title": c.title,
            "headRefName": c.headRefName,
            "lane": c.lane,
            "files_intersecting": c.files,
        }

    summary = {
        "mode": "paths",
        "paths": list(paths),
        "my_lane": my_lane,
        "other_lane_collisions": [_serialise(c) for c in collisions],
        "self_overlap": [_serialise(c) for c in self_overlap],
        "untagged_prs": [
            _serialise(c) for c in collisions if c.lane is None
        ],
    }
    print(json.dumps(summary, ensure_ascii=False, indent=2))

    if collisions:
        tagged = [c for c in collisions if c.lane is not None]
        untagged = [c for c in collisions if c.lane is None]
        msg = [
            f"\nBLOCKED: OPEN PR(s) of other lanes touch the requested paths.",
            "",
        ]
        for c in tagged:
            inter = ", ".join(c.files)
            msg.append(
                f"  - #{c.number} lane={c.lane} head={c.headRefName} "
                f"files=[{inter}] -- {c.title}"
            )
        for c in untagged:
            inter = ", ".join(c.files)
            msg.append(
                f"  - #{c.number} lane=UNREADABLE head={c.headRefName} "
                f"files=[{inter}] -- {c.title}\n"
                f"    (no `Grain:` lane tag in body; cannot attribute. "
                f"Treat as a potential collision: coordinate before pushing.)"
            )
        msg.append(
            "\nDo not start -- coordinate with the owner(s), or pick "
            "another grain that does not intersect the open PR(s)."
        )
        print("\n".join(msg), file=sys.stderr)
        return 2

    if self_overlap:
        own_numbers = ", ".join(f"#{c.number}" for c in self_overlap)
        print(
            f"\nCLEAR for paths {paths!r} -- you already have an OPEN PR on "
            f"the same paths ({own_numbers}). Resuming your own work is fine; "
            f"the path gate does not block your own lane.",
            file=sys.stderr,
        )
        return 0

    print(f"\nCLEAR: no OPEN PR of another lane touches {paths!r}.")
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description=(
            "Lane-claim guard (#9774): check/post [CLAIMED] on an issue before "
            "editing. Defaut-2-safe: server UTC timestamps only."
        )
    )
    p.add_argument("issue", nargs="?", default=None,
                   help="issue number (or URL); optional when --paths is used "
                        "(--paths does not need an issue number, the dispatch "
                        "cote coordinateur calls it pre-claim to detect cross- "
                        "lane PR collisions on the same files)")
    p.add_argument("--lane", required=True,
                   help="your lane, e.g. myia-po-2024:CoursIA")
    p.add_argument("--from-json", metavar="FILE",
                   help="read `gh issue view` JSON from FILE (offline/test mode)")
    p.add_argument("--stale-threshold", type=float, metavar="HOURS", default=None,
                   help="treat OTHER lanes' claims older than HOURS as stale: "
                        "warn and do not block (age from server createdAt, never "
                        "the body). The new claimant must still post its own "
                        "[CLAIMED] -- this is not a silent bypass. Without the "
                        "flag every active claim blocks (current behaviour).")
    p.add_argument("--paths", metavar="PATH", nargs="+", default=None,
                   help="path-mode (#9959): one or more file paths/globs. "
                        "Exits 2 if any OPEN PR of a different lane (or with "
                        "an unreadable lane tag) has files[] intersecting. "
                        "Exits 0 if no collision, 1 on usage/`gh` failure. "
                        "Lane key is full `machine:workspace` (same-machine "
                        "different-workspace counts as different lane). "
                        "Complements the issue-claim check, does not replace. "
                        "When supplied TOGETHER with an issue number "
                        "(`check_lane_claim ISSUE --paths PATH ...`), the "
                        "scope is also applied to `[OVERRIDE]` markers that "
                        "carry a `paths:` clause (#10342): an override whose "
                        "scope does not intersect the caller's paths is "
                        "treated as if it did not exist for the blocker "
                        "decision. Without `--paths`, override scope is "
                        "ignored (legacy epic-wide behaviour, preserved).")
    act = p.add_mutually_exclusive_group()
    act.add_argument("--claim", metavar="INTENTION",
                     help="post a [CLAIMED] comment for your lane")
    act.add_argument("--release", nargs="?", const="", default=None,
                     metavar="NOTE", help="post a [RELEASED] comment")
    args = p.parse_args(argv)

    # #10881 -- `nargs='+'` on --paths swallows a TRAILING positional issue
    # number (`--lane X --paths a b 10678` puts "10678" into the paths list,
    # switches to path mode, and prints a reassuring CLEAR that measured
    # nothing). Warn loudly when a paths entry is a bare integer; the warning
    # is non-blocking (the caller may have meant a numeric path), but the
    # measured trap is precisely this shape.
    if args.paths is not None:
        for entry in _warn_bare_integer_paths(args.paths):
            print(
                f"WARN: --paths entry {entry!r} is a bare integer -- an issue "
                f"number swallowed by nargs='+' (#10881). Correct form: "
                f"`check_lane_claim.py {entry} --lane <lane> --paths ...` "
                f"(positional FIRST).",
                file=sys.stderr,
            )

    # Path-only mode (#9959) does NOT require an issue number -- it is the
    # missing leg of L898 dispatched pre-claim to detect cross-lane PR
    # collisions on the same files. We branch here when `--paths` is supplied
    # WITHOUT an issue; when both are present we go through the issue-claim
    # check with `my_paths` (the `--paths` are then used to scope-bind any
    # `[OVERRIDE]` markers, #10342).
    if args.paths is not None and args.issue is None:
        return _run_check_paths(args.paths, args.lane)

    # Posting modes: short-circuit before any read. Both require an issue.
    if args.issue is None:
        print("error: an issue number is required (or use --paths PATH ...)",
              file=sys.stderr)
        return 1
    if args.claim is not None:
        body = _CLAIM_BODY_TMPL.format(lane=args.lane, intention=args.claim)
        try:
            _post_comment(args.issue, body)
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        print(f"posted [CLAIMED] lane {args.lane} on #{args.issue}")
        return 0
    if args.release is not None:
        note = args.release or "released"
        body = _RELEASE_BODY_TMPL.format(lane=args.lane, note=note)
        try:
            _post_comment(args.issue, body)
        except RuntimeError as exc:
            print(f"error: {exc}", file=sys.stderr)
            return 2
        print(f"posted [RELEASED] lane {args.lane} on #{args.issue}")
        return 0

    # Check mode (default). `--paths` (when supplied with an issue) threads
    # through to `_run_check` as `my_paths` -- it scopes `[OVERRIDE]` blockers
    # by intersection. Posting modes already returned above, so `args.paths`
    # here is unambiguously the scope-binding form.
    try:
        if args.from_json:
            payload = json.loads(Path(args.from_json).read_text(encoding="utf-8"))
        else:
            payload = _gh_issue_comments(args.issue)
    except (RuntimeError, json.JSONDecodeError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return _run_check(
        payload,
        args.lane,
        stale_threshold=args.stale_threshold,
        my_paths=args.paths,
    )


if __name__ == "__main__":
    sys.exit(main())
