#!/usr/bin/env python3
"""ADVISORY detector: open PRs sharing a file path (issues #13359, #13615).

Why this exists
---------------
`detect_duplicate_issues.py` catches duplicate ISSUES (same title, same time
window). It cannot see the more expensive defect: two OPEN pull requests
touching at least one identical file path, opened by the SAME lane or by
coordinateur, usually for the same issue.

Measured firsthand 2026-08-28 on #13296 / #13339 -- the lane
`myia-po-2027:CoursIA-2` opened the same notebook
`Lean-16j-Conway-Hashlife-Correctness-Native.ipynb` twice, 4 h 32 apart, on the
same issue #11703. The second one carried the only corrected README total and
the better markdown, and the worse one was merged. Each duplicate costs twice
the work AND twice the CI (every `pull_request` here fires ~30 runs, cf #12567).

Why no guard saw it
-------------------
`check_lane_claim.py` cannot, by construction -- a lane never blocks ITSELF; the
claim lock only arbitrates across lanes. The only rule covering this case is
the prose ``L898`` (`.claude/rules/proactive-coordination.md`), a rule WITHOUT
an organ: it asks every agent to run four `gh` commands from memory before each
write. It failed twice in the same episode, and the coordinator missed it at
merge time too.

What it does (#13359)
---------------------
Lists all OPEN pull requests, builds a path -> {PR numbers} map, and reports
every unordered pair sharing at least one file path. For each PR involved it
posts (or updates/retracts) ONE advisory comment naming the other PR(s) and the
shared paths. The comment is marker-framed and idempotent: a re-run never
creates a duplicate; a PR whose collisions are resolved loses its comment.

Tiering and false positives (#13615)
------------------------------------
Each pair carries a tier, computed from the issues each PR cites (title ``#N``
convention, plus body keywords ``Closes|Fixes|Resolves|See|refs|Part of #N``):

- **strong** -- shared file AND a common cited issue. The double-delivery
  case: three real pairs in one night (#13556/#13530 and #12737/#13385 both
  cost hard manual arbitration or full duplication).
- **weak** -- shared file, disjoint issues. Same risk class, weaker signal
  (family ``README.md`` edits land here legitimately).

Two classes of expected overlap are excluded entirely, or the guard becomes
noise that gets ignored:

- **Stacked PRs** -- the base of one is the head of the other: the overlap is
  the stack itself, never a conflict.
- **Generated artifacts** -- ``COURSE_CATALOG.generated.*`` and the twin
  registry ``scripts/notebook_tools/twin_pairs.d/``: permanent structural
  overlap with zero signal.

Strong pairs are additionally labelled ``pr-overlap`` (label on both sides),
giving the coordinator a filterable queue. Weak pairs get the comment only.

Scope (from #13359)
-------------------
- Invent NO new claim lock. Do not touch `check_lane_claim.py` -- the claim
  protocol stays the cross-lane arbiter. This covers the intra-lane blind spot
  and the coordinator-at-merge blind spot, neither of which the claim sees.
- The organ never blocks, never closes, never picks a winner: it renders the
  overlap VISIBLE (comment + label); the ordering decision stays with the
  coordinator (#13615).

Usage
-----
::

    # Detect + post/retract advisory comments + label strong pairs:
    python scripts/check_pr_path_collisions.py

    # Log only, post/label nothing (CI workflow_dispatch dry_run):
    python scripts/check_pr_path_collisions.py --dry-run

    # Positive/negative-control self-test (synthetic + historical fixtures,
    # no network):
    python scripts/check_pr_path_collisions.py --self-test

Exit codes:
  0 -- always (advisory). Even a report of collisions exits 0; the actionable
       payload is the comment + the label + the JSON, never the green
       conclusion.
  2 -- only under --self-test, if a control was NOT satisfied (the detector
       is broken and would silence the signal it was built for).

CLI flags
---------
``--limit``       cap PRs fetched via ``gh pr list`` (default 500; the default
                  ``gh pr list`` limit is 30 -- a silent cap that hid entire
                  stacks this month). 500 covers the whole open pool here.
``--repo``        override repo (default: gh default / GITHUB_REPOSITORY).
``--dry-run``     log detections, post/retract/label nothing.
``--same-issue-only``
                  post only STRONG-tier collisions (both PRs cite a common
                  issue). Cuts the shared-README noise.
--json            always on stdout.
--self-test       run the offline control suite; exit 2 if any control fails.
"""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
import os
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from typing import Iterable

# Marker framing the advisory comment, so re-runs find/update/retract it.
COMMENT_MARKER_START = "<!-- PR-PATH-COLLISION:START -->"
COMMENT_MARKER_END = "<!-- PR-PATH-COLLISION:END -->"

# Signature of the dated resolution note left in place of a live advisory
# (retraction is a body swap, not a delete: less destructive, readable in the
# PR history, and still marker-framed so re-runs keep finding it).
RESOLVED_SIGNATURE = "<!-- PR-PATH-COLLISION:RESOLVED -->"

# Label applied to both sides of a STRONG pair (#13615). The comment renders
# the detail; the label gives the coordinator a filterable queue.
OVERLAP_LABEL = "pr-overlap"

TIER_STRONG = "strong"
TIER_WEAK = "weak"

# The synthetic positive control. NOT a live repo pair (those are volatile:
# they merge and vanish). It is seeded straight into the pure detector, so the
# self-test is reproducible offline and fails loudly if the detector breaks.
SELF_TEST_PAIR = (900001, 900002)
SELF_TEST_SHARED_PATH = "MyIA.AI.Notebooks/foo/bar.ipynb"

# Historical pairs from #13615, replayed at their state of then as self-test
# fixtures (acceptance: the positive controls MUST be flagged). The shared
# paths and common issues are the ones measured in the issue.
HISTORICAL_STRONG_PAIRS: tuple[tuple[int, int, str, int], ...] = (
    # Hard manual arbitration: one PR moves a theorem out of ErdosSpencer.lean
    # while the other writes inside the moved region.
    (13556, 13530,
     "MyIA.AI.Notebooks/Search/discrepancy_lean/Discrepancy/ErdosSpencer.lean",
     13508),
    # Full double-delivery of the same notebook; the worse one was merged.
    (12737, 13385,
     "MyIA.AI.Notebooks/GameTheory/GameTheory-04-NashEquilibrium.ipynb",
     13313),
)

# Generated artifacts with permanent structural overlap and zero signal
# (#13615: a guard that reports everything reports nothing).
EXCLUDED_EXACT_PATHS = frozenset({
    "COURSE_CATALOG.generated.json",
    "COURSE_CATALOG.generated.md",
})
EXCLUDED_PATH_RES = (
    re.compile(r"^scripts/notebook_tools/twin_pairs\.d/"),
)

# Body keywords that cite an issue (title already carries bare ``#N`` by
# convention ``fix(scope,#N): ...``; bodies need the keyword to avoid counting
# incidental mentions).
_CITES_RE = re.compile(
    r"\b(?:closes?|fixes?|resolves?|see|refs?|part\s+of)\s*#(\d+)",
    re.IGNORECASE,
)


def _is_signal_path(path: str) -> bool:
    """False for generated artifacts whose sharing carries no information."""
    if path in EXCLUDED_EXACT_PATHS:
        return False
    return not any(rx.match(path) for rx in EXCLUDED_PATH_RES)


@dataclass(frozen=True)
class PathCollision:
    """An unordered pair of open PRs sharing at least one signal file path."""
    a_number: int
    b_number: int
    shared_paths: tuple[str, ...]
    tier: str = TIER_WEAK
    common_issues: tuple[int, ...] = ()

    def other(self, number: int) -> int:
        if number == self.a_number:
            return self.b_number
        if number == self.b_number:
            return self.a_number
        raise ValueError(f"{number} not in collision {self.a_number}/{self.b_number}")

    def as_dict(self) -> dict:
        return {
            "a_number": self.a_number,
            "b_number": self.b_number,
            "shared_paths": list(self.shared_paths),
            "tier": self.tier,
            "common_issues": list(self.common_issues),
        }


@dataclass(frozen=True)
class PrRow:
    """Minimal open PR record the detector needs."""
    number: int
    title: str
    paths: tuple[str, ...]
    body: str = ""
    base_ref: str = ""
    head_ref: str = ""

    @classmethod
    def from_gh_dict(cls, d: dict) -> "PrRow":
        paths = []
        for f in d.get("files") or []:
            p = (f.get("path") or "").strip().replace("\\", "/")
            if p:
                paths.append(p)
        return cls(
            number=int(d["number"]),
            title=(d.get("title") or "").strip(),
            paths=tuple(paths),
            body=(d.get("body") or ""),
            base_ref=(d.get("baseRefName") or "").strip(),
            head_ref=(d.get("headRefName") or "").strip(),
        )

    def cited_issues(self) -> set[int]:
        """Issues this PR cites: bare ``#N`` from the title + keyword-scoped
        ``Closes|Fixes|Resolves|See|refs|Part of #N`` from the body."""
        from_title = {int(n) for n in re.findall(r"#(\d+)", self.title or "")}
        return from_title | {int(n) for n in _CITES_RE.findall(self.body or "")}


def is_stacked(a: PrRow, b: PrRow) -> bool:
    """True when one PR is stacked directly on the other's head.

    The overlap is then the stack itself (expected, coordinated), not a
    conflict -- the case #13615 asks to exclude explicitly. Refs must be
    non-empty on both sides: an unknown head/base never stacks anything.
    """
    if not (a.base_ref and a.head_ref and b.base_ref and b.head_ref):
        return False
    return a.base_ref == b.head_ref or b.base_ref == a.head_ref


@dataclass
class ScanResult:
    """Aggregate of one detection run."""
    total_prs_scanned: int = 0
    distinct_paths: int = 0
    collisions: list[PathCollision] = field(default_factory=list)
    colliding_prs: list[int] = field(default_factory=list)
    stacked_pairs_excluded: list[tuple[int, int]] = field(default_factory=list)

    @property
    def n_collisions(self) -> int:
        return len(self.collisions)

    @property
    def strong_collisions(self) -> list[PathCollision]:
        return [c for c in self.collisions if c.tier == TIER_STRONG]

    def as_dict(self) -> dict:
        return {
            "total_prs_scanned": self.total_prs_scanned,
            "distinct_paths": self.distinct_paths,
            "n_collisions": self.n_collisions,
            "collisions": [c.as_dict() for c in self.collisions],
            "colliding_prs": self.colliding_prs,
            "stacked_pairs_excluded": [list(p) for p in self.stacked_pairs_excluded],
        }


def detect_path_collisions(prs: Iterable[PrRow]) -> ScanResult:
    """Group open PRs by signal file path; report every pair sharing >=1 path.

    ``prs`` is consumed once. The result is deterministic: collisions sorted by
    (lowest number, highest number), shared paths sorted by path string.

    Excluded before pairing (#13615): generated-artifact paths (dropped from
    every row -- they never carry signal), and stacked PR pairs (dropped from
    the pair set -- their overlap is the stack itself).
    """
    result = ScanResult()
    rows = list(prs)
    result.total_prs_scanned = len(rows)
    row_by_number = {r.number: r for r in rows}

    path_to_numbers: dict[str, set[int]] = {}
    for r in rows:
        for p in r.paths:
            if not _is_signal_path(p):
                continue
            path_to_numbers.setdefault(p, set()).add(r.number)
    result.distinct_paths = len(path_to_numbers)

    pair_paths: dict[tuple[int, int], list[str]] = {}
    for path, numbers in path_to_numbers.items():
        if len(numbers) < 2:
            continue
        nums = sorted(numbers)
        for i in range(len(nums)):
            for j in range(i + 1, len(nums)):
                a, b = nums[i], nums[j]
                pair_paths.setdefault((a, b), []).append(path)

    collisions: list[PathCollision] = []
    for (a, b), paths in sorted(
        pair_paths.items(),
        key=lambda kv: (kv[0][0], kv[0][1]),
    ):
        ra, rb = row_by_number.get(a), row_by_number.get(b)
        if ra is not None and rb is not None and is_stacked(ra, rb):
            result.stacked_pairs_excluded.append((a, b))
            continue
        common: tuple[int, ...] = ()
        if ra is not None and rb is not None:
            common = tuple(sorted(ra.cited_issues() & rb.cited_issues()))
        collisions.append(PathCollision(
            a_number=a,
            b_number=b,
            shared_paths=tuple(sorted(paths)),
            tier=TIER_STRONG if common else TIER_WEAK,
            common_issues=common,
        ))
    result.collisions = collisions
    result.colliding_prs = sorted(
        {n for c in collisions for n in (c.a_number, c.b_number)}
    )
    return result


def collisions_for_pr(number: int, collisions: Iterable[PathCollision]) -> list[PathCollision]:
    """Collisions where ``number`` is one side, others normalized to `other`."""
    return [c for c in collisions if number in (c.a_number, c.b_number)]


def strong_collisions(collisions: Iterable[PathCollision]) -> list[PathCollision]:
    """Keep only STRONG-tier collisions (shared file AND common cited issue).

    Replaces the pre-#13615 title-only filter: the tier is computed inside
    ``detect_path_collisions`` from title + keyword-scoped body citations, so
    the CLI mode no longer needs a separate title map.
    """
    return [c for c in collisions if c.tier == TIER_STRONG]


def render_comment(number: int, title: str, own_collisions: list[PathCollision]) -> str:
    """Build the advisory comment body for PR ``number``.

    Names each colliding PR by number, its tier, the shared paths, and (for
    the strong tier) the common cited issues. Marker-framed so a re-run can
    find, refresh, or retract it in place.
    """
    lines = [
        "<!-- PR-PATH-COLLISION:START -->",
        "## Path-collision (organ #13359/#13615) ",
        "",
        f"Cette PR **#{number}** (`{title or '?'}`) touche au moins un chemin "
        "de fichier aussi modifie par d'autres PRs ouvertes. Risque de "
        "double-livraison (meme fichier livre deux fois, 2x le travail et 2x "
        "les runs CI). _Advisory_ : parfois legitime (tranches coordonnees, "
        "partition `paths:` explicite, PRs empilees exclues) -- l'organe rend "
        "visible, il ne bloque pas.",
        "",
    ]
    for c in sorted(own_collisions, key=lambda c: c.other(number)):
        other = c.other(number)
        tier_fr = "fort" if c.tier == TIER_STRONG else "faible"
        line = f"- **{tier_fr}** -- **#{other}** partage : {', '.join(c.shared_paths)}"
        if c.common_issues:
            issues = ", ".join(f"#{i}" for i in c.common_issues)
            line += f" (issues communes : {issues})"
        lines.append(line)
    lines.append("")
    lines.append("<!-- PR-PATH-COLLISION:END -->")
    return "\n".join(lines)


def find_marker_comment(comments: Iterable[dict]) -> str | None:
    """Id of the existing marker comment in ``comments``, or None (pure)."""
    entry = find_marker_entry(comments)
    return entry[0] if entry else None


def find_marker_entry(comments: Iterable[dict]) -> tuple[str, str] | None:
    """(id, body) of the existing marker comment, or None (pure).

    Both are needed by the update/retract paths: the id addresses the
    ``PATCH /issues/comments/{id}`` call, the body decides post vs update vs
    retract (issue #13489).
    """
    for c in comments or []:
        body = c.get("body") or ""
        if COMMENT_MARKER_START in body:
            if c.get("id") is None:
                return None
            return str(c["id"]), body
    return None


def render_resolution_comment(number: int, resolved_on: str) -> str:
    """Dated resolution note replacing a live advisory whose collision ended.

    Marker-framed + RESOLVED-signed so a re-run recognises it as already
    retracted (idempotent) and can swap it back to a live advisory if the
    collision reappears (e.g. a new neighbour PR touches the path again).
    """
    lines = [
        COMMENT_MARKER_START,
        RESOLVED_SIGNATURE,
        "## Path-collision (organ #13359) — résolue",
        "",
        f"La collision de chemins signalée sur **#{number}** n'existe plus "
        f"au passage du {resolved_on} : aucune autre PR ouverte ne partage "
        "désormais de chemin de fichier avec elle. Note laissée en place de "
        "l'avertissement (retraction non destructive).",
        "",
        COMMENT_MARKER_END,
    ]
    return "\n".join(lines)


def is_resolution_note(body: str | None) -> bool:
    """True if ``body`` is already the dated resolution note (pure)."""
    return bool(body) and COMMENT_MARKER_START in body and RESOLVED_SIGNATURE in body


@dataclass(frozen=True)
class PlannedAction:
    """One planned write for a PR, decided BEFORE any network mutation."""
    number: int
    verb: str  # "post" | "update" | "retract" | "none"
    comment_id: str | None  # gh comment id for update/retract
    body: str  # desired body ("none" carries the unchanged existing body)


def plan_actions(
    colliding_prs: Iterable[int],
    collisions: Iterable[PathCollision],
    title_by_number: dict[int, str],
    marker_by_number: dict[int, tuple[str, str] | None],
    resolved_on: str,
) -> list[PlannedAction]:
    """Plan post/update/retract over the UNION colliding ∪ marker-carriers.

    This union is the structural fix of #13489: iterating colliding PRs only
    made retraction unattainable (a resolved PR left the iteration set, so its
    stale comment could never be removed) and made updates blind (a still-
    colliding PR whose neighbour changed kept a comment naming the wrong PR).
    """
    colliding_set = set(colliding_prs)
    candidates = sorted(colliding_set | set(marker_by_number))
    plans: list[PlannedAction] = []
    for number in candidates:
        existing = marker_by_number.get(number)
        if number in colliding_set:
            desired = render_comment(
                number,
                title_by_number.get(number, ""),
                collisions_for_pr(number, collisions),
            )
            if existing is None:
                plans.append(PlannedAction(number, "post", None, desired))
            elif existing[1] == desired:
                plans.append(PlannedAction(number, "none", existing[0], existing[1]))
            else:
                # includes resolution-note -> live-advisory on re-collision
                plans.append(PlannedAction(number, "update", existing[0], desired))
        else:
            if existing is None:
                continue  # not colliding, no marker: nothing to say
            if is_resolution_note(existing[1]):
                plans.append(PlannedAction(number, "none", existing[0], existing[1]))
            else:
                plans.append(PlannedAction(
                    number, "retract", existing[0],
                    render_resolution_comment(number, resolved_on),
                ))
    return plans


# ---------------------------------------------------------------------------
# gh wiring
# ---------------------------------------------------------------------------

def _gh_json(args: list[str], *, stdin: str | None = None) -> object:
    """Run a gh command, return parsed JSON (or None if empty). Raise on failure."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh failed ({proc.returncode}): "
            f"{proc.stderr.strip() or proc.stdout.strip()}"
        )
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def _repo_default() -> str:
    env_repo = os.environ.get("GITHUB_REPOSITORY")
    if env_repo:
        return env_repo
    out = subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True, encoding="utf-8",
    ).stdout.strip()
    return out or "jsboige/CoursIA"


def list_open_prs(repo: str, limit: int) -> list[PrRow]:
    """Open PRs with numbers, titles, bodies, base/head refs and file paths."""
    raw = _gh_json([
        "pr", "list", "--repo", repo, "--state", "open",
        "--limit", str(limit),
        "--json", "number,title,body,baseRefName,headRefName,files",
    ]) or []
    return [PrRow.from_gh_dict(d) for d in raw]


def find_marker(repo: str, number: int) -> tuple[str, str] | None:
    """(id, body) of the marker comment on PR ``number``, or None.

    Reads the REST collection, NOT ``gh pr view --json comments`` (#14421).
    The two routes disagree on what ``id`` means, and only one of them is
    addressable by the writer:

    ==========================================  ==========================
    source                                      ``id`` of a comment
    ==========================================  ==========================
    ``gh pr view --json comments`` (GraphQL)    ``IC_kwDOH2Odns8AAAAB...``
    ``gh api repos/O/R/issues/N/comments``      ``5535634631``
    ==========================================  ==========================

    ``edit_comment`` spends that id on ``PATCH /repos/{repo}/issues/comments/
    {id}``, a REST route that only accepts the database id. Fed a GraphQL
    node id it answers ``404 Not Found`` -- deterministically, for every
    update and every retract, while POST (which needs no id at all) keeps
    succeeding. That asymmetry is the whole signature of #14421: run 364
    reported ``post=13 update=0 retract=0``, 13/13 creations confirmed and
    0/10 in-place writes, and the organ stayed mute ~39 h because it could
    never refresh a marker it had already posted.

    ``--paginate`` matters: a PR whose marker sits past the first page of
    comments would otherwise read as "no marker" and be re-POSTED as a
    duplicate. ``--slurp`` wraps the pages in an outer list, flattened here.
    """
    pages = _gh_json(["api", "--paginate", "--slurp",
                      f"repos/{repo}/issues/{number}/comments"]) or []
    comments = [c for page in pages for c in page]
    return find_marker_entry(comments)


def scan_markers(
    repo: str, numbers: Iterable[int],
) -> tuple[dict[int, tuple[str, str] | None], set[int]]:
    """Marker state for each PR. Returns (state, failed).

    A PR whose comment fetch fails is reported in ``failed`` and excluded from
    planning: treating a fetch failure as "no marker" would let a colliding PR
    be re-POSTED as a duplicate. Advisory organ: a scan failure logs and skips,
    never reds.
    """
    state: dict[int, tuple[str, str] | None] = {}
    failed: set[int] = set()
    for number in numbers:
        try:
            state[number] = find_marker(repo, number)
        except RuntimeError:
            failed.add(number)
    return state, failed


def post_comment(repo: str, number: int, body: str, dry_run: bool) -> bool:
    """POST the marker comment on PR ``number``. Returns True iff the write
    succeeded. A non-zero rc is WARNed, never silently swallowed (#13623).

    Goes through the REST endpoint rather than ``gh pr comment`` (#14236).
    Measured on run 33597345910 (2026-09-02): ``gh pr comment`` returned
    ``Not Found (HTTP 404)`` for 30 of 33 planned writes, on OPEN PRs, in the
    same job where ``gh pr edit --add-label`` wrote successfully with the same
    token -- so the token had write access and the numbers were valid. The
    GraphQL path ``gh pr comment`` takes reports a missing permission as
    ``NOT_FOUND`` rather than ``403``, which is what made the failure
    unreadable. REST returns the real status code, so if this still fails the
    next log names the actual cause instead of masking it.

    The payload travels by ``--input <json>``, never ``-f body=@<file>``.
    ``gh api`` expands a leading ``@`` for ``-F``/``--field`` only; ``-f``
    posts the path as a literal string, which is how every marker came to
    read ``@/tmp/tmpXXXXXXXX.md`` instead of the report (#14541). ``-F``
    would read the file but also coerces ``true``/``123``/``null`` to
    non-string JSON, and a comment body is always a string. ``--input``
    avoids both, and is what the PATCH sibling already used.
    """
    if dry_run:
        return True
    with tempfile.NamedTemporaryFile(
        "w", suffix=".json", encoding="utf-8", delete=False
    ) as tf:
        json.dump({"body": body}, tf, ensure_ascii=False)
        tmp_path = tf.name
    try:
        proc = subprocess.run(
            ["gh", "api", "--method", "POST",
             f"repos/{repo}/issues/{number}/comments",
             "--input", tmp_path],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )
    finally:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)
    if proc.returncode != 0:
        print(
            f"WARN: write failed for #{number} — rc={proc.returncode}, "
            f"{(proc.stderr or proc.stdout).strip()[:200]}",
            file=sys.stderr,
        )
        return False
    return True


def edit_comment(repo: str, number: int, comment_id: str, body: str,
                 dry_run: bool) -> bool:
    """PATCH the existing marker comment in place (update or retract swap).

    ``gh pr comment --edit-last`` is not enough: the marker is not guaranteed
    to be the PR's last comment. The REST id from ``find_marker_entry``
    addresses the comment directly. Returns True iff the write succeeded; a
    non-zero rc is WARNed, never silently swallowed (#13623).
    """
    if dry_run:
        return True
    with tempfile.NamedTemporaryFile(
        "w", suffix=".json", encoding="utf-8", delete=False
    ) as tf:
        json.dump({"body": body}, tf, ensure_ascii=False)
        tmp_path = tf.name
    try:
        proc = subprocess.run(
            ["gh", "api", "--method", "PATCH",
             f"repos/{repo}/issues/comments/{comment_id}",
             "--input", tmp_path],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )
    finally:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)
    if proc.returncode != 0:
        print(
            f"WARN: write failed for #{number} — rc={proc.returncode}, "
            f"{(proc.stderr or proc.stdout).strip()[:200]}",
            file=sys.stderr,
        )
        return False
    return True


def label_strong_pairs(
    repo: str,
    strong: Iterable[PathCollision],
    dry_run: bool,
) -> None:
    """Apply the ``pr-overlap`` label to both sides of every STRONG pair.

    Weak pairs get the comment only: the label is the coordinator's actionable
    queue, and family-README overlaps would flood it. Writes are checked and
    logged (#13623's silent-write class is a known defect of the older wiring;
    no NEW unchecked write is added here). Adding an already-present label is
    a no-op success, so this is idempotent per re-run. Never removes: once a
    pair resolves, the resolution note speaks for it.
    """
    if dry_run:
        return
    create = subprocess.run(
        ["gh", "label", "create", OVERLAP_LABEL, "--repo", repo,
         "--color", "D93F0B",
         "--description",
         "Advisory: another open PR touches the same files (organ #13615)"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if create.returncode != 0 and "already exists" not in (create.stderr or ""):
        print(f"WARN: label create {OVERLAP_LABEL} failed: "
              f"{(create.stderr or create.stdout).strip()}", file=sys.stderr)
    numbers = sorted({n for c in strong for n in (c.a_number, c.b_number)})
    for number in numbers:
        proc = subprocess.run(
            ["gh", "pr", "edit", str(number), "--repo", repo,
             "--add-label", OVERLAP_LABEL],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )
        if proc.returncode != 0:
            print(f"WARN: add label {OVERLAP_LABEL} to #{number} failed: "
                  f"{(proc.stderr or proc.stdout).strip()}", file=sys.stderr)
        else:
            print(f"  label {OVERLAP_LABEL} -> #{number}", file=sys.stderr)


def _format_human_summary(result: ScanResult) -> str:
    lines = []
    lines.append(
        f"scanned={result.total_prs_scanned} "
        f"distinct_paths={result.distinct_paths} "
        f"collisions={result.n_collisions} "
        f"(strong={len(result.strong_collisions)} "
        f"weak={result.n_collisions - len(result.strong_collisions)})"
    )
    for c in result.collisions[:20]:
        lines.append(
            f"  [{c.tier}] #{c.a_number}/#{c.b_number} "
            f"paths={', '.join(c.shared_paths)}"
            + (f" issues={', '.join(f'#{i}' for i in c.common_issues)}"
               if c.common_issues else "")
        )
    if result.n_collisions > 20:
        lines.append(f"  ... and {result.n_collisions - 20} more (see JSON)")
    if result.stacked_pairs_excluded:
        pairs = ", ".join(f"#{a}/#{b}" for a, b in result.stacked_pairs_excluded)
        lines.append(f"  stacked excluded: {pairs}")
    return "\n".join(lines)


def _self_test() -> int:
    """Offline control suite (#13615 acceptance), no network.

    Positive: the synthetic pair, both historical strong pairs. Negative: a
    stacked pair and an artifact-only pair produce NOTHING. A guard that
    reports everything reports nothing -- the negatives are as load-bearing
    as the positives.
    """
    failures: list[str] = []

    def check(name: str, ok: bool) -> None:
        print(f"{'OK  ' if ok else 'FAIL'} {name}")
        if not ok:
            failures.append(name)

    prs = [
        PrRow(number=SELF_TEST_PAIR[0], title="A", paths=(SELF_TEST_SHARED_PATH,)),
        PrRow(number=SELF_TEST_PAIR[1], title="B", paths=(SELF_TEST_SHARED_PATH,)),
        PrRow(number=900003, title="C", paths=("only/unique.ipynb",)),
    ]
    result = detect_path_collisions(prs)
    check("synthetic pair detected",
          any(c.a_number == SELF_TEST_PAIR[0]
              and c.b_number == SELF_TEST_PAIR[1]
              and SELF_TEST_SHARED_PATH in c.shared_paths
              for c in result.collisions))

    # Historical positive controls (#13615 acceptance): both pairs flagged
    # strong, at their state of then.
    for a, b, path, issue in HISTORICAL_STRONG_PAIRS:
        rows = [
            PrRow(number=a, title=f"feat(#{issue}): x",
                  paths=(path,), body=f"Closes #{issue}"),
            PrRow(number=b, title=f"fix(#{issue}): y",
                  paths=(path, f"other/{b}.md"), body=f"See #{issue}"),
        ]
        res = detect_path_collisions(rows)
        coll = next((c for c in res.collisions
                     if {c.a_number, c.b_number} == {a, b}), None)
        check(f"historical #{a}/#{b} flagged strong with #{issue}",
              coll is not None
              and coll.tier == TIER_STRONG
              and issue in coll.common_issues
              and path in coll.shared_paths)

    # Negative: stacked pair (base of one = head of the other) -> NOTHING.
    stacked = detect_path_collisions([
        PrRow(number=900010, title="base tranche", paths=("stacked/x.md",),
              base_ref="main", head_ref="feature/stack-1"),
        PrRow(number=900011, title="upper tranche", paths=("stacked/x.md",),
              base_ref="feature/stack-1", head_ref="feature/stack-2"),
    ])
    check("stacked pair produces no collision",
          stacked.n_collisions == 0
          and (900010, 900011) in stacked.stacked_pairs_excluded)

    # Negative: artifact-only overlap (catalogue + twin registry) -> NOTHING.
    artifacts = detect_path_collisions([
        PrRow(number=900020, title="a", paths=(
            "COURSE_CATALOG.generated.json", "COURSE_CATALOG.generated.md",
            "scripts/notebook_tools/twin_pairs.d/app-1-nqueens.yaml")),
        PrRow(number=900021, title="b", paths=(
            "COURSE_CATALOG.generated.json",
            "scripts/notebook_tools/twin_pairs.d/app-2-pct.yaml")),
    ])
    check("artifact-only overlap produces no collision",
          artifacts.n_collisions == 0)

    # Tier discrimination: shared path, disjoint issues -> weak, not strong.
    weak = detect_path_collisions([
        PrRow(number=900030, title="docs(#100): intro", paths=("README.md",)),
        PrRow(number=900031, title="docs(#200): links", paths=("README.md",)),
    ])
    check("disjoint-issue overlap is weak tier",
          weak.n_collisions == 1 and weak.collisions[0].tier == TIER_WEAK
          and weak.collisions[0].common_issues == ())

    # Body keyword extraction: issues cited only in the body still tier the
    # pair strong (the title-only filter of #13359 missed these).
    body_only = detect_path_collisions([
        PrRow(number=900040, title="feat: X", paths=("n/x.ipynb",),
              body="Closes #12373\n\nPart of #9."),
        PrRow(number=900041, title="fix: Y", paths=("n/x.ipynb",),
              body="See #12373 for context."),
    ])
    check("body-only common issue tiers strong",
          body_only.n_collisions == 1
          and body_only.collisions[0].tier == TIER_STRONG
          and 12373 in body_only.collisions[0].common_issues)

    if failures:
        print(f"SELF-TEST FAILED ({len(failures)} control(s)): {failures}")
        return 2
    print("SELF-TEST OK: all controls satisfied")
    return 0


def _cli(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__.splitlines()[0],
    )
    ap.add_argument("--limit", type=int, default=500,
                    help="open PRs to scan (default 500; gh's own default is 30)")
    ap.add_argument("--repo", default=None,
                    help="repo (default: gh default / GITHUB_REPOSITORY)")
    ap.add_argument("--dry-run", action="store_true",
                    help="log detections, post/label nothing")
    ap.add_argument("--same-issue-only", action="store_true",
                    help="post only STRONG-tier collisions (both PRs cite a "
                         "common issue in title or body)")
    ap.add_argument(
        "--fail-on-write-loss", action="store_true",
        help=(
            "Exit non-zero when confirmed writes fall short of planned ones. "
            "The organ still blocks nothing -- it runs on schedule only, is "
            "absent from the required set and from the PR gate roster -- but "
            "a red run is the one signal a muted organ cannot produce on its "
            "own. Without it, 30 failed writes out of 33 concluded `success` "
            "(#14236), and a green run reads as `nothing to report`."
        ),
    )
    ap.add_argument("--self-test", action="store_true",
                    help="run the offline control suite; exit 2 if any fails")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    repo = args.repo or _repo_default()
    try:
        prs = list_open_prs(repo, args.limit)
    except RuntimeError as e:
        print(str(e), file=sys.stderr)
        return 0  # advisory: a listing failure must not red the run

    result = detect_path_collisions(prs)

    if args.same_issue_only and result.collisions:
        result.collisions = strong_collisions(result.collisions)
        result.colliding_prs = sorted(
            {n for c in result.collisions for n in (c.a_number, c.b_number)}
        )

    print(json.dumps(result.as_dict(), ensure_ascii=False, indent=2))
    print(_format_human_summary(result), file=sys.stderr)

    # Plan over the UNION colliding ∪ marker-carriers (#13489): reads only.
    title_by_number = {p.number: p.title for p in prs}
    marker_by_number, scan_failed = scan_markers(
        repo, [p.number for p in prs]
    )
    for number in sorted(scan_failed):
        print(
            f"WARN: comment scan failed for #{number} -- skipped this run "
            "(no post/update/retract planned for it)",
            file=sys.stderr,
        )
    plan = [
        a for a in plan_actions(
            set(result.colliding_prs), result.collisions, title_by_number,
            marker_by_number,
            datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%MZ"),
        )
        if a.number not in scan_failed
    ]

    counts: dict[str, int] = {}
    for a in plan:
        counts[a.verb] = counts.get(a.verb, 0) + 1
    prefix = "would-" if args.dry_run else ""
    print(
        "actions: "
        + " ".join(
            f"{v}={counts.get(v, 0)}" for v in ("post", "update", "retract", "none")
        ),
        file=sys.stderr,
    )
    confirmed: dict[str, int] = {}
    for a in plan:
        if a.verb == "none":
            continue
        print(f"  {prefix}{a.verb} #{a.number}", file=sys.stderr)
        if a.verb == "post":
            ok = post_comment(repo, a.number, a.body, args.dry_run)
        else:  # update | retract: both are an in-place PATCH by comment id
            ok = edit_comment(repo, a.number, a.comment_id, a.body, args.dry_run)
        if ok:
            confirmed[a.verb] = confirmed.get(a.verb, 0) + 1

    # Label both sides of every strong pair (#13615). In --same-issue-only
    # mode every posted collision is strong; otherwise re-derive the tier.
    label_strong_pairs(repo, result.strong_collisions, args.dry_run)

    if not args.dry_run:
        print(
            "writes confirmed: "
            + " ".join(
                f"{v}={confirmed.get(v, 0)}" for v in ("post", "update", "retract")
            ),
            file=sys.stderr,
        )
        attempted = sum(counts.get(v, 0) for v in ("post", "update", "retract"))
        ok_count = sum(confirmed.get(v, 0) for v in ("post", "update", "retract"))
        failures = attempted - ok_count
        if failures:
            msg = (
                f"{failures} write(s) failed -- planned {attempted}, "
                f"confirmed {ok_count}"
            )
            print(f"advisory: {msg}", file=sys.stderr)
            # An annotation surfaces the loss on the run page itself, where a
            # `success` conclusion would otherwise be the only thing visible.
            print(f"::error title=collision organ mute::{msg}", file=sys.stdout)
            if args.fail_on_write_loss:
                return 1

    return 0  # advisory on the merge path: blocks no PR, gates no check


if __name__ == "__main__":
    sys.exit(_cli())
