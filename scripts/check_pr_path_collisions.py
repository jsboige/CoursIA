#!/usr/bin/env python3
"""ADVISORY detector: open PRs sharing a file path (issue #13359).

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

What it does
------------
Lists all OPEN pull requests, builds a path -> {PR numbers} map, and reports
every unordered pair sharing at least one file path. For each PR involved it
posts (or updates/retracts) ONE advisory comment naming the other PR(s) and the
shared paths. The comment is marker-framed and idempotent: a re-run never
creates a duplicate; a PR whose collisions are resolved loses its comment.

Deliberately ADVISORY. Two open PRs on one file are sometimes legitimate
(co-ordinated tranches, explicit ``paths:`` partition). The defect is
INVISIBILITY, not simultaneity. This organ never blocks: exit code is always 0,
and the workflow grants only read + pull-requests-write, never the merge gate.

Scope (from #13359)
-------------------
- Invent NO new claim lock. Do not touch `check_lane_claim.py` -- the claim
  protocol stays the cross-lane arbiter. This covers the intra-lane blind spot
  and the coordinator-at-merge blind spot, neither of which the claim sees.

Usage
-----
::

    # Detect + post/retract advisory comments on the whole OPEN pool:
    python scripts/check_pr_path_collisions.py

    # Log only, post nothing (CI workflow_dispatch dry_run):
    python scripts/check_pr_path_collisions.py --dry-run

    # Positive-control self-test (synthetic pair --- no network):
    python scripts/check_pr_path_collisions.py --self-test

Exit codes:
  0 -- always (advisory). Even a report of collisions exits 0; the actionable
       payload is the comment + the JSON, never the green conclusion.
  2 -- only under --self-test, if the synthetic positive control was NOT found
       (the detector is broken and would silence the signal it was built for).

CLI flags
---------
``--limit``       cap PRs fetched via ``gh pr list`` (default 500; the default
                  ``gh pr list`` limit is 30 -- a silent cap that hid entire
                  stacks this month). 500 covers the whole open pool here.
``--repo``        override repo (default: gh default / GITHUB_REPOSITORY).
``--dry-run``     log detections, post/retract nothing.
--json            always on stdout.
--self-test       require the synthetic pair to be detected, else exit 2.
"""

from __future__ import annotations

import argparse
import json
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

# The synthetic positive control. NOT a live repo pair (those are volatile:
# they merge and vanish). It is seeded straight into the pure detector, so the
# self-test is reproducible offline and fails loudly if the detector breaks.
SELF_TEST_PAIR = (900001, 900002)
SELF_TEST_SHARED_PATH = "MyIA.AI.Notebooks/foo/bar.ipynb"


@dataclass(frozen=True)
class PathCollision:
    """An unordered pair of open PRs sharing at least one file path."""
    a_number: int
    b_number: int
    shared_paths: tuple[str, ...]

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
        }


@dataclass(frozen=True)
class PrRow:
    """Minimal open PR record the detector needs."""
    number: int
    title: str
    paths: tuple[str, ...]

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
        )


@dataclass
class ScanResult:
    """Aggregate of one detection run."""
    total_prs_scanned: int = 0
    distinct_paths: int = 0
    collisions: list[PathCollision] = field(default_factory=list)
    colliding_prs: list[int] = field(default_factory=list)

    @property
    def n_collisions(self) -> int:
        return len(self.collisions)

    def as_dict(self) -> dict:
        return {
            "total_prs_scanned": self.total_prs_scanned,
            "distinct_paths": self.distinct_paths,
            "n_collisions": self.n_collisions,
            "collisions": [c.as_dict() for c in self.collisions],
            "colliding_prs": self.colliding_prs,
        }


def detect_path_collisions(prs: Iterable[PrRow]) -> ScanResult:
    """Group open PRs by file path; report every pair sharing >=1 path.

    ``prs`` is consumed once. The result is deterministic: collisions sorted by
    (lowest number, highest number), shared paths sorted by path string.
    """
    result = ScanResult()
    rows = list(prs)
    result.total_prs_scanned = len(rows)

    path_to_numbers: dict[str, set[int]] = {}
    for r in rows:
        for p in r.paths:
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

    colliding_pair_set = set(pair_paths.keys())
    collisions = [
        PathCollision(
            a_number=a,
            b_number=b,
            shared_paths=tuple(sorted(paths)),
        )
        for (a, b), paths in sorted(
            pair_paths.items(),
            key=lambda kv: (kv[0][0], kv[0][1]),
        )
    ]
    result.collisions = collisions
    result.colliding_prs = sorted(
        {n for c in collisions for n in (c.a_number, c.b_number)}
    )
    return result


def collisions_for_pr(number: int, collisions: Iterable[PathCollision]) -> list[PathCollision]:
    """Collisions where ``number`` is one side, others normalized to `other`."""
    return [c for c in collisions if number in (c.a_number, c.b_number)]


def _issue_numbers(title: str) -> set[int]:
    """Issue numbers referenced in a PR title."""
    return {int(n) for n in re.findall(r"#(\d+)", title or "")}


def filter_same_issue_collisions(
    collisions: Iterable[PathCollision],
    title_by_number: dict[int, str],
) -> list[PathCollision]:
    """Keep only collisions where BOTH PRs cite the same issue number in title.

    The pure file-path signal over-fires on shared manifest edits: dozens of
    unrelated PRs legitimately touch the same family ``README.md``. The
    expensive double-delivery the organ exists to catch -- same notebook
    delivered twice -- overwhelmingly coincides with BOTH PRs citing the SAME
    issue (#13296/#13339 both cite #11703). This filter keeps just those.
    ``title_by_number`` maps PR number -> title (empty string if unknown).
    """
    keep = []
    for c in collisions:
        a_issues = _issue_numbers(title_by_number.get(c.a_number, ""))
        b_issues = _issue_numbers(title_by_number.get(c.b_number, ""))
        if a_issues & b_issues:
            keep.append(c)
    return keep


def render_comment(number: int, title: str, own_collisions: list[PathCollision]) -> str:
    """Build the advisory comment body for PR ``number``.

    Names each colliding PR by number and lists the shared paths. Marker-framed
    so a re-run can find, refresh, or retract it in place.
    """
    lines = [
        "<!-- PR-PATH-COLLISION:START -->",
        "## Path-collision (organ #13359) ",
        "",
        f"Cette PR **#{number}** (`{title or '?'}`) touche au moins un chemin "
        "de fichier aussi modifie par d'autres PRs ouvertes. Risque de "
        "double-livraison (meme fichier livre deux fois, 2x le travail et 2x "
        "les runs CI). _Advisory_ : parfois legitime (tranches coordonnees, "
        "partition `paths:` explicite) -- l'organe rend visible, il ne bloque pas.",
        "",
    ]
    for c in sorted(own_collisions, key=lambda c: c.other(number)):
        other = c.other(number)
        lines.append(f"- **#{other}** partage : {', '.join(c.shared_paths)}")
    lines.append("")
    lines.append("<!-- PR-PATH-COLLISION:END -->")
    return "\n".join(lines)


def find_marker_comment(comments: Iterable[dict]) -> str | None:
    """Id of the existing marker comment in ``comments``, or None (pure)."""
    for c in comments or []:
        body = c.get("body") or ""
        if COMMENT_MARKER_START in body:
            return str(c.get("id")) if c.get("id") is not None else None
    return None


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
    """Open PRs with numbers, titles and changed file paths."""
    raw = _gh_json([
        "pr", "list", "--repo", repo, "--state", "open",
        "--limit", str(limit),
        "--json", "number,title,headRefName,files",
    ]) or []
    return [PrRow.from_gh_dict(d) for d in raw]


def existing_comment(repo: str, number: int) -> str | None:
    comments = _gh_json(["pr", "view", str(number), "--repo", repo,
                         "--json", "comments"]) or {}
    return find_marker_comment(comments.get("comments") or [])


def post_comment(repo: str, number: int, body: str, dry_run: bool) -> None:
    if dry_run:
        return
    with tempfile.NamedTemporaryFile(
        "w", suffix=".md", encoding="utf-8", delete=False
    ) as tf:
        tf.write(body)
        tmp_path = tf.name
    try:
        subprocess.run(
            ["gh", "pr", "comment", str(number), "--repo", repo,
             "--body-file", tmp_path],
            capture_output=True, text=True, check=False, encoding="utf-8",
        )
    finally:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)


def _format_human_summary(result: ScanResult) -> str:
    lines = []
    lines.append(
        f"scanned={result.total_prs_scanned} "
        f"distinct_paths={result.distinct_paths} "
        f"collisions={result.n_collisions}"
    )
    for c in result.collisions[:20]:
        lines.append(
            f"  #{c.a_number}/#{c.b_number} "
            f"paths={', '.join(c.shared_paths)}"
        )
    if result.n_collisions > 20:
        lines.append(f"  ... and {result.n_collisions - 20} more (see JSON)")
    return "\n".join(lines)


def _self_test() -> int:
    """Synthetic positive control: a seeded pair MUST be detected."""
    prs = [
        PrRow(number=SELF_TEST_PAIR[0], title="A", paths=(SELF_TEST_SHARED_PATH,)),
        PrRow(number=SELF_TEST_PAIR[1], title="B", paths=(SELF_TEST_SHARED_PATH,)),
        PrRow(number=900003, title="C", paths=("only/unique.ipynb",)),
    ]
    result = detect_path_collisions(prs)
    found = any(
        c.a_number == SELF_TEST_PAIR[0]
        and c.b_number == SELF_TEST_PAIR[1]
        and SELF_TEST_SHARED_PATH in c.shared_paths
        for c in result.collisions
    )
    if not found:
        print("SELF-TEST FAILED: seeded pair not detected -- detector is broken")
        return 2
    print("SELF-TEST OK: seeded pair detected")
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
                    help="log detections, post/retract nothing")
    ap.add_argument("--same-issue-only", action="store_true",
                    help="post only collisions where BOTH PRs cite the same "
                         "issue number in title (cuts shared-README noise)")
    ap.add_argument("--self-test", action="store_true",
                    help="require the synthetic pair to be detected; exit 2 if not")
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
        title_by_number = {p.number: p.title for p in prs}
        result.collisions = filter_same_issue_collisions(
            result.collisions, title_by_number
        )
        result.colliding_prs = sorted(
            {n for c in result.collisions for n in (c.a_number, c.b_number)}
        )

    print(json.dumps(result.as_dict(), ensure_ascii=False, indent=2))
    print(_format_human_summary(result), file=sys.stderr)

    if not args.dry_run:
        for number in result.colliding_prs:
            title = next((p.title for p in prs if p.number == number), "?")
            body = render_comment(
                number, title, collisions_for_pr(number, result.collisions)
            )
            existing = existing_comment(repo, number)
            if existing is None:
                post_comment(repo, number, body, args.dry_run)

    return 0  # advisory: always green


if __name__ == "__main__":
    sys.exit(_cli())
