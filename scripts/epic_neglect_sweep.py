#!/usr/bin/env python3
"""ADVISORY sweep: EPICs no merged PR has cited lately (issue #13653).

Why this exists
---------------
Mandate (user, 2026-08-30): « t'assurer que toutes les issues avancent de
front, et qu'aucun Epic notamment n'est neglige. » Measured firsthand the
same morning: the picker's draw IS varied (8 genres over 3 draws, the
`umbrella` urn serves 105-day-old EPICs) -- but **13/28 open EPICs had no
merged PR citing them** over the 48 h window, 6 of them with >= 2 days
without any activity. Nothing renders that neglect visible between two
draws: a lane that does not draw this EPIC this cycle has no way to see it
falling behind.

The mold
--------
Same shape as `GRAIN-ORPHANS-SWEEP` (#13086): a daily workflow recomputes a
list that is invisible between two manual looks, and upserts ONE
marker-guarded comment on a rendez-vous issue. What was invisible becomes a
list everyone reads at the same place.

Standalone by design: the picker selects a grain FOR a lane; this sweep
measures EPIC neglect FLEET-wide -- different cadence, different consumer
(the coordinator), no picker state involved. It reads only `gh issue list`
+ `gh pr list --state merged`.

What it measures
----------------
For each OPEN issue labeled `EPIC`: days since `updatedAt` (`inact`) and the
number of MERGED PRs citing `#N` (title or body) within the window of the
last `--merged-limit` merged PRs. The window is the REAL span of that fetch
(min..max mergedAt) and is WRITTEN in the report -- a ranking without a
vintage reads as current.

What it deliberately does NOT do
--------------------------------
- Does not close, does not assign, does not tag: it NAMES (G.9 -- the
  coordinator reads the EPIC body before concluding anything).
- A PR merely OPEN (not merged) citing the EPIC does not count as a
  citation: delivery is what un-neglects an EPIC here.
- An EPIC whose work advances under a DIFFERENT issue number is invisible
  to this count (the `#N` link is the only thread followed, in PR titles
  and bodies -- not issue comments).
- One point in time, not a trend.

Usage
-----
::

    # Dry run (print the report, post nothing):
    python scripts/epic_neglect_sweep.py

    # Upsert the marker-guarded comment on the rendez-vous issue:
    python scripts/epic_neglect_sweep.py --apply-comment 13653

    # Offline control suite (no network):
    python scripts/epic_neglect_sweep.py --self-test

Exit codes:
  0 -- always for a sweep (advisory; even a report full of neglected EPICs
       is green -- the payload is the comment, not the conclusion).
  2 -- only under --self-test, if a control was not satisfied.

CLI flags
---------
``--repo``          override repo (default: gh default / GITHUB_REPOSITORY).
``--merged-limit``  how many recent merged PRs form the citation window
                    (default 200; matches the founding measurement #13653).
``--apply-comment`` rendez-vous issue number for the marker-guarded upsert.
``--self-test``     run the offline controls; exit 2 if any fails.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Iterable

SWEEP_MARKER_START = "<!-- EPIC-NEGLECT-SWEEP:START -->"
SWEEP_MARKER_END = "<!-- EPIC-NEGLECT-SWEEP:END -->"

EPIC_LABEL = "EPIC"


def _now() -> datetime:
    return datetime.now(timezone.utc)


def _parse_iso(s: str) -> datetime:
    """Parse gh's ISO-8601 (trailing Z) into an aware datetime."""
    return datetime.fromisoformat((s or "").replace("Z", "+00:00"))


@dataclass(frozen=True)
class Epic:
    """One OPEN EPIC-labeled issue."""
    number: int
    title: str
    created_at: datetime
    updated_at: datetime

    @classmethod
    def from_gh_dict(cls, d: dict) -> "Epic":
        return cls(
            number=int(d["number"]),
            title=(d.get("title") or "").strip(),
            created_at=_parse_iso(d["createdAt"]),
            updated_at=_parse_iso(d["updatedAt"]),
        )


@dataclass(frozen=True)
class MergedPr:
    """One recently merged PR (the citation pool)."""
    number: int
    title: str
    body: str
    merged_at: datetime

    @classmethod
    def from_gh_dict(cls, d: dict) -> "MergedPr":
        return cls(
            number=int(d["number"]),
            title=(d.get("title") or ""),
            body=(d.get("body") or ""),
            merged_at=_parse_iso(d["mergedAt"]),
        )

    def cited_issues(self) -> set[int]:
        """`#N` tokens in title+body -- the founding measurement's method."""
        return {int(n) for n in re.findall(r"#(\d+)",
                                           f"{self.title}\n{self.body}")}


@dataclass(frozen=True)
class NeglectRow:
    """An EPIC no merged PR in the window cites."""
    epic: Epic
    inact_days: float
    age_days: float


def measure_neglect(
    epics: Iterable[Epic],
    merged: Iterable[MergedPr],
    now: datetime,
) -> tuple[list[NeglectRow], int, tuple[datetime, datetime] | None]:
    """Pure core: (neglected rows sorted by inact desc, n_cited_epics, window).

    The window is the real span of the merged fetch (min..max mergedAt), so
    the report can carry its own vintage. A cited EPIC never appears in the
    rows -- that exclusion is the positive control of #13653.
    """
    epics = list(epics)
    merged = list(merged)
    cited: set[int] = set()
    for pr in merged:
        cited |= pr.cited_issues()
    rows = [
        NeglectRow(
            epic=e,
            inact_days=(now - e.updated_at).total_seconds() / 86400.0,
            age_days=(now - e.created_at).total_seconds() / 86400.0,
        )
        for e in epics
        if e.number not in cited
    ]
    rows.sort(key=lambda r: (-r.inact_days, r.epic.number))
    n_cited = len(epics) - len(rows)
    window = None
    if merged:
        window = (min(p.merged_at for p in merged),
                  max(p.merged_at for p in merged))
    return rows, n_cited, window


def build_report(
    rows: list[NeglectRow],
    total_epics: int,
    n_cited: int,
    window: tuple[datetime, datetime] | None,
    now: datetime,
    n_merged_scanned: int,
) -> str:
    """Marker-guarded body. The empty case is written too: a mute sweep is
    indistinguishable from a dead one (#13086's lesson)."""
    stamp = now.strftime("%Y-%m-%dT%H:%MZ")
    if window is not None:
        vintage = (
            f"Fenetre de citation : {n_merged_scanned} PR(s) mergee(s), "
            f"{window[0].strftime('%Y-%m-%dT%H:%MZ')} -> "
            f"{window[1].strftime('%Y-%m-%dT%H:%MZ')}"
        )
    else:
        vintage = "Fenetre de citation : aucune PR mergee scannee"
    lines = [SWEEP_MARKER_START]
    lines.append(f"**Balayage du delaissement d'EPIC** ({stamp}) — "
                 f"{len(rows)}/{total_epics} EPIC(s) ouverte(s) sans aucune "
                 f"PR mergee les citant dans la fenetre. {n_cited} citee(s), "
                 f"non listees ci-dessous.")
    lines.append("")
    lines.append(f"_{vintage}. Classement : point dans le temps, pas une tendance._")
    lines.append("")
    if not rows:
        lines.append("**Aucune EPIC delaissee sur la fenetre.** Chaque EPIC "
                     "ouverte est citee par au moins une PR mergeee recemment.")
    else:
        lines.append("| inact | age | EPIC |")
        lines.append("|---|---|---|")
        for r in rows:
            lines.append(
                f"| {r.inact_days:.1f} j | {r.age_days:.0f} j | "
                f"#{r.epic.number} — {r.epic.title} |"
            )
    lines.append("")
    lines.append("_Ce que ce compte NE mesure pas :_ une EPIC citee par une PR "
                 "**ouverte non mergee** compte comme non citee ; une EPIC dont "
                 "le travail avance sous un autre numero est invisible ; la "
                 "citation se lit dans les titres et bodies de PR, pas dans les "
                 "commentaires d'issue. Ne ferme rien, n'assigne rien — le "
                 "tranchage reste au coordinateur (G.9).")
    lines.append("")
    lines.append(f"_Recalcul a la demande : `python scripts/epic_neglect_sweep.py`. "
                 f"Cf #13653._")
    lines.append(SWEEP_MARKER_END)
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# gh wiring
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
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


def list_open_epics(repo: str) -> list[Epic]:
    raw = _gh_json([
        "issue", "list", "--repo", repo, "--state", "open",
        "--limit", "400", "--json", "number,title,createdAt,updatedAt,labels",
    ]) or []
    return [
        Epic.from_gh_dict(d)
        for d in raw
        if any(lb.get("name") == EPIC_LABEL for lb in (d.get("labels") or []))
    ]


def list_recent_merged_prs(repo: str, limit: int) -> list[MergedPr]:
    raw = _gh_json([
        "pr", "list", "--repo", repo, "--state", "merged",
        "--limit", str(limit),
        "--json", "number,title,body,mergedAt",
    ]) or []
    return [MergedPr.from_gh_dict(d) for d in raw]


def upsert_sweep_comment(repo: str, issue_number: int, body: str) -> None:
    """One marker-guarded comment per issue, updated in place (never a flood).

    Writes are checked: a failed fetch/POST/PATCH raises (the caller logs and
    the run stays green -- but a silent no-op is never mistaken for a post).
    """
    comments = _gh_json([
        "issue", "view", str(issue_number), "--repo", repo, "--json", "comments",
    ]) or {}
    cid = next(
        (str(c["id"]) for c in (comments.get("comments") or [])
         if SWEEP_MARKER_START in (c.get("body") or "")),
        None,
    )
    if cid is not None:
        proc = subprocess.run(
            ["gh", "api", "--method", "PATCH",
             f"repos/{repo}/issues/comments/{cid}",
             "-f", f"body={body}"],
            capture_output=True, text=True, encoding="utf-8",
        )
        if proc.returncode != 0:
            raise RuntimeError(f"PATCH comment failed: {proc.stderr.strip()}")
    else:
        proc = subprocess.run(
            ["gh", "issue", "comment", str(issue_number), "--repo", repo,
             "--body-file", "-"],
            input=body, capture_output=True, text=True, encoding="utf-8",
        )
        if proc.returncode != 0:
            raise RuntimeError(f"POST comment failed: {proc.stderr.strip()}")


def _self_test() -> int:
    """Offline controls (#13653 acceptance), no network."""
    failures: list[str] = []

    def check(name: str, ok: bool) -> None:
        print(f"{'OK  ' if ok else 'FAIL'} {name}")
        if not ok:
            failures.append(name)

    now = _now()
    epic_a = Epic(11900, "Meta-EPIC du picker",
                  now.replace(microsecond=0), now)  # updated now -> inact 0
    from datetime import timedelta
    epic_b = Epic(10921, "Site GitHub Pages",
                  now - timedelta(days=15), now - timedelta(days=4))
    epic_cited = Epic(10355, "EPIC citee par une mergee recente",
                      now - timedelta(days=100), now - timedelta(days=1))
    merged_recent = [
        MergedPr(13674, "feat(guards,#13615): x", "Closes #13615",
                 now - timedelta(hours=2)),
        MergedPr(13671, "feat(genai,#13655): y", "See #10355 and #13655.",
                 now - timedelta(hours=30)),
    ]

    rows, n_cited, window = measure_neglect(
        [epic_a, epic_b, epic_cited], merged_recent, now)

    # Acceptance: neglected EPICs named, sorted by inact desc.
    check("neglected named, sorted by inact desc",
          [r.epic.number for r in rows] == [10921, 11900])
    # Acceptance (positive control): a cited EPIC does NOT appear.
    check("cited EPIC excluded from the list",
          all(r.epic.number != 10355 for r in rows) and n_cited == 1)
    # Acceptance: the window and measurement date are written in the report.
    report = build_report(rows, 3, n_cited, window, now, len(merged_recent))
    check("report carries the vintage (window + date)",
          "Fenetre de citation" in report
          and "PR(s) mergee(s)" in report
          and now.strftime("%Y-%m-%dT%H:%MZ")[:10] in report)
    # Acceptance: the report says what it does NOT measure.
    check("limitations written (open-PR, other-number)",
          "ouverte non mergee" in report and "autre numero" in report)
    # The unmerged-citation semantics are structural: the CLI feeds the
    # core ONLY from `gh pr list --state merged`, so an open PR's citation
    # never enters the pool. Offline, that reduces to: citations come from
    # the pool given, nothing else. Control both directions.
    cited_pool = [MergedPr(13700, "cite 10355", "Closes #10355",
                           now - timedelta(hours=1))]
    other_pool = [MergedPr(13701, "cite autre", "Closes #999",
                           now - timedelta(hours=1))]
    rows_c, _, _ = measure_neglect([epic_cited], cited_pool, now)
    rows_o, _, _ = measure_neglect([epic_cited], other_pool, now)
    check("citations come only from the (merged) pool given",
          len(rows_c) == 0 and len(rows_o) == 1)
    # Empty case is written (mute sweep == dead sweep).
    empty = build_report([], 3, 3, window, now, len(merged_recent))
    check("empty case written",
          "Aucune EPIC delaissee" in empty)
    # Marker framing (upsert finds it).
    check("marker framed",
          report.startswith(SWEEP_MARKER_START)
          and report.rstrip().endswith(SWEEP_MARKER_END))
    # Citation parser.
    check("citation parser reads title+body",
          MergedPr(1, "x #12", "See #34", now).cited_issues() == {12, 34})

    if failures:
        print(f"SELF-TEST FAILED ({len(failures)} control(s)): {failures}")
        return 2
    print("SELF-TEST OK: all controls satisfied")
    return 0


def _cli(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=None,
                    help="repo (default: gh default / GITHUB_REPOSITORY)")
    ap.add_argument("--merged-limit", type=int, default=200,
                    help="recent merged PRs forming the citation window "
                         "(default 200, matches the founding measurement)")
    ap.add_argument("--apply-comment", type=int, default=None, metavar="N",
                    help="rendez-vous issue number for the marker-guarded "
                         "upsert (omit: dry run, print only)")
    ap.add_argument("--self-test", action="store_true",
                    help="run the offline controls; exit 2 if any fails")
    args = ap.parse_args(argv)

    if args.self_test:
        return _self_test()

    repo = args.repo or _repo_default()
    now = _now()
    try:
        epics = list_open_epics(repo)
        merged = list_recent_merged_prs(repo, args.merged_limit)
    except RuntimeError as e:
        print(str(e), file=sys.stderr)
        return 0  # advisory: a listing failure must not red the run

    rows, n_cited, window = measure_neglect(epics, merged, now)
    report = build_report(rows, len(epics), n_cited, window, now, len(merged))
    print(report)

    if args.apply_comment is None:
        print("\n(dry run: --apply-comment absent, nothing posted)",
              file=sys.stderr)
        return 0
    try:
        upsert_sweep_comment(repo, args.apply_comment, report)
        print(f"upserted marker-guarded comment on #{args.apply_comment}",
              file=sys.stderr)
    except RuntimeError as e:
        print(f"WARN: upsert failed, nothing posted: {e}", file=sys.stderr)
    return 0  # advisory: always green


if __name__ == "__main__":
    sys.exit(_cli())
