#!/usr/bin/env python3
"""Report open EPIC bodies that no longer reflect merged delivery.

The analyzer is deliberately read-only. It turns two observable discrepancies
into a triage list:

* merged pull requests cite an EPIC, but their PR numbers are absent from its
  body (``unrecorded_merged``);
* the EPIC still declares a dormant stance despite merged delivery
  (``stance_contradicted``).

A citation is only a signal: a PR may mention an EPIC incidentally. The output
therefore names every PR for human review and never edits an issue body.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections.abc import Iterable
from dataclasses import asdict, dataclass
from datetime import UTC, date, datetime, timedelta

EPIC_TITLE_RE = re.compile(r"\bepic\b", re.IGNORECASE)
ISSUE_REF_RE = re.compile(r"(?<![\w])#(\d+)\b")
OPEN_ISSUE_LIMIT = 500
SEARCH_RESULT_CAP = 1000
MERGED_SLICE_DAYS = 3
MAX_LOOKBACK_DAYS = 3650

# A dormant stance must be a declaration, not merely contain a word such as
# "background" or "plus tard" in ordinary prose. Strong phrases stand alone;
# broad status words require a title, heading, or explicit status/priority line.
STRONG_DORMANT_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("pas pour maintenant", re.compile(r"\bpas\s+pour\s+maintenant\b", re.IGNORECASE)),
    (
        "pas à traiter maintenant",
        re.compile(
            r"\bpas\s+(?:forc[ée]ment\s+)?[àa]\s+traiter\s+maintenant\b",
            re.IGNORECASE,
        ),
    ),
    (
        "ne pas démarrer",
        re.compile(r"\bn['’]est\s+pas\s+[àa]\s+d[ée]marrer\b", re.IGNORECASE),
    ),
    (
        "à ouvrir quand on aura le temps",
        re.compile(r"\b[àa]\s+ouvrir\s+quand\s+on\s+aura\s+le\s+temps\b", re.IGNORECASE),
    ),
    (
        "backlog indexé",
        re.compile(r"\bbacklog\s+index[ée]e?s?\b", re.IGNORECASE),
    ),
)
CONTEXTUAL_DORMANT_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (
        "priority-low",
        re.compile(
            r"\b(?:priority\s*[-_: ]\s*low|low\s+priority)\b",
            re.IGNORECASE,
        ),
    ),
    ("background", re.compile(r"\bbackground\b", re.IGNORECASE)),
    ("plus tard", re.compile(r"\bplus\s+tard\b", re.IGNORECASE)),
    ("en veille", re.compile(r"\ben\s+veille\b", re.IGNORECASE)),
)
STATUS_CONTEXT_RE = re.compile(
    r"(?:^|\b)(?:statut|status|priorit[ée]|priority)\b",
    re.IGNORECASE,
)
ACTIVE_OVERRIDE_RE = re.compile(r"\bstatut\s+corrig[ée]\b", re.IGNORECASE)


@dataclass(frozen=True)
class Epic:
    """One open issue identified as an EPIC by title or label."""

    number: int
    title: str
    body: str

    @classmethod
    def from_gh_dict(cls, row: dict) -> Epic:
        return cls(
            number=int(row["number"]),
            title=(row.get("title") or "").strip(),
            body=row.get("body") or "",
        )


@dataclass(frozen=True)
class MergedPullRequest:
    """One merged pull request in the measured corpus."""

    number: int
    title: str
    body: str
    merged_at: str

    @classmethod
    def from_gh_dict(cls, row: dict) -> MergedPullRequest:
        return cls(
            number=int(row["number"]),
            title=row.get("title") or "",
            body=row.get("body") or "",
            merged_at=row.get("mergedAt") or "",
        )

    def cited_issues(self) -> set[int]:
        return {
            int(number)
            for number in ISSUE_REF_RE.findall(f"{self.title}\n{self.body}")
        }


@dataclass(frozen=True)
class EpicStaleness:
    """Triage signals for one EPIC."""

    number: int
    title: str
    unrecorded_merged: tuple[int, ...]
    stance_contradicted: bool
    stance_pattern: str | None


def is_epic(row: dict) -> bool:
    """Recognize both the title convention and labels containing EPIC as a word."""
    labels = (
        label.get("name") or ""
        for label in (row.get("labels") or [])
    )
    return bool(EPIC_TITLE_RE.search(row.get("title") or "")) or any(
        EPIC_TITLE_RE.search(label) for label in labels
    )


def prose_lines_for_stance(title: str, body: str) -> list[str]:
    """Return non-quoted, non-code lines that may declare a live stance.

    Historical prose is often retained in block quotes when an EPIC is updated.
    Treating such a quotation as current recreates the exact false positive that
    motivated issue #13906. Fenced, indented, and inline code are excluded for
    the same reason: examples are not declarations.
    """
    kept = [re.sub(r"`[^`\n]*`", "", title)]
    in_fence = False
    in_quote = False
    for line in body.splitlines():
        if re.match(r"^\s*(```|~~~)", line):
            in_fence = not in_fence
            continue
        if in_fence or re.match(r"^(?: {4}|\t)", line):
            continue
        if re.match(r"^\s*>", line):
            in_quote = True
            continue
        if in_quote:
            if not line.strip():
                in_quote = False
            else:
                continue
        kept.append(re.sub(r"`[^`\n]*`", "", line))
    return kept


def dormant_stance(title: str, body: str) -> str | None:
    """Return the first live dormant-stance pattern, if any."""
    if ACTIVE_OVERRIDE_RE.search(body):
        return None
    lines = prose_lines_for_stance(title, body)
    prose = "\n".join(lines)
    for name, pattern in STRONG_DORMANT_PATTERNS:
        if pattern.search(prose):
            return name
    for index, line in enumerate(lines):
        if index > 0 and not STATUS_CONTEXT_RE.search(line):
            continue
        for name, pattern in CONTEXTUAL_DORMANT_PATTERNS:
            if pattern.search(line):
                return name
    return None


def analyze_epics(
    epics: Iterable[Epic],
    merged_prs: Iterable[MergedPullRequest],
) -> list[EpicStaleness]:
    """Compute staleness signals without network access or side effects."""
    epics = list(epics)
    merged_prs = list(merged_prs)
    cited_by_epic: dict[int, list[MergedPullRequest]] = {
        epic.number: [] for epic in epics
    }
    for pr in merged_prs:
        for issue_number in pr.cited_issues() & cited_by_epic.keys():
            cited_by_epic[issue_number].append(pr)

    findings: list[EpicStaleness] = []
    for epic in epics:
        citing = cited_by_epic[epic.number]
        recorded = {
            int(number) for number in ISSUE_REF_RE.findall(epic.body)
        }
        unrecorded = tuple(
            sorted(
                (pr.number for pr in citing if pr.number not in recorded),
                reverse=True,
            )
        )
        stance = dormant_stance(epic.title, epic.body) if citing else None
        if unrecorded or stance:
            findings.append(
                EpicStaleness(
                    number=epic.number,
                    title=epic.title,
                    unrecorded_merged=unrecorded,
                    stance_contradicted=stance is not None,
                    stance_pattern=stance,
                )
            )

    findings.sort(
        key=lambda finding: (
            -len(finding.unrecorded_merged),
            not finding.stance_contradicted,
            finding.number,
        )
    )
    return findings


def build_payload(
    epics: list[Epic],
    merged_prs: list[MergedPullRequest],
) -> dict:
    """Build an auditable payload whose zero includes the corpus actually read."""
    findings = analyze_epics(epics, merged_prs)
    merged_dates = sorted(pr.merged_at for pr in merged_prs if pr.merged_at)
    return {
        "corpus": {
            "open_epics_examined": len(epics),
            "merged_prs_examined": len(merged_prs),
            "merged_window_start": merged_dates[0] if merged_dates else None,
            "merged_window_end": merged_dates[-1] if merged_dates else None,
        },
        "finding_count": len(findings),
        "findings": [asdict(finding) for finding in findings],
        "limitations": [
            "A PR citation is a triage signal, not proof that the PR delivers the EPIC.",
            "Dormant stances are heuristic signals limited to declarative status wording.",
            "Only the fetched merged-PR corpus is measured; the corpus counts and window are authoritative.",
            "The analyzer is read-only and never rewrites issue bodies.",
        ],
    }


def _gh_json(args: list[str]) -> object:
    try:
        result = subprocess.run(
            ["gh", *args],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
    except OSError as exc:
        raise RuntimeError(f"cannot execute gh: {exc}") from exc
    if result.returncode != 0:
        raise RuntimeError(
            f"gh failed ({result.returncode}): "
            f"{result.stderr.strip() or result.stdout.strip()}"
        )
    return json.loads(result.stdout or "null")


def _default_repo() -> str:
    if repo := os.environ.get("GITHUB_REPOSITORY"):
        return repo
    result = subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    return result.stdout.strip() or "jsboige/CoursIA"


def list_open_epics(repo: str) -> list[Epic]:
    rows = _gh_json(
        [
            "issue",
            "list",
            "--repo",
            repo,
            "--state",
            "open",
            "--limit",
            str(OPEN_ISSUE_LIMIT),
            "--json",
            "number,title,body,labels",
        ]
    ) or []
    if len(rows) >= OPEN_ISSUE_LIMIT:
        raise RuntimeError(
            f"open-issue corpus reached its {OPEN_ISSUE_LIMIT}-issue fetch limit"
        )
    return [Epic.from_gh_dict(row) for row in rows if is_epic(row)]


def _merged_pr_slice(repo: str, since: date, until: date) -> list[dict]:
    """Fetch one ``[since, until)`` merge-time slice without silent truncation."""
    rows = _gh_json(
        [
            "pr",
            "list",
            "--repo",
            repo,
            "--state",
            "merged",
            "--search",
            f"merged:>={since.isoformat()} merged:<{until.isoformat()}",
            "--limit",
            str(SEARCH_RESULT_CAP),
            "--json",
            "number,title,body,mergedAt",
        ]
    ) or []
    if len(rows) >= SEARCH_RESULT_CAP:
        if until - since <= timedelta(days=1):
            raise RuntimeError(
                f"merge-time slice {since.isoformat()} returned "
                f"{len(rows)} PRs at GitHub's {SEARCH_RESULT_CAP}-result cap"
            )
        middle = since + (until - since) // 2
        return _merged_pr_slice(repo, since, middle) + _merged_pr_slice(
            repo, middle, until
        )
    return rows


def list_merged_prs(repo: str, limit: int) -> list[MergedPullRequest]:
    """Return the most recently merged PRs, ordered by ``mergedAt``.

    ``gh pr list --state merged --limit N`` is ordered by creation time, not
    merge time. Walk backwards through bounded merge-time slices until enough
    unique rows are available, then sort and trim locally.
    """
    end = datetime.now(UTC).date() + timedelta(days=1)
    seen: dict[int, MergedPullRequest] = {}
    days_looked_back = 0
    while len(seen) < limit and days_looked_back < MAX_LOOKBACK_DAYS:
        start = end - timedelta(days=MERGED_SLICE_DAYS)
        for row in _merged_pr_slice(repo, start, end):
            pr = MergedPullRequest.from_gh_dict(row)
            seen[pr.number] = pr
        end = start
        days_looked_back += MERGED_SLICE_DAYS

    return sorted(
        seen.values(),
        key=lambda pr: (pr.merged_at, pr.number),
        reverse=True,
    )[:limit]


def _cli(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=None)
    parser.add_argument(
        "--pr-limit",
        type=int,
        default=800,
        help="number of recent merged PRs to examine (default: 800)",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="indent JSON output for human inspection",
    )
    args = parser.parse_args(argv)
    if args.pr_limit <= 0:
        parser.error("--pr-limit must be positive")

    repo = args.repo or _default_repo()
    try:
        epics = list_open_epics(repo)
        merged_prs = list_merged_prs(repo, args.pr_limit)
    except (RuntimeError, json.JSONDecodeError) as exc:
        print(f"epic_body_staleness: {exc}", file=sys.stderr)
        return 1

    json.dump(
        build_payload(epics, merged_prs),
        sys.stdout,
        ensure_ascii=False,
        indent=2 if args.pretty else None,
    )
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(_cli())
