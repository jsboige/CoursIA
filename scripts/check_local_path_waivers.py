#!/usr/bin/env python3
"""Local-path waiver guard -- a comment body that is a path is not a waiver.

#16780 (2026-09-19). On PR #16670, a comment was posted whose ENTIRE body was:

    @C:\\Users\\jsboi\\AppData\\Local\\Temp/a16670.md

-- the visible trace of ``gh ... --body "@$TEMP/a16670.md"`` where
``--body-file`` was meant (``gh`` does not expand ``@file``; it posts the
literal string). Two defects followed, and the second is the real one:

1. A local machine path landed on a PUBLIC, indexed surface.
2. The merge-gate harness READ that body as a DWELL L3 waiver. But the file
   lives on one machine: no reader of the PR (ai-01, a bot, a contributor)
   can open it. The signal carries no verifiable content -- all of its
   meaning lives in the FILENAME. An authorization nobody can re-read is a
    fabricated authorization (B.0: a lift carries an author, an hour, and a
   readable substance on the PR itself).

Convention settled by this guard (issue #16780, work item B): **a waiver by
pointer is forbidden**. If a waiver counts for a merge, its substance is on
the PR -- one sentence saying what is lifted and why. The scratchpad keeps
the detail; the PR carries the decision.

What is flagged (work item A2, exactly as specified):

- LONE_PATH: the trimmed body is entirely a filesystem path, optionally
  ``@``-prefixed (Windows drive letter or unix absolute/home-rooted);
- PROFILE_PATH: the body CONTAINS a Windows profile path segment
  ``[A-Za-z]:[\\/][Uu]sers[\\/]`` anywhere (mixed separators included --
  the incident body itself mixed ``\\`` and ``/``).

Modes:

- ``PR_NUMBER`` (check mode): fetch the PR's issue comments via ``gh`` and
  exit 1 with one line per finding (hand-run before a merge). With
  ``--report-only``: ``::warning`` annotations, exit 0 -- the CI wiring.
- ``--scan-plage START END``: measurement mode (acceptance 3). Enumerates
  repo comments newest-first via the issue-comments listing endpoint,
  keeps those attached to items numbered START..END, reports findings by
  author profile. Exit 0 always -- a measurement is not a verdict. The
  #16670 comment itself was deleted by the user, so the live scan is
  expected to miss it; the POSITIVE CONTROL is the unit test replaying the
  exact incident body (a sweep that does not cover its own positive
  control measures nothing -- issue note).

Arbitrage ai-01 (commentaire issue, 2026-09-19T01:25Z) -- les deux
effets se separent, et les DEUX gardes vivent :

- BLOQUANT, cote organe ``check_unaddressed_nits.py`` : un corps-pointeur
  est INERTE comme levée (``_LONE_PATH_BODY_RE`` dans ``can_lift``) -- c'est
  exactement la question que l'organe repond, et le defaut de #16670 etait
  un vert faux.
- NON BLOQUANT (``--report-only``, le wiring CI) : la FUITE de chemin de
  profil est rendue visible sans faire echouer le gate de la PR victime.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys

REPO = "jsboige/CoursIA"

# Whole trimmed body is a path, optionally @-prefixed (the gh --body "@..."
# accident). Windows drive forms tolerate mixed separators; unix forms are
# anchored on the classic local roots.
LONE_PATH_RE = re.compile(
    r"^@?(?:"
    r"[A-Za-z]:[\\/][^\s]+"  # C:\Users\... or C:/Users/... or C:\...\Temp/x.md
    r"|/(?:tmp|home|Users|var|opt|mnt)/[^\s]+"
    r"|~/[^\s]+"
    r")$"
)

# Windows profile segment anywhere in the body (issue work item A2, verbatim
# rule, [\/] so the incident's mixed separators match).
PROFILE_PATH_RE = re.compile(r"[A-Za-z]:[\\/][Uu]sers[\\/]")


class Finding:
    def __init__(self, kind: str, author: str, created_at: str, url: str, excerpt: str):
        self.kind = kind
        self.author = author
        self.created_at = created_at
        self.url = url
        self.excerpt = excerpt

    def line(self) -> str:
        return (
            f"{self.kind} author={self.author} at={self.created_at} "
            f"url={self.url} body[:90]={self.excerpt[:90]!r}"
        )


def classify_body(body: str) -> list[str]:
    """Pure detector -- returns the list of rule names the body trips ([] = clean).

    Kept side-effect free so tests replay the #16670 incident body offline.
    """
    trimmed = (body or "").strip()
    if not trimmed:
        return []
    kinds = []
    if LONE_PATH_RE.match(trimmed):
        kinds.append("LONE_PATH")
    if PROFILE_PATH_RE.search(trimmed):
        kinds.append("PROFILE_PATH")
    return kinds


def comment_findings(comments: list[dict]) -> list[Finding]:
    out = []
    for c in comments:
        kinds = classify_body(c.get("body", ""))
        for kind in kinds:
            out.append(
                Finding(
                    kind=kind,
                    author=(c.get("author") or {}).get("login", "?"),
                    created_at=c.get("createdAt", "?"),
                    url=c.get("url", "?"),
                    excerpt=(c.get("body") or "").replace("\n", " "),
                )
            )
    return out


# --- gh plumbing --------------------------------------------------------------


def _gh_json(args: list[str]) -> str:
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True,
        text=True,
        shell=False,
        encoding="utf-8",
        errors="replace",
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"gh {' '.join(args[:3])} failed (exit {proc.returncode}): {proc.stderr.strip()}"
        )
    return proc.stdout


def pr_comments(pr_number: int) -> list[dict]:
    payload = _gh_json(["pr", "view", str(pr_number), "--json", "comments"])
    return json.loads(payload).get("comments", [])


def check(pr_number: int, report_only: bool = False) -> int:
    findings = comment_findings(pr_comments(pr_number))
    for f in findings:
        if report_only:
            # Arbitrage ai-01 #16780 : la FUITE est rendue visible mais ne
            # bloque PAS -- le chemin vient d'une commande mal ecrite sur une
            # autre machine ; faire echouer le gate de la PR victime punit
            # l'innocent et n'efface rien. Seule la suppression du commentaire
            # retire le chemin.
            print(f"::warning title=Local path on PR surface::{f.line()}")
        else:
            print(f"::error title=Local path on PR surface::{f.line()}")
        print(f"LOCAL_PATH_WAIVER {f.line()}")
    if findings:
        print(
            f"{'WARN' if report_only else 'FAIL'}: {len(findings)} local-path "
            f"finding(s) on PR #{pr_number}. A comment body that is a path is "
            "not a waiver (#16780): post the substance on the PR instead."
        )
        return 0 if report_only else 1
    print(f"OK: 0 local-path finding(s) on PR #{pr_number} comment surface.")
    return 0


def scan_plage(start: int, end: int) -> int:
    """Enumerate repo issue comments newest-first, keep items START..END.

    Uses the listing endpoint (1 request per 100 comments) instead of one
    request per item: ~500 REST calls would burn shared fleet quota for a
    measurement. Pagination stops once a whole page predates the plage's own
    items (a comment on item N can only exist after item N was created).
    """
    plage_created = json.loads(
        _gh_json(["issue", "view", str(start), "--json", "createdAt"])
    )["createdAt"]
    print(f"# plage #{start}..#{end}; plage opens {plage_created}")
    findings: list[Finding] = []
    covered = 0
    page = 1
    while True:
        raw = _gh_json(
            [
                "api",
                # Query params in the URL: `-f` fields would turn the call
                # into a POST, which this listing endpoint rejects (404).
                f"repos/{REPO}/issues/comments"
                f"?per_page=100&page={page}&sort=created&direction=desc",
            ]
        )
        batch = json.loads(raw)
        if not batch:
            break
        done = True
        for c in batch:
            issue_url = c.get("issue_url", "")
            m = re.search(r"/issues/(\d+)$", issue_url)
            if not m:
                continue
            n = int(m.group(1))
            if start <= n <= end:
                covered += 1
                for kind in classify_body(c.get("body", "")):
                    findings.append(
                        Finding(
                            kind=kind,
                            author=(c.get("user") or {}).get("login", "?"),
                            created_at=c.get("created_at", "?"),
                            url=c.get("html_url", "?"),
                            excerpt=(c.get("body") or "").replace("\n", " "),
                        )
                    )
            # A page entirely older than the plage's opening cannot gain
            # anything by paginating further (comments sort by creation).
            if c.get("created_at", "") >= plage_created:
                done = False
        if done:
            break
        page += 1
    print(f"# comments covered on plage items: {covered}")
    by_author: dict[str, int] = {}
    for f in findings:
        by_author[f.author] = by_author.get(f.author, 0) + 1
        print(f"SCAN_HIT {f.line()}")
    print("# by profile: " + (", ".join(f"{a}={k}" for a, k in sorted(by_author.items())) or "(none)"))
    print(
        "# NOTE: the #16670 incident comment was deleted by the user; the "
        "positive control for this sweep is the unit-test replay of its exact "
        "body (see scripts/tests/test_check_local_path_waivers.py)."
    )
    return 0


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("pr_number", nargs="?", type=int, help="PR to check (check mode)")
    ap.add_argument("--report-only", action="store_true",
                    help="advisory: warn, never fail (arbitration ai-01: the victim PR must not be blocked)")
    ap.add_argument("--scan-plage", nargs=2, type=int, metavar=("START", "END"),
                    help="measurement mode: scan comments of items START..END")
    args = ap.parse_args(argv)
    if args.scan_plage:
        return scan_plage(args.scan_plage[0], args.scan_plage[1])
    if args.pr_number is None:
        ap.error("give a PR number, or --scan-plage START END")
    return check(args.pr_number, report_only=args.report_only)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
