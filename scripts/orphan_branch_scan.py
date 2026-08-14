#!/usr/bin/env python3
"""Orphan-branch deliverable scanner -- the missing ORGAN for issue #10918.

A PR merged into a base OTHER than ``main`` delivers its content onto a
branch. If that branch is never wired to main afterwards, the deliverable is
orphaned: it exists, it is executed, it is referenced by a closed issue -- and
no reader ever sees it. Nothing in the harness signals it today.

Measured firsthand on the last 200 merged PRs (2026-08-14, issue #10918): 3
with ``baseRefName != main``, of which 2 orphaned a deliverable:

  - #10770 (base feature/c8266-sendov-theoremes): Lean-20 notebook ABSENT on main
  - #10684 (base fix/gitleaks-pin-8243):      Z3-Python-13 enrichment DIFFERS from main
  - #10791 (base feature/c245-lean17-knots-headers-phase2): content IDENTICAL to main
    (non-ancestor, yet nothing lost) -- must NOT be flagged

Two signals combine into one, and the verdict is on CONTENT IDENTITY, not on
ancestrality: ``git merge-base --is-ancestor <tip> origin/main`` alone produces
false positives (#10791 is a non-ancestor with byte-identical content). The
scan therefore:

  1. lists merged PRs whose base != main (the branches that received a merge);
  2. for each such branch, checks integration (ancestor of main) and the
     existence of an open PR from that branch to main (a legitimate stack);
  3. only when BOTH are negative, diffs the branch against main and reports
     the files whose content is ABSENT or DIFFERS -- SAME files are dropped
     (the #10791 case).

ADVISORY, never blocking (same posture as candidate-delivered-advisory.yml):
the job always exits 0; the actionable payload is the report (comment on the
issue-register), NEVER the green conclusion.

Usage::

    python scripts/orphan_branch_scan.py --dry-run      # log only, no comment
    python scripts/orphan_branch_scan.py                # upsert report (CI)
    python scripts/orphan_branch_scan.py --limit 200    # merged PRs to scan

Exit code is always 0 (advisory).
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from typing import Iterable

REPORT_ISSUE = 10918  # the issue-register where the periodic report is upserted
MARKER_START = "<!-- ORPHAN-BRANCH-SCAN:START -->"
MARKER_END = "<!-- ORPHAN-BRANCH-SCAN:END -->"

# A file whose branch content is byte-identical to main is NOT a lost
# deliverable (the #10791 case) -- only ABSENT / DIFF count.
STATUS_SAME, STATUS_DIFF, STATUS_ABSENT = "SAME", "DIFF", "ABSENT"


def classify_branch(
    branch: str,
    *,
    exists: bool,
    is_ancestor_of_main: bool,
    open_prs_to_main: int,
    content: list[dict],
) -> tuple[str, str]:
    """Classify one base!=main branch that received a merged PR.

    Args:
        branch: the branch name (base of the merged PR).
        exists: does the branch still exist on the remote?
        is_ancestor_of_main: is ``refs/heads/<branch>`` an ancestor of main?
        open_prs_to_main: open PRs from this branch towards main.
        content: ``[{"path": str, "status": STATUS_*}...]`` -- the branch-vs-main
                 content diff (SAME entries pre-filtered or kept, see caller).

    Returns:
        ``(verdict, detail)`` where verdict is one of:
        ``"gone"``      -- branch deleted after merge (content may live in the
            squash commit already merged, or be lost -- unverifiable)
        ``"integrated"``-- branch is an ancestor of main: content is on main
        ``"stacked"``   -- an open PR from this branch to main exists: a
            legitimate stack, the deliverable is in flight
        ``"orphan"``    -- the defect: not integrated, no open PR, and content
            ABSENT or DIFFERS from main
        ``"same"``      -- not integrated, no open PR, but content is
            byte-identical to main (the #10791 false-positive trap)
    """
    if not exists:
        return ("gone", f"{branch}: branche supprimee apres merge")
    if is_ancestor_of_main:
        return ("integrated", f"{branch}: ancetre de main, contenu integre")
    if open_prs_to_main > 0:
        return ("stacked", f"{branch}: {open_prs_to_main} PR(s) ouverte(s) vers main (stack)")
    lost = [c for c in content if c["status"] in (STATUS_DIFF, STATUS_ABSENT)]
    if not lost:
        return ("same", f"{branch}: contenu byte-identique a main (#10791)")
    return ("orphan", f"{branch}: {len(lost)} fichier(s) absent(s)/divergent(s) de main")


# ---------------------------------------------------------------------------
# gh / git wiring
# ---------------------------------------------------------------------------

def _run(cmd: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, check=False, encoding="utf-8")


def _gh_json(args: list[str]) -> object:
    """Run a gh command, return parsed JSON (or None if empty). Raise on failure."""
    proc = _run(["gh", *args])
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def merged_nonmain_bases(repo: str, limit: int) -> list[str]:
    """Unique base branches of the `limit` most recent merged PRs (base != main).

    Paginates `pulls?state=closed&sort=updated&direction=desc` and stops once
    `limit` merged PRs have been seen (the branch list is then bounded).
    """
    bases: list[str] = []
    seen_merged = 0
    page = 1
    while seen_merged < limit and page <= 20:  # hard ceiling against runaway
        data = _gh_json([
            "api",
            f"repos/{repo}/pulls?state=closed&sort=updated&direction=desc"
            f"&per_page=100&page={page}",
        ]) or []
        if not data:
            break
        merged = [pr for pr in data if pr.get("merged_at")]
        seen_merged += len(merged)
        for pr in merged:
            base = (pr.get("base") or {}).get("ref") or ""
            if base and base != "main" and base not in bases:
                bases.append(base)
        if len(data) < 100:
            break
        page += 1
    return bases


def remote_branches(repo: str) -> dict[str, str]:
    """Map branch name -> tip SHA for all remote heads (ls-remote)."""
    proc = _run(["git", "ls-remote", "--heads", f"https://github.com/{repo}.git"])
    out: dict[str, str] = {}
    if proc.returncode == 0:
        for line in proc.stdout.splitlines():
            sha, ref = line.split("\t", 1)
            if ref.startswith("refs/heads/"):
                out[ref[len("refs/heads/"):]] = sha
    return out


def open_prs_towards_main(repo: str, branch: str) -> int:
    """Open PRs from ``branch`` towards main (the stack signal)."""
    data = _gh_json([
        "pr", "list", "--repo", repo, "--state", "open",
        "--search", f'head:"{branch}"',
        "--json", "number,baseRefName",
    ]) or []
    return sum(1 for pr in data if (pr.get("baseRefName") == "main"))


def is_ancestor_of_main(branch_tip: str, main_ref: str = "origin/main") -> bool:
    proc = _run(["git", "merge-base", "--is-ancestor", branch_tip, main_ref])
    return proc.returncode == 0


def content_diff(branch: str, branch_tip: str, main_ref: str = "origin/main") -> list[dict]:
    """Per-file content verdict: branch vs main, via the merge-base diff.

    For each file the branch changed since its merge-base with main, compare the
    branch blob against the main blob: SAME (byte-identical, drop), DIFF
    (different content), ABSENT (does not exist on main). Files not in the
    branch's own diff (main-only changes) are not reported.
    """
    result: list[dict] = []
    mb = _run(["git", "merge-base", main_ref, branch_tip]).stdout.strip()
    if not mb:
        return result
    files = _run(["git", "diff", "--name-status", mb, branch_tip]).stdout.splitlines()
    for line in files:
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        path = parts[-1]
        if not _run(["git", "cat-file", "-e", f"{branch_tip}:{path}"]).returncode == 0:
            # Deleted on the branch (D) -- content was there, now absent. A
            # deletion vs main that is not on main is still a divergence.
            status = STATUS_ABSENT
        elif not _run(["git", "cat-file", "-e", f"{main_ref}:{path}"]).returncode == 0:
            status = STATUS_ABSENT
        elif _run(["git", "diff", "--quiet", main_ref, branch_tip, "--", path]).returncode == 0:
            status = STATUS_SAME
        else:
            status = STATUS_DIFF
        result.append({"path": path, "status": status})
    return result


# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dry-run", action="store_true", help="log classifications, post no comment")
    ap.add_argument("--repo", default=None, help="repo (default: gh default / GITHUB_REPOSITORY)")
    ap.add_argument("--limit", type=int, default=200, help="merged PRs to scan (0 = no cap)")
    ap.add_argument("--main-ref", default="origin/main", help="local main ref (CI checks out full)")
    args = ap.parse_args(argv)

    repo = args.repo or (subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True, encoding="utf-8").stdout.strip()
        or "jsboige/CoursIA")

    branches = merged_nonmain_bases(repo, args.limit)
    tips = remote_branches(repo)

    counts = {"orphan": 0, "same": 0, "integrated": 0, "stacked": 0, "gone": 0, "unknown": 0}
    reports: list[dict] = []
    print(f"[orphan-branch-scan] repo={repo} mode={'dry-run' if args.dry_run else 'apply'} "
          f"branches={len(branches)} limit={args.limit}")

    for branch in branches:
        tip = tips.get(branch)
        if not tip:
            counts["gone"] += 1
            print(f"  {branch:<55} GONE     branche absente du remote")
            continue
        ancestor = is_ancestor_of_main(tip, args.main_ref)
        open_prs = open_prs_towards_main(repo, branch)
        content = content_diff(branch, tip, args.main_ref) if not ancestor and open_prs == 0 else []
        verdict, why = classify_branch(
            branch, exists=True, is_ancestor_of_main=ancestor,
            open_prs_to_main=open_prs, content=content,
        )
        counts[verdict] = counts.get(verdict, 0) + 1
        if verdict == "orphan":
            lost = [c for c in content if c["status"] != STATUS_SAME]
            reports.append({"branch": branch, "files": lost})
            for c in lost:
                print(f"  {branch:<55} {c['status']:<7} {c['path']}")
        else:
            print(f"  {branch:<55} {verdict.upper():<11} {why}")

    print(f"[orphan-branch-scan] done: {counts}")
    if reports and not args.dry_run:
        _upsert_report(repo, reports)
    return 0


def _upsert_report(repo: str, reports: list[dict]) -> None:
    """Post/update the marker-guarded report on the issue-register (#10918)."""
    lines = [MARKER_START, "## Orphan-branch scan (advisory, #10918)", ""]
    for r in reports:
        lines.append(f"**{r['branch']}**")
        for c in r["files"]:
            lines.append(f"- `{c['status']}` `{c['path']}`")
        lines.append("")
    lines.append(MARKER_END)
    body = "\n".join(lines)

    comments = _gh_json(["issue", "view", str(REPORT_ISSUE), "--repo", repo,
                         "--json", "comments"]) or {}
    for c in (comments.get("comments") or []):
        if MARKER_START in (c.get("body") or ""):
            _run(["gh", "api", f"repos/{repo}/issues/comments/{c['id']}",
                  "-X", "PATCH", "-f", f"body={body}"])
            print(f"[orphan-branch-scan] report updated (comment {c['id']})")
            return
    _run(["gh", "issue", "comment", str(REPORT_ISSUE), "--repo", repo, "--body", body])
    print("[orphan-branch-scan] report posted")


if __name__ == "__main__":
    sys.exit(main())
