#!/usr/bin/env python3
"""Base-not-main PR signaler -- part (a) of issue #10918.

A PR whose base is NOT ``main`` delivers its content onto a branch. If that
branch is never wired to main afterwards, the deliverable is orphaned (see
orphan_branch_scan.py, part (b)). This tool signals the risk AT PR TIME: it
labels the PR ``base-not-main`` and posts an advisory comment telling the
reader whether the base currently has an open PR towards main.

The count of open PRs on the base is what makes the warning useful:

  - 1+ open PR from the base towards main  -> a legitimate stack, the
    deliverable is in flight (comment says so);
  - 0 open PRs                            -> an orphan in formation, nothing
    is scheduled to carry this content to main (comment says so).

ADVISORY, never blocking: label + comment only, exit 0 always. Idempotent:
re-runs (synchronize events) update the marker-guarded comment, never spam.

Usage::

    python scripts/base_not_main.py --pr 10770 --dry-run
    python scripts/base_not_main.py --pr 10770          # apply (CI)

Exit code is always 0 (advisory).
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys

LABEL_NAME = "base-not-main"
LABEL_COLOR = "fbca04"  # yellow -- "targets a non-main base, orphan risk"
LABEL_DESC = "PR dont la base != main : livraison sur branche, risque d'orphelin (#10918)"

MARKER_START = "<!-- BASE-NOT-MAIN:START -->"
MARKER_END = "<!-- BASE-NOT-MAIN:END -->"


def count_open_prs_on_base(repo: str, base: str) -> int:
    """Open PRs whose head is ``base`` and that target ``main`` (the stack)."""
    data = _gh_json([
        "pr", "list", "--repo", repo, "--state", "open",
        "--search", f'head:"{base}" base:main',
        "--json", "number",
    ]) or []
    return len(data)


def build_comment(base: str, open_count: int, title: str) -> str:
    if open_count > 0:
        stack = (
            f"Cette PR ne livre pas sur `main` : son contenu attend le merge de "
            f"`{base}`. **{open_count} PR ouverte(s)** de `{base}` vers `main` "
            f"existe(nt) a cet instant -- c'est un **stack legitime**, le "
            f"contenu est en vol. Verifier au moment du merge que la base est "
            f"effectivement reliee a `main`."
        )
    else:
        stack = (
            f"Cette PR ne livre pas sur `main` : son contenu attend le merge de "
            f"`{base}`. **Aucune PR ouverte** de `{base}` vers `main` a cet "
            f"instant -- si la base n'est jamais mergee, le livrable "
            f"(`{title}`) devient un **orphelin** (personne ne le verra jamais, "
            f"cf. #10918). Remede : ouvrir une PR de `{base}` vers `main`, ou "
            f"rebaser cette PR sur `main`."
        )
    return "\n".join([
        MARKER_START,
        "## Base != main (advisory, #10918)",
        "",
        stack,
        MARKER_END,
    ])


# ---------------------------------------------------------------------------
# gh wiring
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
    proc = subprocess.run(["gh", *args], capture_output=True, text=True,
                          check=False, encoding="utf-8")
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def ensure_label(repo: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "label", "create", LABEL_NAME, "--repo", repo,
         "--color", LABEL_COLOR, "--description", LABEL_DESC, "--force"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def existing_comment(repo: str, number: int) -> int | None:
    comments = _gh_json(["pr", "view", str(number), "--repo", repo,
                         "--json", "comments"]) or {}
    for c in (comments.get("comments") or []):
        if MARKER_START in (c.get("body") or ""):
            return c["id"]
    return None


def update_comment(repo: str, comment_id: int, body: str) -> None:
    subprocess.run(
        ["gh", "api", f"repos/{repo}/issues/comments/{comment_id}",
         "-X", "PATCH", "-f", f"body={body}"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def post_comment(repo: str, number: int, body: str) -> None:
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", repo, "--body", body],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--pr", type=int, required=True, help="PR number to signal")
    ap.add_argument("--dry-run", action="store_true", help="log only, apply nothing")
    ap.add_argument("--repo", default=None, help="repo (default: gh default / GITHUB_REPOSITORY)")
    args = ap.parse_args(argv)

    repo = args.repo or (subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True, encoding="utf-8").stdout.strip()
        or "jsboige/CoursIA")

    pr = _gh_json(["pr", "view", str(args.pr), "--repo", repo,
                   "--json", "baseRefName,title"]) or {}
    base = pr.get("baseRefName", "")
    title = pr.get("title", "")

    if not base or base == "main":
        print(f"[base-not-main] #{args.pr} base={base or '?'} -- pas un defaut, rien a faire")
        return 0

    open_count = count_open_prs_on_base(repo, base)
    print(f"[base-not-main] #{args.pr} base={base} open_prs_to_main={open_count} "
          f"mode={'dry-run' if args.dry_run else 'apply'}")
    if args.dry_run:
        print(build_comment(base, open_count, title))
        return 0

    ensure_label(repo, False)
    body = build_comment(base, open_count, title)
    cid = existing_comment(repo, args.pr)
    if cid is not None:
        update_comment(repo, cid, body)
        print(f"[base-not-main] comment updated ({cid})")
    else:
        post_comment(repo, args.pr, body)
        print("[base-not-main] comment posted")
    return 0


if __name__ == "__main__":
    sys.exit(main())
