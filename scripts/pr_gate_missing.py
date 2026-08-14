#!/usr/bin/env python3
"""PR-gate-absent detector -- the missing ORGAN for issue #10928.

The required check ``PR gate`` (scripts/pr_gate.py, workflow pr-gate.yml) is the
single status check that main's branch protection requires. When it is absent
from a PR's status-check rollup -- never reported, not red -- the PR is
``BLOCKED`` while *every* visible signal reads green: ``gh pr checks`` shows 0
failures, 0 pending, ``mergeable: MERGEABLE``. A required context that is never
reported blocks without displaying anything.

Three distinct causes were measured firsthand on 2026-08-14 (issue #10928):

  - #10898 : the head commit's SUBJECT contained the literal ``[skip ci]`` --
    GitHub skipped every ``pull_request`` workflow (only CodeQL ran). Fixed by a
    re-push whose message does not carry the token.
  - #10558 : PR opened by the bot (``app/github-actions``). A push made with
    ``GITHUB_TOKEN`` does not create a new workflow run (GitHub anti-recursion)
    -- structural, by design, but nowhere written.
  - #10902 : unknown cause; the PR was ``DIRTY`` and its rebase re-triggered CI.

This tool is an ADVISORY organ, never blocking (it cannot block: the missing
context IS the blocker). On each sweep it:

  - flags OPEN non-draft PRs whose rollup has NO ``PR gate`` check-run, and
  - labels ``pr-gate-missing`` (regular) / ``pr-gate-missing-bot`` (bot PRs),
    and posts a remediation comment once (marker-guarded, no spam on re-runs).

PRs whose ``PR gate`` is present but queued/in_progress are NOT flagged:
presence is the signal, conclusion is not (acceptance #1 -- a young PR has the
check-run with no conclusion yet, which is normal).

The classification core (``classify``) is a PURE function -- no network -- so it
is unit-tested with fixtures in ``scripts/tests/test_pr_gate_missing.py``. The
``main`` driver wires it to ``gh`` and applies/removes labels and comments
idempotently.

Usage::

    python scripts/pr_gate_missing.py --dry-run        # log only, no labels
    python scripts/pr_gate_missing.py                  # apply (CI cron)
    python scripts/pr_gate_missing.py --label NAME     # override label name

Exit code is always 0 (advisory). The actionable payload is the set of labeled
PRs and their comments, NEVER the green conclusion.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from typing import Iterable

LABEL_DEFAULT = "pr-gate-missing"
LABEL_BOT_DEFAULT = "pr-gate-missing-bot"
LABEL_COLOR = "b60205"  # red -- "invisible required-context blocker, needs a push"
LABEL_BOT_COLOR = "d93f0b"  # orange -- "structural bot case (GITHUB_TOKEN anti-recursion)"
LABEL_DESC = ("PR gate absent du rollup: contexte requis jamais rapporte -- "
              "PR verrouillee malgre des checks verts (#10928)")
LABEL_BOT_DESC = ("PR du bot sans PR gate: structural (push GITHUB_TOKEN ne cree "
                  "pas de workflow run) -- merge admin ou push humain (#10928)")

# The exact check-run name posted by pr_gate.py --self-name "PR gate" and
# required by main's branch protection. Renaming here silently detaches the
# detector (same invariant as pr-gate.yml: keep the string stable).
GATE_NAME = "PR gate"
BOT_LOGIN = "app/github-actions"

# Marker framing the advisory comment, so re-runs can find and update it.
COMMENT_MARKER_START = "<!-- PR-GATE-MISSING:START -->"
COMMENT_MARKER_END = "<!-- PR-GATE-MISSING:END -->"

# The remediation text must name the push as the remedy and say explicitly that
# close/reopen does not suffice (measured on #10898: `reopened` re-ran nothing;
# only a `synchronize` push restarts pull_request workflows).
REMEDIATION = (
    "`PR gate` est absent du rollup de cette PR : elle est bloquee par un "
    "contexte requis qui n'a jamais ete rapporte, malgre des checks verts "
    "(issue #10928).\n\n"
    "- Verifier d'abord si le message du head commit contient le token "
    "`[skip ci]` (le retirer suffit a le declencher).\n"
    "- Remede : **un nouveau push** (`git merge origin/main` puis push, ou tout "
    "commit dont le message ne porte pas le token).\n"
    "- `close` / `reopen` **ne relance rien** : seul un evenement `synchronize` "
    "refait partir les workflows `pull_request`."
)

REMEDIATION_BOT = (
    "PR ouverte par le bot (`app/github-actions`) sans `PR gate` dans son "
    "rollup : cas **structurel** (issue #10928). Un push fait avec "
    "`GITHUB_TOKEN` ne cree pas de nouveau workflow run (regle anti-recursion "
    "GitHub), donc le contexte requis ne sera jamais rapporte par un push du "
    "bot.\n\n"
    "- Remede : un **push humain** sur la branche (commit par un compte "
    "personnel), ou un **merge admin** via `gh auth switch -u jsboige`.\n"
    "- `close` / `reopen` ne relance rien."
)


def rollup_names(pr: dict) -> list[str]:
    """Check-run names / status contexts present in the PR's rollup.

    ``statusCheckRollup`` entries are either check-runs (carry ``name``) or
    status contexts (carry ``context``). Presence -- regardless of conclusion --
    is what matters: a queued/in_progress ``PR gate`` is not a defect.
    """
    names = []
    for entry in (pr.get("statusCheckRollup") or []):
        name = entry.get("name") or entry.get("context")
        if name:
            names.append(name)
    return names


def classify(pr: dict) -> tuple[str, str]:
    """Classify one open PR against its status-check rollup.

    Args:
        pr: ``{"number", "base_ref_name", "is_draft", "author_login",
               "statusCheckRollup": [...]}``

    Returns:
        ``(verdict, detail)`` where verdict is one of:
        ``"excluded_base"`` -- base branch != main: ``pr-gate.yml`` only fires on
            ``pull_request: branches: [main]``, so the check never appears here
            by design (false positive if flagged)
        ``"draft"``         -- draft PR: not mergeable yet, flagging is noise
        ``"has_gate"``      -- ``PR gate`` present (any conclusion) -- not a defect
        ``"bot_missing"``   -- bot PR, no ``PR gate`` (structural GITHUB_TOKEN case)
        ``"missing"``       -- the defect: no ``PR gate``, non-bot, non-draft
    """
    number = pr.get("number")
    if pr.get("base_ref_name") and pr["base_ref_name"] != "main":
        return ("excluded_base", f"#{number} base={pr['base_ref_name']} (pr-gate.yml ne tire que sur main)")
    if pr.get("is_draft"):
        return ("draft", f"#{number} draft PR, non mergeable")
    if GATE_NAME in rollup_names(pr):
        return ("has_gate", f"#{number} PR gate present (conclusion: {len(rollup_names(pr))} checks)")
    if pr.get("author_login") == BOT_LOGIN:
        return ("bot_missing", f"#{number} bot PR, no PR gate (structural)")
    return ("missing", f"#{number} PR gate absent du rollup")


# ---------------------------------------------------------------------------
# gh wiring
# ---------------------------------------------------------------------------

def _gh_json(args: list[str]) -> object:
    """Run a gh command, return parsed JSON (or None if empty). Raise on failure."""
    proc = subprocess.run(
        ["gh", *args],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )
    if proc.returncode != 0:
        raise RuntimeError(f"gh failed ({proc.returncode}): {proc.stderr.strip() or proc.stdout.strip()}")
    if not proc.stdout.strip():
        return None
    return json.loads(proc.stdout)


def list_open_prs(repo: str) -> list[dict]:
    """Open PRs with the fields classify() needs, plus the rollup."""
    return list(_gh_json([  # type: ignore[return-value]
        "pr", "list", "--repo", repo, "--state", "open", "--limit", "200",
        "--json", "number,baseRefName,isDraft,author,statusCheckRollup",
    ]))


def ensure_label(repo: str, name: str, color: str, desc: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "label", "create", name, "--repo", repo,
         "--color", color, "--description", desc, "--force"],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def has_label(pr: dict, name: str) -> bool:
    return any((lab.get("name") == name) for lab in (pr.get("labels") or []))


def apply_label(repo: str, number: int, name: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "pr", "edit", str(number), "--repo", repo, "--add-label", name],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def remove_label(repo: str, number: int, name: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "pr", "edit", str(number), "--repo", repo, "--remove-label", name],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def existing_comment(repo: str, number: int) -> int | None:
    """Return the id of an existing PR-gate-missing comment, or None."""
    comments = _gh_json(["pr", "view", str(number), "--repo", repo,
                         "--json", "comments"]) or {}
    for c in (comments.get("comments") or []):
        if COMMENT_MARKER_START in (c.get("body") or ""):
            return c["id"]
    return None


def post_comment(repo: str, number: int, body: str, dry_run: bool) -> None:
    if dry_run:
        return
    subprocess.run(
        ["gh", "pr", "comment", str(number), "--repo", repo, "--body", body],
        capture_output=True, text=True, check=False, encoding="utf-8",
    )


def labeled_prs(repo: str, label: str) -> dict[int, bool]:
    """Map PR number -> has-label for all open PRs carrying ``label``.

    Needed so a PR that regains its ``PR gate`` (re-push) gets the label
    retracted idempotently. ``gh pr list`` can filter by label, one query per
    label is enough.
    """
    raw = _gh_json([
        "pr", "list", "--repo", repo, "--state", "open", "--limit", "200",
        "--label", label, "--json", "number,labels",
    ]) or []
    return {pr["number"]: True for pr in raw}


# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--dry-run", action="store_true", help="log classifications, apply no labels/comments")
    ap.add_argument("--repo", default=None, help="repo (default: gh default / GITHUB_REPOSITORY)")
    ap.add_argument("--label", default=LABEL_DEFAULT, help=f"regular label name (default: {LABEL_DEFAULT})")
    ap.add_argument("--label-bot", default=LABEL_BOT_DEFAULT, help=f"bot label name (default: {LABEL_BOT_DEFAULT})")
    ap.add_argument("--limit", type=int, default=0, help="cap PRs processed (0 = all)")
    args = ap.parse_args(argv)

    repo = args.repo or (subprocess.run(
        ["gh", "repo", "view", "--json", "nameWithOwner", "-q", ".nameWithOwner"],
        capture_output=True, text=True, encoding="utf-8").stdout.strip()
        or "jsboige/CoursIA")

    if not args.dry_run:
        ensure_label(repo, args.label, LABEL_COLOR, LABEL_DESC, args.dry_run)
        ensure_label(repo, args.label_bot, LABEL_BOT_COLOR, LABEL_BOT_DESC, args.dry_run)

    prs = list_open_prs(repo)
    if args.limit:
        prs = prs[: args.limit]

    # Map of PRs currently carrying each label (to retract when the gate returns).
    labeled = labeled_prs(repo, args.label)
    labeled_bot = labeled_prs(repo, args.label_bot)

    counts = {"missing": 0, "bot_missing": 0, "has_gate": 0, "draft": 0, "excluded_base": 0}
    print(f"[pr-gate-missing] repo={repo} mode={'dry-run' if args.dry_run else 'apply'} "
          f"open_prs={len(prs)} label={args.label}")

    for pr in prs:
        number = pr["number"]
        enriched = {
            "number": number,
            "base_ref_name": pr.get("baseRefName"),
            "is_draft": pr.get("isDraft", False),
            "author_login": (pr.get("author") or {}).get("login", ""),
            "statusCheckRollup": pr.get("statusCheckRollup") or [],
            "labels": (pr.get("labels") or []),
        }
        verdict, why = classify(enriched)
        counts[verdict] = counts.get(verdict, 0) + 1

        if verdict == "missing":
            if not has_label(enriched, args.label):
                apply_label(repo, number, args.label, args.dry_run)
            if not args.dry_run and existing_comment(repo, number) is None:
                post_comment(repo, number, _comment_body(REMEDIATION), args.dry_run)
            print(f"  #{number:<6} MISSING    {why}")
        elif verdict == "bot_missing":
            if not has_label(enriched, args.label_bot):
                apply_label(repo, number, args.label_bot, args.dry_run)
            if not args.dry_run and existing_comment(repo, number) is None:
                post_comment(repo, number, _comment_body(REMEDIATION_BOT), args.dry_run)
            print(f"  #{number:<6} BOT        {why}")
        elif verdict == "has_gate":
            # Gate back (re-push): retract labels idempotently. The comment is
            # left as history -- the label retraction is the resolution signal.
            if number in labeled:
                remove_label(repo, number, args.label, args.dry_run)
                print(f"  #{number:<6} has_gate   {why}  (label retracted)")
            if number in labeled_bot:
                remove_label(repo, number, args.label_bot, args.dry_run)
                print(f"  #{number:<6} has_gate   {why}  (bot label retracted)")
        elif verdict == "draft":
            pass  # quiet -- the common non-defect case
        else:  # excluded_base
            pass  # quiet -- PRs targeting a feature branch never see PR gate

    print(f"[pr-gate-missing] done: {counts}")
    return 0


def _comment_body(remediation: str) -> str:
    return "\n".join([
        COMMENT_MARKER_START,
        "## PR gate absent du rollup (advisory, #10928)",
        "",
        remediation,
        COMMENT_MARKER_END,
    ])


if __name__ == "__main__":
    sys.exit(main())
