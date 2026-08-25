#!/usr/bin/env python3
"""Detect merged PRs whose delivered content never landed on main.

Motivation (#12723)
-------------------
A PR can be ``state: MERGED``, appear in ``gh pr list --state merged``,
satisfy every CI leg -- and its content be **nowhere on main**. It only
takes a merge whose base was a **feature branch** consumed (or not) by
another route. Two pedagogical deliverables sat in that state with no
signal anywhere: not on the PR, not on the origin issue, not on a guard.

The measured loss shapes differ and need different repair gestures:

1. **base consumed before the child** (#12423): the base branch was
   absorbed before the child PR landed on it -- the deliverable sits on
   a branch nobody pulls anymore. Repair: new PR to main from the head
   branch.
2. **base still open** (#12458 at the time): the deliverable lives in
   the diff of the base PR. Repair: rebase the base PR.

Detection is by **path, not ancestry** -- a squash orphans branch SHAs
and would mute any ancestry-based detector. Renames are honored by
**content**: a delivered path absent from main whose blob exists on
main under another path is a rename, not a loss.

This guard SIGNALS (label + comment naming absent paths, the live source
branch, and the repair recipe); it never blocks -- the PR is already
merged, there is nothing left to block. The signal must reach the origin
issue too (parsed from the PR body), because that is what a lane reads
to conclude "delivered".

Usage
-----
::

    python scripts/check_merged_off_main.py                # human report
    python scripts/check_merged_off_main.py --json         # machine
    python scripts/check_merged_off_main.py --post         # comment on
                                                          # flagged PRs +
                                                          # linked issues
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass, field
from typing import Optional

LABEL = "merged-off-main-not-on-main"
DEFAULT_LOOKBACK = 600  # matches the #12723 recensement denominator


def _run(cmd: list[str]) -> Optional[str]:
    """Run a command, return stdout, or None on non-zero/missing tool."""
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, encoding="utf-8",
            errors="replace",
        )
    except OSError:
        return None
    return proc.stdout if proc.returncode == 0 else None


def gh_merged_prs(lookback: int) -> list[dict]:
    """Merged PRs (most recent first) with the fields the guard needs."""
    out = _run([
        "gh", "pr", "list", "--state", "merged", "--limit", str(lookback),
        "--json", "number,baseRefName,headRefName,title,body,mergedAt,files",
        "--repo", "jsboige/CoursIA",
    ])
    if out is None:
        return []
    try:
        return json.loads(out)
    except json.JSONDecodeError:
        return []


def _ref_exists(ref: str) -> bool:
    return _run(["git", "rev-parse", "--verify", "--quiet", ref]) is not None


def _merge_base(a: str, b: str) -> Optional[str]:
    out = _run(["git", "merge-base", a, b])
    return out.strip() if out else None


def _tree_paths(ref: str) -> set[str]:
    out = _run(["git", "ls-tree", "-r", ref, "--name-only"])
    return set(out.splitlines()) if out else set()


def _tree_blob_map(ref: str) -> dict[str, str]:
    """path -> blob sha for a tree-ish ref."""
    out = _run(["git", "ls-tree", "-r", ref])
    if not out:
        return {}
    blobs: dict[str, str] = {}
    for line in out.splitlines():
        # <mode> <type> <sha>\t<path>
        m = re.match(r"^(\d+) (\w+) ([0-9a-f]+)\t(.+)$", line)
        if m and m.group(2) == "blob":
            blobs[m.group(4)] = m.group(3)
    return blobs


@dataclass
class PathVerdict:
    path: str
    status: str  # PRESENT | RENAMED | LOST | BASE-GONE
    landed_at: Optional[str] = None  # new path when RENAMED


@dataclass
class PrVerdict:
    number: int
    title: str
    base: str
    head: str
    merged_at: str
    verdicts: list[PathVerdict] = field(default_factory=list)
    linked_issues: list[int] = field(default_factory=list)

    @property
    def lost(self) -> list[PathVerdict]:
        return [v for v in self.verdicts if v.status == "LOST"]

    @property
    def flagged(self) -> bool:
        return bool(self.lost)


_ISSUE_REF_RE = re.compile(
    r"(?:closes?|fixes?|see|part of|refs?)\s+#(\d+)", re.IGNORECASE
)


def linked_issues_from_body(body: str) -> list[int]:
    """Issue numbers the PR body declares (See/Closes/Fixes/Part of)."""
    return sorted({int(m.group(1)) for m in _ISSUE_REF_RE.finditer(body or "")})


def classify_pr(pr: dict, main_paths: set[str],
                main_blobs: dict[str, str]) -> PrVerdict:
    """Classify one merged PR's added files against main."""
    base, head = pr.get("baseRefName", ""), pr.get("headRefName", "")
    v = PrVerdict(
        number=pr.get("number", 0),
        title=pr.get("title", ""),
        base=base,
        head=head,
        merged_at=pr.get("mergedAt", ""),
        linked_issues=linked_issues_from_body(pr.get("body", "")),
    )
    files = [f for f in (pr.get("files") or [])
             if (f.get("additions") or 0) > 0]
    if not files:
        return v
    base_ref = f"origin/{base}"
    head_ref = f"origin/{head}"
    if not _ref_exists(base_ref) or not _ref_exists(head_ref):
        # Branches are normally kept alive (no --delete-branch, incident
        # #10093). If one is gone we cannot establish added-ness; say so
        # per path rather than guessing (a wrong guess here would either
        # hide a loss or cry wolf).
        for f in files:
            v.verdicts.append(PathVerdict(f["path"], "BASE-GONE"))
        return v
    # Added-ness must be measured against the base state BEFORE this PR's
    # merge. The base branch TIP now contains the merge (that is what
    # merging means), so ls-tree on the tip would see every delivered
    # path as pre-existing and skip it -- the detector would render 0 on
    # a live loss, exactly the zero-of-denominator trap #12723 forbids.
    # merge-base(head, base) is the pre-merge base point (where head
    # diverged), so a path absent there but present on head was created
    # on head's lineage: delivered-new.
    mb = _merge_base(head_ref, base_ref)
    pre_base_paths = _tree_paths(mb) if mb else set()
    head_paths = _tree_paths(head_ref)
    for f in files:
        path = f["path"]
        if path in pre_base_paths:
            continue  # modified-by-PR, not delivered-new
        if path not in head_paths:
            # Head moved on after the merge (or path spelling differs);
            # nothing we can attribute cleanly.
            continue
        if path in main_paths:
            v.verdicts.append(PathVerdict(path, "PRESENT"))
            continue
        blob = _run(["git", "rev-parse", f"{head_ref}:{path}"])
        if blob is None:
            # Present on head per ls-tree but unresolvable: treat as lost
            # content rather than silently dropping the signal.
            v.verdicts.append(PathVerdict(path, "LOST"))
            continue
        blob = blob.strip()
        landed = next(
            (p for p, sha in main_blobs.items() if sha == blob), None
        )
        if landed is not None:
            v.verdicts.append(PathVerdict(path, "RENAMED", landed_at=landed))
        else:
            v.verdicts.append(PathVerdict(path, "LOST"))
    return v


def render_comment(v: PrVerdict) -> str:
    lines = [
        f"[{LABEL}] Ce contenu livre n'est pas sur `main` a ce jour.",
        "",
        f"PR mergee vers `{v.base}` (branche de feature), pas vers `main`."
        " Le merge est reel, mais les chemins suivants n'ont atterri nulle"
        " part sur `main` (verifie par chemin + par contenu, renommements"
        " exclus) :",
        "",
    ]
    for lv in v.lost:
        lines.append(f"- `{lv.path}`")
    lines += [
        "",
        f"La branche source `{v.head}` est toujours vivante : reparation = "
        "nouvelle PR vers `main` depuis cette branche (verifier C.2 avant :"
        " la branche peut preciser des renommages ulterieurs de la serie),"
        " ou cherry-pick si la branche porte d'autres changements.",
        "",
        "Garde automatique (non-bloquant) -- see #12723.",
    ]
    return "\n".join(lines)


def post_signal(v: PrVerdict) -> None:
    body = render_comment(v)
    _run(["gh", "pr", "comment", str(v.number),
          "--repo", "jsboige/CoursIA", "--body", body])
    for issue in v.linked_issues:
        _run([
            "gh", "issue", "comment", str(issue),
            "--repo", "jsboige/CoursIA",
            "--body",
            f"[{LABEL}] La PR #{v.number} ({v.title}) a ete mergee vers "
            f"`{v.base}` et son contenu n'est pas sur `main` -- l'issue ne "
            "peut pas etre conclue livree. Detail sur la PR. See #12723.",
        ])


def scan(lookback: int, post: bool) -> list[PrVerdict]:
    main_paths = _tree_paths("origin/main")
    main_blobs = _tree_blob_map("origin/main")
    flagged: list[PrVerdict] = []
    for pr in gh_merged_prs(lookback):
        if pr.get("baseRefName") == "main":
            continue
        v = classify_pr(pr, main_paths, main_blobs)
        if v.flagged:
            flagged.append(v)
            if post:
                post_signal(v)
    return flagged


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--lookback", type=int, default=DEFAULT_LOOKBACK,
                    help="number of recent merged PRs to scan (default 600)")
    ap.add_argument("--json", action="store_true",
                    help="machine-readable JSON output")
    ap.add_argument("--post", action="store_true",
                    help="comment on flagged PRs and their linked issues")
    args = ap.parse_args(argv)

    flagged = scan(args.lookback, args.post)

    if args.json:
        print(json.dumps({
            "label": LABEL,
            "lookback": args.lookback,
            "flagged_count": len(flagged),
            "flagged": [
                {
                    "number": v.number,
                    "title": v.title,
                    "base": v.base,
                    "head": v.head,
                    "merged_at": v.merged_at,
                    "lost": [lv.path for lv in v.lost],
                    "renamed": [
                        {"from": rv.path, "to": rv.landed_at}
                        for rv in v.verdicts if rv.status == "RENAMED"
                    ],
                    "linked_issues": v.linked_issues,
                }
                for v in flagged
            ],
        }, indent=2, ensure_ascii=False))
        return 0

    if not flagged:
        print(f"OK: no merged-off-main loss among the last {args.lookback} "
              "merged PRs (renames excluded by content).")
        return 0
    print(f"FLAGGED {len(flagged)} merged-off-main PR(s) with content "
          "absent from main:")
    for v in flagged:
        print(f"\n  #{v.number} {v.title}")
        print(f"    merged -> {v.base} on {v.merged_at}; source branch "
              f"{v.head}")
        for lv in v.lost:
            print(f"    LOST    {lv.path}")
        for rv in v.verdicts:
            if rv.status == "RENAMED":
                print(f"    RENAMED {rv.path} -> {rv.landed_at}")
        if v.linked_issues:
            print(f"    linked issues: "
                  + ", ".join(f"#{i}" for i in v.linked_issues))
    print("\nSignal is non-blocking; use --post to comment on the flagged "
          "PRs and their linked issues.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
