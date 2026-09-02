#!/usr/bin/env python3
r"""list_orphan_prs.py -- detect PRs whose body carries no `Grain:` tag (#13086).

## Why this exists

Issue #13086 measures, on 2026-08-26T08:20Z: 23 PRs were open, blocked on
`variation-tag-guard > tag_required`, with NO `Grain:` line in their body --
and so invisible to every lane's "repare ton rouge d'abord" sweep (the
proactive-coordination rule selects blocked PRs BY lane, and a body without
`lane <machine:workspace>` belongs to no lane).

The diagnosis was already present in `pick_idle_grain.py`'s footer
("ne sont imputables a aucune lane -- ce garde ne les voit pas"), but the
information reached no actor who could act on it. The sweep reported
`success` while 23 PRs sat unsorted. That is a signal without a recipient
(#13086 calls it "le piege qui se referme").

This script is the **reader** half: it pulls `gh pr list --state open`,
filters out any PR whose body yields a non-None parse from
`scripts/grain_tag.parse_grain_tag`, and prints the remainder. The output is
the input of the recipient half (a dashboard append, a DM to ai-01 with the
unattributed block, or a CI advisory check) -- both routes live in #13086's
acceptance criteria; this PR only ships the reader.

## What it does

  $ python scripts/ci/list_orphan_prs.py
  # PRs missing `Grain:` tag in body
  PR 13062  author=myia-po-2023  branch=feature/13062-...  title=...
  PR 13035  author=myia-po-2023  branch=feature/...        title=...
  ...

  $ python scripts/ci/list_orphan_prs.py --json
  {"orphans": [{"number": 13062, "author": "...", "branch": "...", "title": "..."}, ...],
   "total_scanned": 70, "missing_tag": 23}

  $ python scripts/ci/list_orphan_prs.py --author myia-po-2023
  # filtered to one author

The script NEVER pushes, comments, or closes anything -- it only reads.

## Design rules that matter

1. **Tolerates the canonical form-tolerant reader.** Whether the body carries
   `Grain: ...`, `**Grain:** ...`, or `## Grain\n\n...` (all parsed by
   `grain_tag.parse_grain_tag` per #9485), a PR with any of those forms is
   NOT orphan. A PR with NEITHER is. This matches what
   `variation-tag-required` (the BLOCKING job in `variation-tag-guard.yml`)
   would catch at merge time, so the two readers agree on what "orphan" is.
2. **No silent fallback on `gh` failure.** If `gh pr list` errors (auth,
   network, rate-limit), the script exits 2 with a one-line stderr, never a
   partial JSON. The recipient must be able to trust `total_scanned` against
   `orphans_count`.
3. **Limit is explicit and bounded.** `--limit 200` default is enough to
   scan the full pool in one call; raising it costs only wall-clock on the
   `gh` side. The script does NOT page through `--state all --search` --
   that's the recipient's job (e.g. ai-01's nightly dashboard pull).
4. **No comment-writing.** A future "comment-on-orphan" feature lives
   behind a separate flag and a separate PR (#13086 acceptance note:
   "soit (a) rendre l'omission visible a son auteur au moment ou elle se
   produit" -- that is a CI workflow, not a CLI tool).
5. **Tests pin the behaviour at the function boundary**, not via
   `monkeypatch subprocess.run`. A future refactor that swaps `gh` for the
   REST API will not silently break tests.

## Coupling with #13086 and #12095

This script reads the SAME body the merge-gate reads. A PR that this script
flags will ALSO fail `variation-tag-required` at the gate -- so the reader
is a leading indicator, not a separate source of truth. If the two
disagree, the merge-gate wins (a PR MERGED with no tag is a structural
defect regardless of what this script reports).

## Run locally

    python scripts/ci/list_orphan_prs.py
    python scripts/ci/list_orphan_prs.py --author jsboige
    python scripts/ci/list_orphan_prs.py --limit 50 --json

Exit codes:
  0  -- scan completed (with or without orphans found)
  1  -- caller error (bad args)
  2  -- infrastructure error (`gh` failure, JSON parse)
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

# Make the shared extractor importable when the script is invoked from
# anywhere in the repo (CI runs it from the repo root, but local developers
# may run from the script directory).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402


# Default scan ceiling. The pool rarely exceeds 100 OPEN PRs; 200 leaves
# headroom for episodic spikes (catalog cron open-then-merge) without paging.
DEFAULT_LIMIT = 200


def _run_gh_pr_list(limit: int) -> list[dict]:
    """Run `gh pr list` and return the parsed JSON rows.

    Raises RuntimeError on any non-zero exit / non-JSON output -- the caller
    surfaces this as exit code 2 (infrastructure failure).
    """
    cmd = [
        "gh", "pr", "list",
        "--state", "open",
        "--limit", str(limit),
        "--json", "number,title,author,headRefName,body",
    ]
    # encoding="utf-8", errors="replace" per #12811: `text=True` without
    # encoding= crashes on Windows hosts whose default codec is cp1252 when
    # the JSON payload contains UTF-8 multibyte sequences (the `title` field
    # routinely does).
    proc = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
    if proc.returncode != 0:
        raise RuntimeError(f"`gh pr list` failed (rc={proc.returncode}): {proc.stderr.strip()}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        raise RuntimeError(f"`gh pr list` returned non-JSON: {e}")


def _is_orphan(body: str | None) -> bool:
    """True iff the body has no parseable Grain tag (per `grain_tag`).

    Delegates to the canonical form-tolerant reader (#9485) so this script
    and the merge-gate agree on what "no tag" means.
    """
    if body is None:
        return True
    return gt.parse_grain_tag(body) is None


def find_orphans(prs: list[dict]) -> list[dict]:
    """Return the subset of `prs` whose body has no parseable Grain tag.

    Pure function -- testable without `gh`. Each returned row keeps the
    upstream `number / title / author.login / headRefName` and drops `body`
    (the body is the scan input, not the report output).
    """
    out = []
    for pr in prs:
        if _is_orphan(pr.get("body")):
            out.append({
                "number": pr.get("number"),
                "title": pr.get("title", ""),
                "author": (pr.get("author") or {}).get("login", "<unknown>"),
                "branch": pr.get("headRefName", ""),
            })
    return out


def render_text(orphans: list[dict]) -> str:
    """Human-readable report. Used by default (no --json)."""
    if not orphans:
        return "# no orphan PRs found"
    lines = [f"# {len(orphans)} orphan PR(s) (no `Grain:` tag in body)"]
    for o in orphans:
        lines.append(
            f"PR {o['number']:>6}  author={o['author']:<24}  "
            f"branch={o['branch']:<48}  title={o['title'][:60]}"
        )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    p.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                   help=f"max PRs to scan via `gh pr list` (default: {DEFAULT_LIMIT})")
    p.add_argument("--author", help="filter output to PRs by this GitHub login")
    p.add_argument("--json", action="store_true",
                   help="machine-readable output (one JSON object on stdout)")
    args = p.parse_args(argv)

    if args.limit <= 0:
        print("error: --limit must be > 0", file=sys.stderr)
        return 1

    try:
        prs = _run_gh_pr_list(args.limit)
    except RuntimeError as e:
        print(f"error: {e}", file=sys.stderr)
        return 2

    orphans = find_orphans(prs)

    if args.author:
        orphans = [o for o in orphans if o["author"] == args.author]

    if args.json:
        print(json.dumps({
            "total_scanned": len(prs),
            "missing_tag": len(orphans),
            "orphans": orphans,
        }, ensure_ascii=False))
    else:
        print(render_text(orphans))

    return 0


if __name__ == "__main__":
    sys.exit(main())
