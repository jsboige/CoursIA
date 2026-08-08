#!/usr/bin/env python3
r"""variation_tag_required.py -- the BLOCKING half of variation-tag-guard (#10045).

## Why this exists

Issue #10045 measures that 3/10 PRs of the 2026-08-08 merge cycle were
completely unattributable (no `Grain:` tag) and the only consumer of the
advisory signal was the coordinator at merge-gate, who missed it
(`merge-gate-reads-labels-not-check-states`, replayed in the issue).

The existing `check-variation-tag` job posts labels (advisory, exit 0).
A second job, this one, exits 1 when the tag is absent or the lane is
missing -- making the failure GATE `PR gate` red and the PR non-mergeable
without touching the branch protection settings.

## What it does

Reads a PR body (file or stdin), runs the shared `grain_tag.parse_grain_tag`,
and emits a single verdict on stdout:

    {"required_pass": true|false, "reason": "<one line>", "tier": "...", "genre": "...", "lane": "..."}

Exit codes:
  0  -- body carries a canonical Grain tag AND a lane token
  1  -- body fails one or both checks (missing tag, missing lane, empty body)
  2  -- caller error (no body, unreadable file)

## Design rules that matter

1. **The blocking decision is a one-line guard**: `present AND lane`. Nothing
   else. The advisory job has the full nuance (GENRE offlist, short-header
   trio, malformed TIER) -- this one only blocks the two cases that make the
   grain STRUCTURALLY UNACCOUNTABLE (#9485 -- "incomptable" = a cap that cannot
   be computed).
2. **The check is run by the existing `scripts/grain_tag.py` extractor** (the
   single source of truth, #9485). A separate regex is a divergence waiting
   to happen; if the toleration surface moves (e.g. a new form survives),
   this job inherits the move for free.
3. **No `paths:` filter on the workflow** -- the rule from #10045 + the
   general anti-pattern from `pr-gate.yml` L18-22 (path-filtered workflows
   are `pending forever` on out-of-scope PRs, which makes a required check
   stuck at `pending` and the PR unmergeable).
4. **Forks are excluded** (~95 etudiants, cf. student-pr-reviews.md) --
   the workflow does this before invoking us; we never see a fork body.
5. **Bots are excluded** -- the catalog auto-regen workflow is the only
   `*[bot]` author we get, and that branch has no Grain tag by construction
   (it is generated post-merge of the SAME PR).

## Coupling with #10036

PR #10036 introduces an `is_advisory()` classifier in `scripts/pr_gate.py`
that, when present, RETURNS `advisory=True` for jobs whose name matches a
repo convention like ``/advisory|non[-\s]?blocking|^skip[:\s]|optional/i``
(see PR #10036 verdict logic). This job is named `check-variation-tag-required`
-- the `-required` suffix is the explicit signal that it is NOT advisory.
When #10036 merges, its `is_advisory()` must NOT classify this job as
advisory, otherwise the `exit 1` we emit would be neutralised and the gate
rebuilt via the back door. The PR #10036 acceptance criterion 4 must
explicitly name this exception.

The unit test `test_check_variation_tag_required_block.py` pins the
behaviour we depend on, so any regression in the classification is caught
at review time.

## Why a separate file (not a flag in `grain_tag.py`)

- Single responsibility: `grain_tag.py` reads tag content; this script
  decides whether the tag is REQUIRED to be present. The advisory job
  stays advisory even if this one is removed.
- Workflow YAML stays thin: the bash block calls one Python script. The
  same shape as the existing `check-short-header` job.
- Testability: a CLI with a stdout JSON contract is trivial to assert on.
  Workflow-only logic (paths-filter check, fork exclusion) is YAML and
  relies on the same harness-hygiene review that landed the existing
  three jobs.

## Run locally

    python scripts/ci/variation_tag_required.py --body-file <path>
    echo 'Grain: MED/guard -- lane myia-po-2023:CoursIA-2' | python scripts/ci/variation_tag_required.py
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Make the shared extractor importable when the script is invoked from
# anywhere in the repo (CI runs it from the repo root, but local developers
# may run it from the script directory).
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import grain_tag as gt  # noqa: E402


def check(body: str | None) -> dict:
    """Return the blocking verdict for a PR body.

    See module docstring §2. The signature is preserved as a pure function so
    unit tests can pin each branch without going through the CLI.
    """
    if body is None or body.strip() == "":
        return {
            "required_pass": False,
            "reason": "PR body is empty",
            "tier": None,
            "genre": None,
            "lane": None,
        }

    parsed = gt.parse_grain_tag(body)
    if parsed is None:
        return {
            "required_pass": False,
            "reason": "Grain tag absent (no `Grain: <TIER>/<GENRE>` in body)",
            "tier": None,
            "genre": None,
            "lane": None,
        }

    lane = parsed.get("lane")
    if not lane:
        return {
            "required_pass": False,
            "reason": "Grain tag present but `lane <machine:workspace>` missing",
            "tier": parsed.get("tier"),
            "genre": parsed.get("genre"),
            "lane": None,
        }

    return {
        "required_pass": True,
        "reason": "tag + lane present",
        "tier": parsed.get("tier"),
        "genre": parsed.get("genre"),
        "lane": lane,
    }


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    src = p.add_mutually_exclusive_group(required=True)
    src.add_argument("--body-file", metavar="FILE", help="path to the PR body")
    src.add_argument(
        "--stdin",
        action="store_true",
        help="read the PR body from stdin (terminated by EOF)",
    )
    args = p.parse_args(argv)

    if args.body_file:
        try:
            with open(args.body_file, encoding="utf-8") as f:
                body = f.read()
        except OSError as e:
            print(
                json.dumps(
                    {
                        "required_pass": False,
                        "reason": f"caller error: {e}",
                        "tier": None,
                        "genre": None,
                        "lane": None,
                    }
                ),
                file=sys.stderr,
            )
            return 2
    else:
        body = sys.stdin.read()

    verdict = check(body)
    print(json.dumps(verdict))
    return 0 if verdict["required_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
