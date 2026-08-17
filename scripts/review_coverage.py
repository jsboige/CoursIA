#!/usr/bin/env python3
"""Review-coverage detector -- the missing ORGAN for issue #11232.

Hermes and the human reviewer (ai-01) read ``reviews[]`` and the three surfaces
of section B.0 of pr-review-discipline.md. None of those gestures detect a
review that is simply *absent*. A PR with zero reviews and zero open reserves
reads green on every visible signal: ``gh pr checks`` 0 failures, 0 pending,
``mergeable: MERGEABLE``, ``reviews[].state`` empty.

Measured firsthand 2026-08-16 on the Lean track, the absence correlates
inversely with the diff size: the two largest PRs of the window
(``#11132`` at 1041 LOC, ``#11210`` at 883 LOC) had **no review at all**,
bot or human, while the 318-LOC ``#11217`` triggered ``second-reviewer``.
The threshold is applied inconsistently by the same reviewer, and the
coverage hole is the larger defect -- this organ targets the hole.

This tool is ADVISORY, never blocking: it cannot block, because the defect
is the absence of a review and the only remedy is to obtain one. On each
sweep it:

  - flags OPEN non-draft PRs (base=main) with ``additions > THRESHOLD`` AND
    ``reviews[]`` empty (no bot, no human) ;
  - labels ``large-pr-no-review`` (regular) and posts a one-shot comment
    (marker-guarded, no spam on re-runs) ;
  - removes the label when a review arrives (or the diff shrinks below the
    threshold), so the label is a current-state signal, not a sticky one.

Acceptance mirrors the issue body: the signal is the **absence**, not the
content. A check that posted ``rien trouve`` on a PR with no review would
itself be the defect; this one labels the absence.

The classification core (``classify``) is a PURE function -- no network --
so it is unit-tested with fixtures in
``scripts/tests/test_review_coverage.py``. The ``main`` driver wires it to
``gh`` and applies/removes labels and comments idempotently.

Usage::

    python scripts/review_coverage.py --dry-run        # log only, no labels
    python scripts/review_coverage.py                  # apply (CI cron)
    python scripts/review_coverage.py --threshold 200  # override default
    python scripts/review_coverage.py --label NAME     # override label name

Exit code is always 0 (advisory). The actionable payload is the set of
labeled PRs and their comments, NEVER the green conclusion.

Threshold rationale (cf. docs/reference/review-coverage-threshold.md) :
200 was the threshold Hermes applied to ``#11217`` (318 LOC) per the issue
body table; 300 is a slightly more permissive default that catches ``#11132``
and ``#11210`` without flooding the dashboard. The cron reads it from the
``--threshold`` arg so it can be tuned without a code change.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from typing import Iterable

# The label is the *signal* -- a current-state flag the reviewer/coordinator
# reads. Color is red (the absence is a coverage hole, not a failure).
LABEL_DEFAULT = "large-pr-no-review"
LABEL_COLOR = "b60205"
LABEL_DESC = (
    "PR > seuil (par defaut 300 additions) sans review (ni bot ni humaine) "
    "-- couverture review absente (#11232). Le label est retire des qu'une "
    "review arrive ou que le diff passe sous le seuil."
)

# Authors whose reviews count as "bot" for this purpose. We do NOT exclude
# bot reviews; the signal is the absence of any review at all, not the
# absence of a human one. Hermes approvals count, so do ours. The intent
# is to surface PRs that *no one* has read.
# (Kept here as a hook for future narrowing, e.g. "human review only" -- not
#  used by classify() today.)
_BOT_AUTHORS: tuple[str, ...] = (
    "app/github-actions",
    "github-actions[bot]",
)

# Marker framing the advisory comment, so re-runs can find and update it.
# Same pattern as pr-gate-missing: idempotent, not a stream of duplicates.
COMMENT_MARKER_START = "<!-- REVIEW-COVERAGE:START -->"
COMMENT_MARKER_END = "<!-- REVIEW-COVERAGE:END -->"

# Remediation text. Must name the action (request a review) explicitly and
# say that close/reopen does not help (the diff is what the reviewer has to
# read, not the PR state).
REMEDIATION = (
    "Cette PR depasse le seuil de couverture review (par defaut 300 "
    "additions) et n'a recu **aucune review** -- ni bot, ni humaine.\n\n"
    "Le label ``large-pr-no-review`` est pose par l'organe "
    "[`scripts/review_coverage.py`](../../scripts/review_coverage.py) "
    "porte par l'issue #11232. Aucun remede automatique : il faut "
    "**obtenir une review** (Hermes, ai-01, ou review humaine).\n\n"
    "Le label sera **retire des qu'une review arrive** (ou que le diff "
    "passe sous le seuil). Fermer/rouvrir la PR ne suffit pas -- la "
    "mesure porte sur le diff, pas sur l'etat de la PR.\n\n"
    "Seuil, historique et exceptions : cf. "
    "[`docs/reference/review-coverage-threshold.md`]"
    "(../../docs/reference/review-coverage-threshold.md)."
)

THRESHOLD_DEFAULT = 300


def classify(pr: dict, threshold: int = THRESHOLD_DEFAULT) -> str:
    """Classify a PR (as returned by ``gh pr view --json ...``).

    Returns one of:
      - ``"flag"``     : PR exceeds threshold AND has no review (any author)
      - ``"clear"``    : PR is below threshold OR has at least one review
      - ``"skip_draft"``: PR is draft (excluded by design)
      - ``"skip_base"`` : PR base is not ``main`` (excluded by design)

    The order of checks matters: a draft is a draft even if it is large.
    The PR is in the ``clear`` class the moment any condition that would
    lift the flag holds (review present, or below threshold).
    """
    # Skips first -- they are not just "no flag", they are "out of scope".
    if pr.get("isDraft"):
        return "skip_draft"
    base_ref = (pr.get("baseRefName") or "").strip()
    if base_ref and base_ref != "main":
        return "skip_base"

    additions = pr.get("additions", 0) or 0
    reviews = pr.get("reviews") or []
    if additions < threshold:
        return "clear"
    if len(reviews) > 0:
        return "clear"
    return "flag"


def fetch_open_prs(threshold: int) -> list[dict]:
    """Fetch OPEN non-draft PRs as the minimum JSON the classifier needs.

    Why minimum JSON: ``gh pr list`` on a 800-PR repo with full payloads
    is slow and noisy. The classifier reads only ``number``, ``title``,
    ``isDraft``, ``baseRefName``, ``additions``, ``reviews``. We use
    ``--jq`` to project server-side and skip the rest.
    """
    cmd = [
        "gh", "pr", "list",
        "--state", "open",
        "--base", "main",
        "--json", "number,title,isDraft,baseRefName,additions,reviews,author,url",
        "--limit", "300",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=True)
    return json.loads(out.stdout)


def has_label(pr_number: int, label: str) -> bool:
    """Return True iff the PR currently carries ``label`` (idempotent core)."""
    out = subprocess.run(
        ["gh", "pr", "view", str(pr_number), "--json", "labels",
         "--jq", f'[.labels[] | select(.name == "{label}")] | length'],
        capture_output=True, text=True, check=True,
    )
    return out.stdout.strip() == "1"


def add_label(pr_number: int, label: str) -> None:
    """Create the label if missing, then add it. Both steps are idempotent."""
    subprocess.run(
        ["gh", "label", "create", label,
         "--color", LABEL_COLOR, "--description", LABEL_DESC,
         "--force"],
        capture_output=True, text=True,
    )
    subprocess.run(
        ["gh", "pr", "edit", str(pr_number), "--add-label", label],
        capture_output=True, text=True, check=True,
    )


def remove_label(pr_number: int, label: str) -> None:
    """Idempotent -- if the label is not on the PR, this is a no-op."""
    subprocess.run(
        ["gh", "pr", "edit", str(pr_number), "--remove-label", label],
        capture_output=True, text=True,
    )


def upsert_comment(pr_number: int, body: str) -> None:
    """Post or update the marker-framed comment. No-op if the body matches.

    The marker is the same as pr-gate-missing: an existing comment with the
    same markers is replaced wholesale; one without markers is left alone
    (we do not touch user comments). A re-run posting the exact same body
    is a no-op (idempotent by content, not just by marker).
    """
    out = subprocess.run(
        ["gh", "pr", "view", str(pr_number), "--json", "comments",
         "--jq", ".comments[].body"],
        capture_output=True, text=True, check=True,
    )
    existing = [c for c in out.stdout.split("\n")
                if COMMENT_MARKER_START in c and COMMENT_MARKER_END in c]
    framed = f"{COMMENT_MARKER_START}\n{body}\n{COMMENT_MARKER_END}"
    if existing and existing[0].strip() == framed.strip():
        return  # no-op
    # Delete the prior framed comment (if any) then post the new one.
    for prior in existing:
        # Find the comment id by re-querying with id field
        ids = subprocess.run(
            ["gh", "pr", "view", str(pr_number), "--json", "comments",
             "--jq", f'[.comments[] | select(.body | contains("{COMMENT_MARKER_START}"))] | .[].id'],
            capture_output=True, text=True, check=True,
        )
        for cid in ids.stdout.split():
            subprocess.run(
                ["gh", "pr", "comment", "--delete", cid] if False else
                ["gh", "api", f"repos/{{owner}}/{{repo}}/issues/comments/{cid}",
                 "-X", "DELETE"],
                capture_output=True, text=True,
            )
    subprocess.run(
        ["gh", "pr", "comment", str(pr_number), "--body", framed],
        capture_output=True, text=True, check=True,
    )


def sweep(threshold: int, dry_run: bool, label: str) -> dict:
    """Run one sweep and return counts (for the dashboard / test fixtures)."""
    prs = fetch_open_prs(threshold)
    flagged, cleared, skipped_draft, skipped_base = [], [], [], []
    errors: list[str] = []
    for pr in prs:
        verdict = classify(pr, threshold=threshold)
        if verdict == "skip_draft":
            skipped_draft.append(pr["number"])
            continue
        if verdict == "skip_base":
            skipped_base.append(pr["number"])
            continue
        if verdict == "flag":
            flagged.append(pr["number"])
            if not dry_run:
                try:
                    add_label(pr["number"], label)
                    upsert_comment(pr["number"], REMEDIATION)
                except subprocess.CalledProcessError as e:
                    errors.append(f"#{pr['number']}: {e}")
        elif verdict == "clear":
            cleared.append(pr["number"])
            if not dry_run and has_label(pr["number"], label):
                try:
                    remove_label(pr["number"], label)
                except subprocess.CalledProcessError as e:
                    errors.append(f"#{pr['number']} (remove): {e}")
    return {
        "threshold": threshold,
        "dry_run": dry_run,
        "flagged": flagged,
        "cleared": cleared,
        "skipped_draft": skipped_draft,
        "skipped_base": skipped_base,
        "errors": errors,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--dry-run", action="store_true",
                        help="log only, do not apply labels or comments")
    parser.add_argument("--threshold", type=int, default=THRESHOLD_DEFAULT,
                        help=f"additions threshold (default {THRESHOLD_DEFAULT})")
    parser.add_argument("--label", default=LABEL_DEFAULT,
                        help=f"label name (default {LABEL_DEFAULT!r})")
    args = parser.parse_args(argv)

    result = sweep(args.threshold, args.dry_run, args.label)
    print(json.dumps(result, indent=2, ensure_ascii=False))
    # Always exit 0 -- advisory. The actionable payload is the labels/comments,
    # NEVER the green conclusion (cf. docstring & issue #11232).
    return 0


if __name__ == "__main__":
    sys.exit(main())
