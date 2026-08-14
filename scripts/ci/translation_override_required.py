#!/usr/bin/env python3
r"""translation_override_required.py -- gate logic for the translation-guard
override marker (#10332).

## Why this exists

The ``translation-guard.yml`` workflow guards **derived files** (the CSV
sync files and the ``*_<lang>.ipynb`` rendered notebooks). It rightly fires
when a non-bot author hand-edits those files on a feature branch -- the next
run of ``translation-sync.yml`` would silently overwrite the hand-edit.

But two occurrences the same cycle showed the guard was sometimes bypassed
through admin merges without a structured trace (#10299: 13 ``*_en.ipynb``
hand-rendered by po-2025 because the bot pipeline had been broken for 31
runs; #10304: 2 lines added to ``translations/genai/finetuning.csv`` to repair
#10297). The bypass was indistinguishable from a complacent merge, and the
decision lived only in a PR comment that nothing forced anyone to write.

## The discriminator -- LABEL + COMMENT MARKER, both required

The repair proposes a **structured override** matching the precedent set by
the lane-claim ``[OVERRIDE]`` marker (#10223):

  - A label ``translation-override`` on the PR. The label alone is too easy
    (a single click), so it is **not sufficient** by itself.
  - A comment on the PR bearing the marker ``[TRANSLATION-OVERRIDE] <motif>``
    in its first line. A comment without the label is also insufficient.
  - **Both required** -- the same dual-key pattern that ``[OVERRIDE]``
    + ``lane-claim-conflict`` adjudication uses elsewhere (#10223).
  - When **both** are present, the guard **bypasses** with a structured
    ``::notice title=Translation guard::OVERRIDE — <motif>`` log line. The
    motif is **journalised** in the job summary; the override is **auditable**
    without being **easy**.
  - When either is missing, the guard keeps FAILING -- the cliquet is not
    disarmed. This is criterion 4 of #10332.

## Why a separate script (not inline bash)

The verdict is the same shape as the other CI scripts (``scripts/ci/...``):
JSON on stdout, exit 0/1, the YAML reduces to plumbing. The script is
**injectable** so unit tests pass dict-based fetchers and never touch the
network.

## Run locally

    python scripts/ci/translation_override_required.py \
        --body-file body.txt \
        --pr-number 1234 \
        --labels-file labels.json

The label fetcher calls ``gh pr view --json labels`` (CI). The comment
fetcher calls ``gh api .../issues/<n>/comments``.

Exit codes: 0 pass / 1 fail (override not satisfied).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Callable

# Make shared modules importable from anywhere in the repo.
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

# Marker carried in the FIRST LINE of a PR comment. The line is what the
# override detector greps for: a single-line marker is the irreducible unit
# of an audit decision, mirroring the lane-claim ``[OVERRIDE]`` precedent
# (#10223). Multi-line variants would let the marker hide in a sea of prose
# and break the "single reader / single reducer" discipline.
_MARKER_RE = re.compile(
    r"^\s*\[TRANSLATION-OVERRIDE\]\s+(?P<motif>\S.*)$",
    re.MULTILINE,
)

# Label name on the PR. Matches the wording of #10332's repair.
OVERRIDE_LABEL = "translation-override"


# ---------------------------------------------------------------------------
# Fetchers (default = gh; injectable for tests).
# ---------------------------------------------------------------------------

LabelFetcher = Callable[[int], list[str]]
CommentFetcher = Callable[[int], list[dict]]


def gh_label_fetcher(pr_number: int) -> list[str]:
    """Fetch the label NAMES attached to a PR via the ``gh`` CLI.

    Returns an empty list on any failure (auth, rate-limit, network) -- the
    verdict treats a fetch failure as "label not present" (fail-closed on the
    override: a missing label never satisfies the dual-key, so an unknown state
    cannot widen the bypass).
    """
    repo = os.environ.get("GH_REPO") or os.environ.get("GITHUB_REPOSITORY")
    if not repo:
        return []
    try:
        out = subprocess.run(
            [
                "gh", "pr", "view", str(pr_number),
                "--json", "labels",
                "--jq", "[.labels[].name]",
            ],
            capture_output=True, text=True, timeout=20,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if out.returncode != 0:
        return []
    try:
        names = json.loads(out.stdout or "[]")
    except json.JSONDecodeError:
        return []
    return [str(n) for n in names if isinstance(n, str)]


def gh_comment_fetcher(pr_number: int) -> list[dict]:
    """Fetch the COMMENTS of a PR via the ``gh`` CLI.

    Each comment is returned as ``{author, body, createdAt}``. Returns an empty
    list on any failure. The dual-key verdict treats a fetch failure as
    "comment with marker not present" (fail-closed) -- same rationale as
    ``gh_label_fetcher``.
    """
    repo = os.environ.get("GH_REPO") or os.environ.get("GITHUB_REPOSITORY")
    if not repo:
        return []
    try:
        out = subprocess.run(
            [
                "gh", "api", f"repos/{repo}/issues/{pr_number}/comments",
                "--jq", "[.[] | {author: .user.login, body: .body, createdAt: .created_at}]",
            ],
            capture_output=True, text=True, timeout=30,
        )
    except (OSError, subprocess.SubprocessError):
        return []
    if out.returncode != 0:
        return []
    try:
        comments = json.loads(out.stdout or "[]")
    except json.JSONDecodeError:
        return []
    return comments


# ---------------------------------------------------------------------------
# Pure decision.
# ---------------------------------------------------------------------------


def _extract_marker(body: str | None) -> str | None:
    """Return the motif after ``[TRANSLATION-OVERRIDE]`` in ``body`` or None.

    The marker must appear on its own line (the regex anchors with ``^``).
    We return the **first** hit -- the override is a single decision, and the
    dual-key already restricts its scope.
    """
    if not body:
        return None
    m = _MARKER_RE.search(body)
    return m.group("motif").strip() if m else None


def check(
    pr_number: int,
    comment_bodies: list[str] | None = None,
    label_names: list[str] | None = None,
    comment_fetcher: CommentFetcher | None = None,
    label_fetcher: LabelFetcher | None = None,
) -> dict:
    """Pure decision: does the PR carry the dual-key override (#10332)?

    Args:
        pr_number: the PR number. Used by the default fetchers; tests inject
            fetcher functions and pass a placeholder.
        comment_bodies: optional pre-fetched list of comment-body strings.
            When supplied, ``comment_fetcher`` is bypassed (test fast-path).
        label_names: optional pre-fetched list of label names. When supplied,
            ``label_fetcher`` is bypassed.
        comment_fetcher: ``int -> list[dict]``. Default ``gh_comment_fetcher``.
        label_fetcher: ``int -> list[str]``. Default ``gh_label_fetcher``.

    Returns the JSON verdict on stdout -- the YAML reads exit code:

        {
          "guard_pass": True|False,
          "reason": str,
          "override_applied": bool,
          "label_present": bool,
          "marker_present": bool,
          "motif": str|None,
          "warnings": [str, ...]
        }

    ``guard_pass`` is True iff the dual-key is satisfied (label AND marker).
    The override is the **only** way the guard can pass once ``violated=true``
    has been computed upstream by ``translation-guard.yml`` itself; on a clean
    PR (no derived files touched), ``translation-guard.yml`` short-circuits
    before this script is consulted -- this helper exists for the
    ``violated=true`` path.
    """
    labels = (
        label_names
        if label_names is not None
        else (label_fetcher or gh_label_fetcher)(pr_number)
    )
    label_present = OVERRIDE_LABEL in labels

    bodies: list[str]
    if comment_bodies is not None:
        bodies = list(comment_bodies)
    else:
        comments = (comment_fetcher or gh_comment_fetcher)(pr_number)
        bodies = [c.get("body", "") for c in comments if isinstance(c, dict)]

    marker: str | None = None
    for body in bodies:
        marker = _extract_marker(body)
        if marker is not None:
            break
    marker_present = marker is not None

    warnings: list[str] = []
    if not label_present and not marker_present:
        return {
            "guard_pass": False,
            "reason": (
                f"translation-guard violation: no override label '{OVERRIDE_LABEL}' "
                f"and no comment marker '[TRANSLATION-OVERRIDE] <motif>'. "
                f"Edit the source notebook instead and let translation-sync re-derive. "
                f"See #10332."
            ),
            "override_applied": False,
            "label_present": False,
            "marker_present": False,
            "motif": None,
            "warnings": warnings,
        }
    if not label_present:
        return {
            "guard_pass": False,
            "reason": (
                f"translation-guard violation: comment marker present but label "
                f"'{OVERRIDE_LABEL}' missing. Both required (dual-key). See #10332."
            ),
            "override_applied": False,
            "label_present": False,
            "marker_present": True,
            "motif": marker,
            "warnings": warnings,
        }
    if not marker_present:
        return {
            "guard_pass": False,
            "reason": (
                f"translation-guard violation: label '{OVERRIDE_LABEL}' present but "
                f"no comment with marker '[TRANSLATION-OVERRIDE] <motif>'. Both "
                f"required (dual-key). See #10332."
            ),
            "override_applied": False,
            "label_present": True,
            "marker_present": False,
            "motif": None,
            "warnings": warnings,
        }

    # Both keys satisfied: the override applies.
    assert motif_safe(marker), "marker validated by regex"  # nosec - regex anchored
    return {
        "guard_pass": True,
        "reason": (
            f"translation-guard OVERRIDE accepted: label '{OVERRIDE_LABEL}' "
            f"and comment marker '[TRANSLATION-OVERRIDE]' both present. "
            f"Motif: {marker!r}. The override is journalised in this job's log; "
            f"see #10332 for the protocol."
        ),
        "override_applied": True,
        "label_present": True,
        "marker_present": True,
        "motif": marker,
        "warnings": warnings,
    }


def motif_safe(motif: str | None) -> bool:
    """Light sanity check on the motif: must be non-empty after stripping."""
    return bool(motif) and bool(motif.strip())


# ---------------------------------------------------------------------------
# CLI plumbing.
# ---------------------------------------------------------------------------


def _read_labels_file(path: str) -> list[str]:
    """Read a labels file as a JSON array of strings (test path).

    Empty/missing -> empty list (treat as no labels present).
    """
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    if isinstance(data, list):
        return [str(x) for x in data]
    return []


def _read_comments_file(path: str) -> list[str]:
    """Read a comments file as a JSON array of comment-body strings (test path).

    Empty/missing -> empty list.
    """
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    if isinstance(data, list):
        return [str(x) for x in data]
    return []


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="translation-guard override decision (#10332)"
    )
    parser.add_argument("--pr-number", type=int, required=True)
    parser.add_argument(
        "--labels-file",
        default=None,
        help="JSON array of label names (skips the gh label fetch).",
    )
    parser.add_argument(
        "--comments-file",
        default=None,
        help="JSON array of comment-body strings (skips the gh comment fetch).",
    )
    args = parser.parse_args(argv)

    labels = _read_labels_file(args.labels_file) if args.labels_file else None
    comments = _read_comments_file(args.comments_file) if args.comments_file else None

    verdict = check(
        pr_number=args.pr_number,
        comment_bodies=comments,
        label_names=labels,
    )
    print(json.dumps(verdict, indent=1, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
