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


class FetchError(RuntimeError):
    """A fetcher could not READ its source (auth, rate-limit, network).

    Raised by ``gh_label_fetcher`` / ``gh_comment_fetcher`` on any failure.
    Distinct from a successful read that found nothing: an unreadable source
    must never be rendered as a measured absence (#15342) -- ``check()``
    turns this into a fail-closed verdict whose ``reason`` says the read
    failed, with ``label_present``/``marker_present`` set to ``None``.
    """


# ---------------------------------------------------------------------------
# Fetchers (default = gh; injectable for tests).
# ---------------------------------------------------------------------------

LabelFetcher = Callable[[int], list[str]]
CommentFetcher = Callable[[int], list[dict]]


def gh_label_fetcher(pr_number: int) -> list[str]:
    """Fetch the label NAMES attached to a PR via the ``gh`` CLI.

    Raises :class:`FetchError` on any failure (missing repo env, auth,
    rate-limit, network, bad JSON) -- never an empty list. An empty list is
    reserved for the measured fact "the PR has no labels". The verdict stays
    fail-closed on an unreadable source (an override is never widened by an
    unknown state) but renders the read failure, not a false absence (#15342).
    """
    repo = os.environ.get("GH_REPO") or os.environ.get("GITHUB_REPOSITORY")
    if not repo:
        raise FetchError(
            "cannot read PR labels: neither GH_REPO nor GITHUB_REPOSITORY is set"
        )
    try:
        out = subprocess.run(
            [
                "gh", "pr", "view", str(pr_number),
                "--repo", repo,
                "--json", "labels",
                "--jq", "[.labels[].name]",
            ],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=20,
        )
    except (OSError, subprocess.SubprocessError) as e:
        raise FetchError(f"cannot read PR labels: gh pr view failed: {e}") from e
    if out.returncode != 0:
        stderr = (out.stderr or "").strip()[:200]
        raise FetchError(
            f"cannot read PR labels: gh pr view rc={out.returncode}: {stderr}"
        )
    try:
        names = json.loads(out.stdout or "[]")
    except json.JSONDecodeError as e:
        raise FetchError(
            f"cannot read PR labels: gh pr view output is not JSON: {e}"
        ) from e
    return [str(n) for n in names if isinstance(n, str)]


def gh_comment_fetcher(pr_number: int) -> list[dict]:
    """Fetch the COMMENTS of a PR via the ``gh`` CLI.

    Each comment is returned as ``{author, body, createdAt}``. Raises
    :class:`FetchError` on any failure -- never an empty list. An empty list
    is reserved for the measured fact "the PR has no comments". Same
    fail-closed-with-honest-restitution rationale as ``gh_label_fetcher``
    (#15342).
    """
    repo = os.environ.get("GH_REPO") or os.environ.get("GITHUB_REPOSITORY")
    if not repo:
        raise FetchError(
            "cannot read PR comments: neither GH_REPO nor GITHUB_REPOSITORY is set"
        )
    try:
        out = subprocess.run(
            [
                "gh", "api", f"repos/{repo}/issues/{pr_number}/comments",
                "--jq", "[.[] | {author: .user.login, body: .body, createdAt: .created_at}]",
            ],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=30,
        )
    except (OSError, subprocess.SubprocessError) as e:
        raise FetchError(f"cannot read PR comments: gh api failed: {e}") from e
    if out.returncode != 0:
        stderr = (out.stderr or "").strip()[:200]
        raise FetchError(
            f"cannot read PR comments: gh api rc={out.returncode}: {stderr}"
        )
    try:
        comments = json.loads(out.stdout or "[]")
    except json.JSONDecodeError as e:
        raise FetchError(
            f"cannot read PR comments: gh api output is not JSON: {e}"
        ) from e
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
          "label_present": True|False|None,
          "marker_present": True|False|None,
          "motif": str|None,
          "warnings": [str, ...],
          "fetch_error": str|None
        }

    ``guard_pass`` is True iff the dual-key is satisfied (label AND marker).
    ``label_present``/``marker_present`` are ``None`` when that side could not
    be READ (fetcher raised): an unreadable source is never rendered as a
    measured absence -- the verdict stays fail-closed but says so (#15342).
    ``fetch_error`` carries the cause(s); it is ``None`` on a clean read.

    The override is the **only** way the guard can pass once ``violated=true``
    has been computed upstream by ``translation-guard.yml`` itself; on a clean
    PR (no derived files touched), ``translation-guard.yml`` short-circuits
    before this script is consulted -- this helper exists for the
    ``violated=true`` path.
    """
    fetch_errors: list[str] = []

    labels: list[str] | None = label_names
    if labels is None:
        try:
            labels = (label_fetcher or gh_label_fetcher)(pr_number)
        except Exception as e:  # noqa: BLE001 - any fetcher failure is a read failure
            fetch_errors.append(f"labels: {type(e).__name__}: {e}")
    label_present: bool | None = (
        None if labels is None else OVERRIDE_LABEL in labels
    )

    bodies: list[str] | None
    if comment_bodies is not None:
        bodies = list(comment_bodies)
    else:
        try:
            comments = (comment_fetcher or gh_comment_fetcher)(pr_number)
        except Exception as e:  # noqa: BLE001 - any fetcher failure is a read failure
            fetch_errors.append(f"comments: {type(e).__name__}: {e}")
            bodies = None
        else:
            bodies = [c.get("body", "") for c in comments if isinstance(c, dict)]

    marker: str | None = None
    if bodies is not None:
        for body in bodies:
            marker = _extract_marker(body)
            if marker is not None:
                break
    marker_present: bool | None = None if bodies is None else marker is not None

    warnings: list[str] = []
    if fetch_errors:
        unreadable = [
            name
            for name, present in (
                ("les labels", label_present),
                ("les commentaires", marker_present),
            )
            if present is None
        ]
        return {
            "guard_pass": False,
            "reason": (
                f"translation-guard: impossible de lire {' et '.join(unreadable)} : "
                f"{'; '.join(fetch_errors)}. "
                f"Ceci n'est pas une absence mesuree (fail-closed inchange). See #15342."
            ),
            "override_applied": False,
            "label_present": label_present,
            "marker_present": marker_present,
            "motif": marker,
            "warnings": warnings,
            "fetch_error": "; ".join(fetch_errors),
        }
    if not label_present and not marker_present:
        return {
            "guard_pass": False,
            "reason": (
                f"translation-guard violation: no override label '{OVERRIDE_LABEL}' "
                f"and no comment marker '[TRANSLATION-OVERRIDE] <motif>'. "
                f"NOTE (#15198): translation-sync is on manual-maintainer hold since "
                f"2026-08-12 (#10038) -- editing the FR source does not refresh the "
                f"derived file until the hold is lifted; while it stands, the dual-key "
                f"override (#10332) is the expected exit for a legitimate change. "
            ),
            "override_applied": False,
            "label_present": False,
            "marker_present": False,
            "motif": None,
            "warnings": warnings,
            "fetch_error": None,
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
            "fetch_error": None,
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
            "fetch_error": None,
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
        "fetch_error": None,
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
