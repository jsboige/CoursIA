#!/usr/bin/env python3
r"""exec_sequence_ack_required.py -- gate logic for the exec-sequence-ratchet
fail-by-design ack (#11577, #21273).

## Why this exists

The ``notebook-exec-sequence-ratchet.yml`` workflow guards the
``execution_count`` sequence of every changed notebook: a notebook that was
CLEAN at base must stay CLEAN at head. The guard rightly fires when a single
cell is re-executed while the downstream artifact is gitignored
(``scripts/results/**``, GPU runs of 10 h+): the ``execution_count`` sequence
turns DUPLICATE or NOT_FROM_1, and the gate reddens (#11577, #11574
precedent).

The repair proposes a **structured ack** matching the dual-key pattern set by
``[TRANSLATION-OVERRIDE]`` + label ``translation-override`` (#10332):

  - A label ``exec-sequence-ack`` on the PR. The label alone is too easy
    (a single click), so it is **not sufficient** by itself.
  - A comment or review on the PR bearing the marker
    ``[EXEC-SEQ-ACK] head=<sha40>`` in its **own line**, from the **sole**
    login ``myia-ai-01``. The head must equal the EXACT current head of the
    PR: a push after the ack invalidates the marker, and ``check()`` says so
    (head mismatch is the named failure of #21273).
  - **Both required** -- the same dual-key pattern that ``[OVERRIDE]``
    + ``lane-claim-conflict`` adjudication uses elsewhere (#10223, #10332).
  - When **both** are present at the exact head: the ratchet **bypasses**
    with a structured ``::notice title=Exec-sequence ack::ACK — head=<sha>``
    log line. The ack is **journalised** in the job summary; the override is
    **auditable** without being **easy**.
  - When either is missing or stale: the guard keeps FAILING -- the cliquet
    is not disarmed. This is criterion 4 of #21273.

## Why a separate script (not inline bash)

The verdict is the same shape as the other CI scripts (``scripts/ci/...``):
JSON on stdout, exit 0/1, the YAML reduces to plumbing. The script is
**injectable** so unit tests pass dict-based fetchers and never touch the
network.

## Run locally

    python scripts/ci/exec_sequence_ack_required.py \
        --body-file body.txt \
        --pr-number 1234 \
        --labels-file labels.json \
        --comments-file comments.json \
        --reviews-file reviews.json \
        --head <sha40>

The label fetcher calls ``gh pr view --json labels`` (CI). The comment
fetcher calls ``gh api .../issues/<n>/comments``. The review fetcher calls
``gh api .../pulls/<n>/reviews`` (not ``issues/<n>/reviews`` -- that endpoint
returns 404 on PRs; Hermes review on #21273 measured it live). ``--head`` is
the PR head SHA.

Exit codes: 0 pass / 1 fail (ack not satisfied).
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

# Marker carried in its own line of a PR comment or review body.
# `<sha40>` is the EXACT 40-char hex head SHA of the PR at the time of ack.
# The regex anchors with `^` (line start) so the marker cannot hide in a sea
# of prose; the dual-key already restricts its scope. Mirrors the
# ``[TRANSLATION-OVERRIDE]`` discipline (#10332).
_MARKER_RE = re.compile(
    r"^\s*\[EXEC-SEQ-ACK\]\s+head=(?P<head>[0-9a-fA-F]{40})\s*$",
    re.MULTILINE,
)

# Label name on the PR. Matches the wording of #21273's repair.
ACK_LABEL = "exec-sequence-ack"

# Sole login authorised to ack the runner. ``myia-ai-01`` is the coordinator
# lane; the login matches ``jsboige/CoursIA``'s shared ``myia-ai-01`` account
# (the only one with admin-merge rights). A comment or review from another
# author is invalid by construction.
ACK_AUTHOR = "myia-ai-01"


class FetchError(RuntimeError):
    """A fetcher could not READ its source (auth, rate-limit, network).

    Raised by ``gh_label_fetcher`` / ``gh_comment_fetcher`` /
    ``gh_review_fetcher`` on any failure. Distinct from a successful read that
    found nothing: an unreadable source must never be rendered as a measured
    absence (#15342) -- ``check()`` turns this into a fail-closed verdict
    whose ``reason`` says the read failed, with ``label_present`` /
    ``marker_present`` set to ``None``.
    """


# ---------------------------------------------------------------------------
# Fetchers (default = gh; injectable for tests).
# ---------------------------------------------------------------------------

LabelFetcher = Callable[[int], list[str]]
CommentFetcher = Callable[[int], list[dict]]
ReviewFetcher = Callable[[int], list[dict]]


def gh_label_fetcher(pr_number: int) -> list[str]:
    """Fetch the label NAMES attached to a PR via the ``gh`` CLI.

    Raises :class:`FetchError` on any failure (missing repo env, auth,
    rate-limit, network, bad JSON) -- never an empty list. An empty list is
    reserved for the measured fact "the PR has no labels". The verdict stays
    fail-closed on an unreadable source (an ack is never widened by an
    unknown state) but renders the read failure, not a false absence
    (#15342).
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


def gh_review_fetcher(pr_number: int) -> list[dict]:
    """Fetch the REVIEWS of a PR via the ``gh`` CLI.

    Each review is returned as ``{author, body, state, submittedAt}``. The
    ack marker may appear in a review body just as it may in a comment; the
    dual-key does not care which surface carries it. Same fail-closed
    rationale as ``gh_comment_fetcher`` (#15342).
    """
    repo = os.environ.get("GH_REPO") or os.environ.get("GITHUB_REPOSITORY")
    if not repo:
        raise FetchError(
            "cannot read PR reviews: neither GH_REPO nor GITHUB_REPOSITORY is set"
        )
    try:
        out = subprocess.run(
            [
                "gh", "api", f"repos/{repo}/pulls/{pr_number}/reviews",
                "--jq", "[.[] | {author: .user.login, body: .body, state: .state, submittedAt: .submitted_at}]",
            ],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=30,
        )
    except (OSError, subprocess.SubprocessError) as e:
        raise FetchError(f"cannot read PR reviews: gh api failed: {e}") from e
    if out.returncode != 0:
        stderr = (out.stderr or "").strip()[:200]
        raise FetchError(
            f"cannot read PR reviews: gh api rc={out.returncode}: {stderr}"
        )
    try:
        reviews = json.loads(out.stdout or "[]")
    except json.JSONDecodeError as e:
        raise FetchError(
            f"cannot read PR reviews: gh api output is not JSON: {e}"
        ) from e
    return reviews


# ---------------------------------------------------------------------------
# Pure decision.
# ---------------------------------------------------------------------------


def _extract_marker(body: str | None) -> str | None:
    """Return the head SHA after ``[EXEC-SEQ-ACK] head=<sha40>`` in ``body``
    or None.

    The marker must appear on its own line (the regex anchors with ``^``).
    We return the **first** hit -- the ack is a single decision, and the
    dual-key already restricts its scope. The 40-char hex constraint is what
    differentiates a fresh ack from a generic prose mention (#21273).
    """
    if not body:
        return None
    m = _MARKER_RE.search(body)
    return m.group("head").lower() if m else None


def _author_ok(item: dict | None) -> bool:
    """The ack marker must come from the authorised coordinator login.

    A reviewer comment from ``jsboige`` (the shared login) or
    ``clusterManager-Myia`` is NOT an ack: only ``myia-ai-01`` carries the
    dual-key authority. Anything else is a finding, not an ack.
    """
    if not isinstance(item, dict):
        return False
    auth = item.get("author")
    return isinstance(auth, str) and auth == ACK_AUTHOR


def check(
    pr_number: int,
    head: str,
    comment_bodies: list[str] | None = None,
    review_bodies: list[str] | None = None,
    label_names: list[str] | None = None,
    comment_items: list[dict] | None = None,
    review_items: list[dict] | None = None,
    comment_fetcher: CommentFetcher | None = None,
    review_fetcher: ReviewFetcher | None = None,
    label_fetcher: LabelFetcher | None = None,
) -> dict:
    """Pure decision: does the PR carry the dual-key exec-sequence ack?

    Args:
        pr_number: the PR number. Used by the default fetchers; tests inject
            fetcher functions and pass a placeholder.
        head: 40-char hex SHA of the PR head. The marker must match this
            exactly; any push after the ack invalidates the marker.
        comment_bodies: optional pre-fetched list of comment-body strings.
            When supplied, ``comment_fetcher`` is bypassed (test fast-path).
        review_bodies: optional pre-fetched list of review-body strings.
            Same fast-path as comments.
        label_names: optional pre-fetched list of label names. When supplied,
            ``label_fetcher`` is bypassed.
        comment_items: optional pre-fetched list of comment dicts
            (author, body, ...). Used to filter by author without a re-fetch.
        review_items: optional pre-fetched list of review dicts. Same.
        comment_fetcher: ``int -> list[dict]``. Default ``gh_comment_fetcher``.
        review_fetcher: ``int -> list[dict]``. Default ``gh_review_fetcher``.
        label_fetcher: ``int -> list[str]``. Default ``gh_label_fetcher``.

    Returns the JSON verdict on stdout -- the YAML reads exit code::

        {
          "guard_pass": True|False,
          "reason": str,
          "ack_applied": bool,
          "label_present": True|False|None,
          "marker_present": True|False|None,
          "marker_head": str|None,
          "expected_head": str|None,
          "head_match": True|False|None,
          "author_ok": True|False|None,
          "warnings": [str, ...],
          "fetch_error": str|None
        }

    ``guard_pass`` is True iff the dual-key is satisfied (label AND marker at
    the EXACT head from the authorised author). ``label_present`` /
    ``marker_present`` / ``head_match`` / ``author_ok`` are ``None`` when
    that side could not be READ (fetcher raised): an unreadable source is
    never rendered as a measured absence -- the verdict stays fail-closed
    but says so (#15342). ``fetch_error`` carries the cause(s); it is
    ``None`` on a clean read.
    """
    fetch_errors: list[str] = []
    ack_author: str | None = None

    # Normalise the expected head.
    expected = (head or "").strip().lower()
    if expected and not re.fullmatch(r"[0-9a-f]{40}", expected):
        # Caller bug: head must be a 40-char hex SHA.
        return {
            "guard_pass": False,
            "reason": (
                f"exec-sequence ack: invalid head parameter {head!r}: "
                f"expected a 40-char hex SHA (#21273)."
            ),
            "ack_applied": False,
            "ack_author": ack_author,
            "label_present": None,
            "marker_present": None,
            "marker_head": None,
            "expected_head": expected or None,
            "head_match": None,
            "author_ok": None,
            "warnings": [],
            "fetch_error": None,
        }

    labels: list[str] | None = label_names
    if labels is None:
        try:
            labels = (label_fetcher or gh_label_fetcher)(pr_number)
        except Exception as e:  # noqa: BLE001
            fetch_errors.append(f"labels: {type(e).__name__}: {e}")
    label_present: bool | None = (
        None if labels is None else ACK_LABEL in labels
    )

    # Comments: prefer pre-fetched items (author filter), else bodies-only,
    # else fetch via the gh fetcher. If the caller supplied EITHER side
    # (items or bodies) AND not the other, treat the other as empty by
    # default so a missing one does not crash the test/CI run with a fetch
    # error (#15342 fail-closed semantics).
    comment_bodies_final: list[str] | None
    if comment_bodies is not None:
        comment_bodies_final = list(comment_bodies)
    elif comment_items is not None:
        comment_bodies_final = [
            c.get("body", "") for c in comment_items if isinstance(c, dict)
        ]
    else:
        # Neither items nor bodies provided. Fetch via gh, but only if the
        # caller hasn't already supplied the OTHER side as items/bodies --
        # in that case treat this side as empty (no entries).
        if review_items is not None or review_bodies is not None:
            comment_bodies_final = []
        else:
            try:
                comments = (comment_fetcher or gh_comment_fetcher)(pr_number)
            except Exception as e:  # noqa: BLE001
                fetch_errors.append(f"comments: {type(e).__name__}: {e}")
                comment_bodies_final = None
            else:
                comment_bodies_final = [
                    c.get("body", "") for c in comments if isinstance(c, dict)
                ]

    # Same fast-path shape for reviews.
    review_bodies_final: list[str] | None
    if review_bodies is not None:
        review_bodies_final = list(review_bodies)
    elif review_items is not None:
        review_bodies_final = [
            r.get("body", "") for r in review_items if isinstance(r, dict)
        ]
    else:
        if comment_items is not None or comment_bodies is not None:
            review_bodies_final = []
        else:
            try:
                reviews = (review_fetcher or gh_review_fetcher)(pr_number)
            except Exception as e:  # noqa: BLE001
                fetch_errors.append(f"reviews: {type(e).__name__}: {e}")
                review_bodies_final = None
            else:
                review_bodies_final = [
                    r.get("body", "") for r in reviews if isinstance(r, dict)
                ]

    # Author filtering: walk the original items so we know which surface
    # carries the marker AND from whom. ``comment_items`` / ``review_items``
    # take priority over bodies-only fetches (the body fast-path skips the
    # author check entirely, which is a debug-only escape hatch).
    marker_present: bool | None = None
    marker_head: str | None = None
    head_match: bool | None = None
    author_ok: bool | None = None

    if comment_items is not None or review_items is not None:
        combined: list[tuple[str, dict]] = []
        if comment_items is not None:
            combined.extend(("comment", c) for c in comment_items if isinstance(c, dict))
        if review_items is not None:
            combined.extend(("review", r) for r in review_items if isinstance(r, dict))
        for surface, item in combined:
            head_in_body = _extract_marker(item.get("body", ""))
            if head_in_body is None:
                continue
            auth = item.get("author")
            author_ok = bool(isinstance(auth, str) and auth == ACK_AUTHOR)
            marker_present = True
            marker_head = head_in_body
            head_match = bool(expected) and (head_in_body == expected)
            ack_author = auth if author_ok else None
            break
    elif comment_bodies_final is not None and review_bodies_final is not None:
        # Bodies-only fast-path: we cannot check the author here, so the
        # author dimension is reported as ``None`` to surface that limitation.
        combined_bodies = list(comment_bodies_final) + list(review_bodies_final)
        any_marker = False
        for body in combined_bodies:
            head_in_body = _extract_marker(body)
            if head_in_body is None:
                continue
            any_marker = True
            marker_head = head_in_body
            head_match = bool(expected) and (head_in_body == expected)
            break
        marker_present = any_marker
        author_ok = None if any_marker else False
        ack_author = None

    warnings: list[str] = []
    if fetch_errors:
        # A surface is "unreadable" if it could not be read (None) and the
        # fetch error log does not already name it (the log entry IS the
        # unreadable signal). Simpler than the previous ternary
        # `fetch_errors and "comments" or ""` which conflated truthiness of
        # the list with membership of the literal "comments".
        comment_error = any("comments" in e for e in fetch_errors)
        review_error = any("reviews" in e for e in fetch_errors)
        unreadable = [
            name for name, present in (
                ("labels", label_present),
                ("comments", comment_bodies_final is None and not comment_error),
                ("reviews", review_bodies_final is None and not review_error),
            )
            if present is None
        ]
        return {
            "guard_pass": False,
            "reason": (
                f"exec-sequence ack: impossible de lire {' / '.join(unreadable)} : "
                f"{'; '.join(fetch_errors)}. "
                f"Ceci n'est pas une absence mesuree (fail-closed inchange). See #15342."
            ),
            "ack_applied": False,
            "ack_author": ack_author,
            "label_present": label_present,
            "marker_present": marker_present,
            "marker_head": marker_head,
            "expected_head": expected or None,
            "head_match": head_match,
            "author_ok": author_ok,
            "warnings": warnings,
            "fetch_error": "; ".join(fetch_errors),
        }

    if not label_present and not marker_present:
        return {
            "guard_pass": False,
            "reason": (
                f"exec-sequence ratchet: pas de label '{ACK_LABEL}' et pas de "
                f"commentaire/review avec marker '[EXEC-SEQ-ACK] head=<sha40>'. "
                f"Les deux sont requis (cle double, #21273). "
                f"Si la sequence degradee est assumee, documenter la PR avec le "
                f"template 'Ratchet exec-sequence fail-by-design' "
                f"(docs/reference/regles-validation-detail.md) et obtenir un ack "
                f"de myia-ai-01 a la tete exacte."
            ),
            "ack_applied": False,
            "ack_author": ack_author,
            "label_present": False,
            "marker_present": False,
            "marker_head": None,
            "expected_head": expected or None,
            "head_match": None,
            "author_ok": False,
            "warnings": warnings,
            "fetch_error": None,
        }
    if not label_present:
        return {
            "guard_pass": False,
            "reason": (
                f"exec-sequence ratchet: marker present mais label '{ACK_LABEL}' "
                f"manquant. Les deux sont requis (cle double, #21273)."
            ),
            "ack_applied": False,
            "ack_author": ack_author,
            "label_present": False,
            "marker_present": True,
            "marker_head": marker_head,
            "expected_head": expected or None,
            "head_match": head_match,
            "author_ok": author_ok,
            "warnings": warnings,
            "fetch_error": None,
        }
    if not marker_present:
        return {
            "guard_pass": False,
            "reason": (
                f"exec-sequence ratchet: label '{ACK_LABEL}' present mais aucun "
                f"commentaire/review avec marker '[EXEC-SEQ-ACK] head=<sha40>'. "
                f"Les deux sont requis (cle double, #21273)."
            ),
            "ack_applied": False,
            "ack_author": ack_author,
            "label_present": True,
            "marker_present": False,
            "marker_head": None,
            "expected_head": expected or None,
            "head_match": None,
            "author_ok": author_ok,
            "warnings": warnings,
            "fetch_error": None,
        }
    # Both keys satisfied at the structure level; now verify the head matches
    # and the author is the authorised one. Either failure kills the ack:
    # a stale head means the PR moved since the ack, an unknown author means
    # the marker came from a non-coordinator (a finding, not an ack).
    if not head_match:
        return {
            "guard_pass": False,
            "reason": (
                f"exec-sequence ratchet: ack present mais la tete du marker "
                f"({marker_head[:12] if marker_head else '?'}) ne correspond pas "
                f"a la tete courante ({expected[:12] if expected else '?'}). "
                f"Un push ulterieur a perime l'ack ; redemander un ack a la tete "
                f"exacte (#21273)."
            ),
            "ack_applied": False,
            "ack_author": ack_author,
            "label_present": True,
            "marker_present": True,
            "marker_head": marker_head,
            "expected_head": expected or None,
            "head_match": False,
            "author_ok": author_ok,
            "warnings": warnings,
            "fetch_error": None,
        }
    if author_ok is False:
        return {
            "guard_pass": False,
            "reason": (
                f"exec-sequence ratchet: marker present mais l'auteur n'est pas "
                f"l'autorise ({ACK_AUTHOR!r}). Un commentaire/review d'un autre "
                f"login est un finding, pas un ack (#21273)."
            ),
            "ack_applied": False,
            "ack_author": ack_author,
            "label_present": True,
            "marker_present": True,
            "marker_head": marker_head,
            "expected_head": expected or None,
            "head_match": True,
            "author_ok": False,
            "warnings": warnings,
            "fetch_error": None,
        }

    # All three checks passed.
    return {
        "guard_pass": True,
        "reason": (
            f"exec-sequence ratchet ACK accepted: label '{ACK_LABEL}', "
            f"marker '[EXEC-SEQ-ACK] head={marker_head}' by {ACK_AUTHOR}, "
            f"matches current head {expected[:12]}. The ack is journalised in "
            f"this job's log; see #21273 for the protocol."
        ),
        "ack_applied": True,
            "ack_author": ack_author,
        "label_present": True,
        "marker_present": True,
        "marker_head": marker_head,
        "expected_head": expected or None,
        "head_match": True,
        "author_ok": True,
        "warnings": warnings,
        "fetch_error": None,
    }


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


def _read_string_list_file(path: str) -> list[str]:
    """Read a JSON array of strings from a file (test path)."""
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    if isinstance(data, list):
        return [str(x) for x in data]
    return []


def _read_items_file(path: str) -> list[dict]:
    """Read a JSON array of dicts from a file (test path)."""
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
    except (OSError, json.JSONDecodeError):
        return []
    if isinstance(data, list):
        return [x for x in data if isinstance(x, dict)]
    return []


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="exec-sequence ratchet fail-by-design ack decision (#21273)"
    )
    parser.add_argument("--pr-number", type=int, required=True)
    parser.add_argument(
        "--head",
        required=True,
        help="40-char hex SHA of the PR head (the ack marker must match this).",
    )
    parser.add_argument(
        "--labels-file",
        default=None,
        help="JSON array of label names (skips the gh label fetch).",
    )
    parser.add_argument(
        "--comments-file",
        default=None,
        help="JSON array of comment objects {author, body, createdAt} "
             "(skips the gh comment fetch).",
    )
    parser.add_argument(
        "--reviews-file",
        default=None,
        help="JSON array of review objects {author, body, state, submittedAt} "
             "(skips the gh review fetch).",
    )
    args = parser.parse_args(argv)

    labels = _read_labels_file(args.labels_file) if args.labels_file else None
    comments = _read_items_file(args.comments_file) if args.comments_file else None
    reviews = _read_items_file(args.reviews_file) if args.reviews_file else None

    verdict = check(
        pr_number=args.pr_number,
        head=args.head,
        label_names=labels,
        comment_items=comments,
        review_items=reviews,
    )
    print(json.dumps(verdict, indent=1, ensure_ascii=False))
    return 0 if verdict["guard_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())