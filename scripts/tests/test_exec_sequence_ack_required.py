#!/usr/bin/env python3
"""Unit tests for ``exec_sequence_ack_required.py`` (#11577, #21273).

The script is a pure decision over (labels, comments, reviews, head) ->
verdict. Fetchers are default ``gh``-based and injectable; these tests pass
dict-based fixtures so the test runner never touches the network.

Coverage map (mirrors the acceptance criteria of #21273):
  - test_ack_pass_label_marker_at_correct_head    : pass
  - test_ack_fail_label_only                       : label without marker -> fail
  - test_ack_fail_marker_only                      : marker without label -> fail
  - test_ack_fail_neither                          : nothing -> fail (cliquet)
  - test_ack_fail_stale_head                       : marker at a stale head -> fail
  - test_ack_fail_wrong_author                     : marker from non-myia-ai-01 -> fail
  - test_ack_fail_empty_sha                        : malformed marker (not 40 hex) -> fail
  - test_ack_pass_in_review_body                   : marker in review body works
  - test_ack_pass_picks_first_marker               : multiple markers -> first wins
  - test_ack_label_case_sensitive                  : case-sensitive label match

Fetch-failure restitution (#15342) -- a read error is never an absence:
  - test_fetch_error_label_fetcher_raises          : label unreadable -> None + cause
  - test_fetch_error_comment_fetcher_raises        : comments unreadable -> None + cause
  - test_fetch_error_review_fetcher_raises         : reviews unreadable -> None + cause
  - test_gh_label_fetcher_no_repo_env_raises       : real fetcher raises FetchError
  - test_gh_comment_fetcher_no_repo_env_raises     : real fetcher raises FetchError
  - test_gh_review_fetcher_no_repo_env_raises      : real fetcher raises FetchError
  - test_invalid_head_parameter                    : head not 40 hex chars -> fail-closed
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ci.exec_sequence_ack_required import (  # noqa: E402
    ACK_AUTHOR,
    ACK_LABEL,
    FetchError,
    _extract_marker,
    check,
    gh_comment_fetcher,
    gh_label_fetcher,
    gh_review_fetcher,
)

HEAD_1 = "1" * 40
HEAD_2 = "2" * 40  # a stale head (push after the ack)


def test_ack_pass_label_marker_at_correct_head():
    """Dual-key satisfied at the EXACT head from myia-ai-01: pass."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {"author": ACK_AUTHOR, "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n"},
        ],
        label_names=[ACK_LABEL, "other-label"],
    )
    assert verdict["guard_pass"] is True, verdict
    assert verdict["ack_applied"] is True
    assert verdict["label_present"] is True
    assert verdict["marker_present"] is True
    assert verdict["marker_head"] == HEAD_1
    assert verdict["expected_head"] == HEAD_1
    assert verdict["head_match"] is True
    assert verdict["author_ok"] is True
    assert "ACK accepted" in verdict["reason"]


def test_ack_fail_label_only():
    """Label without marker: dual-key unsatisfied -> fail."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[{"author": "jsboige", "body": "no marker here"}],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert verdict["ack_applied"] is False
    assert verdict["label_present"] is True
    assert verdict["marker_present"] is False
    assert "label" in verdict["reason"].lower()
    assert "marker" in verdict["reason"].lower()


def test_ack_fail_marker_only():
    """Marker without label: dual-key unsatisfied -> fail."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {"author": ACK_AUTHOR, "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n"},
        ],
        label_names=["unrelated-label"],
    )
    assert verdict["guard_pass"] is False
    assert verdict["ack_applied"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is True
    assert "label" in verdict["reason"].lower()


def test_ack_fail_neither():
    """Nothing: cliquet non disarmé -> fail (criterion 4 of #21273)."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[{"author": "jsboige", "body": "unrelated"}],
        label_names=["random-label"],
    )
    assert verdict["guard_pass"] is False
    assert verdict["ack_applied"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is False


def test_ack_fail_stale_head():
    """Marker head does NOT match current head: ack is perime -> fail.

    This is the named failure of #21273 criterion 2: a push after the ack
    MUST invalidate it.
    """
    verdict = check(
        pr_number=999,
        head=HEAD_1,  # current head
        comment_items=[
            {"author": ACK_AUTHOR, "body": f"[EXEC-SEQ-ACK] head={HEAD_2}\n"},
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert verdict["ack_applied"] is False
    assert verdict["marker_present"] is True
    assert verdict["head_match"] is False
    assert "perime" in verdict["reason"].lower() or "périm" in verdict["reason"].lower() or "stale" in verdict["reason"].lower()


def test_ack_fail_wrong_author():
    """Marker from a non-authorised author (jsboige, clusterManager-Myia): fail.

    Only ``myia-ai-01`` carries the dual-key authority. Anything else is a
    finding, not an ack.
    """
    for author in ("jsboige", "clusterManager-Myia", "myia-po-2025", "dependabot[bot]"):
        verdict = check(
            pr_number=999,
            head=HEAD_1,
            comment_items=[
                {"author": author, "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n"},
            ],
            label_names=[ACK_LABEL],
        )
        assert verdict["guard_pass"] is False, author
        assert verdict["author_ok"] is False, author
        assert verdict["head_match"] is True, author


def test_ack_fail_empty_sha():
    """Marker with a malformed SHA (not 40 hex chars): fail."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {"author": ACK_AUTHOR, "body": "[EXEC-SEQ-ACK] head=deadbeef\n"},
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert verdict["marker_present"] is False
    # The dual-key check stays unsatisfied: malformed marker = no marker.


def test_ack_pass_in_review_body():
    """A marker placed in a REVIEW body (not a comment) is honoured."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        review_items=[
            {
                "author": ACK_AUTHOR,
                "state": "COMMENTED",
                "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n",
            },
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is True, verdict
    assert verdict["author_ok"] is True


def test_ack_pass_picks_first_marker():
    """Multiple markers (comment + review): the FIRST hit decides.

    The dual-key already restricts it; multi-marker is not a multi-decision.
    """
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {"author": ACK_AUTHOR, "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n"},
        ],
        review_items=[
            {"author": ACK_AUTHOR, "body": f"[EXEC-SEQ-ACK] head={HEAD_2}\n"},
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is True
    assert verdict["marker_head"] == HEAD_1  # first wins
    assert verdict["head_match"] is True


def test_ack_label_case_sensitive():
    """Label match is case-sensitive: ``Exec-Sequence-Ack`` does NOT trigger."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {"author": ACK_AUTHOR, "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n"},
        ],
        label_names=["Exec-Sequence-Ack"],  # wrong case
    )
    assert verdict["guard_pass"] is False
    assert verdict["label_present"] is False


def test_ack_marker_in_prose_does_not_count():
    """The regex anchors with ``^``; a marker mentioned in prose doesn't count."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {
                "author": ACK_AUTHOR,
                "body": (
                    "I could write `[EXEC-SEQ-ACK] head=" + HEAD_1 + "` in prose "
                    "but that is not an ack on its own line."
                ),
            },
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert verdict["marker_present"] is False


def test_ack_extra_whitespace_still_passes():
    """A trailing newline / leading whitespace on the marker line is tolerated."""
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {"author": ACK_AUTHOR, "body": f"  [EXEC-SEQ-ACK] head={HEAD_1}\n"},
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is True, verdict


def test_fetch_error_label_fetcher_raises():
    """Label fetcher raises: fail-closed with ``label_present=None`` (#15342)."""
    def _raise(_n):
        raise FetchError("simulated network failure")

    verdict = check(
        pr_number=999,
        head=HEAD_1,
        label_fetcher=_raise,
        comment_items=[{"author": ACK_AUTHOR, "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n"}],
    )
    assert verdict["guard_pass"] is False
    assert verdict["label_present"] is None
    assert "impossible de lire" in verdict["reason"]


def test_fetch_error_comment_fetcher_raises():
    """Comment fetcher raises: ``marker_present=None`` -> fail-closed."""
    def _raise(_n):
        raise FetchError("simulated network failure")

    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_fetcher=_raise,
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert verdict["marker_present"] is None


def test_fetch_error_review_fetcher_raises():
    """Review fetcher raises: combined bodies are None -> fail-closed."""
    def _raise(_n):
        raise FetchError("simulated network failure")

    verdict = check(
        pr_number=999,
        head=HEAD_1,
        review_fetcher=_raise,
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False


def test_gh_label_fetcher_no_repo_env_raises():
    """The real fetcher raises FetchError when the env is unset."""
    env = os.environ.copy()
    env.pop("GH_REPO", None)
    env.pop("GITHUB_REPOSITORY", None)
    with pytest.raises(FetchError):
        gh_label_fetcher(999)  # noqa: F841 - we don't care about the return


def test_gh_comment_fetcher_no_repo_env_raises():
    env = os.environ.copy()
    env.pop("GH_REPO", None)
    env.pop("GITHUB_REPOSITORY", None)
    with pytest.raises(FetchError):
        gh_comment_fetcher(999)  # noqa: F841


def test_gh_review_fetcher_no_repo_env_raises():
    env = os.environ.copy()
    env.pop("GH_REPO", None)
    env.pop("GITHUB_REPOSITORY", None)
    with pytest.raises(FetchError):
        gh_review_fetcher(999)  # noqa: F841


def test_invalid_head_parameter():
    """Caller passes a non-40-hex head: the script fails closed at the boundary."""
    verdict = check(
        pr_number=999,
        head="not-a-sha",
        comment_items=[{"author": ACK_AUTHOR, "body": "[EXEC-SEQ-ACK] head=deadbeef\n"}],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert "invalid head" in verdict["reason"]


def test_extract_marker_basic():
    """The marker extraction is anchored to a line start."""
    assert _extract_marker(f"[EXEC-SEQ-ACK] head={HEAD_1}") == HEAD_1
    assert _extract_marker(f"[EXEC-SEQ-ACK] head={HEAD_1}\n") == HEAD_1
    # Mid-prose mentions don't count.
    assert _extract_marker(
        f"see [EXEC-SEQ-ACK] head={HEAD_1} in the docs"
    ) is None
    # Empty / None bodies return None.
    assert _extract_marker(None) is None
    assert _extract_marker("") is None