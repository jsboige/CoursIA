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

Marker selection (#21332, re-review 5574107628) -- the ack is a property of
the head, not of the last word in the thread:
  - test_ack_pass_most_recent_authorised_marker_wins : old ack must not mask
  - test_ack_pass_authorised_ack_after_other_author   : other author's marker
  - test_ack_fail_authorised_ack_stale_other_author_at_head : cliquet kept

Pagination (#21332, re-review 5574107628) -- the API returns 30 items
otherwise, and the ack is posted last:
  - test_gh_comment_fetcher_paginates             : every page is read
  - test_gh_review_fetcher_paginates              : every page is read

Fetch-failure restitution (#15342) -- a read error is never an absence:
  - test_fetch_error_label_fetcher_raises          : label unreadable -> None + cause
  - test_fetch_error_comment_fetcher_raises        : comments unreadable -> None + cause
  - test_fetch_error_review_fetcher_raises         : reviews unreadable -> None + cause
  - test_gh_label_fetcher_no_repo_env_raises       : real fetcher raises FetchError
  - test_gh_comment_fetcher_no_repo_env_raises     : real fetcher raises FetchError
  - test_gh_review_fetcher_no_repo_env_raises      : real fetcher raises FetchError
  - test_invalid_head_parameter                    : head not 40 hex chars -> fail-closed
"""

import json
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
    """Multiple markers (comment + review) without timestamps: the FIRST wins.

    Undated markers (the fixtures carry no timestamp) keep the API order;
    with timestamps, the most recent authorised marker at the exact head
    decides -- see ``test_ack_pass_most_recent_authorised_marker_wins``.
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


def test_ack_pass_most_recent_authorised_marker_wins():
    """An OLD authorised ack must not mask a NEWER one at the current head.

    The path this unblocks is ``ack -> update-branch -> re-ack``: the head
    moves, the coordinator re-acks at the new head, and the first marker
    found in API order (the stale one) used to decide the verdict
    (#21332, re-review 5574107628).
    """
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {
                "author": ACK_AUTHOR,
                "body": f"[EXEC-SEQ-ACK] head={HEAD_2}\n",
                "createdAt": "2026-10-19T05:00:00Z",
            },
            {
                "author": ACK_AUTHOR,
                "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n",
                "createdAt": "2026-10-19T13:00:00Z",
            },
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is True, verdict
    assert verdict["marker_head"] == HEAD_1
    assert verdict["head_match"] is True
    assert verdict["author_ok"] is True


def test_ack_pass_authorised_ack_after_other_author():
    """A marker by another author does not hide a valid ack that follows.

    The verdict must be decided by the authorised marker, not by the first
    marker met in the thread (#21332, re-review 5574107628).
    """
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {
                "author": "jsboige",
                "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n",
                "createdAt": "2026-10-19T05:00:00Z",
            },
            {
                "author": ACK_AUTHOR,
                "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n",
                "createdAt": "2026-10-19T13:00:00Z",
            },
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is True, verdict
    assert verdict["author_ok"] is True
    assert verdict["ack_author"] == ACK_AUTHOR


def test_ack_fail_authorised_ack_stale_other_author_at_head():
    """Cliquet kept: an authorised ack at a STALE head still fails.

    The other author's marker sits at the current head -- it is not an
    ack, and it must not promote the verdict to a pass nor mask the real
    cause (the authorised ack is stale and must be renewed).
    """
    verdict = check(
        pr_number=999,
        head=HEAD_1,
        comment_items=[
            {
                "author": ACK_AUTHOR,
                "body": f"[EXEC-SEQ-ACK] head={HEAD_2}\n",
                "createdAt": "2026-10-19T05:00:00Z",
            },
            {
                "author": "jsboige",
                "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n",
                "createdAt": "2026-10-19T13:00:00Z",
            },
        ],
        label_names=[ACK_LABEL],
    )
    assert verdict["guard_pass"] is False, verdict
    assert verdict["head_match"] is False
    assert verdict["marker_head"] == HEAD_2


class _FakeCompleted:
    """The shape of ``subprocess.CompletedProcess`` the fetchers read."""

    def __init__(self, stdout: str, returncode: int = 0, stderr: str = ""):
        self.stdout = stdout
        self.returncode = returncode
        self.stderr = stderr


def _fake_gh_run(lines: list[str], captured: list[list[str]]):
    """A ``subprocess.run`` stand-in printing ``lines`` (one JSON per line)."""

    def _run(argv, **_kwargs):
        captured.append(list(argv))
        return _FakeCompleted("\n".join(lines) + "\n")

    return _run


def _install_fake_gh(monkeypatch, module, lines: list[str]) -> list[list[str]]:
    """Point the organ's ``subprocess`` at the fake and capture the argv."""
    real = module.subprocess
    captured: list[list[str]] = []
    monkeypatch.setattr(
        module,
        "subprocess",
        type(
            "FakeSubprocess",
            (),
            {
                "run": staticmethod(_fake_gh_run(lines, captured)),
                "SubprocessError": real.SubprocessError,
            },
        ),
    )
    monkeypatch.setenv("GH_REPO", "jsboige/CoursIA")
    return captured


def test_gh_comment_fetcher_paginates(monkeypatch):
    """The REAL comment fetcher asks for every page and reads them all.

    Regression (#21332, re-review 5574107628): without ``--paginate`` the
    API returns only the first 30 comments, and an ack posted last on a
    busy PR falls outside the page read -- the gate then says "no marker".
    Measured on the PRs of #21273: 24 comments on #20369 and #20377, 35 on
    #20246.
    """
    import ci.exec_sequence_ack_required as module

    payload = [
        json.dumps(
            {
                "author": "jsboige",
                "body": f"comment {i}",
                "createdAt": "2026-10-19T05:00:00Z",
            }
        )
        for i in range(45)
    ]
    captured = _install_fake_gh(monkeypatch, module, payload)

    items = module.gh_comment_fetcher(21332)

    assert len(items) == 45, len(items)
    assert items[0]["body"] == "comment 0"
    assert items[-1]["body"] == "comment 44"
    argv = captured[0]
    assert "--paginate" in argv, argv
    assert any("per_page=100" in a for a in argv), argv
    assert any("issues/21332/comments" in a for a in argv), argv


def test_gh_review_fetcher_paginates(monkeypatch):
    """The REAL review fetcher asks for every page too."""
    import ci.exec_sequence_ack_required as module

    payload = [
        json.dumps(
            {
                "author": ACK_AUTHOR,
                "body": f"[EXEC-SEQ-ACK] head={HEAD_1}\n",
                "state": "COMMENTED",
                "submittedAt": "2026-10-19T05:00:00Z",
            }
        )
        for _ in range(12)
    ]
    captured = _install_fake_gh(monkeypatch, module, payload)

    items = module.gh_review_fetcher(21332)

    assert len(items) == 12, len(items)
    argv = captured[0]
    assert "--paginate" in argv, argv
    assert any("per_page=100" in a for a in argv), argv
    assert any("pulls/21332/reviews" in a for a in argv), argv


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