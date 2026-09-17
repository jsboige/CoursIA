"""Causal tests for the adjoint prevalidation entry gate (#16442)."""

import importlib.util
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_adjoint_prevalidation.py"
spec = importlib.util.spec_from_file_location("check_adjoint_prevalidation", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_adjoint_prevalidation"] = mod
spec.loader.exec_module(mod)

HEAD = "0123456789abcdef0123456789abcdef01234567"


def _comment(
    body: str,
    login: str = "jsboige",
    created_at: str = "2026-09-17T09:00:00Z",
) -> dict:
    return {
        "id": f"comment-{abs(hash(body))}",
        "author": {"login": login},
        "createdAt": created_at,
        "body": body,
    }


def _base_snapshot() -> dict:
    return {
        "number": 123,
        "body": "PR body",
        "createdAt": "2026-09-16T08:00:00Z",
        "headRefOid": HEAD,
        "commits": [{"oid": HEAD, "committedDate": "2026-09-17T07:00:00Z"}],
        "state": "OPEN",
        "title": "PR title",
        "isDraft": False,
        "baseRefName": "main",
        "labels": [],
        "comments": [_comment("ordinary earlier comment")],
        "reviews": [
            {"state": "COMMENTED", "commit": {"oid": HEAD}},
            {"state": "APPROVED", "commit": {"oid": HEAD}},
        ],
        "threads": [{"isResolved": True}],
        "statusCheckRollup": [{"name": "PR gate", "conclusion": "SUCCESS"}],
        "changedFiles": 3,
        "additions": 42,
        "deletions": 7,
    }


def _body(source: dict | None = None, **changes: str) -> str:
    source = source or _base_snapshot()
    fields = {
        "schema": "1",
        "lane": "myia-po-2025:CoursIA-2",
        "pr": "123",
        "head": source["headRefOid"],
        "complete": "true",
        "body": "read",
        "comments-reviewed": str(len(source.get("comments") or [])),
        "reviews-reviewed": str(len(source.get("reviews") or [])),
        "threads-reviewed": str(len(source.get("threads") or [])),
        "threads-unresolved": str(sum(
            not thread.get("isResolved", False)
            for thread in source.get("threads") or []
        )),
        "surfaces-sha256": mod.surfaces_fingerprint(source),
        "diff-files": str(source["changedFiles"]),
        "diff-additions": str(source["additions"]),
        "diff-deletions": str(source["deletions"]),
        "checks": "latest-wins-green",
        "b0": "clear",
        "scope": "pass",
        "domain": "pass",
        "verdict": "READY",
    }
    fields.update(changes)
    lines = [mod.START, *(f"{key}: {value}" for key, value in fields.items()), mod.END]
    return "\n".join(lines)


def _snapshot(dossier: str | None = None) -> dict:
    snapshot = _base_snapshot()
    if dossier is not None:
        snapshot["comments"].append(_comment(dossier))
    return snapshot


def _errors(snapshot: dict) -> list[str]:
    ready, errors = mod.evaluate(snapshot)
    assert not ready
    return errors


def _queue_snapshot(**dossier_fields: str) -> dict:
    snapshot = _base_snapshot()
    snapshot["comments"].append(_comment(
        _body(snapshot, **dossier_fields),
        created_at="2026-09-17T09:30:00Z",
    ))
    return snapshot


def _now() -> datetime:
    return datetime(2026, 9, 17, 12, 0, tzinfo=timezone.utc)


def test_exact_head_complete_ready_dossier_passes():
    ready, errors = mod.evaluate(_snapshot(_body()))
    assert ready
    assert errors == []


def test_missing_dossier_fails_closed():
    assert "no [ADJOINT PREFLIGHT]" in " ".join(_errors(_snapshot()))


def test_stale_head_fails_closed():
    errors = _errors(_snapshot(_body(head="f" * 40)))
    assert any("head is stale" in error for error in errors)


def test_closed_draft_retargeted_or_retitled_pr_fails_closed():
    for field, value in (
        ("state", "MERGED"),
        ("isDraft", True),
        ("baseRefName", "release"),
        ("title", "retitled after preflight"),
    ):
        snapshot = _snapshot(_body())
        snapshot[field] = value
        errors = _errors(snapshot)
        assert errors, field


def test_incomplete_surface_attestation_fails_closed():
    body = _body().replace("reviews-reviewed: 2\n", "")
    errors = _errors(_snapshot(body))
    assert any("reviews-reviewed" in error for error in errors)


def test_each_live_surface_count_is_checked():
    cases = {
        "comments-reviewed": {"comments-reviewed": "0"},
        "reviews-reviewed": {"reviews-reviewed": "1"},
        "threads-reviewed": {"threads-reviewed": "0"},
        "diff-files": {"diff-files": "2"},
        "diff-additions": {"diff-additions": "41"},
        "diff-deletions": {"diff-deletions": "6"},
    }
    for field, change in cases.items():
        errors = _errors(_snapshot(_body(**change)))
        assert any(error.startswith(f"{field} is stale") for error in errors), field


def test_checks_and_b0_require_canonical_complete_verdicts():
    for field, value in (
        ("checks", "pending"),
        ("b0", "blocked"),
        ("scope", "fail"),
        ("domain", "fail"),
        ("complete", "false"),
        ("body", "not-read"),
    ):
        errors = _errors(_snapshot(_body(**{field: value})))
        assert any(error.startswith(f"{field} must") for error in errors), field


def test_worker_lane_cannot_satisfy_gate():
    errors = _errors(_snapshot(_body(lane="myia-po-2027:CoursIA")))
    assert any(error.startswith("lane must") for error in errors)


def test_non_shared_github_author_cannot_satisfy_gate():
    snapshot = _snapshot(None)
    snapshot["comments"].append(_comment(_body(), login="worker-bot"))
    errors = _errors(snapshot)
    assert any(error.startswith("comment author must") for error in errors)


def test_blocked_preflight_cannot_satisfy_gate():
    errors = _errors(_snapshot(_body(verdict="BLOCKED")))
    assert any(error.startswith("verdict must") for error in errors)


def test_unresolved_thread_cannot_be_ready():
    snapshot = _snapshot(_body(**{"threads-unresolved": "1"}))
    snapshot["threads"] = [{"isResolved": False}]
    errors = _errors(snapshot)
    assert "READY requires zero unresolved threads" in errors


def test_comment_after_dossier_invalidates_it():
    snapshot = _snapshot(_body())
    snapshot["comments"].append(_comment("new concern after preflight"))
    errors = _errors(snapshot)
    assert any("discussion changed after dossier" in error for error in errors)


def test_same_count_surface_mutation_invalidates_fingerprint():
    for surface, mutate in (
        ("body", lambda snapshot: snapshot.__setitem__("body", "edited body")),
        (
            "review",
            lambda snapshot: snapshot["reviews"][0].__setitem__(
                "state", "CHANGES_REQUESTED"
            ),
        ),
        (
            "thread",
            lambda snapshot: snapshot["threads"][0].__setitem__(
                "isResolved", False
            ),
        ),
        (
            "checks",
            lambda snapshot: snapshot["statusCheckRollup"][0].__setitem__(
                "conclusion", "FAILURE"
            ),
        ),
    ):
        snapshot = _snapshot(_body())
        mutate(snapshot)
        errors = _errors(snapshot)
        assert any("discussion surfaces changed" in error for error in errors), surface


def test_latest_dossier_wins_and_stale_latest_cannot_fall_back():
    snapshot = _snapshot(_body())
    snapshot["comments"].append(_comment(_body(head="e" * 40, **{"comments-reviewed": "2"})))
    errors = _errors(snapshot)
    assert any("head is stale" in error for error in errors)


def test_marker_inside_prose_or_quote_is_not_a_dossier():
    snapshot = _snapshot(None)
    snapshot["comments"] = [_comment("Quoted example:\n[ADJOINT PREFLIGHT]\nverdict: READY")]
    assert "no [ADJOINT PREFLIGHT]" in " ".join(_errors(snapshot))


def test_unknown_and_duplicate_fields_fail_closed():
    unknown = _body().replace(mod.END, "extra-proof: yes\n" + mod.END)
    assert any("unknown fields" in error for error in _errors(_snapshot(unknown)))

    duplicate = _body().replace("schema: 1", "schema: 1\nschema: 1")
    assert any("duplicate field" in error for error in _errors(_snapshot(duplicate)))


def test_truncated_or_trailed_dossier_is_reported_as_malformed():
    truncated = _body().replace("\n" + mod.END, "")
    assert "missing closing marker" in _errors(_snapshot(truncated))

    trailed = _body() + "\ntext after the contract"
    assert "content after closing marker" in _errors(_snapshot(trailed))


def test_noncanonical_integer_and_pr_mismatch_fail_closed():
    errors = _errors(_snapshot(_body(**{"diff-additions": "+42"})))
    assert any("canonical non-negative integer" in error for error in errors)

    errors = _errors(_snapshot(_body(pr="124")))
    assert any(error.startswith("pr is stale") for error in errors)


def test_template_populates_mechanical_fields_but_not_verdicts():
    template = mod.render_template(_base_snapshot())
    assert f"head: {HEAD}" in template
    assert "comments-reviewed: 1" in template
    assert "reviews-reviewed: 2" in template
    assert "threads-reviewed: 1" in template
    assert "surfaces-sha256: " + mod.surfaces_fingerprint(_base_snapshot()) in template
    assert "verdict: REPLACE_WITH_READY_OR_BLOCKED" in template
    assert "verdict: READY" not in template


def test_metadata_identity_ignores_only_check_order():
    first = {
        "number": 123,
        "updatedAt": "2026-09-16T19:00:00Z",
        "statusCheckRollup": [
            {"name": "A", "conclusion": "SUCCESS"},
            {"name": "B", "conclusion": "SUCCESS"},
        ],
    }
    reordered = dict(first)
    reordered["statusCheckRollup"] = list(reversed(first["statusCheckRollup"]))
    assert mod._metadata_identity(first) == mod._metadata_identity(reordered)

    changed = dict(first)
    changed["updatedAt"] = "2026-09-16T19:00:01Z"
    assert mod._metadata_identity(first) != mod._metadata_identity(changed)


def test_ready_dossier_is_evidence_not_merge_authorization():
    ready, _ = mod.evaluate(_snapshot(_body()))
    assert ready
    # The result intentionally has no merge/approve decision or mutation API.
    assert not hasattr(mod, "merge")
    assert not hasattr(mod, "approve")


def test_queue_typo_sha_is_blocked_never_ready():
    entry = mod.classify_snapshot(
        _queue_snapshot(head="f" * 39), now=_now()
    )
    assert entry.status == mod.BLOCKED
    assert any("40-character SHA" in reason for reason in entry.reject_cause)


def test_queue_in_flight_checks_contradict_green_claim():
    snapshot = _base_snapshot()
    snapshot["statusCheckRollup"] = [
        {"name": "PR gate", "status": "IN_PROGRESS", "conclusion": None}
    ]
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T09:30:00Z"
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.status == mod.BLOCKED
    assert entry.checks == "in-flight"
    assert "checks in-flight: PR gate" in entry.reject_cause


def test_queue_latest_started_check_wins_over_older_completed_success():
    snapshot = _base_snapshot()
    snapshot["statusCheckRollup"] = [
        {
            "name": "PR gate", "status": "COMPLETED", "conclusion": "SUCCESS",
            "startedAt": "2026-09-17T08:00:00Z",
            "completedAt": "2026-09-17T11:00:00Z",
        },
        {
            "name": "PR gate", "status": "IN_PROGRESS", "conclusion": None,
            "startedAt": "2026-09-17T10:00:00Z",
        },
    ]
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T09:30:00Z"
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.verdict == mod.BLOCKED
    assert entry.checks == "in-flight"


def test_grain_tag_comes_only_from_pr_body():
    snapshot = _base_snapshot()
    snapshot["body"] = "Grain: MED/guard — lane author-lane"
    snapshot["comments"].append(_comment(
        "Bot instructions:\nGrain: <DEEP|MED|LIGHT>/<genre> -- lane placeholder"
    ))

    entry = mod.classify_snapshot(snapshot, now=_now())

    assert entry.grain_tag == "MED/guard — lane author-lane"


def test_comment_cannot_create_a_missing_grain_tag():
    snapshot = _base_snapshot()
    snapshot["comments"].append(_comment("Grain: DEEP/notebook-python -- lane bot"))

    entry = mod.classify_snapshot(snapshot, now=_now())

    assert entry.grain_tag is None


def test_only_missing_exact_head_approval_is_review_ready():
    snapshot = _base_snapshot()
    snapshot["reviews"] = []
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T09:30:00Z"
    ))

    entry = mod.classify_snapshot(snapshot, now=_now())

    assert entry.verdict == mod.REVIEW_READY
    assert not entry.review_qualifying
    assert entry.review_disposition == "unreviewed"
    assert entry.reject_cause == [
        "no qualifying APPROVED review on exact head"
    ]


def test_review_ready_remains_visible_while_dwell_runs():
    snapshot = _base_snapshot()
    snapshot["reviews"] = []
    snapshot["commits"] = [{
        "oid": HEAD, "committedDate": "2026-09-17T11:30:00Z"
    }]
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T11:40:00Z"
    ))

    entry = mod.classify_snapshot(snapshot, now=_now())

    assert entry.verdict == mod.REVIEW_READY
    assert entry.dwell_until == "2026-09-17T13:30:00Z"


def test_latest_changes_requested_prevents_qualifying_review():
    snapshot = _base_snapshot()
    snapshot["reviews"][1].update({
        "id": "approval", "submittedAt": "2026-09-17T08:00:00Z",
        "author": {"login": "reviewer"},
    })
    snapshot["reviews"].append({
        "id": "request", "submittedAt": "2026-09-17T09:00:00Z",
        "author": {"login": "reviewer"},
        "state": "CHANGES_REQUESTED", "commit": {"oid": HEAD},
    })
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T09:30:00Z"
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.verdict == mod.REVIEW_READY
    assert not entry.review_qualifying
    assert entry.review_disposition == "changes-requested"


def test_approval_on_prior_head_is_distinct_review_ready_disposition():
    snapshot = _base_snapshot()
    snapshot["reviews"] = [{
        "id": "approval", "submittedAt": "2026-09-17T08:00:00Z",
        "author": {"login": "reviewer"}, "state": "APPROVED",
        "commit": {"oid": "1" * 40},
    }]
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T09:30:00Z"
    ))

    entry = mod.classify_snapshot(snapshot, now=_now())

    assert entry.verdict == mod.REVIEW_READY
    assert entry.review_disposition == "approval-not-on-head"


def test_later_approval_supersedes_same_reviewers_change_request():
    snapshot = _base_snapshot()
    snapshot["reviews"] = [
        {
            "id": "request", "submittedAt": "2026-09-17T08:00:00Z",
            "author": {"login": "reviewer"}, "state": "CHANGES_REQUESTED",
            "commit": {"oid": HEAD},
        },
        {
            "id": "approval", "submittedAt": "2026-09-17T09:00:00Z",
            "author": {"login": "reviewer"}, "state": "APPROVED",
            "commit": {"oid": HEAD},
        },
    ]
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T09:30:00Z"
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.verdict == mod.READY
    assert entry.review_qualifying


def test_queue_dossier_not_last_comment_is_stale_and_exposes_tail():
    snapshot = _queue_snapshot()
    snapshot["comments"].append(_comment(
        "new concern", created_at="2026-09-17T10:00:00Z"
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.status == mod.STALE
    assert not entry.last_comment_is_dossier
    assert [row["body"] for row in entry.tail_to_read] == ["new concern"]


def test_queue_dwell_pending_until_floor_elapses():
    snapshot = _queue_snapshot()
    snapshot["commits"] = [{"oid": HEAD, "committedDate": "2026-09-17T11:30:00Z"}]
    pending = mod.classify_snapshot(snapshot, now=_now())
    ready = mod.classify_snapshot(
        snapshot,
        now=datetime(2026, 9, 17, 13, 31, tzinfo=timezone.utc),
    )
    assert pending.status == mod.DWELL_PENDING
    assert pending.dwell_until == "2026-09-17T13:30:00Z"
    assert ready.status == mod.READY


def test_dwell_waiver_label_allows_ready_and_is_fingerprinted():
    snapshot = _base_snapshot()
    snapshot["commits"] = [{"oid": HEAD, "committedDate": "2026-09-17T11:30:00Z"}]
    snapshot["labels"] = [{"name": mod.DWELL_WAIVER_LABEL}]
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T11:40:00Z"
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.verdict == mod.READY
    snapshot["labels"] = []
    assert mod.classify_snapshot(snapshot, now=_now()).verdict == mod.DWELL_PENDING


def test_head_timestamp_must_belong_to_exact_head():
    snapshot = _queue_snapshot()
    snapshot["commits"] = [
        {"oid": "f" * 40, "committedDate": "2026-09-01T00:00:00Z"}
    ]
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.verdict == mod.BLOCKED
    assert any("head commit timestamp unavailable" in reason for reason in entry.reject_cause)


def test_dossier_age_becomes_stale_and_zero_disables_age_guard():
    snapshot = _base_snapshot()
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-15T00:00:00Z"
    ))
    stale = mod.classify_snapshot(snapshot, now=_now())
    disabled = mod.classify_snapshot(
        snapshot, now=_now(), stale_after_minutes=0
    )
    assert stale.verdict == mod.STALE
    assert any("stale by age" in reason for reason in stale.reject_cause)
    assert disabled.verdict == mod.READY


def test_latest_failed_check_blocks_queue():
    snapshot = _base_snapshot()
    snapshot["statusCheckRollup"] = [
        {"name": "PR gate", "status": "COMPLETED", "conclusion": "FAILURE"}
    ]
    snapshot["comments"].append(_comment(
        _body(snapshot), created_at="2026-09-17T09:30:00Z"
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.verdict == mod.BLOCKED
    assert entry.checks == "not-green"


def test_queue_unresolved_b0_is_blocked():
    entry = mod.classify_snapshot(
        _queue_snapshot(b0="blocked", verdict="BLOCKED"),
        now=_now(), b0_result=(1, "BLOCKED"),
    )
    assert entry.status == mod.BLOCKED
    assert entry.b0_rc == 1
    assert any("b0 must" in reason for reason in entry.reject_cause)


def test_live_b0_nonzero_blocks_even_when_dossier_claims_clear():
    entry = mod.classify_snapshot(
        _queue_snapshot(), now=_now(), b0_result=(1, "BLOCKED -- live nit")
    )
    assert entry.verdict == mod.BLOCKED
    assert entry.b0_rc == 1
    assert any("B.0 organ blocked" in reason for reason in entry.reject_cause)


def test_stacked_pr_domain_not_applicable_stays_ready():
    snapshot = _base_snapshot()
    snapshot["baseRefName"] = "feature/base-stack"
    snapshot["comments"].append(_comment(
        _body(snapshot, domain="not-applicable"),
        created_at="2026-09-17T09:30:00Z",
    ))
    entry = mod.classify_snapshot(snapshot, now=_now())
    assert entry.status == mod.READY


def test_build_queue_sorts_oldest_first_and_counts_statuses():
    newer = _base_snapshot()
    newer["number"] = 124
    newer["createdAt"] = "2026-09-16T09:00:00Z"
    newer["comments"].append(_comment(
        _body(newer, pr="124"), created_at="2026-09-17T09:30:00Z"
    ))
    older = _queue_snapshot()
    older["createdAt"] = "2026-09-15T09:00:00Z"
    snapshots = {123: older, 124: newer}
    result, complete = mod.build_queue(
        [124, 123, 124], now=_now(), loader=snapshots.__getitem__,
        b0_runner=lambda _pr: (0, "OK"),
    )
    assert complete
    assert [entry["pr"] for entry in result["queue"]] == [123, 124]
    assert all(entry["verdict"] == mod.READY for entry in result["queue"])
    assert result["metrics"]["received"] == 2
    assert result["metrics"][mod.READY] == 2


def test_b0_timeout_classifies_unknown_without_aborting_batch():
    surviving = _base_snapshot()
    surviving["number"] = 124
    surviving["comments"].append(_comment(
        _body(surviving, pr="124"), created_at="2026-09-17T09:30:00Z"
    ))
    snapshots = {124: surviving}

    def b0_runner(pr: int) -> tuple[int, str]:
        if pr == 123:
            raise subprocess.TimeoutExpired("check_unaddressed_nits.py", 120)
        return 0, "OK"

    result, complete = mod.build_queue(
        [123, 124], now=_now(), loader=snapshots.__getitem__,
        b0_runner=b0_runner,
    )

    assert not complete
    assert [entry["pr"] for entry in result["queue"]] == [124]
    assert result["queue"][0]["verdict"] == mod.READY
    assert result["unknown"] == [{
        "pr": 123,
        "error": (
            "UNKNOWN: Command 'check_unaddressed_nits.py' timed out "
            "after 120 seconds"
        ),
    }]
    assert result["metrics"]["received"] == 2
    assert result["metrics"]["classified"] == 1
    assert result["metrics"]["unknown"] == 1


def test_consume_rereads_live_and_fails_closed_on_head_move():
    snapshot = _queue_snapshot()
    calls = 0

    def loader(_pr: int) -> dict:
        nonlocal calls
        calls += 1
        if calls == 1:
            return snapshot
        moved = dict(snapshot)
        moved["headRefOid"] = "f" * 40
        return moved

    queue, complete = mod.build_queue(
        [123], now=_now(), loader=loader, b0_runner=lambda _pr: (0, "OK")
    )
    consumed = mod.consume_pr(
        123, now=_now(), loader=loader, b0_runner=lambda _pr: (0, "OK")
    )
    assert complete and queue["queue"][0]["verdict"] == mod.READY
    assert calls == 2
    assert consumed.status == mod.STALE
    assert any("head is stale" in reason for reason in consumed.reject_cause)
