"""Causal tests for the adjoint prevalidation entry gate (#16442)."""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_adjoint_prevalidation.py"
spec = importlib.util.spec_from_file_location("check_adjoint_prevalidation", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_adjoint_prevalidation"] = mod
spec.loader.exec_module(mod)

HEAD = "0123456789abcdef0123456789abcdef01234567"


def _comment(body: str, login: str = "jsboige") -> dict:
    return {"author": {"login": login}, "body": body}


def _base_snapshot() -> dict:
    return {
        "number": 123,
        "body": "PR body",
        "headRefOid": HEAD,
        "state": "OPEN",
        "title": "PR title",
        "isDraft": False,
        "baseRefName": "main",
        "comments": [_comment("ordinary earlier comment")],
        "reviews": [{"state": "COMMENTED"}, {"state": "APPROVED"}],
        "threads": [{"isResolved": True}],
        "statusCheckRollup": [{"name": "PR gate", "conclusion": "SUCCESS"}],
        "changedFiles": 3,
        "additions": 42,
        "deletions": 7,
    }


def _body(**changes: str) -> str:
    fields = {
        "schema": "1",
        "lane": "myia-po-2025:CoursIA-2",
        "pr": "123",
        "head": HEAD,
        "complete": "true",
        "body": "read",
        "comments-reviewed": "1",
        "reviews-reviewed": "2",
        "threads-reviewed": "1",
        "threads-unresolved": "0",
        "surfaces-sha256": mod.surfaces_fingerprint(_base_snapshot()),
        "diff-files": "3",
        "diff-additions": "42",
        "diff-deletions": "7",
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
