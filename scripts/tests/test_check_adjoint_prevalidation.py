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
        "checkRuns": [
            {
                "id": 1,
                "name": "PR gate",
                "status": "completed",
                "conclusion": "success",
                "started_at": "2026-09-20T10:00:00Z",
                "output": {"title": "PR gate -- all green"},
            }
        ],
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
    """Assert the snapshot yields NO trustworthy dossier, and return why."""
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == ""
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


def test_blocked_preflight_is_a_valid_dossier_but_never_ready():
    """An honest BLOCKED dossier must be distinguishable from an absent one.

    Requiring verdict:READY for exit 0 made the right to READ depend on the state
    of MERGEABILITY, so the coordinator could only open pull requests that were
    already fine -- never the oldest ones, which are old precisely because they
    are blocked. It also pushed the adjoint to write READY just to be visible,
    which measurably produced a false `b0: clear` on a PR with three open HIGH
    findings (#16160). See #16800.
    """
    verdict, errors = mod.evaluate(_snapshot(_body(verdict="BLOCKED")))
    assert verdict == mod.VERDICT_BLOCKED
    assert errors == []


def test_blocked_dossier_still_requires_full_structural_integrity():
    """exit 3 is NOT a softer gate: the fingerprint stays mandatory."""
    for field, value in (
        ("surfaces-sha256", "0" * 64),
        ("head", "f" * 40),
        ("lane", "myia-po-2023:CoursIA"),
        ("complete", "false"),
        ("schema", "2"),
    ):
        errors = _errors(_snapshot(_body(verdict="BLOCKED", **{field: value})))
        assert errors, f"a BLOCKED dossier with a bad {field} must not be trusted"


def test_blocked_dossier_tolerates_the_very_facts_that_block_it():
    """Unresolved threads and a red B.0 refute READY, not BLOCKED.

    Built in the right order on purpose: the unresolved thread is placed BEFORE
    the fingerprint is taken, because the fingerprint covers threads. Computing
    it first and mutating after produces a mismatch -- which is the gate working,
    not a tolerance to test.
    """
    live = _base_snapshot()
    live["threads"] = [{"isResolved": False}]
    dossier = _body(
        verdict="BLOCKED", b0="blocked", checks="BLOCKED", scope="fail",
        domain="fail",
        **{"threads-unresolved": "1",
           "surfaces-sha256": mod.surfaces_fingerprint(live)},
    )
    live["comments"].append(_comment(dossier))
    verdict, errors = mod.evaluate(live)
    assert verdict == mod.VERDICT_BLOCKED, errors


def test_noncanonical_verdict_is_not_a_dossier():
    for bogus in ("ready", "PREFLIGHT_HOLD", "RIPE", ""):
        errors = _errors(_snapshot(_body(verdict=bogus)))
        assert any(error.startswith("verdict must be one of") for error in errors)


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
    # "checks" is deliberately absent: check-runs are no longer a hashed
    # surface (#16957). A conclusion change is caught by the claim
    # verification instead -- see test_red_check_refuses_ready_naming_the_check.
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


# --- The coordinator's own later acts do not expire the dossier (#16800) ------
#
# Measured trap this closes: the gate returned exit 0 on #16072, the coordinator
# read it as authorised, lifted its OWN CHANGES_REQUESTED -- and that very review
# made `reviews-reviewed` stale, so the gate then refused the merge. The act the
# gate authorised invalidated the dossier the gate required. Without this, a PR
# whose only blocker is a coordinator reserve can never be merged without a full
# adjoint round-trip.

T0 = "2026-09-19T00:00:00Z"
T1 = "2026-09-19T01:00:00Z"


def _stamped_snapshot(dossier_body: str) -> dict:
    snapshot = _base_snapshot()
    for row in snapshot["comments"]:
        row.setdefault("createdAt", T0)
    for row in snapshot["reviews"]:
        row.setdefault("submittedAt", T0)
        row.setdefault("author", {"login": "clusterManager-Myia"})
    comment = _comment(dossier_body)
    comment["createdAt"] = T0
    snapshot["comments"].append(comment)
    return snapshot


def _dossier_for(snapshot: dict, **changes: str) -> str:
    """Body whose fingerprint and counts match `snapshot` as it stands."""
    return _body(
        **{
            "surfaces-sha256": mod.surfaces_fingerprint(snapshot),
            "comments-reviewed": str(len(snapshot["comments"])),
            "reviews-reviewed": str(len(snapshot["reviews"])),
            **changes,
        }
    )


def test_coordinator_own_later_review_does_not_expire_the_dossier():
    base = _stamped_snapshot("")
    base["comments"].pop()
    snapshot = _stamped_snapshot(_dossier_for(base))
    snapshot["reviews"].append(
        {
            "state": "APPROVED",
            "author": {"login": mod.COORDINATOR_LOGIN},
            "submittedAt": T1,
            "body": "LIFT -- my own CHANGES_REQUESTED, re-measured at exact head.",
        }
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_coordinator_own_later_comment_does_not_expire_the_dossier():
    base = _stamped_snapshot("")
    base["comments"].pop()
    snapshot = _stamped_snapshot(_dossier_for(base))
    own = _comment("Lifting the stale PREFLIGHT_HOLD.", login=mod.COORDINATOR_LOGIN)
    own["createdAt"] = T1
    snapshot["comments"].append(own)
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_any_other_author_still_expires_the_dossier():
    """The negative control: neutrality is for the coordinator ALONE."""
    for login in ("jsboige", "clusterManager-Myia", "lcetinsoy"):
        base = _stamped_snapshot("")
        base["comments"].pop()
        snapshot = _stamped_snapshot(_dossier_for(base))
        foreign = _comment("a new concern", login=login)
        foreign["createdAt"] = T1
        snapshot["comments"].append(foreign)
        errors = _errors(snapshot)
        assert any("discussion changed after dossier" in e for e in errors), login

        snapshot2 = _stamped_snapshot(_dossier_for(base))
        snapshot2["reviews"].append(
            {"state": "CHANGES_REQUESTED", "author": {"login": login},
             "submittedAt": T1, "body": "new reserve"}
        )
        assert _errors(snapshot2), login


def test_coordinator_review_BEFORE_the_dossier_must_still_be_attested():
    """Neutrality is bounded by time, not by identity alone.

    A coordinator reserve posted before the dossier is exactly what the adjoint
    must have read; neutralising it by author would let a dossier ignore a live
    CHANGES_REQUESTED.
    """
    base = _stamped_snapshot("")
    base["comments"].pop()
    stale_body = _dossier_for(base)
    snapshot = _stamped_snapshot(stale_body)
    snapshot["reviews"].append(
        {"state": "CHANGES_REQUESTED", "author": {"login": mod.COORDINATOR_LOGIN},
         "submittedAt": "2026-09-18T00:00:00Z", "body": "reserve posee AVANT le dossier"}
    )
    assert _errors(snapshot)


# --- Checks are re-verified, not hashed (#16957) --------------------------------
#
# Measured trap this closes: `perimeter review guard (#11268)` starts on a
# review, the adjoint posts the dossier while the guard is in flight, the
# guard concludes SUCCESS -- and the stamp expired on a check nobody wrote.
# 7 of the 54 dossiers at exact head died of this, 4 of them on the same
# guard within three seconds of each other. Hashing the check state both
# guaranteed that race and certified nothing about the `checks:` claim.


def test_check_completing_green_after_dossier_does_not_expire_it():
    """Positive control: a green conclusion after the stamp must not kill it."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"].append(
        {"id": 2, "name": "perimeter review guard (#11268)",
         "status": "completed", "conclusion": "success",
         "started_at": "2026-09-20T11:14:54Z",
         "output": {"title": "perimeter review guard -- pass"}}
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_green_check_may_also_move_the_rollup_after_the_stamp():
    """The rollup is neither hashed (new stamps) nor read for the claim: only
    the per-name latest-wins verdicts of the head's check-runs are."""
    snapshot = _snapshot(_body())
    snapshot["statusCheckRollup"].append(
        {"name": "perimeter review guard (#11268)", "conclusion": "SUCCESS"}
    )
    snapshot["checkRuns"].append(
        {"id": 2, "name": "perimeter review guard (#11268)",
         "status": "completed", "conclusion": "success",
         "started_at": "2026-09-20T11:14:54Z", "output": {}}
    )
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_red_check_refuses_ready_naming_the_check():
    """A red conclusion after the stamp is caught BY NAME, not by hash drift."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 3, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T12:00:00Z",
         "output": {"title": "FAIL -- failing checks: notebook-validate"}}
    ]
    errors = _errors(snapshot)
    assert any(
        "checks claim 'latest-wins-green' is contradicted by live check "
        "'PR gate' (failure; FAIL -- failing checks: notebook-validate)" in error
        for error in errors
    )


def test_lying_dossier_claiming_green_over_a_red_head_is_refused():
    """Decisive negative control: the claim itself is verified.

    Pre-#16957 the hash certified the check STATE at stamp time but never that
    `checks: latest-wins-green` matched it: a dossier could claim green on a
    red head and pass, as long as nobody posted after it. Built with the
    fingerprint computed over the red live state, so ONLY the claim
    verification can refuse it.
    """
    live = _base_snapshot()
    live["checkRuns"] = [
        {"id": 1, "name": "notebook-validate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z",
         "output": {}}
    ]
    dossier = _body(**{"surfaces-sha256": mod.surfaces_fingerprint(live)})
    live["comments"].append(_comment(dossier))
    errors = _errors(live)
    assert any(
        "contradicted by live check 'notebook-validate' (failure)" in error
        for error in errors
    )


def test_latest_wins_picks_the_most_recent_completed_run_per_name():
    """The rollup-twin trap: a cancelled older run must not paint the head red."""
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "cancelled", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "PR gate", "status": "completed",
         "conclusion": "success", "started_at": "2026-09-20T10:05:00Z"},
    ]
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_latest_wins_red_older_run_loses_to_newer_green():
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "PR gate", "status": "completed",
         "conclusion": "success", "started_at": "2026-09-20T10:05:00Z"},
    ]
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_skipped_and_neutral_conclusions_are_not_red():
    snapshot = _snapshot(_body())
    snapshot["checkRuns"] = [
        {"id": 1, "name": "codeql", "status": "completed",
         "conclusion": "skipped", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "coverage", "status": "completed",
         "conclusion": "neutral", "started_at": "2026-09-20T10:01:00Z"},
    ]
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_in_flight_rerun_has_no_verdict_and_hides_nothing():
    """A rerun still in flight cannot veto; the last completed verdict stands --
    green stays ready, red stays refused."""
    green = _snapshot(_body())
    green["checkRuns"].append(
        {"id": 9, "name": "PR gate", "status": "in_progress",
         "conclusion": None, "started_at": "2026-09-20T13:00:00Z"}
    )
    verdict, errors = mod.evaluate(green)
    assert verdict == mod.VERDICT_READY, errors

    red = _snapshot(_body())
    red["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z"},
        {"id": 2, "name": "PR gate", "status": "in_progress",
         "conclusion": None, "started_at": "2026-09-20T13:00:00Z"},
    ]
    assert any("'PR gate'" in error for error in _errors(red))


def test_blocked_dossier_is_not_refuted_by_a_red_check():
    """Claim verification targets the READY claim; a BLOCKED dossier attesting a
    red head is honest and stays a valid dossier (exit 3 semantics, #16800)."""
    live = _base_snapshot()
    live["checkRuns"] = [
        {"id": 1, "name": "PR gate", "status": "completed",
         "conclusion": "failure", "started_at": "2026-09-20T10:00:00Z",
         "output": {"title": "DWELL -- leve au premier balayage"}}
    ]
    dossier = _body(
        verdict="BLOCKED", b0="blocked", checks="BLOCKED", scope="pass",
        domain="not-applicable",
        **{"surfaces-sha256": mod.surfaces_fingerprint(live)},
    )
    live["comments"].append(_comment(dossier))
    verdict, errors = mod.evaluate(live)
    assert verdict == mod.VERDICT_BLOCKED, errors


def test_legacy_stamp_still_accepted_while_checks_unchanged():
    """Backward acceptance: pre-#16957 stamps hashed the rollup as well; both
    digests are valid certificates of the discussion surfaces."""
    legacy = mod.legacy_surfaces_fingerprint(_base_snapshot())
    snapshot = _snapshot(_body(**{"surfaces-sha256": legacy}))
    verdict, errors = mod.evaluate(snapshot)
    assert verdict == mod.VERDICT_READY, errors


def test_legacy_stamp_whose_checks_moved_needs_a_mechanical_restamp():
    """A legacy stamp whose checks moved matches NEITHER digest: the hash
    embedded data that has since changed, and a SHA-256 over changed data
    cannot be re-derived. The refusal names the recovery (--template), and the
    re-stamped dossier can never again be expired by a check conclusion."""
    snapshot = _snapshot(_body(**{
        "surfaces-sha256": mod.legacy_surfaces_fingerprint(_base_snapshot())
    }))
    snapshot["statusCheckRollup"][0]["conclusion"] = "PENDING"
    errors = _errors(snapshot)
    assert any(
        "discussion surfaces changed" in error
        and "--template re-stamp" in error
        for error in errors
    )


def test_surfaces_fingerprint_is_insensitive_to_check_state():
    """The new digest must not move when only checks move -- that is the race
    being closed. The legacy digest still does, which is why it is legacy."""
    base = _base_snapshot()
    moved = _base_snapshot()
    moved["checkRuns"][0]["conclusion"] = "failure"
    moved["statusCheckRollup"] = [{"name": "PR gate", "conclusion": "FAILURE"}]
    assert mod.surfaces_fingerprint(base) == mod.surfaces_fingerprint(moved)
    assert mod.legacy_surfaces_fingerprint(base) != mod.legacy_surfaces_fingerprint(moved)
