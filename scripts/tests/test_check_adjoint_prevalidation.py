"""Causal tests for the adjoint prevalidation entry gate (#16442)."""

import importlib.util
import json
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


# The carrying lane of the default fixture. It must differ from the `lane` of
# `_body()` (the adjoint), or every nominal case would be a self-attestation.
# It is a real tag because an absent one is now a refusal: a dossier can only be
# trusted when the gate can see WHO carries the pull request (#16928).
CARRIER = "myia-po-2026:CoursIA"


def _base_snapshot() -> dict:
    return {
        "number": 123,
        "body": f"Grain: MED/harnais -- lane {CARRIER} -- prev: MED\n\nPR body",
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


def _snapshot_with_body(pr_body: str, **dossier_changes: str) -> dict:
    """Snapshot whose PR body is `pr_body`, attested by a dossier over THAT body.

    `surfaces-sha256` covers the body (see `surfaces_fingerprint`), so the
    fingerprint is taken AFTER the body is set. Mutating the body afterwards
    would perime the dossier and mask the check under test.
    """
    snapshot = _base_snapshot()
    snapshot["body"] = pr_body
    fields = dict(dossier_changes)
    fields["surfaces-sha256"] = mod.surfaces_fingerprint(snapshot)
    snapshot["comments"].append(_comment(_body(**fields)))
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


def test_unknown_lane_cannot_satisfy_gate():
    """A lane outside the cluster set fails closed, as does a malformed string."""
    for lane in ("not-a-lane", "myia-po-9999:CoursIA", ""):
        errors = _errors(_snapshot(_body(lane=lane)))
        assert any(error.startswith("lane must") for error in errors), lane


def test_qualifying_third_party_lane_satisfies_gate():
    """Any cluster lane may attest a pull request it does not carry (#16904).

    The binding constraint is third-party review, not one named lane. Before
    this, `ADJOINT_LANE` made a single lane's throughput the merge throughput of
    the whole repository.
    """
    for lane in ("myia-po-2027:CoursIA", "myia-po-2023:CoursIA", "myia-ai-01:CoursIA"):
        ready, errors = mod.evaluate(_snapshot(_body(lane=lane)))
        assert ready, (lane, errors)
        assert errors == [], lane


def test_lane_carrying_the_pr_cannot_prevalidate_itself():
    """Self-attestation is refused: the `Grain:` tag names the carrying lane."""
    carrier = "myia-po-2027:CoursIA"
    snapshot = _snapshot_with_body(
        "Grain: DEEP/notebook-python -- lane %s -- prev: MED" % carrier, lane=carrier
    )
    errors = _errors(snapshot)
    assert any(error.startswith("self-prevalidation refused") for error in errors)
    # Le refus est le SEUL motif : sans cette assertion, une empreinte perimee
    # ferait passer le test pour la mauvaise raison.
    assert not any(error.startswith("discussion surfaces") for error in errors), errors


def test_third_party_lane_passes_when_carrier_is_declared():
    """A declared carrier does not block a dossier from a different lane."""
    snapshot = _snapshot_with_body(
        "Grain: DEEP/lean -- lane myia-po-2027:CoursIA -- prev: MED",
        lane="myia-po-2025:CoursIA-2",
    )
    ready, errors = mod.evaluate(snapshot)
    assert ready, errors
    assert errors == []


def test_absent_grain_tag_is_not_an_authorization():
    """No readable tag means the self-check CANNOT run -- so the dossier fails.

    The first version of this test passed `lane="not-a-lane"`, so the refusal
    came from the allowlist and the missing tag was never exercised at all: the
    test carried the right name and proved something else, while the code let a
    qualifying lane carrying an untagged PR file its own dossier. A QUALIFYING
    lane is what makes the absent tag the only thing left to refuse on -- hence
    the second assertion, which fails if the allowlist starts doing the work
    again.
    """
    snapshot = _snapshot_with_body(
        "pas de tag Grain ici", lane="myia-po-2023:CoursIA"
    )
    errors = _errors(snapshot)
    assert any(
        error.startswith("carrying lane cannot be established") for error in errors
    )
    assert not any(error.startswith("lane must") for error in errors)


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
    """exit 3 is NOT a softer gate: the fingerprint stays mandatory.

    The bad `lane` must be one that is genuinely DISQUALIFYING. This case read
    `myia-po-2023:CoursIA` while a single lane could attest; #16906 makes that a
    qualifying lane, so it would silently stop testing anything. The assertion
    survives by naming a lane outside `QUALIFYING_LANES`, not by narrowing the
    set back.
    """
    for field, value in (
        ("surfaces-sha256", "0" * 64),
        ("head", "f" * 40),
        ("lane", "myia-po-9999:CoursIA"),
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


def test_truncated_dossier_is_reported_as_malformed():
    """An unclosed block stays refused: its extent is undefined."""
    truncated = _body().replace("\n" + mod.END, "")
    assert "missing closing marker" in _errors(_snapshot(truncated))


def test_prose_after_the_closing_marker_is_ignored_not_refused():
    """The contract is the delimited block; what follows is for a human.

    Refusing it discarded four dossiers in a single cycle whose machine-readable
    block was complete and whose firsthand evidence -- `check_unaddressed_nits`
    rc, comment counts, exact head -- was written below the marker so a reader
    could see it (#16928).
    """
    trailed = _body() + "\n\n### Verifications firsthand\n- B.0 : rc=0, 6 commentaires lus."
    verdict, errors = mod.evaluate(_snapshot(trailed))
    assert verdict == mod.VERDICT_READY, errors
    assert errors == []


def test_trailing_prose_cannot_smuggle_a_contract_field():
    """What the old refusal actually had to protect -- and still does.

    `content` stops at the closing marker, so a field written after it is never
    parsed. Tolerating prose is therefore not tolerating a second, contradicting
    contract: the BLOCKED verdict inside the block wins over the READY written
    below it.
    """
    smuggled = _body(verdict="BLOCKED") + "\nverdict: READY\nb0: clear\nchecks: latest-wins-green"
    verdict, _ = mod.evaluate(_snapshot(smuggled))
    assert verdict == mod.VERDICT_BLOCKED



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


def test_template_renders_the_emitting_lane_not_a_borrowed_name():
    """A lane renders its OWN name, or the self-attestation refusal is defeated.

    A template hardcoding one lane hands every other lane a dossier declaring a
    name that is not its own. The carrying lane could then prevalidate itself
    under a borrowed name and `validate_dossier` would see two different lanes.
    """
    for lane in ("myia-po-2027:CoursIA", "myia-po-2023:CoursIA"):
        template = mod.render_template(_base_snapshot(), lane)
        assert f"lane: {lane}" in template, lane


def test_template_lane_defaults_to_the_adjoint():
    """The adjoint stays the canonical emitter: the default is unchanged."""
    assert f"lane: {mod.ADJOINT_LANE}" in mod.render_template(_base_snapshot())


# ------------------------------------------- the attested reason, exposed (#17290)
#
# On exit 3 the dossier is INTACT -- that is what the code means -- so `errors`
# is [] by construction. The rule then tells the coordinator to "dispatch from
# the dossier's stated reason" while publishing none of it, and re-parsing the
# dossier comment by hand is the only way out. Measured cost: 13 PRs at rc=3 in
# one cycle, 6 of them with a reason that was already dead.
#
# Exposing it must not weaken the gate: a REFUSED dossier is not a fainter
# dossier, and must publish nothing at all.


def test_blocking_fields_name_checks_on_a_checks_blocked_dossier():
    """Controle positif 1 : `checks: BLOCKED`, `b0: clear` -> ["checks"]."""
    snapshot = _snapshot(_body(verdict="BLOCKED", checks="BLOCKED"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert (verdict, errors) == (mod.VERDICT_BLOCKED, [])
    assert mod.blocking_fields(dossier) == ["checks"]


def test_blocking_fields_name_b0_on_a_b0_blocked_dossier():
    """Controle positif 2 : `b0: blocked`, `checks: latest-wins-green` -> ["b0"].

    The two reasons send the work to DIFFERENT places -- a dead `checks` goes to
    the adjoint for a `--template`, a real `b0` goes to the carrying lane for a
    lift sentence. Telling them apart is the whole point of the exposure.
    """
    snapshot = _snapshot(_body(verdict="BLOCKED", b0="blocked"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert (verdict, errors) == (mod.VERDICT_BLOCKED, [])
    assert mod.blocking_fields(dossier) == ["b0"]


def test_blocking_fields_are_listed_in_the_contract_order():
    """A dossier blocked on every field orders them the way the contract does."""
    snapshot = _snapshot(
        _body(verdict="BLOCKED", checks="BLOCKED", b0="blocked", scope="fail",
              domain="fail")
    )
    _, _, dossier = mod.evaluate_with_dossier(snapshot)
    assert mod.blocking_fields(dossier) == ["checks", "b0", "scope", "domain"]


def test_a_blocked_dossier_can_name_no_blocking_field():
    """Honesty edge: the contract ALLOWS a blocked dossier with clear fields.

    `validate_dossier` constrains `checks`/`b0`/`scope`/`domain` only when the
    dossier claims READY. An honest blocked dossier may therefore declare them
    all at their READY value and carry its reason in prose. Reporting [] then is
    the true answer -- inventing a field to fill the silence would fabricate the
    very reason this issue exists to publish.
    """
    snapshot = _snapshot(_body(verdict="BLOCKED"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert (verdict, errors) == (mod.VERDICT_BLOCKED, [])
    assert mod.blocking_fields(dossier) == []


def test_ready_result_publishes_the_dossier_with_no_blocker():
    """Acceptance: rc=0 carries the same block, with `blocking_fields: []`."""
    snapshot = _snapshot(_body())
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    assert result["verdict"] == mod.VERDICT_READY
    assert result["ready"] is True
    assert result["blocking_fields"] == []
    assert result["dossier"]["checks"] == "latest-wins-green"


def test_blocked_result_publishes_the_dossier_and_its_blocker():
    """Acceptance: rc=3 exposes the parsed dossier and a non-empty blocker."""
    snapshot = _snapshot(_body(verdict="BLOCKED", checks="BLOCKED"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    assert result["verdict"] == mod.VERDICT_BLOCKED
    assert result["blocking_fields"] == ["checks"]
    assert result["dossier"]["lane"] == "myia-po-2025:CoursIA-2"
    assert result["dossier"]["head"] == HEAD
    assert result["dossier"]["comment_index"] == 1


def test_a_refused_dossier_is_not_published_at_all():
    """Controle NEGATIF -- the exposure must not launder a refused dossier.

    A dossier whose fingerprint no longer covers the live surfaces is refused
    (rc=1). If the payload published its parsed fields anyway, a referee reading
    the JSON would see a lane, a head and a verdict for a PR the gate just
    rejected -- exactly the confusion the refusal exists to prevent.
    """
    snapshot = _snapshot(_body())
    snapshot["title"] = "mutated after the stamp"
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    assert verdict == "" and dossier is None
    assert errors, "a perimed fingerprint must still be refused"
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    assert result["verdict"] == "NO_DOSSIER"
    assert "dossier" not in result
    assert "blocking_fields" not in result


def test_dossier_payload_publishes_every_read_field():
    """Acceptance: "tous les champs lus" -- the whole contract, not a subset.

    Publishing a curated handful would leave the next consumer re-parsing the
    comment for the field that was left out, which is the defect itself.
    """
    dossier, parse_errors = mod.parse_dossier(_body(), 1, "jsboige", T0)
    assert parse_errors == []
    payload = mod.dossier_payload(dossier)
    assert mod.REQUIRED_FIELDS <= set(payload)
    assert payload["author"] == "jsboige"
    assert payload["created_at"] == T0


def test_result_is_json_serializable():
    """`--json` must actually serialize: a Dossier is not a dict."""
    snapshot = _snapshot(_body(verdict="BLOCKED", b0="blocked"))
    verdict, errors, dossier = mod.evaluate_with_dossier(snapshot)
    result = mod.build_result(123, snapshot, verdict, errors, dossier)
    decoded = json.loads(json.dumps(result, ensure_ascii=False))
    assert decoded["dossier"]["b0"] == "blocked"


def test_evaluate_keeps_its_two_tuple_shape():
    """The gate's historical view is unchanged: no caller moves under it."""
    verdict, errors = mod.evaluate(_snapshot(_body()))
    assert (verdict, errors) == (mod.VERDICT_READY, [])
