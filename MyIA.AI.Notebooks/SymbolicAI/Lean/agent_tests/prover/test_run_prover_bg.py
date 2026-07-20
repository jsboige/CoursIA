# Pytest unit coverage for `run_prover_bg._derive_result_kind`.
#
# `_derive_result_kind` is the canonical run-verdict classifier consumed by the
# ai-01 harvest step + BG launcher. It ranks a run dict into one of 8 verdicts
# (crashed > sorry_decreased > structural_only > provider_outage >
# correctly_refused > heartbeat_budget_exceeded > decomposition_regression >
# no_progress). The three forensic verdicts (correctly_refused / heartbeat_
# budget_exceeded / decomposition_regression) were added by #7477 (P2a / P5a /
# P3) to stop mis-classifying legitimate refusals, heartbeat walls, and
# unverified sub-sorry sprays as `no_progress` — which burned iteration_cap
# without distinguishing "agent did the right thing" from "agent spun".
#
# These tests lock the ranking contract so future harness edits (new verdicts,
# re-ordering) must deliberately update or preserve the precedence. The
# function is pure (dict + two ints -> str), so the tests run without an LLM,
# network, or lake build.

import pytest

from run_prover_bg import _derive_result_kind


# --- each verdict in isolation (happy path) ---


def test_crashed_when_error_present():
    # An exception/error in the result is the highest-priority verdict: the run
    # did not complete cleanly, so the sorry count is unreliable regardless of
    # any delta.
    assert _derive_result_kind({"error": "boom"}, final_sorry=5, original_sorry=8) == "crashed"


def test_sorry_decreased_when_count_dropped():
    assert _derive_result_kind({}, final_sorry=5, original_sorry=8) == "sorry_decreased"


def test_structural_only_when_decomposition_landed():
    # A decomposition landed but the textual sorry count did not drop — keep
    # iterating (the sub-sorries are attackable).
    assert _derive_result_kind({"structural_progress": True}, final_sorry=8, original_sorry=8) == "structural_only"


def test_provider_outage_when_flag_set():
    assert _derive_result_kind({"provider_outage": True}, final_sorry=8, original_sorry=8) == "provider_outage"


def test_correctly_refused_when_intractable_p2a():
    # #7477 P2a: the Coordinator explicitly abandoned the goal via
    # mark_sorry_intractable (after F9 Director + B2 SearchAgent gates).
    assert _derive_result_kind({"intractable": True}, final_sorry=8, original_sorry=8) == "correctly_refused"


def test_heartbeat_budget_exceeded_when_flag_set_p5a():
    # #7477 P5a: a Lean tactic blew the maxHeartbeats budget (latched in
    # TacticTools.compile via tools._is_heartbeat_timeout).
    assert _derive_result_kind({"heartbeat_budget_exceeded": True}, final_sorry=8, original_sorry=8) == "heartbeat_budget_exceeded"


def test_decomposition_regression_when_flag_set_p3():
    # #7477 P3: a net-sorry-INCREASE decomposition with ZERO build-verified
    # tactics — an unproven sub-sorry spray the multi-agent path previously
    # mis-labelled as structural_progress.
    assert _derive_result_kind({"decomposition_regression": True}, final_sorry=8, original_sorry=8) == "decomposition_regression"


def test_no_progress_fallthrough():
    # Diagnostic data only — nothing harvestable, nothing pathological.
    assert _derive_result_kind({}, final_sorry=8, original_sorry=8) == "no_progress"


# --- ranking precedence (the #7477 contract: progress outranks pathology) ---


def test_sorry_decreased_outranks_structural_progress():
    # A run that lowered sorry AND landed a decomposition is a harvest, not
    # structural_only.
    assert _derive_result_kind({"structural_progress": True}, final_sorry=5, original_sorry=8) == "sorry_decreased"


def test_sorry_decreased_outranks_heartbeat_budget():
    # A run that lowered the sorry count before blowing the heartbeat budget is
    # still a harvest (P5a is ranked AFTER sorry_decreased).
    assert _derive_result_kind({"heartbeat_budget_exceeded": True}, final_sorry=5, original_sorry=8) == "sorry_decreased"


def test_sorry_decreased_outranks_correctly_refused():
    assert _derive_result_kind({"intractable": True}, final_sorry=5, original_sorry=8) == "sorry_decreased"


def test_structural_only_outranks_provider_outage():
    assert _derive_result_kind({"structural_progress": True, "provider_outage": True}, final_sorry=8, original_sorry=8) == "structural_only"


def test_structural_only_outranks_correctly_refused():
    # A run that landed a verified decomposition before abandoning is still
    # progress (P2a is ranked AFTER structural_only).
    assert _derive_result_kind({"structural_progress": True, "intractable": True}, final_sorry=8, original_sorry=8) == "structural_only"


def test_correctly_refused_outranks_heartbeat_budget():
    assert _derive_result_kind({"intractable": True, "heartbeat_budget_exceeded": True}, final_sorry=8, original_sorry=8) == "correctly_refused"


def test_heartbeat_budget_outranks_decomposition_regression():
    assert _derive_result_kind({"heartbeat_budget_exceeded": True, "decomposition_regression": True}, final_sorry=8, original_sorry=8) == "heartbeat_budget_exceeded"


# --- edge cases / legacy safety ---


def test_none_result_is_no_progress():
    # Non-dict result (legacy autonomous path / old traces): every isinstance
    # check is False, falls through to no_progress.
    assert _derive_result_kind(None, final_sorry=8, original_sorry=8) == "no_progress"


def test_legacy_result_without_forensic_fields():
    # Legacy-safe: a dict without any of the #7477 forensic fields returns the
    # same verdict as before the forensic verdicts were added.
    assert _derive_result_kind({"status": "ok"}, final_sorry=8, original_sorry=8) == "no_progress"


def test_equal_sorry_is_not_decreased():
    # final == original is NOT sorry_decreased (strict <).
    assert _derive_result_kind({}, final_sorry=8, original_sorry=8) == "no_progress"


def test_sorry_increase_is_not_decreased():
    # A net sorry INCREASE without the decomposition_regression flag is still
    # no_progress (the P3 guard is what reclassifies regressions).
    assert _derive_result_kind({}, final_sorry=9, original_sorry=8) == "no_progress"


def test_falsy_flag_values_are_ignored():
    # Explicitly-falsy flag values must not trigger the verdict (the classifier
    # uses truthiness via dict.get).
    result = {
        "error": "",
        "structural_progress": False,
        "provider_outage": False,
        "intractable": False,
        "heartbeat_budget_exceeded": False,
        "decomposition_regression": False,
    }
    assert _derive_result_kind(result, final_sorry=8, original_sorry=8) == "no_progress"
