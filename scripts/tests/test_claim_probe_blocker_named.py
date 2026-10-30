#!/usr/bin/env python3
"""Tests for the claim-probe blocker-naming predicate (#23098).

The belt draw keeps a candidate servable when the claim probe fails open --
that is deliberate: refusing a grain because the probe could not be read
would starve the pool. But a verdict that **names** its blocker is not a
silent probe: the organ answered, and the answer is negative.

Before the fix, the batch path reduced only the probe's **stdout**, while
the `NOT_SCOPED` verdict is written to **stderr** (the repository's own test
asserts `assert "NOT_SCOPED" in captured.err`). Every occupied candidate
therefore came back as `code=ERROR, human=(ERROR)` -- and `ERROR` is
servable by default, so the belt retained a grain another lane was holding.

These tests pin:
- the reducer sees the blocker when the verdict is on stderr (#23098);
- an `ERROR` that names a blocker is not servable, while a genuinely silent
  `ERROR` stays servable (the fail-open must remain *proven*, not just
  declared);
- the positive control: on the pre-fix behaviour the test fails.

Run: python -m pytest scripts/tests/test_claim_probe_blocker_named.py
"""
from __future__ import annotations

import io
import json
import sys
from contextlib import redirect_stdout
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402
import pick_idle_grain as pig  # noqa: E402


# --------------------------------------------------------------------------
# Fakes
# --------------------------------------------------------------------------

def _summary_json(blocking_lanes=(), active_claims=None, blocked=False):
    """The JSON synthesis the probe prints on stdout."""
    return json.dumps({
        "issue": 19741,
        "my_lane": "myia-po-2024:CoursIA-2",
        "my_active_claim": False,
        "blocking_lanes": list(blocking_lanes),
        "stale_claims": [],
        "active_claims": active_claims or {},
        "blocked": blocked,
    })


NOT_SCOPED_STDERR = (
    "\nNOT_SCOPED: this call did not pass `--paths` so we cannot "
    "prove disjointness on #19741. The blockers below may not actually "
    "conflict with the files you intend to edit.\n"
    "  Blocked-by (legacy `blocking_lanes` field, taken at face value): "
    "myia-po-2028:CoursIA\n"
    "  Claimed scopes (marker-line excerpts -- #10395 Variante 2):\n"
    "  - myia-po-2028:CoursIA: lane myia-po-2028:CoursIA -- PR #23101 -- "
    "paths: docs/reference/gorard-lanyonai-etape3.md\n"
    "  ACTION: re-run with `--paths <glob1> --paths <glob2> ...` matching "
    "the files you intend to edit.\n"
)

BLOCKED_STDOUT = (
    "BLOCKED: another lane holds an active claim on #19741 "
    "(myia-po-2028:CoursIA).\n"
)


# --------------------------------------------------------------------------
# 1. The reducer sees the blocker that lives on stderr
# --------------------------------------------------------------------------

def test_not_scoped_on_stderr_is_reduced_as_blocked():
    """The `NOT_SCOPED` verdict is on stderr; the reducer must read it.

    Pre-fix, the batch reduced stdout only, so `code` was `ERROR` for a
    verdict that named its blocker.
    """
    code = clc._summarize_run_check_output(NOT_SCOPED_STDERR, 2)
    assert code == "BLOCKED", (
        "un verdict NOT_SCOPED qui nomme son bloquant doit etre reduit "
        f"BLOCKED, pas {code!r}")


def test_silent_exit_2_stays_error():
    """A genuinely silent probe stays `ERROR` -- the fail-open class."""
    code = clc._summarize_run_check_output("", 2)
    assert code == "ERROR"


# --------------------------------------------------------------------------
# 2. The blocker-naming predicate
# --------------------------------------------------------------------------

def test_names_a_blocker_on_not_scoped_stderr():
    assert clc._names_a_blocker(NOT_SCOPED_STDERR) is True


def test_names_a_blocker_on_blocked_stdout():
    assert clc._names_a_blocker(BLOCKED_STDOUT) is True


def test_names_a_blocker_from_the_json_blocking_lanes():
    payload = _summary_json(blocking_lanes=["myia-po-2028:CoursIA"])
    assert clc._names_a_blocker("", stdout_json=payload) is True


def test_does_not_name_a_blocker_on_a_silent_probe():
    """A probe that could not be read names nobody -> fail-open preserved."""
    assert clc._names_a_blocker("") is False
    assert clc._names_a_blocker("gh: rate limit exceeded") is False
    assert clc._names_a_blocker(
        "", stdout_json=_summary_json(blocking_lanes=[])) is False


# --------------------------------------------------------------------------
# 3. The picker: a named blocker is not servable, a silent one is
# --------------------------------------------------------------------------

def _batch_result(code, human, blocker_named):
    return {
        "results": {
            "19741": {
                "issue": "19741",
                "exit": 2,
                "code": code,
                "human": human,
                "blocker_named": blocker_named,
            }
        }
    }


def test_picker_refuses_a_candidate_whose_blocker_is_named():
    code, human = pig._summarize_claim_from_batch(
        _batch_result("ERROR", "(ERROR)", True), 19741)
    assert code == pig.CLAIM_CODE_BLOCKED
    assert "bloquant nomme" in human


def test_picker_keeps_the_fail_open_for_a_silent_probe():
    """The fail-open must stay *proven*, not merely declared."""
    code, human = pig._summarize_claim_from_batch(
        _batch_result("ERROR", "(ERROR)", False), 19741)
    assert code == pig.CLAIM_CODE_ERROR


def test_picker_still_maps_the_plain_codes():
    payload = {
        "results": {
            "1": {"code": "FREE", "human": "libre"},
            "2": {"code": "BLOCKED", "human": "bloque"},
            "3": {"code": "IMPLICIT", "human": "PR ouverte"},
        }
    }
    assert pig._summarize_claim_from_batch(payload, 1)[0] == pig.CLAIM_CODE_FREE
    assert pig._summarize_claim_from_batch(payload, 2)[0] == pig.CLAIM_CODE_BLOCKED
    assert pig._summarize_claim_from_batch(payload, 3)[0] == pig.CLAIM_CODE_IMPLICIT


# --------------------------------------------------------------------------
# 4. The positive control -- the pre-fix behaviour must FAIL these tests
# --------------------------------------------------------------------------

def test_positive_control_prefix_behaviour_is_refused():
    """Simulate the pre-fix reducer (stdout only) and prove the outcome differs.

    Pre-fix, the batch fed **stdout only** to the reducer, so a verdict on
    stderr was invisible and the candidate stayed servable. This test
    pins that difference: the pre-fix reduction is NOT a blocker, the
    current one is.
    """
    stdout_only = _summary_json(blocking_lanes=["myia-po-2028:CoursIA"])
    pre_fix_code = clc._summarize_run_check_output(stdout_only, 2)
    assert pre_fix_code == "ERROR"  # the pre-fix path was blind to stderr

    current_code = clc._summarize_run_check_output(
        stdout_only + "\n" + NOT_SCOPED_STDERR, 2)
    assert current_code == "BLOCKED"
