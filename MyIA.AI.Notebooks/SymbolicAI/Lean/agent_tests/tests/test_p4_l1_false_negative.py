"""Unit tests for P4 fuller L1 false-negative fix (#7477, #6790 '(b)/(c) await').

Background (DEMO 62 L2892, 2026-07-16, conway_lean): the autonomous prover
final-verify gate at ``provers.py ~1828-1870`` formerly keyed on
``verify_result["level_1_build"]`` alone, a manifest/cache-sensitive signal
(see ``tools.py::compile``). When the worktree emitted
``warning: manifest out of date`` Lean's ``verifier.success`` flipped to
False while the regex error parser returned ``error_count == 0`` on the
exact same content. The blind revert destroyed a real 5-sub-goal
decomposition (structural progress lost, exhumed only by manual span
extraction).

Fix (#7477 P4): extract ``_evaluate_final_verify(verify_result)`` in
``prover/p4_final_verify.py`` (stdlib-only) that promotes the authoritative
``: error:`` substring contract (#6831, ``prover.tools._parse_lean_errors``)
to the PRIMARY signal and demotes ``level_1_build`` to a secondary
cross-check. A genuine build failure always produces >=1 parseable compile
error in the raw lake output, so promoting the substring contract does not
mask real breakage.

These tests load ``prover/p4_final_verify.py`` by file path (bypassing
``prover/__init__.py`` and the LLM stack) and stub
``prover.tools._parse_lean_errors`` via ``sys.modules`` so the helper's
late-import resolves to a controlled replica of the contract (we test the
P4 wiring, not the parser -- ``_parse_lean_errors`` has its own dedicated
regression suite in ``test_prover_guards.py::test_parse_lean_errors_*``).
"""

from __future__ import annotations

import importlib.util
import re
import sys
import types
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))


# --- stubbed parser (replica of _parse_lean_errors #6831 contract) -----


def _parse_lean_errors_stub(raw_output):
    """Replica of ``prover.tools._parse_lean_errors`` (#6831 contract).

    We stub instead of import because ``prover/tools.py`` has relative
    imports (``from .state`` etc.) that the file-path load of
    ``p4_final_verify.py`` does not bring along. The contract we mirror:
      * regex-first: standard ``<f>:<l>:<c>: error:`` then lake-prefix
        ``error: <f>:<l>:<c>:``
      * substring fallback: ``": error:"`` (module-level)
      * skip probe scratch files ``_GoalExtract.lean`` and
        ``_SorryVerify.lean`` (Pathologie 1b, #6790).
    """
    if raw_output is None:
        raw_output = ""
    elif isinstance(raw_output, (list, tuple)):
        raw_output = "\n".join(str(item) for item in raw_output)
    errors = []
    for line in raw_output.split("\n"):
        if "_GoalExtract.lean" in line or "_SorryVerify.lean" in line:
            continue
        m = re.search(r"(\d+):(\d+): error: (.*)", line)
        if m:
            errors.append({"line": int(m.group(1)), "message": m.group(3)})
            continue
        m = re.search(r"error: .*?(\d+):(\d+): (.*)", line)
        if m:
            errors.append({"line": int(m.group(1)), "message": m.group(3)})
            continue
        if ": error:" in line:
            errors.append({"line": None, "message": line.split(": error:", 1)[1].strip()})
    return errors


# Stub ``prover.tools`` BEFORE loading p4_final_verify so the helper's
# late-import ``from prover.tools import _parse_lean_errors`` resolves.
_fake_tools = types.ModuleType("prover.tools")
_fake_tools._parse_lean_errors = _parse_lean_errors_stub
sys.modules.setdefault("prover.tools", _fake_tools)


# Load p4_final_verify.py DIRECTLY by file path (bypasses prover/__init__.py
# which eagerly imports the LLM stack -- agent_framework /
# agent_framework_openai -- absent on a bare CI runner). Mirrors
# tests/test_bg_tree_lock.py and tests/test_prover_forensic_guards.py.
_p4_spec = importlib.util.spec_from_file_location(
    "prover_p4_final_verify", ROOT / "prover" / "p4_final_verify.py"
)
_p4_final_verify = importlib.util.module_from_spec(_p4_spec)
_p4_spec.loader.exec_module(_p4_final_verify)
_evaluate_final_verify = _p4_final_verify._evaluate_final_verify


# --- DEMO 62 -- the founding incident -----------------------------------


def test_dem62_founding_incoherence_passes_through():
    """THE BUG CASE (DEMO 62 conway_lean L2892, 2026-07-16):
    ``level_1_build=False`` because Lean's verifier flagged the worktree's
    manifest as out-of-date, while the raw lake output contains ZERO
    parseable compile errors (the build actually passed). The historical
    gate on ``level_1_build`` alone destroyed a real 5-sub-goal
    decomposition here. The P4 helper returns ``True`` so the autonomous
    path PRESERVES the build-passing snapshot (mirrors the multi-agent
    path behavior of ``_reverify_compiles_clean`` on the same dict)."""
    incoherent = {
        "success": False,
        "level_1_build": False,
        "error_count": 0,
        "errors": [],
        "sorry_count": 8,
        "raw_output": (
            "warning: manifest out of date: "
            "git revision of dependency 'mathlib' in lockfile differs\n"
            "info: invocation took 18.3s\n"
        ),
    }
    assert _evaluate_final_verify(incoherent) is True, (
        "P4 must NOT gate on level_1_build alone: zero parseable errors in "
        "the raw output means the build passed -- DEMO 62 false-negative "
        "must surface as a build-OK verdict so the 5-sub-goal decomposition "
        "is preserved (not reverted)."
    )


def test_dem62_variant_no_raw_output_falls_back_to_errors_list():
    """Same incoherence but the verifier result carries no ``raw_output``
    field -- only the parsed ``errors`` list (which is empty here). The
    helper falls back to parsing ``errors`` via ``_parse_lean_errors``,
    which treats list input as one entry per item. Empty list -> zero
    errors -> still passes through."""
    incoherent_no_raw = {
        "level_1_build": False,
        "errors": [],
        "error_count": 0,
    }
    assert _evaluate_final_verify(incoherent_no_raw) is True, (
        "When raw_output is absent, the helper must fall back to the "
        "errors list. Zero entries -> build actually passed."
    )


# --- real build failure ------------------------------------------------


def test_real_compile_failure_reverts():
    """A genuine build failure produces >=1 parseable compile error in
    the raw output (``Foo.lean:12:3: error: type mismatch``). The helper
    returns ``False`` regardless of ``level_1_build`` -- a real breakage
    must still trigger revert (the guard never masks it)."""
    real_failure = {
        "level_1_build": False,
        "error_count": 2,
        "errors": [
            {"line": 12, "message": "type mismatch"},
            {"line": 38, "message": "unknown identifier 'foo'"},
        ],
        "raw_output": (
            "Foo.lean:12:3: error: type mismatch\n"
            "  term\n"
            "Foo.lean:38:14: error: unknown identifier 'foo'\n"
        ),
    }
    assert _evaluate_final_verify(real_failure) is False, (
        "Real compile errors in the raw output must ALWAYS gate the verdict "
        "to False -- P4 does not soften the real-failure path."
    )


def test_real_compile_failure_lake_prefix_format():
    """Lake-prefix error format (grain a-2, #6845): ``error: <file>:<l>:<c>:
    <msg>`` -- no ``': error:'`` substring in the conventional middle
    position. ``_parse_lean_errors`` handles it regex-first; the helper
    must still gate the verdict to False."""
    real_failure_lake_prefix = {
        "level_1_build": False,
        "error_count": 1,
        "raw_output": (
            "error: Conway/Life/HashlifeCorrectness.lean:2940:79: "
            "Application type mismatch\n"
        ),
    }
    assert _evaluate_final_verify(real_failure_lake_prefix) is False, (
        "Lake-prefix error format must be detected by _parse_lean_errors "
        "and gate the verdict to False (grain a-2 of #6790)."
    )


def test_real_compile_failure_module_level_error():
    """Module-level error with NO line:col position -- the bare
    ``': error:'`` substring case. ``_parse_lean_errors`` handles it;
    the helper must gate to False."""
    real_failure_module = {
        "level_1_build": False,
        "error_count": 1,
        "raw_output": "HashlifeCorrectness.lean: error: type mismatch\n",
    }
    assert _evaluate_final_verify(real_failure_module) is False, (
        "Module-level error (no line:col) must be detected via the bare "
        "': error:' substring (the regression case for #6831) and gate "
        "the verdict to False."
    )


def test_level_1_build_true_does_not_save_us_from_real_errors():
    """Defensive cross-check: even when ``level_1_build=True`` (the
    historical primary signal would say PASS), if the raw output contains
    a real ``: error:`` substring, the helper MUST return ``False``.
    The substring contract is the primary signal; level_1_build is the
    secondary cross-check only (not the other way around)."""
    real_failure_subordinate = {
        "level_1_build": True,
        "error_count": 0,
        "errors": [],
        "raw_output": "Foo.lean:1:1: error: type mismatch\n",
    }
    assert _evaluate_final_verify(real_failure_subordinate) is False, (
        "level_1_build=True MUST NOT save a real ': error:' substring -- "
        "P4 demotes level_1_build to secondary cross-check, not the gate."
    )


# --- clean pass --------------------------------------------------------


def test_clean_pass_agrees_with_both_signals():
    """A clean pass: ``level_1_build=True`` AND ``error_count=0`` AND no
    parseable compile errors in the raw output. The two signals agree;
    the helper returns ``True``."""
    ok = {
        "success": True,
        "level_1_build": True,
        "error_count": 0,
        "errors": [],
        "sorry_count": 4,
        "raw_output": "info: invocation took 8.1s\n",
    }
    assert _evaluate_final_verify(ok) is True


# --- probe scratch files must not pollute the verdict -----------------


def test_probe_scratch_file_error_does_not_gate_to_false():
    """Goal-extraction and sorry-verify probes emit deliberate compile
    errors (e.g. ``exact ()`` in ``_GoalExtract.lean``) as part of their
    goal-printing mechanism. ``_parse_lean_errors`` SKIPS those lines
    (see ``tools.py`` comment #6790 forensic, GoalExtract miscount /
    Pathologie 1b). A raw_output that mixes a probe error with a genuine
    clean target must gate to True, not False. The helper inherits the
    skip behavior verbatim from ``_parse_lean_errors``."""
    raw_with_probe = (
        "info: probing goal state...\n"
        "error: _GoalExtract.lean:5:8: type mismatch\n"  # probe by design
        "info: done.\n"
    )
    target_only = {
        "level_1_build": False,
        "error_count": 0,
        "errors": [],
        "raw_output": raw_with_probe,
    }
    assert _evaluate_final_verify(target_only) is True, (
        "Probe scratch file errors must be skipped by _parse_lean_errors "
        "(Pathologie 1b fix, #6790) -- the helper must NOT gate on them."
    )


def test_sorry_verify_probe_also_skipped():
    """``_SorryVerify.lean`` is the second probe scratch file (used by
    the sorry-verify step to print goal context). It must also be skipped
    by ``_parse_lean_errors`` and not gate the verdict."""
    raw = "error: _SorryVerify.lean:1:1: sorry\n"
    target = {"level_1_build": False, "raw_output": raw}
    assert _evaluate_final_verify(target) is True


# --- null / None / list input -------------------------------------------


def test_none_raw_output_returns_true():
    """``raw_output=None`` (crash-synthetic verify dict, no Lake output
    at all) and empty ``errors`` list -> zero parseable errors -> the
    helper returns ``True``. The caller's ``_reverify_compiles_clean``
    handles crash conservatism separately (returns False on crash), so
    the helper does NOT need to second-guess crash input -- it just
    reports on the parseable evidence."""
    target = {"level_1_build": False, "errors": [], "raw_output": None}
    assert _evaluate_final_verify(target) is True, (
        "None raw_output + empty errors -> zero parseable errors -> True. "
        "Crash safety is the caller's responsibility (see "
        "_reverify_compiles_clean)."
    )
