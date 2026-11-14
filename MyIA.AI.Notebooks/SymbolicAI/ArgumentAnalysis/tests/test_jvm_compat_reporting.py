"""Pytest suite for the two remaining argumentation_lib infrastructure utilities:
`_jvm_compat` (JVM init shim) and `_reporting_noop` (no-op trace reporter).

COMPLETES the argumentation_lib test arc: with _shared_state (#4664),
_state_manager_plugin (#4665), _runner (#4670) already covered, and _config +
_paths exercised by #4664, these two modules were the last untested pieces.
After this file, every vendored module of the shim is under contract.

Durable findings (documented):
- `_jvm_compat` is the JVM-OPTIONAL boundary of the shim: `is_jvm_started()` falls
  back to a module-level flag when `jpype` is absent, and `initialize_jvm()` returns
  False gracefully (never raises) when the Tweety init module is not found. Both
  properties are what make the shim import-safe and runnable without a JVM -- they
  are the contract, so we enforce them (incl. the jpype-absent fallback via a
  sys.modules sentinel).
- `_reporting_noop` replaces a real disk-writing trace analyzer with 7 no-op
  stubs. Their contract is NEGATIVE: they must never write a file, never raise,
  and `save_enhanced_pm_report` must return False (does not persist). We assert
  no file is created on disk.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

# Make `argumentation_lib` importable (../argumentation_lib relative to tests/).
_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_ARG_ANALYSIS_DIR = os.path.dirname(_TESTS_DIR)
if _ARG_ANALYSIS_DIR not in sys.path:
    sys.path.insert(0, _ARG_ANALYSIS_DIR)

import pytest  # noqa: E402

from argumentation_lib import _jvm_compat  # noqa: E402
from argumentation_lib import _reporting_noop as rep  # noqa: E402


# ---------------------------------------------------------------------------
# _jvm_compat fixtures: reset module-level JVM flag + restore cwd
# ---------------------------------------------------------------------------
@pytest.fixture
def jvm_flag_reset():
    saved = _jvm_compat._jvm_initialized
    _jvm_compat._jvm_initialized = False
    yield
    _jvm_compat._jvm_initialized = saved


@pytest.fixture
def preserve_cwd():
    cwd = os.getcwd()
    yield
    os.chdir(cwd)


# ---------------------------------------------------------------------------
# is_jvm_started
# ---------------------------------------------------------------------------
def test_is_jvm_started_returns_bool(jvm_flag_reset):
    assert isinstance(_jvm_compat.is_jvm_started(), bool)


def test_is_jvm_started_falls_back_to_flag_when_jpype_absent(jvm_flag_reset, monkeypatch):
    """When jpype is not importable, is_jvm_started() must return _jvm_initialized."""
    # sentinel: None in sys.modules makes `import jpype` raise ImportError
    monkeypatch.setitem(sys.modules, "jpype", None)
    _jvm_compat._jvm_initialized = False
    assert _jvm_compat.is_jvm_started() is False
    _jvm_compat._jvm_initialized = True
    assert _jvm_compat.is_jvm_started() is True


# ---------------------------------------------------------------------------
# initialize_jvm — cached path + not-found path (no real JVM started)
# ---------------------------------------------------------------------------
def test_initialize_jvm_cached_returns_true_without_chdir(jvm_flag_reset, preserve_cwd):
    """If already initialized, returns True immediately with no side effects."""
    _jvm_compat._jvm_initialized = True
    cwd_before = os.getcwd()
    assert _jvm_compat.initialize_jvm() is True
    assert os.getcwd() == cwd_before  # no chdir happened


def test_initialize_jvm_returns_false_when_tweety_init_missing(
    jvm_flag_reset, preserve_cwd, monkeypatch, tmp_path
):
    """When the Tweety init module is absent, returns False gracefully (no raise)."""
    # Point SYMBOLIC_AI_DIR at an empty tmp dir so <dir>/Tweety/tweety_init.py is absent.
    import argumentation_lib._paths as paths

    monkeypatch.setattr(paths, "SYMBOLIC_AI_DIR", tmp_path)
    cwd_before = os.getcwd()
    result = _jvm_compat.initialize_jvm(verbose=False)
    assert result is False
    assert os.getcwd() == cwd_before  # returned before the chdir
    assert _jvm_compat._jvm_initialized is False  # not cached on failure


def test_initialize_jvm_does_not_propagate_exceptions(
    jvm_flag_reset, preserve_cwd, monkeypatch, tmp_path
):
    """Even if something inside blows up, initialize_jvm must swallow + return False."""
    import argumentation_lib._paths as paths

    monkeypatch.setattr(paths, "SYMBOLIC_AI_DIR", tmp_path)
    # Force the existence check path to raise by replacing Path.exists on a tmp child.
    tweety_dir = tmp_path / "Tweety"
    tweety_dir.mkdir()
    bad = tweety_dir / "tweety_init.py"
    bad.write_text("# not importable")
    # Make the inner `from Tweety.tweety_init import init_tweety` fail by ensuring
    # no Tweety package is on sys.path from tmp_path. initialize_jvm catches Exception.
    result = _jvm_compat.initialize_jvm(verbose=False)
    assert result is False


# ---------------------------------------------------------------------------
# shutdown_jvm
# ---------------------------------------------------------------------------
def test_shutdown_jvm_does_not_raise_when_jpype_absent(jvm_flag_reset, monkeypatch):
    monkeypatch.setitem(sys.modules, "jpype", None)
    _jvm_compat._jvm_initialized = True
    # must not raise
    _jvm_compat.shutdown_jvm()


def test_shutdown_jvm_safe_when_no_jvm_started(jvm_flag_reset, monkeypatch):
    monkeypatch.setitem(sys.modules, "jpype", None)
    _jvm_compat._jvm_initialized = False
    _jvm_compat.shutdown_jvm()
    assert _jvm_compat._jvm_initialized is False


# ---------------------------------------------------------------------------
# _reporting_noop — public surface
# ---------------------------------------------------------------------------
def test_reporting_noop_exposes_seven_symbols():
    for name in (
        "EnhancedGlobalTraceAnalyzer",
        "enhanced_global_trace_analyzer",
        "start_enhanced_pm_capture",
        "stop_enhanced_pm_capture",
        "start_pm_orchestration_phase",
        "capture_shared_state",
        "get_enhanced_pm_report",
        "save_enhanced_pm_report",
    ):
        assert hasattr(rep, name), f"missing noop symbol: {name}"


def test_singleton_is_instance_of_analyzer_class():
    assert isinstance(
        rep.enhanced_global_trace_analyzer, rep.EnhancedGlobalTraceAnalyzer
    )


def test_get_report_returns_empty_dict():
    assert rep.EnhancedGlobalTraceAnalyzer().get_report() == {}
    assert rep.enhanced_global_trace_analyzer.get_report() == {}


def test_get_enhanced_pm_report_returns_empty_dict():
    assert rep.get_enhanced_pm_report() == {}


# ---------------------------------------------------------------------------
# _reporting_noop — NEGATIVE contract: no side effects, never raise
# ---------------------------------------------------------------------------
@pytest.mark.parametrize(
    "fn,args",
    [
        (rep.start_enhanced_pm_capture, ()),
        (rep.stop_enhanced_pm_capture, ()),
        (rep.start_pm_orchestration_phase, ("p1", "Phase 1", ["AgentA", "AgentB"])),
        (rep.capture_shared_state, ("p1", 3, "AgentA", {"x": 1}, {"meta": True})),
    ],
)
def test_noop_functions_return_none_and_do_not_raise(fn, args):
    assert fn(*args) is None


def test_noop_capture_accepts_minimal_args():
    # all args optional -> callable with none
    assert rep.capture_shared_state() is None
    assert rep.start_pm_orchestration_phase("p1") is None


def test_save_enhanced_pm_report_returns_false_and_writes_nothing(tmp_path):
    target = tmp_path / "trace.json"
    result = rep.save_enhanced_pm_report(str(target))
    assert result is False
    assert not target.exists(), "noop save must NOT create a file on disk"


def test_full_noop_cycle_leaves_no_disk_artifacts(tmp_path, monkeypatch):
    """A full capture cycle must not write anything anywhere."""
    monkeypatch.chdir(tmp_path)
    rep.start_enhanced_pm_capture()
    rep.start_pm_orchestration_phase("p1", "Phase 1")
    rep.capture_shared_state("p1", 1, "AgentA", {"k": "v"})
    rep.stop_enhanced_pm_capture()
    rep.save_enhanced_pm_report(str(tmp_path / "out.json"))
    # tmp_path must still be empty (no trace files, no out.json)
    assert list(tmp_path.iterdir()) == []


def test_noop_report_is_stable_singleton():
    """The module-level singleton is a stable object across attribute access."""
    a = rep.enhanced_global_trace_analyzer
    b = rep.enhanced_global_trace_analyzer
    assert a is b
    assert a.get_report() == {}
