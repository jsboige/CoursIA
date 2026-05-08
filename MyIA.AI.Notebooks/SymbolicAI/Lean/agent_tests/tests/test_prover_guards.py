"""Unit tests for prover guards (lean_server import, stub guard, build check).

These cover the three regressions reported by po-2026 on 2026-05-08:
  #1 CRITICAL — `lean_server.py` import failed silently → compile() always True
  #3 HIGH      — sorry guard ignored non-`sorry` placeholders (`exact _`, ...)
  #2 HIGH      — multi-agent workflow had no per-call timeout → infinite hang

Run from `agent_tests/`:
    python -m pytest tests/ -q
"""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

# Make `prover/` importable regardless of how pytest was invoked.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.state import ProofState, SorryContext  # noqa: E402
from prover.tools import TacticTools  # noqa: E402


# ──────────────────────────────────────────────────────────────────────────
# CRITICAL #1 — lean_server import is path-independent
# ──────────────────────────────────────────────────────────────────────────


def test_lean_server_class_loads_via_spec_import():
    """The verifier's spec-based loader finds lean_server.py one level up."""
    from prover.verifier import _load_lean_verifier_class

    cls = _load_lean_verifier_class()
    assert cls.__name__ == "LeanVerifier"
    # Idempotent — second call returns the cached class.
    assert _load_lean_verifier_class() is cls


def test_get_verifier_instantiates_without_lean_project():
    """get_verifier() must not crash when project_dir is set explicitly."""
    from prover import verifier as vmod

    # Reset module-level singleton so each test starts clean.
    vmod._verifier = None
    v = vmod.get_verifier(project_dir="/tmp/dummy-not-real")
    assert v is not None
    assert v.project_dir == "/tmp/dummy-not-real"


# ──────────────────────────────────────────────────────────────────────────
# HIGH #3 — stub guard rejects non-compiling placeholders
# ──────────────────────────────────────────────────────────────────────────


@pytest.fixture
def tactic_tools(tmp_path):
    """A TacticTools instance against a fake file (no real Lean needed).

    File is padded with realistic boilerplate so the file-size guard
    (which blocks >50% size deltas) does not fire on small edits.
    """
    fake = tmp_path / "Fake.lean"
    body = (
        "import Mathlib.Tactic\n"
        "namespace TestSpace\n"
        + "\n".join(f"-- comment line {i} for size padding" for i in range(50))
        + "\ntheorem t : True := by\n  sorry\n"
        + "\n".join(f"-- trailing line {i} for size padding" for i in range(50))
        + "\nend TestSpace\n"
    )
    fake.write_text(body, encoding="utf-8")
    sorry_line = next(
        i + 1 for i, line in enumerate(body.split("\n")) if "sorry" in line
    )
    state = ProofState(theorem_statement="t")
    sctx = SorryContext(
        filepath=str(fake), sorry_line=sorry_line, indentation=2,
        indent_str="  ", full_file=body,
    )
    tt = TacticTools(state, str(fake), sctx)
    # Stash the sorry line on the instance so tests can reach it.
    tt._test_sorry_line = sorry_line
    return tt


@pytest.mark.parametrize("stub", [
    "exact _",
    "exact ?_",
    "exact ?h",
    "refine ?_",
    "admit",
    "_",
])
def test_stub_guard_rejects_known_placeholders(tactic_tools, stub):
    err = tactic_tools._check_stub_guard(stub, "test")
    assert err is not None
    assert "BLOCKED by stub guard" in err


@pytest.mark.parametrize("ok", [
    "exact h",
    "exact And.intro hp hq",
    "rfl",
    "simp [foo]",
    "omega",
    "intro x; rfl",
    "have h : True := trivial\nexact h",
])
def test_stub_guard_accepts_real_tactics(tactic_tools, ok):
    assert tactic_tools._check_stub_guard(ok, "test") is None


def test_stub_guard_ignores_comments(tactic_tools):
    # A `-- exact _` comment must NOT trigger the guard.
    assert tactic_tools._check_stub_guard("-- exact _\nrfl", "test") is None


# ──────────────────────────────────────────────────────────────────────────
# HIGH #3 — file_replace_sorry rejects stubs without writing
# ──────────────────────────────────────────────────────────────────────────


def test_file_replace_sorry_blocks_exact_underscore(tactic_tools):
    """file_replace_sorry must NOT write a stub replacement to disk."""
    import json
    before = Path(tactic_tools._filepath).read_text(encoding="utf-8")
    # build_check=False keeps the test offline (no lake needed).
    out = json.loads(
        tactic_tools.file_replace_sorry(
            tactic_tools._test_sorry_line, "exact _", build_check=False,
        )
    )
    assert "error" in out
    assert "stub guard" in out["error"]
    after = Path(tactic_tools._filepath).read_text(encoding="utf-8")
    assert before == after  # file untouched


def test_file_replace_sorry_writes_real_tactic(tactic_tools):
    """A real tactic replaces the sorry and the file is updated."""
    import json
    out = json.loads(
        tactic_tools.file_replace_sorry(
            tactic_tools._test_sorry_line, "trivial", build_check=False,
        )
    )
    assert "error" not in out, out
    content = Path(tactic_tools._filepath).read_text(encoding="utf-8")
    assert "sorry" not in content
    assert "trivial" in content


# ──────────────────────────────────────────────────────────────────────────
# HIGH #2 — workflow ProofMessage carries iteration cap
# ──────────────────────────────────────────────────────────────────────────


def test_proof_message_has_iteration_cap_field():
    """ProofMessage must carry max_iterations so the graph can bail out."""
    from prover.workflow import ProofMessage, DEFAULT_AGENT_TIMEOUT_S

    m = ProofMessage(content="x", max_iterations=3)
    assert m.max_iterations == 3
    assert m.iteration == 0
    # Default per-agent timeout is bounded so a stalled provider can't
    # freeze the workflow indefinitely.
    assert 30 <= DEFAULT_AGENT_TIMEOUT_S <= 600


def test_multi_agent_prover_accepts_workflow_timeout():
    """MultiAgentSorryProver.prove_sorry exposes a wall-clock cap."""
    import inspect
    from prover.provers import MultiAgentSorryProver

    sig = inspect.signature(MultiAgentSorryProver.prove_sorry)
    assert "workflow_timeout_s" in sig.parameters
