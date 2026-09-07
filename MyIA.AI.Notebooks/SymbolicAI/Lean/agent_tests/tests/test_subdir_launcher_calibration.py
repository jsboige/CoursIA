"""Tests for the #1453 calibration stub in the INNER launcher
(prover/run_prover_bg.py).

Forensic (#1453, measured on demo 39): a ``sorry_type: sorry_replacement``
DEMO targets scaffolding committed WITH its approved proof, so the inner
launcher's dynamic pre-check counted 0 real sorry and returned a FALSE
``already_solved`` — the Conway calibration gradient (DEMOS 39-52) was
dead-on-arrival through this launcher. The fix ports the root-launcher
mechanism (#13907, agent_tests/run_prover_bg.py ``_run_locked``): stub the
approved proof to ``sorry`` in place (0 -> 1 before preflight/spawn), run
under the tree lock, restore the original BYTES in ``finally``.

All tests are offline — MultiAgentSorryProver is replaced by a recording
fake (the LLM boundary), so no provider key is needed. The fixture is
EMBEDDED for the same reason as tests/test_calibration_stub.py: a live
prover run stubs the real Nim.lean in place and a test reading it races
the run.

Run from `agent_tests/`:
    python -m pytest tests/test_subdir_launcher_calibration.py -q
"""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path

import pytest

# The launcher import chain pulls the prover LLM stack
# (agent_framework / agent_framework_openai) — skip cleanly off-stack, same
# pattern as tests/test_bg_tree_lock.py.
_LLM_STACK = "agent_framework"

# Make `prover/` importable regardless of how pytest was invoked.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

DEMO_ID = 39  # the false-already_solved forensic demo

# DEMO39-like shape (conway_lean/Conway/Nim.lean): approved proofs, ZERO real
# sorry token — the committed state the calibration targets start from.
NIM_LIKE = """\
/-
  Fixture DEMO39-like : cible de calibration committed avec sa preuve approuvee.
-/
import Mathlib.Data.List.Basic

namespace Conway
/-- Le nim-sum d'une position : XOR-fold des tailles de tas. -/
def nimSum (heaps : List Nat) : Nat :=
  heaps.foldl (· ^^^ ·) 0

/-- Une position de Nim est gagnante pour le premier joueur ssi son nim-sum est non nul. -/
def isWinningNim (heaps : List Nat) : Bool :=
  nimSum heaps != 0

/-- Ancre prouvee : la position vide a un nim-sum nul. -/
theorem nimSum_nil : nimSum [] = 0 := rfl

/-- CALIBRATION (decide) : la position [3,4,5] est gagnante pour le premier joueur. -/
theorem isWinningNim_345 : isWinningNim [3, 4, 5] = true := by
  decide

/-- CALIBRATION (unfold + zero_xor) : un tas unique a un nim-sum egal a sa taille. -/
theorem nimSum_single (n : Nat) : nimSum [n] = n := by
  simp [nimSum, Nat.xor_zero]

end Conway
"""


def _load():
    """Import the launcher behind the LLM-stack guard."""
    pytest.importorskip(_LLM_STACK, reason="prover LLM stack absent (bare CI)")
    import prover.run_prover_bg as launcher
    from prover.lean_utils import count_real_sorries, stub_theorem_proof

    return launcher, count_real_sorries, stub_theorem_proof


def _make_setup(tmp_path, source):
    """Write a DEMO39-like target + lakefile in tmp_path, return (demo, path)."""
    target = tmp_path / "Nim.lean"
    # newline="\n": stub_theorem_proof hardcodes an LF stub line — keep the
    # whole fixture LF so byte comparisons stay deterministic.
    target.write_text(source, encoding="utf-8", newline="\n")
    (tmp_path / "lakefile.lean").write_text("-- lake", encoding="utf-8")
    demo = {
        "name": "CALIBRATION_CONWAY_NIM_WINNING_345",
        "file": str(target),
        "line": 22,
        "sorry_type": "sorry_replacement",
        "theorem_name": "isWinningNim_345",
        "description": "Calibration: position [3,4,5] is a first-player win.",
        "difficulty": "easy",
    }
    return demo, target


def _patch_fake_prover(monkeypatch, prove_behavior=None, init_raises=None):
    """Replace launcher MultiAgentSorryProver with an offline recording fake.

    The prover class is the LLM boundary: patching it keeps every test
    key-free while the launcher's stub -> preflight -> spawn -> restore
    lifecycle runs for real.
    """
    launcher, count_real_sorries, _ = _load()
    calls = {"constructed": 0, "spawn_sorry_counts": [], "spawn_bytes": []}

    class _FakeProver:
        def __init__(self, **kwargs):
            calls["constructed"] += 1
            if init_raises is not None:
                raise init_raises

        async def prove_sorry(self, demo=None, max_iterations=8, **kwargs):
            raw = Path(demo["file"]).read_bytes()
            calls["spawn_bytes"].append(raw)
            calls["spawn_sorry_counts"].append(
                count_real_sorries(raw.decode("utf-8"))
            )
            if prove_behavior is not None:
                return prove_behavior(demo)
            return {"success": True, "iterations": 1}

    monkeypatch.setattr(launcher, "MultiAgentSorryProver", _FakeProver)
    return calls


def _run(monkeypatch, tmp_path, demo):
    """Run the inner launcher on the fake DEMO_ID, hermetically."""
    launcher, _, _ = _load()
    monkeypatch.setattr(launcher, "DEMOS", {DEMO_ID: demo})
    monkeypatch.setattr(launcher, "PROVED_DEMOS", set())
    traces = tmp_path / "traces"
    traces.mkdir(exist_ok=True)
    monkeypatch.setattr(launcher, "TRACES_DIR", traces)
    return launcher.run_prover(demo_num=DEMO_ID, mode="multi", iterations=1)


# ──────────────────────────────────────────────────────────────────────────
# The fix: sorry_replacement + clean target -> stub, run, restore
# ──────────────────────────────────────────────────────────────────────────


def test_calibration_stub_runs_prover_and_restores(tmp_path, monkeypatch, capsys):
    """DEMO39-like with approved proof: stub 0->1 BEFORE preflight/spawn,
    no false already_solved, original bytes restored exactly after."""
    demo, target = _make_setup(tmp_path, NIM_LIKE)
    original_bytes = target.read_bytes()
    original_sha = hashlib.sha256(original_bytes).hexdigest()

    def _reprove(demo):
        # The "prover" reproduces the approved proof: replaces the stub with
        # a decide proof (bytes-level, no newline translation).
        p = Path(demo["file"])
        p.write_bytes(
            p.read_bytes().replace(
                b"= true := by sorry", b"= true := by\n  decide", 1
            )
        )
        return {"success": True, "iterations": 1}

    calls = _patch_fake_prover(monkeypatch, prove_behavior=_reprove)
    summary = _run(monkeypatch, tmp_path, demo)

    # Not the false already_solved: the preflight saw the STUBBED state.
    assert summary["result_kind"] != "already_solved"
    assert summary["result_kind"] == "sorry_decreased"
    assert summary["original_sorry"] == 1  # 0 -> 1 before the preflight
    assert summary["final_sorry"] == 0
    # The spawn itself saw exactly one sorry on disk (and the stubbed file,
    # not the approved original).
    assert calls["constructed"] == 1
    assert calls["spawn_sorry_counts"] == [1]
    assert b":= by sorry" in calls["spawn_bytes"][0]
    assert calls["spawn_bytes"][0] != original_bytes
    # Same signal tokens as the root launcher (#13907).
    out = capsys.readouterr().out
    assert "[CALIBRATION_STUB] theorem=isWinningNim_345" in out
    assert "[CALIBRATION_RESTORE] approved proof restored" in out
    # Original approved proof restored byte-exact (sha included).
    assert target.read_bytes() == original_bytes
    assert hashlib.sha256(target.read_bytes()).hexdigest() == original_sha


def test_calibration_restore_survives_exception(tmp_path, monkeypatch, capsys):
    """An exception anywhere in the locked run body still restores the
    original bytes — the restore lives in a finally, not on the happy path."""
    demo, target = _make_setup(tmp_path, NIM_LIKE)
    original_bytes = target.read_bytes()

    # Constructor raise escapes _run_prover_locked's internal try (which only
    # wraps prove_sorry), exercising the wrapper's finally directly.
    _patch_fake_prover(
        monkeypatch, init_raises=RuntimeError("provider stack blew up")
    )
    with pytest.raises(RuntimeError, match="provider stack blew up"):
        _run(monkeypatch, tmp_path, demo)

    assert target.read_bytes() == original_bytes
    out = capsys.readouterr().out
    assert "[CALIBRATION_STUB] theorem=isWinningNim_345" in out
    assert "[CALIBRATION_RESTORE] approved proof restored" in out


# ──────────────────────────────────────────────────────────────────────────
# The guards: no stub outside the sorry_replacement + 0-sorry condition
# ──────────────────────────────────────────────────────────────────────────


def test_clean_target_outside_calibration_keeps_skip(tmp_path, monkeypatch, capsys):
    """A full_proof DEMO on a clean file keeps the honest already_solved
    skip — only sorry_replacement stubs."""
    demo, target = _make_setup(tmp_path, NIM_LIKE)
    demo["sorry_type"] = "full_proof"
    original_bytes = target.read_bytes()

    calls = _patch_fake_prover(monkeypatch)
    summary = _run(monkeypatch, tmp_path, demo)

    assert summary["result_kind"] == "already_solved"
    assert calls["constructed"] == 0  # skip: no prover spawned
    out = capsys.readouterr().out
    assert "CALIBRATION_STUB" not in out
    assert "CALIBRATION_RESTORE" not in out
    assert target.read_bytes() == original_bytes


def test_demo_without_sorry_type_never_stubs(tmp_path, monkeypatch, capsys):
    """A DEMO dict with NO sorry_type key (the direct --file/--line shape)
    never stubs — the calibration only applies to declared targets."""
    demo, target = _make_setup(tmp_path, NIM_LIKE)
    demo.pop("sorry_type", None)
    original_bytes = target.read_bytes()

    calls = _patch_fake_prover(monkeypatch)
    summary = _run(monkeypatch, tmp_path, demo)

    assert summary["result_kind"] == "already_solved"
    assert calls["constructed"] == 0
    out = capsys.readouterr().out
    assert "CALIBRATION_STUB" not in out
    assert "CALIBRATION_RESTORE" not in out
    assert target.read_bytes() == original_bytes


def test_sorry_replacement_with_live_sorry_no_stub(tmp_path, monkeypatch, capsys):
    """sorry_replacement target whose file ALREADY carries a real sorry: the
    stub condition (count == 0) is False — run proceeds on the real locus,
    the launcher never rewrites the file."""
    _, _, stub_theorem_proof = _load()
    pre_stubbed = stub_theorem_proof(NIM_LIKE, "isWinningNim_345")
    demo, target = _make_setup(tmp_path, pre_stubbed)
    original_bytes = target.read_bytes()

    calls = _patch_fake_prover(monkeypatch)  # no-op prover
    summary = _run(monkeypatch, tmp_path, demo)

    assert summary["result_kind"] != "already_solved"
    assert calls["spawn_sorry_counts"] == [1]
    # The spawn saw the file untouched (no stub write, no restore).
    assert calls["spawn_bytes"] == [original_bytes]
    out = capsys.readouterr().out
    assert "CALIBRATION_STUB" not in out
    assert "CALIBRATION_RESTORE" not in out
    assert target.read_bytes() == original_bytes
