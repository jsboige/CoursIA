"""Regression tests for calibration preparation in the legacy CLI entrypoints."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import sys
from pathlib import Path

import pytest

pytest.importorskip("agent_framework", reason="prover LLM stack absent (bare CI)")

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

SOURCE = """\
namespace Calibration

def targetValue : Nat := 3

theorem approved_target : targetValue = 3 := by
  decide

end Calibration
"""


def _demo(target: Path) -> dict:
    return {
        "name": "CALIBRATION_TEST",
        "file": str(target),
        "line": 5,
        "sorry_type": "sorry_replacement",
        "theorem_name": "approved_target",
        "description": "Calibration fixture committed with its approved proof.",
    }


def _target(tmp_path: Path) -> Path:
    target = tmp_path / "Calibration.lean"
    target.write_bytes(SOURCE.encode("utf-8"))
    return target


def _args(**overrides) -> argparse.Namespace:
    values = {
        "mode": "autonomous",
        "provider": "offline",
        "max_iterations": 2,
        "hints": "",
    }
    values.update(overrides)
    return argparse.Namespace(**values)


def test_multi_cli_stub_restores_bytes_after_success(
    tmp_path, monkeypatch, capsys
):
    launcher = importlib.import_module("multi_agent_proof")
    target = _target(tmp_path)
    original = target.read_bytes()
    original_hash = hashlib.sha256(original).hexdigest()
    seen = []

    class FakeProver:
        def __init__(self, **kwargs):
            pass

        def prove_sorry(self, demo, **kwargs):
            current = Path(demo["file"]).read_bytes()
            seen.append(current)
            return {"success": False, "iterations": 1, "total_s": 0.0}

    monkeypatch.setattr(launcher, "AutonomousProver", FakeProver)
    result = launcher._prove_demo(
        _demo(target), _args(), launcher.TraceLogger()
    )

    assert result["iterations"] == 1
    assert len(seen) == 1
    assert b":= by sorry" in seen[0]
    assert target.read_bytes() == original
    assert hashlib.sha256(target.read_bytes()).hexdigest() == original_hash
    output = capsys.readouterr().out
    assert "[CALIBRATION_STUB] theorem=approved_target" in output
    assert "[CALIBRATION_RESTORE] approved proof restored" in output


def test_multi_cli_stub_restores_bytes_after_exception(tmp_path, monkeypatch):
    launcher = importlib.import_module("multi_agent_proof")
    target = _target(tmp_path)
    original = target.read_bytes()

    class ExplodingProver:
        def __init__(self, **kwargs):
            pass

        def prove_sorry(self, demo, **kwargs):
            assert b":= by sorry" in Path(demo["file"]).read_bytes()
            raise RuntimeError("provider unavailable")

    monkeypatch.setattr(launcher, "AutonomousProver", ExplodingProver)
    with pytest.raises(RuntimeError, match="provider unavailable"):
        launcher._prove_demo(
            _demo(target), _args(), launcher.TraceLogger()
        )

    assert target.read_bytes() == original


def test_multi_cli_non_calibration_target_is_not_rewritten(
    tmp_path, monkeypatch, capsys
):
    launcher = importlib.import_module("multi_agent_proof")
    target = _target(tmp_path)
    original = target.read_bytes()
    demo = _demo(target)
    demo["sorry_type"] = "full_proof"

    class FakeProver:
        def __init__(self, **kwargs):
            pass

        def prove_sorry(self, demo, **kwargs):
            assert Path(demo["file"]).read_bytes() == original
            return {"success": False, "iterations": 1, "total_s": 0.0}

    monkeypatch.setattr(launcher, "AutonomousProver", FakeProver)
    launcher._prove_demo(demo, _args(), launcher.TraceLogger())

    assert target.read_bytes() == original
    assert "CALIBRATION_STUB" not in capsys.readouterr().out


def test_multi_cli_lean_mode_matches_clean_calibration_before_skip(
    tmp_path, monkeypatch, capsys
):
    launcher = importlib.import_module("multi_agent_proof")
    target = _target(tmp_path)
    original = target.read_bytes()
    demo = _demo(target)
    seen = []

    class FakeTrace:
        def __init__(self, **kwargs):
            pass

        def save(self, name):
            pass

    class FakeProver:
        def __init__(self, **kwargs):
            pass

        def prove_sorry(self, demo, **kwargs):
            seen.append(Path(demo["file"]).read_bytes())
            return {"success": False, "iterations": 1, "total_s": 0.0}

    monkeypatch.setattr(launcher, "DEMOS", {39: demo})
    monkeypatch.setattr(launcher, "TraceLogger", FakeTrace)
    monkeypatch.setattr(launcher, "AutonomousProver", FakeProver)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "multi_agent_proof.py",
            "--lean",
            str(target),
            "--sorry-line",
            "5",
            "--provider",
            "offline",
        ],
    )

    launcher.main()

    assert len(seen) == 1
    assert b":= by sorry" in seen[0]
    assert target.read_bytes() == original
    output = capsys.readouterr().out
    assert "No sorry found" not in output
    assert "Matched DEMO 'CALIBRATION_TEST'" in output
    assert "CALIBRATION_STUB" in output


def test_multi_cli_demo_mode_routes_through_calibration_wrapper(
    tmp_path, monkeypatch, capsys
):
    launcher = importlib.import_module("multi_agent_proof")
    target = _target(tmp_path)
    original = target.read_bytes()
    seen = []

    class FakeTrace:
        def __init__(self, **kwargs):
            pass

        def save(self, name):
            pass

    class FakeProver:
        def __init__(self, **kwargs):
            pass

        def prove_sorry(self, demo, **kwargs):
            seen.append(Path(demo["file"]).read_bytes())
            return {"success": False, "iterations": 1, "total_s": 0.0}

    monkeypatch.setattr(launcher, "DEMOS", {39: _demo(target)})
    monkeypatch.setattr(launcher, "TraceLogger", FakeTrace)
    monkeypatch.setattr(launcher, "AutonomousProver", FakeProver)
    monkeypatch.setattr(
        sys,
        "argv",
        ["multi_agent_proof.py", "--demo", "39", "--provider", "offline"],
    )

    launcher.main()

    assert len(seen) == 1
    assert b":= by sorry" in seen[0]
    assert target.read_bytes() == original
    output = capsys.readouterr().out
    assert "RESULT: FAILED" in output
    assert "CALIBRATION_STUB" in output


def test_multi_cli_batch_prepares_each_calibration_target(
    tmp_path, monkeypatch, capsys
):
    launcher = importlib.import_module("multi_agent_proof")
    target = _target(tmp_path)
    original = target.read_bytes()
    seen = []

    class FakeProver:
        def __init__(self, **kwargs):
            pass

        def prove_sorry(self, demo, **kwargs):
            seen.append(Path(demo["file"]).read_bytes())
            return {"success": False, "iterations": 1, "total_s": 0.0}

    monkeypatch.setattr(launcher, "AutonomousProver", FakeProver)
    monkeypatch.setattr(launcher, "DEMOS", {39: _demo(target)})
    results = launcher._run_batch([39], provider="offline", max_iterations=1)

    assert len(results) == 1
    assert b":= by sorry" in seen[0]
    assert target.read_bytes() == original
    output = capsys.readouterr().out
    assert "CALIBRATION_STUB" in output
    assert "CALIBRATION_RESTORE" in output


def test_positional_cli_prepares_and_restores_calibration(
    tmp_path, monkeypatch, capsys
):
    launcher = importlib.import_module("run_prover")
    target = _target(tmp_path)
    original = target.read_bytes()
    seen = []

    class FakeTrace:
        def __init__(self, **kwargs):
            pass

        def save(self, name):
            pass

    class FakeProver:
        def __init__(self, *args, **kwargs):
            pass

        def prove_sorry(self, demo, **kwargs):
            seen.append(Path(demo["file"]).read_bytes())
            return {"success": False, "iterations": 1, "total_s": 0.0}

    monkeypatch.setattr(launcher, "TraceLogger", FakeTrace)
    monkeypatch.setattr(launcher, "AutonomousProver", FakeProver)
    result = launcher._run_demo(_demo(target), 2, 30, "offline")

    assert result["iterations"] == 1
    assert b":= by sorry" in seen[0]
    assert target.read_bytes() == original
    output = capsys.readouterr().out
    assert "[CALIBRATION_STUB] theorem=approved_target" in output
    assert "[CALIBRATION_RESTORE] approved proof restored" in output


def test_positional_cli_fails_before_write_when_theorem_is_missing(tmp_path):
    launcher = importlib.import_module("run_prover")
    target = _target(tmp_path)
    original = target.read_bytes()
    demo = _demo(target)
    demo["theorem_name"] = "missing_target"

    with pytest.raises(ValueError):
        launcher._run_demo(demo, 2, 30, "offline")

    assert target.read_bytes() == original
