"""Unit tests for the C4 execution-leftover sweep (#1453 forensic, 2026-09-19).

The 2026-09-19 calibration forensic (po-2024, docs/lean/prover_iteration_history.md)
found that runs reported as complete left untracked files next to their target:
the GoalExtract probe ``_GoalExtract.lean`` (written by ``is_true_placeholder_goal``
/ ``get_goal_state``) and SizeGuard snapshots ``<target>.<random>.sandbox``.
Root cause: the probe loop unlinked only at its return points — any exception
unwound past every cleanup.

Two layers close C4:
- ``get_goal_state`` wraps its probe loop in try/finally (root cause);
- ``sweep_execution_leftovers`` is called from both launchers' ``finally``
  (defence in depth — covers paths the try/finally cannot, e.g. a sandbox
  left by an early SizeGuard exit).

These tests exercise the sweep helper and the root-cause try/finally with a
monkeypatched verifier that raises — no real Lean build is spawned.
"""

from __future__ import annotations

import sys
from pathlib import Path
from unittest import mock

import pytest

# Mirror the conftest used by the other prover test modules.
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from prover.lean_utils import (  # noqa: E402
    get_goal_state,
    sweep_execution_leftovers,
)


# --- sweep_execution_leftovers --------------------------------------------


def test_sweep_removes_probe_and_anchored_sandboxes(tmp_path: Path) -> None:
    target = tmp_path / "ConwayDemo.lean"
    target.write_text("theorem demo : True := trivial\n", encoding="utf-8")
    probe = tmp_path / "_GoalExtract.lean"
    probe.write_text("-- garbage\n", encoding="utf-8")
    anchored = tmp_path / "ConwayDemo.lean.ab12cd.sandbox"
    anchored.write_text("-- snapshot\n", encoding="utf-8")

    removed = sweep_execution_leftovers(str(target))

    removed_names = {p.name for p in removed}
    assert removed_names == {"_GoalExtract.lean", "ConwayDemo.lean.ab12cd.sandbox"}
    assert not probe.exists()
    assert not anchored.exists()
    assert target.exists()  # the target itself is never touched


def test_sweep_keeps_non_anchored_sandboxes(tmp_path: Path) -> None:
    """Narrow scope: a sibling target's sandbox is another crash's evidence."""
    target = tmp_path / "ConwayDemo.lean"
    target.write_text("theorem demo : True := trivial\n", encoding="utf-8")
    foreign = tmp_path / "OtherTarget.lean.xy99zz.sandbox"
    foreign.write_text("-- foreign snapshot\n", encoding="utf-8")

    removed = sweep_execution_leftovers(str(target))

    assert removed == []
    assert foreign.exists()


def test_sweep_keep_sandboxes_removes_probe_only(tmp_path: Path) -> None:
    """keep_sandboxes=True: crash evidence survives, the stale probe does not."""
    target = tmp_path / "ConwayDemo.lean"
    target.write_text("theorem demo : True := trivial\n", encoding="utf-8")
    probe = tmp_path / "_GoalExtract.lean"
    probe.write_text("-- garbage\n", encoding="utf-8")
    anchored = tmp_path / "ConwayDemo.lean.ab12cd.sandbox"
    anchored.write_text("-- snapshot\n", encoding="utf-8")

    removed = sweep_execution_leftovers(str(target), keep_sandboxes=True)

    assert {p.name for p in removed} == {"_GoalExtract.lean"}
    assert not probe.exists()
    assert anchored.exists()


def test_sweep_never_raises_on_missing_files(tmp_path: Path) -> None:
    target = tmp_path / "DoesNotExist.lean"
    # No probe, no sandbox, no target — a cleanup path must stay silent.
    removed = sweep_execution_leftovers(str(target))
    assert removed == []


# --- get_goal_state try/finally (root cause) ------------------------------


def test_get_goal_state_cleans_probe_when_verifier_raises(tmp_path: Path) -> None:
    """Root cause: a verifier crash must not strand the probe file."""
    target = tmp_path / "ConwayDemo.lean"
    target.write_text(
        "theorem demo : True := by\n  sorry\n",
        encoding="utf-8",
    )
    probe = tmp_path / "_GoalExtract.lean"

    fake_verifier = mock.Mock()
    fake_verifier.verify_project_file.side_effect = RuntimeError("kernel died")

    with mock.patch("prover.verifier.get_verifier", return_value=fake_verifier):
        with pytest.raises(RuntimeError, match="kernel died"):
            get_goal_state(str(target), sorry_line=2)

    assert not probe.exists(), (
        "C4 regression: the GoalExtract probe survived a verifier crash"
    )


def test_get_goal_state_cleans_probe_on_exception_no_target_write(
    tmp_path: Path,
) -> None:
    """The probe write itself failing must not leave a partial file either.

    Defensive check that the try/finally sits around the whole probe loop:
    even the first write+verify cycle is covered.
    """
    target = tmp_path / "ConwayDemo.lean"
    target.write_text(
        "theorem demo : True := by\n  sorry\n",
        encoding="utf-8",
    )

    def _boom(_rel: str) -> None:
        raise RuntimeError("subprocess spawn failed")

    fake_verifier = mock.Mock()
    fake_verifier.verify_project_file.side_effect = _boom

    with mock.patch(
        "prover.verifier.get_verifier", return_value=fake_verifier
    ):
        with pytest.raises(RuntimeError, match="subprocess spawn failed"):
            get_goal_state(str(target), sorry_line=2)

    probe = tmp_path / "_GoalExtract.lean"
    assert not probe.exists()
