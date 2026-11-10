"""Offline tests for the ``persist_on_success`` write-back of
``verify_sorry_replacement`` (#21323).

Why this file exists: the persist block of ``verify_sorry_replacement``
(``lean_utils.py``) was NEVER offline-testable. ``test_lean_utils.py``
loads ``lean_utils.py`` directly by file path (bypassing
``prover/__init__.py`` and its agent_framework cascade), but that load has
no package context, so the deferred ``from .verifier import get_verifier``
inside the function raises ImportError — the persist path could only be
exercised through a real verifier. Consequence measured in #21323: the
write-back raised ``NameError`` on ``subdir`` (never assigned) BEFORE
touching the real file, so ``persist_on_success=True`` never worked and
crashed its caller (``workflow.py``'s verify loop) on every success.

Load strategy here: mount ``lean_utils.py`` under a SYNTHETIC package
(``prover_persist_under_test``) whose ``verifier`` submodule is a stub
registered in ``sys.modules`` — the deferred relative import resolves to
the stub without executing the real ``verifier.py`` (no agent_framework,
no Lean toolchain, CI-safe). The fake verifier's
``verify_project_file`` distinguishes the probe (``_SorryVerify.lean``,
returned clean) from the real module (configurable output) so each test
drives the persist decision.

Pins:
  1. Success persists the replacement to the REAL file and the rebuild
     is requested on the PROJECT-RELATIVE path (``Knots/SameFile.lean``,
     no drive letter, no ``subdir`` NameError) — the #21323 regression.
  2. A real-module rebuild error restores the original content
     (``persist_build_failed``).
  3. An implicit-sorry warning in the real rebuild output also restores
     (single-quote wording — the v4.33 backticked wording is carried by
     #21324's regex widening; once merged, this call site inherits it).
  4. ``persist_on_success=False`` never touches the real file.
  5. A filepath that ends up OUTSIDE the derived project root is a
     contract failure (``persist_path_outside_project``), not an uncaught
     ValueError crashing the caller — the escape class NanoClaw flagged on
     #21325; simulated by pointing ``resolve_lake_module`` at a foreign
     root (layout drift, symlinked monorepo).

Run from ``agent_tests/``:
    python -m pytest tests/test_persist_writeback.py -q

See #21323 (this fix), See #1453 (prover co-evolution epic, persist intro).
"""

from __future__ import annotations

import importlib.util
import sys
import types
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

# ── Synthetic package + verifier stub ──────────────────────────────────────
_PKG = "prover_persist_under_test"

if f"{_PKG}.lean_utils" not in sys.modules:
    _pkg = types.ModuleType(_PKG)
    _pkg.__path__ = [str(ROOT / "prover")]  # real dir, unused imports land here
    sys.modules[_PKG] = _pkg

    _verifier_stub = types.ModuleType(f"{_PKG}.verifier")


    class _FakeVerifier:
        """Returns a clean probe build; the real-module output is scripted."""


        def __init__(self, real_output: str = "info: build succeeded"):
            self.real_output = real_output
            self.calls = []  # (relpath, force) pairs, probe first


        def verify_project_file(self, relpath: str, force: bool = False):
            self.calls.append((relpath, force))
            if relpath.endswith("_SorryVerify.lean"):
                return {"success": True, "raw_output": "info: probe ok",
                        "errors": "", "time_s": 0, "backend": "fake"}
            return {"success": "error:" not in self.real_output,
                    "raw_output": self.real_output,
                    "errors": self.real_output, "time_s": 0, "backend": "fake"}


    _ACTIVE = {"verifier": _FakeVerifier()}


    def _fake_get_verifier(project_dir):
        return _ACTIVE["verifier"]


    _verifier_stub.get_verifier = _fake_get_verifier
    sys.modules[f"{_PKG}.verifier"] = _verifier_stub

    _spec = importlib.util.spec_from_file_location(
        f"{_PKG}.lean_utils", ROOT / "prover" / "lean_utils.py",
    )
    lu = importlib.util.module_from_spec(_spec)
    sys.modules[f"{_PKG}.lean_utils"] = lu
    _spec.loader.exec_module(lu)
else:
    lu = sys.modules[f"{_PKG}.lean_utils"]


# ── Fixture: minimal Lake project with one sorried theorem ────────────────

_SOURCE = (
    "def IsNice (n : Nat) : Prop := n = n\n"
    "\n"
    "theorem nice_zero : IsNice 0 := by\n"
    "  sorry\n"
)


@pytest.fixture
def lake_project(tmp_path):
    """tmp Lake project; the sorry sits at line 4 of Knots/SameFile.lean."""
    (tmp_path / "lakefile.toml").write_text('name = "persistt"\n', encoding="utf-8")
    knots = tmp_path / "Knots"
    knots.mkdir()
    f = knots / "SameFile.lean"
    f.write_text(_SOURCE, encoding="utf-8")
    return f


def _run(f, real_output="info: build succeeded", persist=True):
    fake = _FakeVerifier(real_output=real_output)
    _ACTIVE["verifier"] = fake
    result = lu.verify_sorry_replacement(
        str(f), 4, "rfl", persist_on_success=persist,
    )
    return result, fake, f.read_text(encoding="utf-8")


# ── 1. Success persists + project-relative rebuild path ───────────────────

class TestPersistSuccess:
    def test_success_persists_and_targets_project_relative_path(self, lake_project):
        # #21323 regression: on main this call raised NameError (`subdir`
        # undefined) before any write; the caller (workflow.py) crashed.
        result, fake, disk = _run(lake_project)

        assert result["success"] is True
        assert result["persisted"] is True
        assert result["real_build_ok"] is True
        # Real file holds the replacement, sorry gone.
        assert "sorry" not in disk
        assert "rfl" in disk
        # Rebuild asked on the PROJECT-RELATIVE path (no drive letter, no
        # absolute path) — probe first, then the real module.
        assert fake.calls == [
            ("Knots/_SorryVerify.lean", True),
            ("Knots/SameFile.lean", True),
        ]


# ── 2/3. Real-module rejection restores the original ──────────────────────

class TestPersistRestore:
    def test_real_rebuild_error_restores_original(self, lake_project):
        result, fake, disk = _run(
            lake_project,
            real_output="error: Knots/SameFile.lean:4:6: unknown identifier 'rfl'",
        )

        assert result["success"] is False
        assert result["persisted"] is False
        assert result["real_build_ok"] is False
        assert result["error_type"] == "persist_build_failed"
        # Byte-identical restore — the file is never left broken.
        assert disk == _SOURCE
        assert len(fake.calls) == 2  # probe + refused rebuild

    def test_implicit_sorry_in_real_output_restores_original(self, lake_project):
        # Single-quote wording: the historical regex (and the organ it
        # delegates to) catches it. The v4.33 backticked wording is #21324's
        # widening — this call site inherits it once that PR merges.
        result, fake, disk = _run(
            lake_project,
            real_output="warning: Knots/SameFile.lean:4:6: declaration uses 'sorry'",
        )

        assert result["success"] is False
        assert result["persisted"] is False
        assert result["error_type"] == "persist_build_failed"
        assert "implicit_sorry=True" in result["errors"]
        assert disk == _SOURCE


# ── 4. persist_on_success=False leaves the real file untouched ────────────

class TestPersistOptIn:
    def test_no_persist_leaves_file_untouched(self, lake_project):
        result, fake, disk = _run(lake_project, persist=False)

        assert result["success"] is True
        assert result["persisted"] is False
        assert result["real_build_ok"] is None
        assert disk == _SOURCE  # sorry still there
        assert len(fake.calls) == 1  # probe only, no real-module rebuild


# ── 5. filepath outside the derived project root: contract failure ─────────

class TestPersistOutsideProject:
    def test_outside_project_dir_fails_clean_not_crash(
            self, lake_project, monkeypatch):
        # #21325 review (NanoClaw): real_relative used to sit OUTSIDE the
        # try — a filepath not under the derived root raised an UNCAUGHT
        # ValueError, crashing the caller (same escape class as the #21323
        # NameError). Simulate the drift: resolve_lake_module lands on a
        # root that does not contain the file (lakefile found on another
        # subtree after a layout change / symlinked monorepo). The probe's
        # own ValueError fallback keeps the probe path working.
        elsewhere = lake_project.parent / "elsewhere"
        elsewhere.mkdir()
        monkeypatch.setattr(
            lu, "resolve_lake_module", lambda fp: (str(elsewhere), "Other"),
        )
        result, fake, disk = _run(lake_project)

        assert result["success"] is False
        assert result["persisted"] is False
        assert result["real_build_ok"] is False
        assert result["error_type"] == "persist_path_outside_project"
        assert "real file untouched" in result["errors"]
        # Never written, never left broken.
        assert disk == _SOURCE
