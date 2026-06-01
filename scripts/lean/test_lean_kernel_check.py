"""Tests for scripts/lean/lean_kernel_check.py — canonical kernel.json wrapper check."""

import json
import sys
from pathlib import Path

import pytest

# Add scripts/lean to import path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_kernel_check import (
    CORRECT_PY_WRAPPER,
    OLD_BASH_WRAPPER,
    candidate_kernel_json_paths,
    inspect_kernel_wrapper,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _make_kernel_json(tmp_path: Path, argv: list[str]) -> Path:
    """Create a temporary kernel.json with the given argv."""
    kernel_dir = tmp_path / "kernels" / "lean4-wsl"
    kernel_dir.mkdir(parents=True, exist_ok=True)
    kjson = kernel_dir / "kernel.json"
    kjson.write_text(json.dumps({"argv": argv, "display_name": "Lean 4"}), encoding="utf-8")
    return kjson


# ---------------------------------------------------------------------------
# candidate_kernel_json_paths
# ---------------------------------------------------------------------------

class TestCandidatePaths:
    def test_returns_at_least_one(self):
        paths = candidate_kernel_json_paths("lean4-wsl")
        assert len(paths) >= 1
        assert all(isinstance(p, Path) for p in paths)

    def test_includes_appdata_on_windows(self, monkeypatch):
        monkeypatch.setenv("APPDATA", "C:\\fake\\appdata")
        paths = candidate_kernel_json_paths("lean4-wsl")
        appdata_paths = [p for p in paths if "fake" in str(p)]
        assert len(appdata_paths) == 1

    def test_no_appdata_on_linux(self, monkeypatch):
        monkeypatch.delenv("APPDATA", raising=False)
        paths = candidate_kernel_json_paths("lean4-wsl")
        assert all("AppData" not in str(p) and "appdata" not in str(p).lower() for p in paths)


# ---------------------------------------------------------------------------
# inspect_kernel_wrapper — ok status
# ---------------------------------------------------------------------------

class TestOkStatus:
    def test_correct_python_wrapper(self, tmp_path):
        kjson = _make_kernel_json(tmp_path, [
            "python", str(Path.home() / CORRECT_PY_WRAPPER),
            "{connection_file}",
        ])
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "ok"
        assert "v5 correct" in message

    def test_correct_wrapper_with_fqdn(self, tmp_path):
        kjson = _make_kernel_json(tmp_path, [
            "/usr/bin/python3",
            f"/home/user/{CORRECT_PY_WRAPPER}",
            "{connection_file}",
        ])
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "ok"


# ---------------------------------------------------------------------------
# inspect_kernel_wrapper — error status (regression #1618)
# ---------------------------------------------------------------------------

class TestErrorStatus:
    def test_old_bash_wrapper_detected(self, tmp_path):
        kjson = _make_kernel_json(tmp_path, [
            "bash",
            f"/home/user/{OLD_BASH_WRAPPER}",
            "{connection_file}",
        ])
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "error"
        assert "regression #1618" in message
        assert OLD_BASH_WRAPPER in message

    def test_old_wrapper_in_path(self, tmp_path):
        kjson = _make_kernel_json(tmp_path, [
            "bash", f"/home/user/bin/{OLD_BASH_WRAPPER}", "{connection_file}",
        ])
        status, _ = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "error"


# ---------------------------------------------------------------------------
# inspect_kernel_wrapper — warning status
# ---------------------------------------------------------------------------

class TestWarningStatus:
    def test_missing_kernel_json(self, tmp_path):
        missing = tmp_path / "nonexistent" / "kernel.json"
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(missing))
        assert status == "warning"
        assert "aucun" in message

    def test_unknown_wrapper(self, tmp_path):
        kjson = _make_kernel_json(tmp_path, [
            "python", "/some/unknown/wrapper.py", "{connection_file}",
        ])
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "warning"
        assert "inconnu" in message

    def test_malformed_json(self, tmp_path):
        kernel_dir = tmp_path / "kernels" / "lean4-wsl"
        kernel_dir.mkdir(parents=True, exist_ok=True)
        kjson = kernel_dir / "kernel.json"
        kjson.write_text("{invalid json!!!", encoding="utf-8")
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "warning"
        assert "erreur lecture" in message

    def test_empty_kernel_json(self, tmp_path):
        kernel_dir = tmp_path / "kernels" / "lean4-wsl"
        kernel_dir.mkdir(parents=True, exist_ok=True)
        kjson = kernel_dir / "kernel.json"
        kjson.write_text("{}", encoding="utf-8")
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "warning"
        assert "inconnu" in message

    def test_no_argv_field(self, tmp_path):
        kernel_dir = tmp_path / "kernels" / "lean4-wsl"
        kernel_dir.mkdir(parents=True, exist_ok=True)
        kjson = kernel_dir / "kernel.json"
        kjson.write_text(json.dumps({"display_name": "Lean 4"}), encoding="utf-8")
        status, message = inspect_kernel_wrapper("lean4-wsl", kernel_json_path=str(kjson))
        assert status == "warning"


# ---------------------------------------------------------------------------
# CLI integration (smoke test)
# ---------------------------------------------------------------------------

class TestCLI:
    def test_cli_missing_kernel(self, tmp_path, monkeypatch):
        """CLI should exit 1 when kernel.json not found (no kernel registered)."""
        import subprocess
        result = subprocess.run(
            [sys.executable, "-m", "lean_kernel_check", "--kernel", "nonexistent-test"],
            capture_output=True, text=True,
            cwd=str(Path(__file__).resolve().parent),
        )
        assert result.returncode == 1
        assert "WARNING" in result.stdout or "aucun" in result.stdout
