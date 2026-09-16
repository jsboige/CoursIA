#!/usr/bin/env python3
"""Regression tests for the deployed Lean 4 WSL kernel wrapper (#16181)."""

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[3]
WRAPPER_PATH = (
    REPO_ROOT
    / "MyIA.AI.Notebooks"
    / "SymbolicAI"
    / "Lean"
    / "scripts"
    / "lean4-kernel-wrapper.py"
)
INSTALLER_PATH = (
    REPO_ROOT
    / "MyIA.AI.Notebooks"
    / "GameTheory"
    / "scripts"
    / "setup_wsl_lean4.sh"
)


def _load_wrapper():
    spec = importlib.util.spec_from_file_location("lean4_kernel_wrapper", WRAPPER_PATH)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def wrapper():
    return _load_wrapper()


def test_installer_deploys_versioned_wrapper():
    installer = INSTALLER_PATH.read_text(encoding="utf-8")
    assert '../../SymbolicAI/Lean/scripts/lean4-kernel-wrapper.py' in installer
    assert 'if [ ! -f "$CANONICAL_WRAPPER" ]; then' in installer
    assert 'cp "$CANONICAL_WRAPPER" "$HOME/.lean4-kernel-wrapper.py"' in installer
    assert "bootstrap conserve" not in installer


def test_find_lake_root_starts_from_execution_directory(wrapper, tmp_path):
    lake = tmp_path / "conway_lean"
    notebook_dir = lake / "notebooks" / "companions"
    notebook_dir.mkdir(parents=True)
    (lake / "lakefile.toml").write_text("name = 'conway'\n", encoding="utf-8")

    assert wrapper.find_lake_root(str(notebook_dir)) == str(lake)


def test_find_lake_root_returns_none_outside_lake(wrapper, tmp_path):
    notebook_dir = tmp_path / "notebooks"
    notebook_dir.mkdir()

    assert wrapper.find_lake_root(str(notebook_dir)) is None


def test_main_fails_visibly_without_lake(wrapper, monkeypatch, tmp_path, capsys):
    notebook_dir = tmp_path / "notebooks"
    notebook_dir.mkdir()
    monkeypatch.chdir(notebook_dir)
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])
    monkeypatch.setattr(wrapper.os.path, "expanduser", lambda _: str(tmp_path / "wrapper.log"))

    assert wrapper.main() == 2
    stderr = capsys.readouterr().err
    assert "kernel startup failed" in stderr
    assert "--cwd <lake-root>" in stderr
    assert "notebook_context" not in stderr


def test_entrypoint_propagates_failure_exit_code(tmp_path):
    result = subprocess.run(
        [sys.executable, str(WRAPPER_PATH)],
        cwd=tmp_path,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        timeout=10,
    )

    assert result.returncode == 2
    assert "kernel startup failed" in result.stderr
    assert "--cwd <lake-root>" in result.stderr
