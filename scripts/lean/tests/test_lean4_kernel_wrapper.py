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


def test_clean_path_is_built_from_the_user_home(wrapper, monkeypatch, tmp_path):
    """Le PATH du kernel vise ~/.elan/bin et ~/.lean4-venv/bin de l'utilisateur
    courant, jamais un compte code en dur (#17654, D1)."""
    home = tmp_path / "home"
    home.mkdir()
    notebook_dir = tmp_path / "notebooks"
    notebook_dir.mkdir()
    monkeypatch.chdir(notebook_dir)
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.setenv("USERPROFILE", str(home))
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])

    assert wrapper.main() == 2
    entries = wrapper.os.environ["PATH"].split(wrapper.os.pathsep)
    assert entries[:2] == [str(home / ".elan" / "bin"), str(home / ".lean4-venv" / "bin")]


# --------------------------------------------------------------------------
# #18511 -- toolchain einglee, REPL couple, refus sur divergence
# --------------------------------------------------------------------------

REPL_DOC_URL = b"https://lean-lang.org/doc/reference/4.30.0/"


def _write_repl(path, version=b"4.30.0"):
    """Faux binaire REPL portant l'URL de documentation de sa version."""
    path.parent.mkdir(parents=True, exist_ok=True)
    url = b"https://lean-lang.org/doc/reference/" + version + b"/"
    path.write_bytes(b"\x7fELF" + url + b"\x00" * 32)
    return path


def test_find_toolchain_anchor_returns_the_nearest_pin(wrapper, tmp_path):
    root = tmp_path / "series"
    root.mkdir()
    (root / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    nested = root / "sub" / "notebooks"
    nested.mkdir(parents=True)
    (nested / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n", encoding="utf-8")

    assert wrapper.find_toolchain_anchor(str(nested)) == (
        str(nested), "leanprover/lean4:v4.33.0")


def test_find_toolchain_anchor_returns_none_without_pin(wrapper, tmp_path):
    assert wrapper.find_toolchain_anchor(str(tmp_path)) == (None, None)


def test_repl_lean_version_reads_the_embedded_url(wrapper, tmp_path):
    repl = _write_repl(tmp_path / "repl", b"4.30.0")
    assert wrapper.repl_lean_version(str(repl)) == "4.30.0"


def test_repl_lean_version_is_none_when_unreadable(wrapper, tmp_path):
    repl = tmp_path / "repl"
    repl.write_bytes(b"no version here")
    assert wrapper.repl_lean_version(str(repl)) is None


def test_resolve_repl_prefers_the_matched_binary(wrapper, tmp_path):
    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl", b"4.30.0")
    _write_repl(home / ".elan" / "bin" / "repl-4.33.0", b"4.33.0")

    path, version = wrapper.resolve_repl(str(home), "v4.33.0")
    assert path == str(home / ".elan" / "bin" / "repl-4.33.0")
    assert version == "4.33.0"


def test_resolve_repl_accepts_the_default_when_versions_match(wrapper, tmp_path):
    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl", b"4.30.0")

    path, version = wrapper.resolve_repl(str(home), "v4.30.0")
    assert path == str(home / ".elan" / "bin" / "repl")
    assert version == "4.30.0"


def test_resolve_repl_refuses_a_divergent_default(wrapper, tmp_path):
    """Le repl par defaut construit pour une autre version NE PAS servir de
    repli silencieux : c'est lui qui produisait les cellules en erreur de
    parse sous exit 0 (#18511)."""
    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl", b"4.29.0")

    path, version = wrapper.resolve_repl(str(home), "v4.30.0")
    assert path is None
    assert version == "4.29.0"


def test_resolve_repl_refuses_a_mislabelled_matched_binary(wrapper, tmp_path):
    """Un binaire `repl-<tag>` dont la version embarquee differe est refuse
    (incident du 2026-08-21 : un repl-4.32.1 construit pour v4.31.0)."""
    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl-4.32.1", b"4.31.0")

    path, version = wrapper.resolve_repl(str(home), "v4.32.1")
    assert path is None
    assert version == "4.31.0"


def test_resolve_repl_refuses_when_the_default_version_is_unknown(wrapper, tmp_path):
    home = tmp_path / "home"
    (home / ".elan" / "bin").mkdir(parents=True)
    (home / ".elan" / "bin" / "repl").write_bytes(b"version illisible")

    path, version = wrapper.resolve_repl(str(home), "v4.30.0")
    assert path is None
    assert version is None


def test_main_refuses_to_start_on_repl_divergence(wrapper, monkeypatch, tmp_path, capsys):
    """Divergence REPL/toolchain => le kernel ECHOUE (exit 3), il ne rend pas
    des cellules en erreur sous un exit 0."""
    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl", b"4.29.0")
    notebook_dir = tmp_path / "series"
    notebook_dir.mkdir()
    (notebook_dir / "lean-toolchain").write_text(
        "leanprover/lean4:v4.30.0\n", encoding="utf-8")
    monkeypatch.chdir(notebook_dir)
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])
    monkeypatch.setattr(wrapper.os.path, "expanduser", lambda _: str(home))

    assert wrapper.main() == 3
    stderr = capsys.readouterr().err
    assert "kernel startup failed" in stderr
    assert "v4.30.0" in stderr
    assert "4.29.0" in stderr
    assert "build-repl" in stderr


def test_main_pins_the_toolchain_and_exports_it(wrapper, monkeypatch, tmp_path):
    """Le chemin nominal epingle ELAN_TOOLCHAIN sur l'ancrage trouve."""
    import ipykernel.kernelapp as ipk

    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl", b"4.30.0")
    notebook_dir = tmp_path / "series"
    notebook_dir.mkdir()
    (notebook_dir / "lean-toolchain").write_text(
        "leanprover/lean4:v4.30.0\n", encoding="utf-8")
    monkeypatch.chdir(notebook_dir)
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])
    monkeypatch.setattr(wrapper.os.path, "expanduser", lambda _: str(home))

    class _Boom(Exception):
        pass

    def _stop(*args, **kwargs):
        raise _Boom()

    monkeypatch.setattr(ipk.IPKernelApp, "launch_instance", _stop)

    with pytest.raises(SystemExit):
        wrapper.main()
    assert wrapper.os.environ.get("ELAN_TOOLCHAIN") == "leanprover/lean4:v4.30.0"
    # Le repertoire d'execution devient l'ancrage : plus de lacet sur `stable`.
    assert str(Path.cwd()) == str(notebook_dir)


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
