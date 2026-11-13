#!/usr/bin/env python3
"""Regression tests for the deployed Lean 4 WSL kernel wrapper (#16181)."""

import importlib.util
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest


def _symlinks_available():
    """Le shim du wrapper est un lien symbolique : sous Windows sans le
    privilege de creer des liens, `os.symlink` echoue et le wrapper refuse
    alors de demarrer, ce qui est son comportement voulu. Le wrapper, lui, ne
    tourne que sous Linux ou WSL."""
    with tempfile.TemporaryDirectory() as directory:
        try:
            os.symlink(os.path.join(directory, "target"),
                       os.path.join(directory, "link"))
        except (OSError, NotImplementedError):
            return False
    return True


needs_symlink = pytest.mark.skipif(
    not _symlinks_available(),
    reason="le shim du wrapper exige os.symlink (indisponible ici)")


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
NATIVE_INSTALLER_PATH = INSTALLER_PATH.with_name("setup_lean4_native.sh")


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
    assert 'cp "$CANONICAL_WRAPPER" "$WRAPPER_PATH"' in installer
    assert "bootstrap conserve" not in installer


@pytest.mark.parametrize(
    ("language", "argv", "returncode"),
    [
        ("lean4", ["python", "/tmp/lean4-kernel-wrapper.py", "-f", "{connection_file}"], 0),
        ("python", ["python", "-m", "ipykernel_launcher", "-f", "{connection_file}"], 1),
    ],
)
def test_native_installer_check_verifies_the_real_kernel_class(
    tmp_path, language, argv, returncode
):
    """`lean4` is a language/wrapper contract, not just a kernelspec name."""
    import json
    import os

    elan_home = tmp_path / "elan"
    venv = tmp_path / "venv"
    mockbin = tmp_path / "bin"
    inventory = tmp_path / "kernelspecs.json"
    (elan_home / "bin").mkdir(parents=True)
    (venv / "bin").mkdir(parents=True)
    mockbin.mkdir()

    for name, body in {
        "elan": "#!/bin/sh\necho 'Lean (version 4.33.0)'\n",
        "repl": "#!/bin/sh\nexit 0\n",
    }.items():
        executable = elan_home / "bin" / name
        executable.write_text(body, encoding="utf-8")
        executable.chmod(0o755)
    python_stub = venv / "bin" / "python3"
    python_stub.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
    python_stub.chmod(0o755)
    jupyter = mockbin / "jupyter"
    jupyter.write_text(f'#!/bin/sh\ncat "{inventory}"\n', encoding="utf-8")
    jupyter.chmod(0o755)
    inventory.write_text(json.dumps({"kernelspecs": {
        "lean4-wsl": {"spec": {"language": language, "argv": argv}}
    }}), encoding="utf-8")

    env = os.environ.copy()
    env.update({
        "ELAN_HOME": str(elan_home),
        "LEAN4_VENV": str(venv),
        "PATH": str(mockbin) + os.pathsep + env["PATH"],
    })
    result = subprocess.run(
        ["bash", str(NATIVE_INSTALLER_PATH), "--check"],
        cwd=REPO_ROOT,
        env=env,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == returncode, result.stdout + result.stderr
    if returncode:
        assert "noyau IPython ne convient pas" in result.stdout
    else:
        assert "language=lean4, wrapper Lean" in result.stdout


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


def test_clean_path_honors_explicit_install_paths(wrapper, monkeypatch, tmp_path):
    home = tmp_path / "home"
    home.mkdir()
    elan_home = tmp_path / "toolchains" / "elan"
    venv = tmp_path / "venvs" / "lean4"
    notebook_dir = tmp_path / "notebooks"
    notebook_dir.mkdir()
    monkeypatch.chdir(notebook_dir)
    monkeypatch.setenv("HOME", str(home))
    monkeypatch.setenv("ELAN_HOME", str(elan_home))
    monkeypatch.setenv("LEAN4_VENV", str(venv))
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])

    assert wrapper.main() == 2
    entries = wrapper.os.environ["PATH"].split(wrapper.os.pathsep)
    assert entries[:2] == [str(elan_home / "bin"), str(venv / "bin")]


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


def test_resolve_repl_supports_an_explicit_elan_home(wrapper, tmp_path):
    home = tmp_path / "home"
    elan_home = tmp_path / "toolchains" / "elan"
    _write_repl(elan_home / "bin" / "repl-4.33.0", b"4.33.0")

    path, version = wrapper.resolve_repl(
        str(home), "v4.33.0", elan_home=str(elan_home))
    assert path == str(elan_home / "bin" / "repl-4.33.0")
    assert version == "4.33.0"


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
    # La commande suggeree doit etre recevable : `build-repl` prend le tag
    # avec son `v` (cles de REPL_TOOLCHAIN_TAGS).
    assert "build-repl v4.30.0" in stderr


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


# --------------------------------------------------------------------------
# #24913 -- le binaire apparie est celui qui tourne, ou le noyau refuse
# --------------------------------------------------------------------------

class _LegacyFork:
    """lean4_jupyter anterieur a LEAN4_JUPYTER_REPL, hors lake : `lake env repl`."""


class _PairedFork:
    """lean4_jupyter qui lance le binaire exporte par le wrapper."""

    @staticmethod
    def _repl_from_caller():
        return None


def _legacy_fork_with_table(chosen):
    class _Fork:
        @staticmethod
        def _repl_for_toolchain(lake_root):
            return chosen
    return _Fork


def test_legacy_target_is_none_for_a_fork_that_reads_the_variable(wrapper, tmp_path):
    default = _write_repl(tmp_path / "bin" / "repl", b"4.33.0")
    assert wrapper.legacy_launch_target(_PairedFork, None, str(default)) is None


def test_legacy_target_outside_a_lake_is_the_default_repl(wrapper, tmp_path):
    """`lake env` met ~/.elan/bin en tete du PATH : le REPL par defaut gagne."""
    default = _write_repl(tmp_path / "bin" / "repl", b"4.33.0")
    assert wrapper.legacy_launch_target(_LegacyFork, None, str(default)) == str(default)


def test_legacy_target_without_default_repl_is_the_shim(wrapper, tmp_path):
    """Sans ~/.elan/bin/repl, `lake env repl` trouve le shim : rien a refuser."""
    assert wrapper.legacy_launch_target(_LegacyFork, None, str(tmp_path / "repl")) is None


def test_legacy_target_in_a_lake_is_the_fork_table_choice(wrapper, tmp_path):
    chosen = _write_repl(tmp_path / "bin" / "repl-4.30.0-rc2", b"4.30.0")
    default = _write_repl(tmp_path / "bin" / "repl", b"4.33.0")
    fork = _legacy_fork_with_table(str(chosen))
    assert wrapper.legacy_launch_target(fork, str(tmp_path), str(default)) == str(chosen)


def _series_with_two_repls(tmp_path):
    """Arbre ancre en v4.30.0 sur une machine qui porte deux REPL."""
    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl", b"4.33.0")
    paired = _write_repl(home / ".elan" / "bin" / "repl-4.30.0", b"4.30.0")
    series = tmp_path / "series"
    series.mkdir()
    (series / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    return home, series, paired


def _install_fake_fork(monkeypatch, fork_cls):
    import types
    package = types.ModuleType("lean4_jupyter")
    module = types.ModuleType("lean4_jupyter.repl")
    module.Lean4ReplWrapper = fork_cls
    package.repl = module
    monkeypatch.setitem(sys.modules, "lean4_jupyter", package)
    monkeypatch.setitem(sys.modules, "lean4_jupyter.repl", module)


@needs_symlink
def test_main_refuses_a_fork_that_would_run_another_version(wrapper, monkeypatch,
                                                           tmp_path, capsys):
    """Le fork ancien lancerait le REPL par defaut (4.33.0) sur un arbre en
    v4.30.0 : cellules en erreur sous exit 0. Le noyau refuse de demarrer."""
    home, series, paired = _series_with_two_repls(tmp_path)
    _install_fake_fork(monkeypatch, _LegacyFork)
    monkeypatch.chdir(series)
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])
    monkeypatch.setattr(wrapper.os.path, "expanduser", lambda _: str(home))

    assert wrapper.main() == 3
    stderr = capsys.readouterr().err
    assert "ignores LEAN4_JUPYTER_REPL" in stderr
    assert "4.33.0" in stderr
    assert str(paired) in stderr
    assert "setup_native_lean4_import.py install" in stderr


@needs_symlink
def test_main_exports_the_paired_repl_to_a_fork_that_reads_it(wrapper, monkeypatch,
                                                              tmp_path):
    import ipykernel.kernelapp as ipk

    home, series, paired = _series_with_two_repls(tmp_path)
    _install_fake_fork(monkeypatch, _PairedFork)
    monkeypatch.chdir(series)
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.delenv("LEAN4_JUPYTER_REPL", raising=False)
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])
    monkeypatch.setattr(wrapper.os.path, "expanduser", lambda _: str(home))

    def _stop(*args, **kwargs):
        raise SystemExit(0)

    monkeypatch.setattr(ipk.IPKernelApp, "launch_instance", _stop)

    with pytest.raises(SystemExit):
        wrapper.main()
    assert wrapper.os.environ.get("LEAN4_JUPYTER_REPL") == str(paired)


def test_main_accepts_a_legacy_fork_when_versions_agree(wrapper, monkeypatch, tmp_path):
    """Un seul REPL, a la version de l'ancrage : le fork ancien lance le bon
    binaire, le noyau demarre comme avant."""
    import ipykernel.kernelapp as ipk

    home = tmp_path / "home"
    _write_repl(home / ".elan" / "bin" / "repl", b"4.30.0")
    series = tmp_path / "series"
    series.mkdir()
    (series / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    _install_fake_fork(monkeypatch, _LegacyFork)
    monkeypatch.chdir(series)
    monkeypatch.setenv("PATH", wrapper.os.environ["PATH"])
    monkeypatch.setattr(wrapper.sys, "argv", ["lean4-kernel-wrapper.py"])
    monkeypatch.setattr(wrapper.os.path, "expanduser", lambda _: str(home))

    def _stop(*args, **kwargs):
        raise SystemExit(0)

    monkeypatch.setattr(ipk.IPKernelApp, "launch_instance", _stop)

    with pytest.raises(SystemExit):
        wrapper.main()


def test_repl_lean_version_keeps_the_rc_suffix(wrapper, tmp_path):
    """Une toolchain rc embarque `.../reference/4.33.0-rc1/` (mesure)."""
    repl = _write_repl(tmp_path / "repl", b"4.33.0-rc1")
    assert wrapper.repl_lean_version(str(repl)) == "4.33.0-rc1"


def test_resolve_repl_accepts_a_matched_rc_binary(wrapper, tmp_path):
    """Avant : la version lue s'arretait a `4.33.0`, et le binaire rc
    correctement construit etait refuse."""
    _write_repl(tmp_path / ".elan" / "bin" / "repl-4.33.0-rc1", b"4.33.0-rc1")
    path, version = wrapper.resolve_repl(str(tmp_path), "v4.33.0-rc1")
    assert path is not None and path.endswith("repl-4.33.0-rc1")
    assert version == "4.33.0-rc1"


def test_resolve_repl_refuses_an_rc_default_for_a_release_pin(wrapper, tmp_path):
    """Temoin du precedent : un REPL construit sur le rc ne passe plus pour
    la release."""
    _write_repl(tmp_path / ".elan" / "bin" / "repl", b"4.33.0-rc1")
    path, version = wrapper.resolve_repl(str(tmp_path), "v4.33.0")
    assert path is None
    assert version == "4.33.0-rc1"
