#!/usr/bin/env python3
"""Le REPL du kernel Lean doit etre couple a la toolchain, ou le kernel echoue (#18511).

Le defaut fautif etait un repli SILENCIEUX : un lake dont la toolchain n'a
pas de REPL construit contre elle (`repl-<tag>`) retombait sur
``~/.elan/bin/repl``, construit pour une autre version de Lean. Chaque cellule
alors rendait une erreur de parse, et papermill sortait quand meme en 0.

Ces tests exercent la LOGIQUE DU TEMPLATE (`REPL_PY_PATCH`), qui est le code
reellement installe dans la fourche `lean4_jupyter` sur la machine : le
template est execute dans un namespace de classe pour que ses fonctions
pures soient testables sans WSL, sans Lean et sans GPU.
"""

import importlib.util
import os
import re
import textwrap
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
ORGAN_PATH = REPO_ROOT / "scripts" / "lean" / "setup_native_lean4_import.py"


def _load_organ():
    spec = importlib.util.spec_from_file_location(
        "setup_native_lean4_import", ORGAN_PATH)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def organ():
    return _load_organ()


@pytest.fixture(scope="module")
def fork(organ):
    """La classe de la fourche, telle qu'elle est splicee dans repl.py."""
    source = ("class Lean4ReplWrapper:\n"
              + textwrap.indent(organ.REPL_PY_PATCH, "    "))
    namespace = {"os": os, "re": re}
    exec(compile(source, "<repl.py fork>", "exec"), namespace)
    return namespace["Lean4ReplWrapper"]


def _write_repl(path, version):
    """Faux binaire REPL portant l'URL de documentation de sa version."""
    path.parent.mkdir(parents=True, exist_ok=True)
    url = b"https://lean-lang.org/doc/reference/" + version + b"/"
    path.write_bytes(b"\x7fELF" + url + b"\x00" * 32)
    return path


@pytest.fixture
def home(tmp_path, monkeypatch):
    """Redirige `~` vers un repertoire temporaire (Windows: USERPROFILE,
    POSIX: HOME)."""
    fake = tmp_path / "home"
    fake.mkdir()
    monkeypatch.setenv("HOME", str(fake))
    monkeypatch.setenv("USERPROFILE", str(fake))
    monkeypatch.delenv("ELAN_TOOLCHAIN", raising=False)
    return fake


def test_repl_lean_version_reads_the_embedded_url(fork, tmp_path):
    repl = _write_repl(tmp_path / "repl", b"4.30.0")
    assert fork._repl_lean_version(str(repl)) == "4.30.0"


def test_repl_lean_version_is_none_when_absent(fork, tmp_path):
    repl = tmp_path / "repl"
    repl.write_bytes(b"rien ici")
    assert fork._repl_lean_version(str(repl)) is None


def test_default_repl_is_accepted_when_its_version_matches(fork, home, tmp_path):
    _write_repl(home / ".elan" / "bin" / "repl", b"4.30.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")

    chosen = fork._repl_for_toolchain(str(lake))
    assert os.path.normpath(chosen) == os.path.normpath(str(home / ".elan" / "bin" / "repl"))


def test_divergent_default_repl_is_refused(fork, home, tmp_path):
    """Le REPL par defaut construit pour une autre version NE PAS servir de
    repli silencieux."""
    _write_repl(home / ".elan" / "bin" / "repl", b"4.29.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")

    with pytest.raises(fork.ReplPairingError) as excinfo:
        fork._repl_for_toolchain(str(lake))
    message = str(excinfo.value)
    assert "4.30.0" in message
    assert "4.29.0" in message
    assert "build-repl" in message


def test_matched_binary_wins_over_the_default(fork, home, tmp_path):
    _write_repl(home / ".elan" / "bin" / "repl", b"4.30.0")
    _write_repl(home / ".elan" / "bin" / "repl-4.33.0", b"4.33.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n", encoding="utf-8")

    chosen = fork._repl_for_toolchain(str(lake))
    assert os.path.normpath(chosen) == os.path.normpath(str(home / ".elan" / "bin" / "repl-4.33.0"))


def test_elan_toolchain_pin_is_used_when_the_lake_has_none(fork, home, tmp_path, monkeypatch):
    """Le wrapper epingle ELAN_TOOLCHAIN : c'est lui qui fait foi quand le
    lake ne declare pas de toolchain."""
    _write_repl(home / ".elan" / "bin" / "repl", b"4.30.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    monkeypatch.setenv("ELAN_TOOLCHAIN", "leanprover/lean4:v4.30.0")

    chosen = fork._repl_for_toolchain(str(lake))
    assert os.path.normpath(chosen) == os.path.normpath(str(home / ".elan" / "bin" / "repl"))


def test_elan_toolchain_pin_divergence_is_refused(fork, home, tmp_path, monkeypatch):
    _write_repl(home / ".elan" / "bin" / "repl", b"4.29.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    monkeypatch.setenv("ELAN_TOOLCHAIN", "leanprover/lean4:v4.30.0")

    with pytest.raises(fork.ReplPairingError):
        fork._repl_for_toolchain(str(lake))


def test_launch_does_not_swallow_the_pairing_error(organ):
    """La fourche attrape `Exception` autour du chemin natif : l'erreur de
    couple doit REMONTER, sinon le repli silencieux revient."""
    template = organ.REPL_PY_PATCH
    assert "except Lean4ReplWrapper.ReplPairingError:" in template
    assert template.index("except Lean4ReplWrapper.ReplPairingError:") < \
        template.index("except Exception:")
