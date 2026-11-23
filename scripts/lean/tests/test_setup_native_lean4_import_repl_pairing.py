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




def test_pairing_error_suggests_the_build_repl_tag_with_its_v(fork, home, tmp_path):
    """`build-repl` n'accepte que les tags de REPL_TOOLCHAIN_TAGS, qui portent
    leur `v` : la commande suggeree doit etre recevable telle quelle."""
    _write_repl(home / ".elan" / "bin" / "repl", b"4.29.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")

    with pytest.raises(fork.ReplPairingError) as excinfo:
        fork._repl_for_toolchain(str(lake))
    assert "build-repl v4.30.0" in str(excinfo.value)


# --------------------------------------------------------------------------
# #24913 -- tag compare exactement, binaire apparie par le wrapper
# --------------------------------------------------------------------------

def test_rc_lake_is_not_served_the_release_repl(fork, home, tmp_path):
    """Une comparaison par sous-chaine faisait servir `repl-4.33.0` a un lake
    en `v4.33.0-rc1` (`'v4.33.0' in 'leanprover/lean4:v4.33.0-rc1'`)."""
    _write_repl(home / ".elan" / "bin" / "repl-4.33.0", b"4.33.0")
    _write_repl(home / ".elan" / "bin" / "repl-4.33.0-rc1", b"4.33.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lean-toolchain").write_text(
        "leanprover/lean4:v4.33.0-rc1\n", encoding="utf-8")

    chosen = fork._repl_for_toolchain(str(lake))
    assert os.path.basename(chosen) == "repl-4.33.0-rc1"


def test_rc_lake_without_its_repl_is_refused(fork, home, tmp_path):
    """Temoin du precedent : sans `repl-4.33.0-rc1`, le lake rc1 ne retombe
    pas en silence sur le binaire de la release."""
    _write_repl(home / ".elan" / "bin" / "repl-4.33.0", b"4.33.0")
    _write_repl(home / ".elan" / "bin" / "repl", b"4.33.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lean-toolchain").write_text(
        "leanprover/lean4:v4.33.0-rc1\n", encoding="utf-8")

    with pytest.raises(fork.ReplPairingError):
        fork._repl_for_toolchain(str(lake))


def test_template_table_follows_repl_toolchain_tags(organ):
    """La table inlinee du gabarit suit REPL_TOOLCHAIN_TAGS : c'est ce qui part
    dans la fourche, et une table en retard sert le REPL par defaut."""
    assert organ._extract_repl_table(organ.REPL_PY_PATCH) == organ.REPL_TOOLCHAIN_TAGS


def test_repo_anchors_have_a_build_repl_tag(organ):
    """Chaque toolchain qu'epingle un `lean-toolchain` de carnet est un tag que
    `build-repl` accepte (v4.30.0 et v4.33.0-rc1 manquaient)."""
    root = REPO_ROOT / "MyIA.AI.Notebooks"
    pins = set()
    for tc in root.rglob("lean-toolchain"):
        parts = tc.relative_to(root).parts
        if ".lake" in parts or "reference_docs" in parts:
            continue
        for line in tc.read_text(encoding="utf-8").split("leanprover/lean4:"):
            line = line.strip()
            if line:
                pins.add(line)
    assert pins, "aucun lean-toolchain trouve"
    assert pins <= set(organ.REPL_TOOLCHAIN_TAGS), sorted(pins - set(organ.REPL_TOOLCHAIN_TAGS))


class _FakePexpect:
    """Enregistre les appels a `pexpect.spawn` du gabarit."""

    def __init__(self):
        self.calls = []

    def spawn(self, command, **kwargs):
        self.calls.append((command, kwargs))
        return ("spawned", command)


@pytest.fixture
def launching_fork(organ):
    """La classe de la fourche avec un `pexpect` factice, pour `launch()`."""
    fake = _FakePexpect()
    source = ("class Lean4ReplWrapper:\n"
              + textwrap.indent(organ.REPL_PY_PATCH, "    "))
    namespace = {"os": os, "re": re, "pexpect": fake}
    exec(compile(source, "<repl.py fork>", "exec"), namespace)
    return namespace["Lean4ReplWrapper"], fake


def test_from_caller_returns_the_exported_binary(launching_fork, home, monkeypatch):
    cls, _ = launching_fork
    repl = _write_repl(home / ".elan" / "bin" / "repl-4.30.0", b"4.30.0")
    monkeypatch.setenv("LEAN4_JUPYTER_REPL", str(repl))
    assert cls._repl_from_caller() == str(repl)


def test_from_caller_ignores_an_absent_binary(launching_fork, home, monkeypatch):
    cls, _ = launching_fork
    monkeypatch.setenv("LEAN4_JUPYTER_REPL", str(home / "nope"))
    assert cls._repl_from_caller() is None
    monkeypatch.delenv("LEAN4_JUPYTER_REPL")
    assert cls._repl_from_caller() is None


def test_launch_outside_a_lake_runs_the_paired_binary(launching_fork, home,
                                                      tmp_path, monkeypatch):
    """Hors lake, `lake env repl` lancerait ~/.elan/bin/repl (le PATH de
    `lake env` le met en tete) : le binaire apparie est lance directement."""
    cls, fake = launching_fork
    _write_repl(home / ".elan" / "bin" / "repl", b"4.33.0")
    paired = _write_repl(home / ".elan" / "bin" / "repl-4.30.0", b"4.30.0")
    series = tmp_path / "series"
    series.mkdir()
    (series / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    monkeypatch.chdir(series)
    monkeypatch.setenv("LEAN4_JUPYTER_REPL", str(paired))

    cls.launch()
    command, kwargs = fake.calls[-1]
    assert command == str(paired)
    # Le PATH du REPL est un PATH POSIX (le REPL tourne sous Linux ou WSL) :
    # le comparer par prefixe, un `split(":")` couperait la lettre de lecteur
    # d'un HOME Windows.
    assert kwargs["env"]["PATH"].startswith(os.path.expanduser("~/.elan/bin") + ":")


def test_launch_inside_a_lake_runs_the_paired_binary(launching_fork, home,
                                                     tmp_path, monkeypatch):
    """Dans un lake, le binaire apparie prime sur la table de la fourche, et
    garde le LEAN_PATH que donne `lake env`."""
    import subprocess

    cls, fake = launching_fork
    _write_repl(home / ".elan" / "bin" / "repl-4.30.0-rc2", b"4.30.0")
    paired = _write_repl(home / ".elan" / "bin" / "repl-4.30.0", b"4.30.0")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lakefile.toml").write_text("name = 'probe'\n", encoding="utf-8")
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.30.0\n", encoding="utf-8")
    monkeypatch.chdir(lake)
    monkeypatch.setenv("LEAN4_JUPYTER_REPL", str(paired))

    class _Done:
        stdout = "/sysroot/lib/lean:/lake/.lake/build/lib/lean\n"

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Done())

    cls.launch()
    command, kwargs = fake.calls[-1]
    assert command == str(paired)
    assert kwargs["env"]["LEAN_PATH"] == "/sysroot/lib/lean:/lake/.lake/build/lib/lean"


def test_launch_outside_a_lake_without_caller_keeps_lake_env(launching_fork, home,
                                                             tmp_path, monkeypatch):
    """Sans binaire exporte (lancement hors wrapper), le comportement de la
    fourche reste `lake env repl`."""
    cls, fake = launching_fork
    series = tmp_path / "series"
    series.mkdir()
    monkeypatch.chdir(series)
    monkeypatch.delenv("LEAN4_JUPYTER_REPL", raising=False)

    cls.launch()
    assert fake.calls[-1][0] == "lake env repl"


def test_repl_lean_version_keeps_the_rc_suffix(fork, tmp_path):
    repl = _write_repl(tmp_path / "repl", b"4.33.0-rc1")
    assert fork._repl_lean_version(str(repl)) == "4.33.0-rc1"


def test_rc_default_repl_is_refused_for_a_release_lake(fork, home, tmp_path):
    _write_repl(home / ".elan" / "bin" / "repl", b"4.33.0-rc1")
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lean-toolchain").write_text("leanprover/lean4:v4.33.0\n", encoding="utf-8")

    with pytest.raises(fork.ReplPairingError):
        fork._repl_for_toolchain(str(lake))


# --- Review de #25360 : aucun repli silencieux sur `lake env repl` ---------


def _lake(tmp_path, tag="v4.30.0"):
    lake = tmp_path / "lake"
    lake.mkdir()
    (lake / "lakefile.toml").write_text("name = 'probe'\n", encoding="utf-8")
    (lake / "lean-toolchain").write_text(f"leanprover/lean4:{tag}\n", encoding="utf-8")
    return lake


class _Ran:
    """Resultat de `subprocess.run` pour `lake env`."""

    def __init__(self, stdout, returncode=0, stderr=""):
        self.stdout = stdout
        self.returncode = returncode
        self.stderr = stderr


def test_launch_in_a_lake_raises_the_pairing_error(launching_fork, home,
                                                   tmp_path, monkeypatch):
    """Sans binaire apparie, un REPL par defaut d'une autre version est refuse,
    et rien n'est lance a sa place."""
    import subprocess

    cls, fake = launching_fork
    _write_repl(home / ".elan" / "bin" / "repl", b"4.33.0")
    monkeypatch.chdir(_lake(tmp_path))
    monkeypatch.delenv("LEAN4_JUPYTER_REPL", raising=False)
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Ran("/sysroot/lib/lean\n"))

    with pytest.raises(cls.ReplPairingError):
        cls.launch()
    assert fake.calls == []


def test_launch_in_a_lake_fails_when_lake_env_fails(launching_fork, home,
                                                    tmp_path, monkeypatch):
    """Un `lake env` qui expire leve une erreur nommee : avant, le gabarit
    lancait alors `lake env repl`, donc le REPL par defaut."""
    import subprocess

    cls, fake = launching_fork
    paired = _write_repl(home / ".elan" / "bin" / "repl-4.30.0", b"4.30.0")
    lake = _lake(tmp_path)
    monkeypatch.chdir(lake)
    monkeypatch.setenv("LEAN4_JUPYTER_REPL", str(paired))

    def _timeout(*args, **kwargs):
        raise subprocess.TimeoutExpired(cmd="lake env", timeout=240)

    monkeypatch.setattr(subprocess, "run", _timeout)

    with pytest.raises(cls.ReplLaunchError) as caught:
        cls.launch()
    assert str(lake) in str(caught.value)
    assert "TimeoutExpired" in str(caught.value)
    assert fake.calls == []


def test_launch_in_a_lake_fails_when_lake_is_missing(launching_fork, home,
                                                     tmp_path, monkeypatch):
    """`lake` absent du PATH : meme refus, pas de repli."""
    import subprocess

    cls, fake = launching_fork
    paired = _write_repl(home / ".elan" / "bin" / "repl-4.30.0", b"4.30.0")
    monkeypatch.chdir(_lake(tmp_path))
    monkeypatch.setenv("LEAN4_JUPYTER_REPL", str(paired))

    def _absent(*args, **kwargs):
        raise FileNotFoundError("lake")

    monkeypatch.setattr(subprocess, "run", _absent)

    with pytest.raises(cls.ReplLaunchError):
        cls.launch()
    assert fake.calls == []


def test_launch_in_a_lake_fails_on_an_empty_lean_path(launching_fork, home,
                                                      tmp_path, monkeypatch):
    """Un LEAN_PATH vide fait echouer le lancement, avec le code de sortie et
    l'erreur de `lake env`, au lieu de retomber sur `lake env repl`."""
    import subprocess

    cls, fake = launching_fork
    paired = _write_repl(home / ".elan" / "bin" / "repl-4.30.0", b"4.30.0")
    lake = _lake(tmp_path)
    monkeypatch.chdir(lake)
    monkeypatch.setenv("LEAN4_JUPYTER_REPL", str(paired))
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Ran(
        "", returncode=1, stderr="error: lakefile.toml: unknown field\n"))

    with pytest.raises(cls.ReplLaunchError) as caught:
        cls.launch()
    message = str(caught.value)
    assert str(lake) in message
    assert "exit 1" in message
    assert "unknown field" in message
    assert fake.calls == []


def test_launch_in_a_lake_fails_when_the_binary_is_missing(launching_fork, home,
                                                           tmp_path, monkeypatch):
    """Un binaire choisi par la table mais absent du disque : erreur nommee."""
    import subprocess

    cls, fake = launching_fork
    monkeypatch.chdir(_lake(tmp_path))
    monkeypatch.delenv("LEAN4_JUPYTER_REPL", raising=False)
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: _Ran("/sysroot/lib/lean\n"))
    missing = str(home / ".elan" / "bin" / "repl-4.30.0")
    monkeypatch.setattr(cls, "_repl_for_toolchain", staticmethod(lambda _root: missing))

    with pytest.raises(cls.ReplLaunchError) as caught:
        cls.launch()
    assert missing in str(caught.value)
    assert fake.calls == []


def test_launch_has_no_blanket_exception_handler(organ):
    """Le `except Exception: pass` qui menait au repli a disparu de `launch()` :
    seules les erreurs de `lake env` sont attrapees, pour etre nommees."""
    template = organ.REPL_PY_PATCH
    body = template[template.index("def launch(cls):"):]
    assert "except Exception" not in body
    assert "except (OSError, _sp.SubprocessError)" in body
    assert body.count('pexpect.spawn("lake env repl"') == 1
