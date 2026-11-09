"""Tests for ``scripts/notebook_tools/_dotnet_env.py`` -- DOTNET_ROOT repair.

Pins the residual hole measured on #23972: when ``DOTNET_ROOT`` is absent *or*
empty **and** no ``dotnet`` sits on ``PATH``, the effective root is unknowable.
``sdk_bearing_dotnet_root()`` used to return ``None`` there without probing a
single known root -- on exactly the host shape the repair exists for. The known
roots are now probed instead.

No .NET runtime is needed: the roots are real directories under ``tmp_path``
and only ``shutil.which`` / ``os.environ`` / the platform predicate are
substituted. ``_on_windows`` is patched through the module's own indirection,
never ``os.name`` (see the module docstring, #23353).
"""
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import _dotnet_env  # noqa: E402


def _sdk_root(base: Path, name: str) -> Path:
    """A root that carries a non-empty ``sdk/`` directory."""
    root = base / name
    (root / "sdk" / "10.0.100").mkdir(parents=True)
    return root


def _runtime_only_root(base: Path, name: str) -> Path:
    """A root that ships runtimes but no ``sdk/`` -- cannot restore."""
    root = base / name
    (root / "shared" / "Microsoft.NETCore.App").mkdir(parents=True)
    return root


def _isolate(monkeypatch, tmp_path, which=None):
    """Windows shape with isolated env: per-user install carries the SDK."""
    local_appdata = tmp_path / "local"
    program_files = tmp_path / "pf"
    per_user = local_appdata / "Microsoft" / "dotnet"
    (per_user / "sdk" / "10.0.100").mkdir(parents=True)
    _runtime_only_root(program_files, "dotnet")
    monkeypatch.setattr(_dotnet_env, "_on_windows", lambda: True)
    monkeypatch.setattr(_dotnet_env.shutil, "which", lambda _name: which)
    monkeypatch.setenv("LOCALAPPDATA", str(local_appdata))
    monkeypatch.setenv("ProgramFiles", str(program_files))
    return per_user


@pytest.mark.parametrize("value", [None, ""], ids=["absent", "empty"])
def test_unknown_effective_root_still_probes_known_roots(
    monkeypatch, tmp_path, value
):
    """#23972: absent/empty DOTNET_ROOT + no dotnet on PATH is not a stand-down."""
    per_user = _isolate(monkeypatch, tmp_path, which=None)
    if value is None:
        monkeypatch.delenv("DOTNET_ROOT", raising=False)
    else:
        monkeypatch.setenv("DOTNET_ROOT", value)

    assert _dotnet_env.sdk_bearing_dotnet_root() == str(per_user)


def test_configured_root_without_sdk_is_still_repaired(monkeypatch, tmp_path):
    """Control: a defined but runtime-only root keeps being repaired (#17361)."""
    per_user = _isolate(monkeypatch, tmp_path, which=None)
    runtime_only = _runtime_only_root(tmp_path, "configured")
    monkeypatch.setenv("DOTNET_ROOT", str(runtime_only))

    assert _dotnet_env.sdk_bearing_dotnet_root() == str(per_user)


def test_no_sdk_anywhere_returns_none_without_raising(monkeypatch, tmp_path):
    """Negative: nothing carries an SDK -> explicit degraded None, no crash.

    The guarantee carried over from the previous contract: the repair never
    *invents* a root. It only returns one that actually carries ``sdk/``.
    """
    monkeypatch.setattr(_dotnet_env, "_on_windows", lambda: True)
    monkeypatch.setattr(_dotnet_env.shutil, "which", lambda _name: None)
    monkeypatch.delenv("DOTNET_ROOT", raising=False)
    monkeypatch.setenv("LOCALAPPDATA", str(_runtime_only_root(tmp_path, "local")))
    monkeypatch.setenv("ProgramFiles", str(_runtime_only_root(tmp_path, "pf")))

    assert _dotnet_env.sdk_bearing_dotnet_root() is None


def test_dotnet_root_present_and_sdk_bearing_needs_no_repair(monkeypatch, tmp_path):
    """Nothing to repair: the effective root already carries the SDK."""
    sdk_root = _sdk_root(tmp_path, "good")
    monkeypatch.setattr(_dotnet_env, "_on_windows", lambda: True)
    monkeypatch.setattr(_dotnet_env.shutil, "which", lambda _name: None)
    monkeypatch.setenv("DOTNET_ROOT", str(sdk_root))

    assert _dotnet_env.sdk_bearing_dotnet_root() is None
