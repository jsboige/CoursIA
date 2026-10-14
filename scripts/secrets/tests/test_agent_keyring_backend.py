"""`assert_backend_is_native` nomme le backend ACTIF, pas le module `keyring`.

Defaut mesure le 26/09 : la fonction lisait `type(keyring).__name__`, qui vaut
`module` sur toutes les machines. Elle refusait donc tout depot de passphrase,
backend natif compris, et `bootstrap` echouait apres avoir valide la passphrase
contre le coffre.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
from types import SimpleNamespace

import pytest

_MODULE_PATH = Path(__file__).resolve().parents[1] / "agent_keyring.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("agent_keyring_backend_under_test", _MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


mod = _load_module()


def _backend(module: str, name: str):
    """Instance d'une classe au nom et au module donnes, comme un vrai backend."""
    cls = type(name, (), {})
    cls.__module__ = module
    return cls()


def _fake_keyring(backend):
    return SimpleNamespace(get_keyring=lambda: backend)


def test_native_windows_backend_is_accepted(monkeypatch):
    monkeypatch.setattr(mod, "_keyring", lambda: _fake_keyring(
        _backend("keyring.backends.Windows", "WinVaultKeyring")))
    assert mod.assert_backend_is_native() == "keyring.backends.Windows.WinVaultKeyring"


def test_plaintext_fallback_is_refused(monkeypatch):
    monkeypatch.setattr(mod, "_keyring", lambda: _fake_keyring(
        _backend("keyrings.alt.file", "PlaintextKeyring")))
    with pytest.raises(SystemExit) as exc:
        mod.assert_backend_is_native()
    assert exc.value.code == mod.EXIT_DEFECT


def test_alt_backend_with_accepted_name_is_refused(monkeypatch):
    # Un repli `keyrings.alt` qui porterait un nom accepte reste refuse.
    monkeypatch.setattr(mod, "_keyring", lambda: _fake_keyring(
        _backend("keyrings.alt.Windows", "WinVaultKeyring")))
    with pytest.raises(SystemExit):
        mod.assert_backend_is_native()


def test_real_keyring_module_is_not_mistaken_for_a_backend():
    # Temoin du defaut : sans `get_keyring()`, le type lu serait `module`.
    keyring = pytest.importorskip("keyring")
    assert type(keyring).__name__ == "module"
    assert type(keyring.get_keyring()).__name__ != "module"
