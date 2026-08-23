"""Tests for scripts/genai-stack/core/safe_ssl.py — issue #12068.

Module : scripts/tests/test_safe_ssl.py
Statut : MED/tooling, see issue #12068

Ces tests verifient le contrat du module safe_ssl :
- Idempotence : installer 2x ne double pas le patch.
- Reversibilite : disable restaure l'original.
- Comportement attendu : SSLError catch + return [].
- Pas de SSLErr masking : les autres exceptions propagent.
- force_raise() active le mode test sans modifier la machine.
- No-op documente sur Linux/Mac (methode _load_windows_store_certs absente).

Reference : #12068, ICT-25 cell[32], rlpt_3 cell[2].
"""

from __future__ import annotations

import os
import ssl
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "genai-stack"))

# Importer le module safe_ssl via un import tolerant
from core import safe_ssl  # type: ignore  # noqa: E402


@pytest.fixture(autouse=True)
def reset_state():
    """Reset l'etat du module avant ET apres chaque test."""
    safe_ssl.disable_safe_windows_store()
    safe_ssl.force_raise(False)
    yield
    safe_ssl.disable_safe_windows_store()
    safe_ssl.force_raise(False)


def test_is_patched_initially_false():
    """Un module frais doit rapporter non-patche."""
    assert safe_ssl.is_patched() is False


def test_install_returns_bool():
    """install retourne un booleen (True ou False selon plateforme)."""
    result = safe_ssl.install_safe_windows_store()
    if not hasattr(ssl.SSLContext, "_load_windows_store_certs"):
        assert result is False
    else:
        assert result is True


def test_install_is_idempotent():
    """Deux install() consecutifs ne doublent pas le patch."""
    if not hasattr(ssl.SSLContext, "_load_windows_store_certs"):
        pytest.skip("not on Windows — _load_windows_store_certs absent")
    first = safe_ssl.install_safe_windows_store()
    second = safe_ssl.install_safe_windows_store()
    assert first is True
    assert second is True
    # Toujours patche, jamais double-patche.
    assert safe_ssl.is_patched() is True
    # La methode est bien notre wrapper.
    assert ssl.SSLContext._load_windows_store_certs is safe_ssl._patched_load


def test_disable_restores_original():
    """disable retire le wrapper et restaure la version d'origine."""
    if not hasattr(ssl.SSLContext, "_load_windows_store_certs"):
        pytest.skip("not on Windows — _load_windows_store_certs absent")
    safe_ssl.install_safe_windows_store()
    assert safe_ssl.is_patched() is True
    removed = safe_ssl.disable_safe_windows_store()
    assert removed is True
    assert safe_ssl.is_patched() is False
    # is_patched() retourne False sur un disable() subsequentiel (idempotent).
    again = safe_ssl.disable_safe_windows_store()
    assert again is False


def test_force_raise_catches_sslerror():
    """force_raise simule un store malforme, et le wrapper retourne []."""
    if not hasattr(ssl.SSLContext, "_load_windows_store_certs"):
        pytest.skip("not on Windows — _load_windows_store_certs absent")
    safe_ssl.install_safe_windows_store()
    safe_ssl.force_raise(True)
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    # L'appel doit retourner [] sans lever.
    result = ctx._load_windows_store_certs("ROOT", None)
    assert result == []


def test_force_raise_off_does_not_swallow_real_errors():
    """Sans force_raise, le wrapper ne masque pas les autres exceptions."""
    if not hasattr(ssl.SSLContext, "_load_windows_store_certs"):
        pytest.skip("not on Windows — _load_windows_store_certs absent")
    safe_ssl.install_safe_windows_store()
    # Avec force_raise=False, le wrapper appelle l'original.
    # Si l'original leve TypeError (args invalides), le wrapper doit laisser passer.
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    with pytest.raises(TypeError):
        # _load_windows_store_certs(self, storename, purpose) — args manquent
        ctx._load_windows_store_certs()


def test_disable_after_force_raise_resets_state():
    """disable apres force_raise doit remettre a plat les deux flags."""
    if not hasattr(ssl.SSLContext, "_load_windows_store_certs"):
        pytest.skip("not on Windows — _load_windows_store_certs absent")
    safe_ssl.install_safe_windows_store()
    safe_ssl.force_raise(True)
    safe_ssl.disable_safe_windows_store()
    assert safe_ssl.is_patched() is False
    # force_raise reset aussi par disable_safe_windows_store.
    safe_ssl.install_safe_windows_store()
    ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    # force_raise est False apres disable -> appel natif (peut reussir ou echouer
    # selon la machine, mais sans notre wrapper simulant).
    # On verifie juste qu'on n'est pas en mode simule.
    assert safe_ssl._force_raise_active is False


def test_module_docstring_preserved():
    """Le docstring expose les formes d'usage (auto via sitecustomize)."""
    assert "sitecustomize" in safe_ssl.__doc__
    assert "#12068" in safe_ssl.__doc__
    # Regle secrets-hygiene rule 2 est explicitement mentionnee.
    assert "verify=False" in safe_ssl.__doc__
    assert "CERT_NONE" in safe_ssl.__doc__


def test_no_op_on_non_windows():
    """Sur Linux/Mac, install() retourne False sans alterer ssl.SSLContext."""
    # `_load_windows_store_certs` existe sur TOUTES les plateformes CPython
    # (no-op hors Windows), donc le skip se base sur `sys.platform`, pas `hasattr`.
    if sys.platform.startswith("win"):
        pytest.skip("Windows — store de certificats natif actif")
    # Pas de plateforme Windows : on documente le no-op.
    result = safe_ssl.install_safe_windows_store()
    assert result is False
    assert safe_ssl.is_patched() is False
