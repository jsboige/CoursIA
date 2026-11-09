"""Tests de la phase 4 de #17558 : --check compare le coffre MyIA-Keys a master.env.

Deux familles :

* **unitaires** sur ``keyring_master_report`` (pure : empreintes pre-calculees) ;
* **bout en bout hermetiques** sur ``sync(check_only=True, ...)`` avec un module
  ``agent_keyring`` FAITAGE injecte dans ``sys.modules`` -- le vrai coffre n'est
  jamais ouvert par un test (il contient du materiel vivant). La paire
  discriminante : une divergence d'empreinte sort 1, une cle non migree ne sort
  1 qu'en --strict, un coffre injoignable ne sort JAMAIS 1 sur --check.

L'empreinte fake (``fp:<valeur>``) n'est pas cryptographique : le test mesure
l'ORCHESTRATION (qui compare quoi, et quel exit code en sort), pas la force de
l'empreinte -- c'est celle d'``agent_keyring.fingerprint``, testee ailleurs.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

ORGANE = Path(__file__).resolve().parents[1] / "secrets" / "render_envs.py"


@pytest.fixture(scope="module")
def mod():
    spec = importlib.util.spec_from_file_location("render_envs_u4", ORGANE)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


# --------------------------------------------------------------------------- #
# keyring_master_report -- unitaires (empreintes pre-calculees)
# --------------------------------------------------------------------------- #

def test_report_aligned_names_no_drift(mod):
    lines, diverging, unmigrated = mod.keyring_master_report(
        {"A": "x1", "B": "x2"}, {"A": "x1", "B": "x2"})
    assert diverging == [] and unmigrated == []
    assert any("2 entree(s) au coffre" in ln for ln in lines)


def test_report_diverging_key_named_without_value(mod):
    lines, diverging, unmigrated = mod.keyring_master_report(
        {"A": "x1", "B": "x2"}, {"A": "x1", "B": "OTHER"})
    assert diverging == ["B"] and unmigrated == []
    named = [ln for ln in lines if "DRIFT" in ln]
    assert len(named) == 1 and "B" in named[0]
    # aucune valeur ni empreinte ne sort -- seulement des noms de cles
    assert "OTHER" not in "".join(lines) and "x2" not in "".join(lines)


def test_report_unmigrated_named_not_drift(mod):
    lines, diverging, unmigrated = mod.keyring_master_report(
        {"A": "x1", "M": "x9"}, {"A": "x1"})
    assert diverging == [] and unmigrated == ["M"]
    assert any("phase 3" in ln and "M" in ln for ln in lines)


def test_report_vault_only_is_info_not_failure(mod):
    lines, diverging, unmigrated = mod.keyring_master_report(
        {"A": "x1"}, {"A": "x1", "EXTRA": "y"})
    assert diverging == [] and unmigrated == []
    assert any("EXTRA" in ln and "norme" in ln for ln in lines)


def test_report_unreachable_vault_is_unknown_never_fails(mod):
    lines, diverging, unmigrated = mod.keyring_master_report(
        {"A": "x1"}, None, "coffre injoignable (test)")
    assert diverging == [] and unmigrated == []
    assert len(lines) == 1 and "UNKNOWN" in lines[0] and "doctor" in lines[0]


# --------------------------------------------------------------------------- #
# sync(check_only=True) -- bout en bout hermetique, coffre faitage
# --------------------------------------------------------------------------- #

class _FakeVault:
    """Module agent_keyring faitage : open_vault/iter_entries/fingerprint.

    entries : dict title -> valeur ; reachable False simule un coffre
    injoignable (SystemExit, comme le vrai open_vault).
    """

    def __init__(self, entries, reachable=True):
        self.entries = entries
        self.reachable = reachable

    def open_vault(self, passphrase=None, quiet=False):
        if not self.reachable:
            raise SystemExit(3)
        return self

    def iter_entries(self, kp, group):
        return [SimpleNamespace(title=t, password=v)
                for t, v in sorted(self.entries.items())]

    @staticmethod
    def fingerprint(value):
        return "fp:" + value


@pytest.fixture()
def hermetic(tmp_path, monkeypatch, mod):
    """master.env tmp + zero cibles ; rend (set_vault, run)."""
    master = tmp_path / "master.env"
    master.write_text("SHARED_A=vault_a\n", encoding="utf-8")
    monkeypatch.setattr(mod, "MASTER_ENV", master)
    monkeypatch.setattr(mod, "TARGET_ENVS", [])

    def run(entries, reachable=True, strict=False):
        fake = _FakeVault(entries, reachable)
        monkeypatch.setitem(sys.modules, "agent_keyring", fake)
        return mod.sync(check_only=True, strict=strict)

    return run


def test_sync_check_vault_aligned_exit0(capsys, hermetic):
    rc = hermetic({"SHARED_A": "vault_a"})
    assert rc == 0
    out = capsys.readouterr().out
    assert "phase 4" in out and "UNKNOWN" not in out


def test_sync_check_diverging_fingerprint_exit1(capsys, hermetic):
    rc = hermetic({"SHARED_A": "different_b"})
    assert rc == 1
    out = capsys.readouterr().out
    assert "SHARED_A" in out and "different_b" not in out


def test_sync_check_unmigrated_named_exit0_then_strict_exit1(capsys, hermetic):
    # cle au coffre totalement differente : SHARED_A devient unmigree
    rc = hermetic({"OTHER": "x"})
    assert rc == 0
    assert "phase 3" in capsys.readouterr().out
    rc_strict = hermetic({"OTHER": "x"}, strict=True)
    assert rc_strict == 1


def test_sync_check_unreachable_vault_exit0(capsys, hermetic):
    rc = hermetic({}, reachable=False)
    assert rc == 0
    out = capsys.readouterr().out
    assert "UNKNOWN" in out and "non compare" in out
