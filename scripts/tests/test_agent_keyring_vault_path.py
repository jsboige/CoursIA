#!/usr/bin/env python3
"""Resolution du chemin du coffre MyIA-Keys a travers les arbres .shared-state.

Fond : le Drive partage porte deux `.shared-state` cote a cote
(`Synchronisation` et `Synchronisation (1)`). Le coffre ne vit pas dans le meme
des deux selon la machine, donc un chemin code en dur rend `ABSENT` sur un
siege ou le fichier est pourtant la (mesure 2026-11-05 : doctor annoncait
ABSENT sur po-2025 alors que le sha256 du jumeau egalait celui publie par
ai-01 a l'octet).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "secrets"))

import agent_keyring as ak  # noqa: E402


def _arbre(root: Path, nom_arbre: str, avec_coffre: bool) -> Path:
    """Fabrique `<root>/<nom_arbre>/RooSync/.shared-state/MyIA-Keys.kdbx`."""
    dossier = root / nom_arbre / "RooSync" / ".shared-state"
    dossier.mkdir(parents=True)
    coffre = dossier / "MyIA-Keys.kdbx"
    if avec_coffre:
        coffre.write_bytes(b"kdbx-factice")
    return coffre


def test_coffre_dans_l_arbre_jumeau_est_trouve(tmp_path, monkeypatch):
    """Le defaut fondateur : absent de `Synchronisation`, present dans le jumeau."""
    monkeypatch.delenv("MYIA_KEYS_VAULT", raising=False)
    _arbre(tmp_path, "Synchronisation", avec_coffre=False)
    jumeau = _arbre(tmp_path, "Synchronisation (1)", avec_coffre=True)
    monkeypatch.setattr(
        ak, "DEFAULT_VAULT",
        str(tmp_path / "Synchronisation" / "RooSync" / ".shared-state" / "MyIA-Keys.kdbx"),
    )

    assert ak.vault_path() == jumeau


def test_arbre_par_defaut_prioritaire_quand_il_porte_le_coffre(tmp_path, monkeypatch):
    monkeypatch.delenv("MYIA_KEYS_VAULT", raising=False)
    principal = _arbre(tmp_path, "Synchronisation", avec_coffre=True)
    _arbre(tmp_path, "Synchronisation (1)", avec_coffre=True)
    monkeypatch.setattr(
        ak, "DEFAULT_VAULT",
        str(tmp_path / "Synchronisation" / "RooSync" / ".shared-state" / "MyIA-Keys.kdbx"),
    )

    assert ak.vault_path() == principal
    # les deux copies restent enumerees : c'est ce qui permet a doctor de crier
    assert len([c for c in ak.vault_candidates() if c.is_file()]) == 2


def test_aucun_coffre_rend_le_chemin_par_defaut(tmp_path, monkeypatch):
    """On ne fabrique pas un chemin plausible : l'absence doit rester visible."""
    monkeypatch.delenv("MYIA_KEYS_VAULT", raising=False)
    _arbre(tmp_path, "Synchronisation", avec_coffre=False)
    defaut = tmp_path / "Synchronisation" / "RooSync" / ".shared-state" / "MyIA-Keys.kdbx"
    monkeypatch.setattr(ak, "DEFAULT_VAULT", str(defaut))

    assert ak.vault_path() == defaut
    assert not ak.vault_path().is_file()


def test_override_par_variable_d_environnement_gagne(tmp_path, monkeypatch):
    _arbre(tmp_path, "Synchronisation", avec_coffre=True)
    explicite = tmp_path / "ailleurs" / "coffre.kdbx"
    monkeypatch.setenv("MYIA_KEYS_VAULT", str(explicite))

    assert ak.vault_path() == explicite


def test_arbre_absent_ne_leve_pas(tmp_path, monkeypatch):
    """Racine Drive absente (poste sans montage) : resolution sans exception."""
    monkeypatch.delenv("MYIA_KEYS_VAULT", raising=False)
    defaut = tmp_path / "inexistant" / "Synchronisation" / "RooSync" / ".shared-state" / "MyIA-Keys.kdbx"
    monkeypatch.setattr(ak, "DEFAULT_VAULT", str(defaut))

    assert ak.vault_candidates() == [defaut]
    assert ak.vault_path() == defaut
