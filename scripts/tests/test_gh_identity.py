"""Tests de gh_identity — helper unique d'epinglage de jeton machine (#17418 Phase A).

Unitaires (aucun reseau) pour la cartographie hostname->compte, le respect
d'un GH_TOKEN deja pose, l'echec BRUYANT sans repli silencieux, et la
classification rate-limit qui distingue rc=2 de rc=1.
"""

import os
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import gh_identity  # noqa: E402


# --- machine_account -------------------------------------------------------


def test_machine_account_connu():
    assert gh_identity.machine_account("myia-po-2023") == "myia-po-2023"
    assert gh_identity.machine_account("MYIA-AI-01") == "myia-ai-01"
    # La Phase B/C provisionnera ces comptes ; la cartographie existe deja.
    assert gh_identity.machine_account("myia-po-2025") == "myia-po-2025"


def test_machine_hostname_normalise(monkeypatch):
    monkeypatch.setenv("COMPUTERNAME", "MyIA-PO-2023")
    assert gh_identity.machine_hostname() == "myia-po-2023"


def test_machine_account_override_explicite(monkeypatch):
    monkeypatch.setenv("COURSIA_GH_ACCOUNT", "MyIA-Web1")
    assert gh_identity.machine_account("unknown-host") == "MyIA-Web1"


def test_machine_account_inconnu_echoue_avec_remediation():
    with pytest.raises(gh_identity.GhIdentityError) as exc:
        gh_identity.machine_account("laptop-perso")
    msg = str(exc.value)
    # L'echec porte sa remediation — jamais de repli muet sur le compte actif.
    assert "COURSIA_GH_ACCOUNT" in msg or "COURSIA_GH_PINNING" in msg
    assert "myia-po-2023" in msg  # la liste des comptes mappees est citee


# --- pin_gh_token ----------------------------------------------------------


def test_pin_respecte_gh_token_deja_pose(monkeypatch):
    monkeypatch.setenv("GH_TOKEN", "tok-deja-pose")
    assert gh_identity.pin_gh_token() == "tok-deja-pose"
    assert gh_identity.resolve_gh_token() == "tok-deja-pose"


def test_pin_epingle_le_jeton_resolu(monkeypatch, gh_token_env):
    """Le jeton resolu est epingle dans l'environnement du processus.

    Le fixture `gh_token_env` porte la restauration : `pin_gh_token()` ecrit
    `os.environ["GH_TOKEN"]` DIRECTEMENT, et le `monkeypatch.delenv` du
    debut n'a rien enregistre (la variable etait absente) -- l'ecriture
    survivait donc au test, laissait un jeton fictif pose pour toute la
    session pytest et masquait 12 echecs REELS du picker (#21994).
    """
    monkeypatch.delenv("GH_TOKEN", raising=False)
    monkeypatch.delenv("COURSIA_GH_PINNING", raising=False)
    monkeypatch.setattr(gh_identity, "resolve_gh_token", lambda: "tok-machine")
    assert gh_identity.pin_gh_token() == "tok-machine"
    assert os.environ["GH_TOKEN"] == "tok-machine"


def test_le_pin_ne_laisse_pas_de_jeton_derriere_lui(monkeypatch, gh_token_env):
    """Non-regression #21994 : un pin reussi se restaure.

    Le jeton ecrit par `pin_gh_token()` doit disparaitre de l'environnement
    une fois le test fini -- sinon le verdict des modules suivants depend de
    l'ordre de leurs fichiers.
    """
    monkeypatch.delenv("GH_TOKEN", raising=False)
    monkeypatch.setattr(gh_identity, "resolve_gh_token", lambda: "tok-machine")
    assert gh_identity.pin_gh_token() == "tok-machine"
    assert os.environ["GH_TOKEN"] == "tok-machine"  # le pin ecrit bien
    assert gh_token_env.restore() is None  # la restauration l'efface
    assert os.environ.get("GH_TOKEN") is None


def test_pin_pinning_off_avertit_et_ne_epingle_pas(monkeypatch, capsys):
    monkeypatch.delenv("GH_TOKEN", raising=False)
    monkeypatch.setenv("COURSIA_GH_PINNING", "off")
    called = []
    monkeypatch.setattr(
        gh_identity, "resolve_gh_token",
        lambda: called.append(1) or "tok-machine",
    )
    assert gh_identity.pin_gh_token() == ""
    assert os.environ.get("GH_TOKEN") is None
    assert called == []  # transition : on n'a meme pas tente de resoudre
    err = capsys.readouterr().err
    assert "WARN" in err and gh_identity.SHARED_LOGIN in err


def test_resolve_echoue_bruyament_sans_compte_tresor(monkeypatch):
    monkeypatch.delenv("GH_TOKEN", raising=False)
    # Hermetique : sans compte explicite, machine_account() leve AVANT le
    # sous-processus sur tout hostname non mappe (le runner GA), et le
    # message n'est alors pas celui de l'echec de trousseau.
    monkeypatch.setenv("COURSIA_GH_ACCOUNT", "myia-po-test")

    class FakeProc:
        returncode = 1
        stderr = "no users found"
        stdout = ""

    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc())
    with pytest.raises(gh_identity.GhIdentityError) as exc:
        gh_identity.resolve_gh_token()
    msg = str(exc.value)
    # Parties stables du message : commande nommee, compte attendu, rc --
    # pas la reformulation de la remediation (re-review Hermes, 0393a1d1).
    assert "gh auth token" in msg
    assert "myia-po-test" in msg
    assert "rc=1" in msg


# --- classification rate-limit (rc=2 != rc=1) ------------------------------


@pytest.mark.parametrize("text", [
    "API rate limit already exceeded for user ID 3159389",
    "You have exceeded a secondary rate limit",
    "RATE LIMIT: too many requests",
])
def test_is_rate_limit_error_positif(text):
    assert gh_identity.is_rate_limit_error(text) is True


@pytest.mark.parametrize("text", ["Not Found", "gh: issue not found", ""])
def test_is_rate_limit_error_negatif(text):
    assert gh_identity.is_rate_limit_error(text) is False


def test_banniere_distingue_rc2_de_rc1():
    banner = gh_identity.rate_limit_banner(
        "gh: API rate limit already exceeded for user ID 3159389"
    )
    # La ligne que l'appelant lit sans --json doit nommer la confusion et la
    # remediation — c'est ce qui a coute ~3 h de merge le 2026-09-22.
    assert "RATE-LIMIT" in banner
    assert "rc=1" in banner
    assert "gh auth token" in banner


def test_gh_env_pose_le_jeton_resolu(monkeypatch):
    monkeypatch.delenv("GH_TOKEN", raising=False)
    monkeypatch.delenv("COURSIA_GH_PINNING", raising=False)
    monkeypatch.setattr(gh_identity, "resolve_gh_token", lambda: "tok-env")
    env = gh_identity.gh_env({"PATH": "/bin"})
    assert env["GH_TOKEN"] == "tok-env"
    assert env["PATH"] == "/bin"


# --- #17437/Q187 : l'App PROPRE a la lane coordinatrice, auteur de dossier ----


def test_coordinator_lane_app_est_un_auteur_de_dossier_accepte():
    """Q187 (2026-11-14) : l'App propre a la lane coordinatrice (App 5763709,
    cle dediee) signe des dossiers. Litteral EXPLICITE, pas derive du
    prefixe ``coursia-lane-`` : ce test epingle l'appartenance ET la non
    derivation (un slug construit par forme ne doit pas passer)."""
    assert gh_identity.COORDINATOR_LANE_APP_LOGIN == "coursia-coord-ai01[bot]"
    assert gh_identity.COORDINATOR_LANE_APP_LOGIN in gh_identity.ACCEPTED_DOSSIER_AUTHORS
    # L'App de MACHINE reste un auteur accepte (elle signe, elle ne
    # neutralise pas -- cf check_adjoint_prevalidation).
    assert (gh_identity.APP_LOGIN_PREFIX + "ai-01[bot]"
            in gh_identity.ACCEPTED_DOSSIER_AUTHORS)


def test_coordinator_lane_app_hors_prefixe_de_lane_est_refuse_par_forme():
    """Fail-closed par forme : l'ensemble ne derive PAS de ``APP_DOSSIER_LANES``
    -- un login qui n'est que la RESSEMBLANCE du slug coordinateur sous le
    prefixe de lane est refuse, comme tout login absent de la table figee."""
    for impostor in (
        "coursia-lane-coord-ai01[bot]",   # slug coordinateur sous prefixe de lane
        "coursia-coord-ai01",             # forme nue sans type ni suffixe
        "coursia-coord-ai01[bot]x",       # suffixe valide plus caractere parasite
        "coursia-coord-ai02[bot]",        # slug voisin inexistant
    ):
        assert impostor not in gh_identity.ACCEPTED_DOSSIER_AUTHORS, impostor


def test_coordinator_lane_app_normalisee_passe_le_predicat():
    """``is_accepted_dossier_author`` compare sur le login NORMALISE : la
    forme GraphQL nue typee ``Bot`` (login sans suffixe) est repliee en
    forme REST suffixee et acceptee ; l'homonyme UTILISATEUR type ``User``
    reste nu et est refuse."""
    assert gh_identity.is_accepted_dossier_author(
        {"login": "coursia-coord-ai01", "__typename": "Bot"}) is True
    assert gh_identity.is_accepted_dossier_author(
        {"login": "coursia-coord-ai01[bot]"}) is True
    assert gh_identity.is_accepted_dossier_author(
        {"login": "coursia-coord-ai01", "__typename": "User"}) is False
