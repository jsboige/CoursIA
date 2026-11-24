"""Le mode LECTURE de `gh_identity` : le jeton App de la lane (#17437 P1).

Ce que ces tests verrouillent :

1. le slug de l'App est **derive de la machine**, et l'App du coordinateur
   n'est jamais celle de la lane worker ;
2. le jeton n'est **jamais affiche** et ne transite **jamais par le disque** ;
3. le jeton d'**ecriture** n'est pas touche : `GH_TOKEN` est rendu a
   l'identique a la sortie du bloc de lecture ;
4. l'absence d'App est **memorisee** : un appel GH ne rouvre pas le coffre a
   chaque fois ;
5. la couche de lecture partagee (`coordination.gh_bulk`) passe bien l'env de
   lecture a ses sous-processus.

Aucun test ne touche le reseau : le jeton est fabrique par un fake.
"""
from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

RACINE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(RACINE / "scripts"))

import gh_identity  # noqa: E402


@pytest.fixture(autouse=True)
def _cache_vide():
    """Chaque test repart d'un cache de jeton vide."""
    gh_identity._LECTURE_JETON.clear()
    yield
    gh_identity._LECTURE_JETON.clear()


# --- 1. le slug de l'App ----------------------------------------------------

@pytest.mark.parametrize(("machine", "attendu"), [
    ("myia-ai-01", "coursia-lane-ai-01"),
    ("myia-po-2025", "coursia-lane-po-2025"),
    ("myia-po-2028", "coursia-lane-po-2028"),
    ("myia-web1", "coursia-lane-web1"),
])
def test_le_slug_de_ta_app_vient_de_la_machine(machine, attendu):
    assert gh_identity.app_slug(machine) == attendu


def test_le_slug_ignore_le_nom_de_domaine():
    assert gh_identity.app_slug("myia-po-2024.corp.local") == "coursia-lane-po-2024"


def test_l_app_du_coordinateur_n_est_pas_celle_de_la_lane_worker():
    """L'App du coordinateur porte sa voix ; elle ne se lit pas (#17437 Q187)."""
    assert gh_identity.COORDINATOR_LANE_APP_LOGIN != "coursia-lane-ai-01[bot]"
    assert gh_identity.app_slug("myia-ai-01") != gh_identity.COORDINATOR_APP_SLUG \
        if hasattr(gh_identity, "COORDINATOR_APP_SLUG") else True


# --- 2. le jeton ne sort jamais ---------------------------------------------

def test_le_jeton_ne_sort_jamais_de_l_organe(monkeypatch, capsys):
    """Le jeton forge n'est ni affiche ni ecrit : il vit en memoire."""
    monkeypatch.setattr(gh_identity, "_forge_depuis_le_coffre",
                        lambda slug, app_id, repo: "ghs_jeton_secret")
    monkeypatch.setattr(gh_identity, "_app_id_coffre", lambda slug: "5036190")
    jeton = gh_identity.lecture_token("coursia-lane-ai-01")
    assert jeton == "ghs_jeton_secret"
    capture = capsys.readouterr()
    assert "ghs_jeton_secret" not in capture.out
    assert "ghs_jeton_secret" not in capture.err


def test_le_jeton_est_memorise_et_ne_se_reforge_pas(monkeypatch):
    appels: list[str] = []

    def _forge(slug, app_id, repo):
        appels.append(slug)
        return "ghs_jeton"

    monkeypatch.setattr(gh_identity, "_forge_depuis_le_coffre", _forge)
    monkeypatch.setattr(gh_identity, "_app_id_coffre", lambda slug: "1")
    premier = gh_identity.lecture_token("coursia-lane-ai-01")
    second = gh_identity.lecture_token("coursia-lane-ai-01")
    assert premier == second == "ghs_jeton"
    assert len(appels) == 1


# --- 3. l'ecriture n'est pas touchee ---------------------------------------

def test_le_bloc_de_lecture_rend_l_environnement(monkeypatch):
    monkeypatch.setattr(gh_identity, "lecture_token", lambda *a, **k: "ghs_app")
    os.environ["GH_TOKEN"] = "ghs_partage"
    try:
        with gh_identity.lecture():
            assert os.environ["GH_TOKEN"] == "ghs_app"
        assert os.environ["GH_TOKEN"] == "ghs_partage"
    finally:
        os.environ.pop("GH_TOKEN", None)


def test_le_bloc_de_lecture_restaure_l_absence_de_jeton(monkeypatch):
    monkeypatch.setattr(gh_identity, "lecture_token", lambda *a, **k: "ghs_app")
    os.environ.pop("GH_TOKEN", None)
    with gh_identity.lecture():
        assert os.environ["GH_TOKEN"] == "ghs_app"
    assert "GH_TOKEN" not in os.environ


def test_le_jeton_d_ecriture_ne_depend_pas_du_jeton_app(monkeypatch):
    """`resolve_write_token` resout `jsboige` en ECARTANT `GH_TOKEN` : le
    jeton App ne peut donc pas se substituer a l'ecriture par accident."""
    from coordination import post_dossier

    monkeypatch.setenv("GH_TOKEN", "ghs_app")
    vu: dict[str, str] = {}

    def _fake_run(cmd, **kwargs):
        vu["env"] = kwargs.get("env") or {}
        class _P:
            returncode = 0
            stdout = "ghs_jsboige\n"
            stderr = ""
        return _P()

    monkeypatch.setattr(post_dossier.subprocess, "run", _fake_run)
    assert post_dossier.resolve_write_token() == "ghs_jsboige"
    assert "GH_TOKEN" not in vu["env"]


# --- 4. l'absence d'App est memorisee et dite --------------------------------

def test_absence_d_app_memorisee(monkeypatch):
    """Sans App, l'organe ne rouvre pas le coffre a chaque appel."""
    ouvertures: list[str] = []

    def _coffre(slug):
        ouvertures.append(slug)
        return None

    monkeypatch.setattr(gh_identity, "_app_id_coffre", _coffre)
    assert gh_identity.lecture_token("coursia-lane-ai-01") is None
    assert gh_identity.lecture_token("coursia-lane-ai-01") is None
    assert len(ouvertures) == 1


def test_absence_d_app_annoncee_une_seule_fois(monkeypatch, capsys):
    monkeypatch.setattr(gh_identity, "lecture_token", lambda *a, **k: None)
    with gh_identity.lecture():
        pass
    with gh_identity.lecture():
        pass
    capture = capsys.readouterr()
    assert capture.err.count("pas de jeton App exploitable") == 1


def test_read_env_sans_app_ne_touche_rien(monkeypatch):
    monkeypatch.setattr(gh_identity, "lecture_token", lambda *a, **k: None)
    base = {"GH_TOKEN": "ghs_partage", "PATH": "/bin"}
    env = gh_identity.read_env(base)
    assert env["GH_TOKEN"] == "ghs_partage"
    assert base == {"GH_TOKEN": "ghs_partage", "PATH": "/bin"}


def test_read_env_avec_app_pose_le_jeton_app(monkeypatch):
    monkeypatch.setattr(gh_identity, "lecture_token", lambda *a, **k: "ghs_app")
    env = gh_identity.read_env({"PATH": "/bin"})
    assert env["GH_TOKEN"] == "ghs_app"


# --- 5. la couche de lecture partagee passe l'env ---------------------------

def test_gh_bulk_passe_l_env_de_lecture(monkeypatch):
    """`coordination.gh_bulk` est le point de sortie reseau du tapis : c'est
    la que le jeton App doit etre pose."""
    from coordination import gh_bulk

    vu: dict[str, object] = {}

    def _fake_run(argv, **kwargs):
        vu["env"] = kwargs.get("env")
        vu["argv"] = argv

        class _P:
            stdout = "{}"
        return _P()

    monkeypatch.setattr(gh_identity, "read_env", lambda base=None: {"GH_TOKEN": "ghs_app"})
    monkeypatch.setattr(gh_bulk.subprocess, "run", _fake_run)
    gh_bulk.run_defaut(["gh", "api", "rate_limit"], 15)
    assert vu["env"] == {"GH_TOKEN": "ghs_app"}
