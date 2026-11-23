"""Tests du funnel d'appel gh avec bascule unique vers le jeton App (#27012 p3).

Couvre les invariants du module ``scripts/ci/gh_app_failover.py`` :

- detection du rate-limit (403/429 au motif texte rendu par ``gh``) et refus
  des autres echecs (permissions, absence de stderr) ;
- bascule UNIQUE par process : forge, epinglage ``GH_TOKEN``, re-essai une
  fois, message sur stderr ;
- impossibilite de forger (PEM absente) : message de remédiation, exception
  d'origine qui remonte, drapeau quand meme pose (pas de boucle) ;
- un echec non rate-limit traverse sans forge ;
- le routing ETag est preserve (304 compte via ``on_304``), le chemin direct
  rend le JSON parse ;
- resolution de lane et d'app_id (endpoint public, cache par process).

Aucun test ne touche le reseau : forge, urlopen et gh sont monkeypatches.
"""

from __future__ import annotations

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parents[1]


def _load_module():
    spec = importlib.util.spec_from_file_location(
        "gh_app_failover", SCRIPTS_DIR / "ci" / "gh_app_failover.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture()
def mod():
    m = _load_module()
    m._STATE["failover_done"] = False
    m._STATE["app_id"] = None
    yield m
    m._STATE["failover_done"] = False
    m._STATE["app_id"] = None


def _rl_error(stderr="gh: API rate limit exceeded for installation 123"):
    return subprocess.CalledProcessError(1, ["gh", "api", "x"], stderr=stderr)


# --- lane / slug / PEM ------------------------------------------------------


def test_lane_of_host_strippe_le_prefixe_myia(mod):
    assert mod.lane_of_host("myia-po-2028") == "po-2028"
    assert mod.lane_of_host("MYIA-WEB1") == "web1"
    assert mod.lane_of_host("myia-ai-01") == "ai-01"


def test_lane_of_host_refuse_un_hote_hors_convention(mod):
    with pytest.raises(RuntimeError, match="ne designe pas une lane"):
        mod.lane_of_host("portable-perso")


def test_app_slug_et_pem_path(mod, monkeypatch):
    monkeypatch.setattr(mod.gh_identity, "machine_hostname",
                        lambda: "myia-po-2028")
    assert mod.app_slug(mod.lane_of_host()) == "coursia-lane-po-2028"
    assert mod.pem_path().name == "coursia-lane-po-2028.pem"
    assert mod.pem_path().parent == mod.KEY_DIR


# --- detection --------------------------------------------------------------


def test_rate_limited_detecte_le_motif_gh(mod):
    assert mod._rate_limited(_rl_error())
    assert mod._rate_limited(_rl_error(
        "gh: You have exceeded a secondary rate limit"))
    # le motif peut vivre dans stdout (gh api -i renvoie les erreurs melangees)
    exc = subprocess.CalledProcessError(1, ["gh"], output="rate limit exceeded")
    assert mod._rate_limited(exc)


def test_rate_limited_refuse_les_autres_403(mod):
    assert not mod._rate_limited(_rl_error(
        "gh: Resource not accessible by integration"))
    assert not mod._rate_limited(_rl_error(""))


# --- bascule unique ---------------------------------------------------------


def test_attempt_bascule_puis_reessaie(mod, monkeypatch, capsys):
    forge = {"n": 0}
    monkeypatch.setattr(mod, "forge_app_token",
                        lambda: forge.__setitem__("n", forge["n"] + 1) or "tok-app")
    calls = {"n": 0}

    def flaky():
        calls["n"] += 1
        if calls["n"] == 1:
            raise _rl_error()
        return "ok"

    monkeypatch.setattr(mod.gh_identity, "machine_hostname",
                        lambda: "myia-po-2027")
    assert mod._attempt(flaky) == "ok"
    assert forge["n"] == 1
    assert os.environ.get("GH_TOKEN") == "tok-app"
    out = capsys.readouterr().err
    assert "[RATE-LIMIT]" in out
    assert "bascule effectuee vers coursia-lane-po-2027" in out


def test_attempt_ne_bascule_qu_une_fois(mod, monkeypatch):
    forge = {"n": 0}
    monkeypatch.setattr(mod, "forge_app_token",
                        lambda: forge.__setitem__("n", forge["n"] + 1) or "tok")

    def always_rl():
        raise _rl_error()

    with pytest.raises(subprocess.CalledProcessError):
        mod._attempt(always_rl)  # bascule + re-essai rate-limite -> remonte
    with pytest.raises(subprocess.CalledProcessError):
        mod._attempt(always_rl)  # drapeau pose : plus AUCUNE forge
    assert forge["n"] == 1


def test_attempt_peM_absente_remedie_et_remonte(mod, monkeypatch, capsys):
    monkeypatch.setattr(mod, "pem_path", lambda: Path("Z:/absente.pem"))
    with pytest.raises(subprocess.CalledProcessError):
        mod._attempt(lambda: (_ for _ in ()).throw(_rl_error()))
    out = capsys.readouterr().err
    assert "bascule IMPOSSIBLE" in out
    assert "absente.pem" in out
    assert mod._STATE["failover_done"] is True  # pas de boucle au suivant


def test_bascule_reussie_sur_un_hote_hors_convention(mod, monkeypatch, capsys):
    """#28272 : sur un runner CI (hostname = id de conteneur), une bascule
    REUSSIE ne doit pas lever dans son message de succes.

    Mesure CI : `app_slug(lane_of_host())` etait appele dans le print de
    succes, hors du try/except, donc la resolution de lane levait APRES la
    bascule et `test_attempt_ne_bascule_qu_une_fois` rendait RuntimeError.
    """
    monkeypatch.setattr(mod.gh_identity, "machine_hostname",
                        lambda: "7b3c06ed8710")
    monkeypatch.setattr(mod, "forge_app_token", lambda: "tok")
    monkeypatch.delenv("GH_TOKEN", raising=False)

    def always_rl():
        raise _rl_error()

    with pytest.raises(subprocess.CalledProcessError):
        mod._attempt(always_rl)
    err = capsys.readouterr().err
    assert "bascule effectuee" in err
    assert "le seau de l'App de la lane" in err
    assert os.environ.get("GH_TOKEN") == "tok"


def test_pem_absente_est_nommee_sur_un_hote_hors_convention(
        mod, monkeypatch, capsys):
    """#28272 : la PEM absente se juge AVANT la resolution de la lane -- le
    message de remediation doit nommer le chemin meme quand l'hote ne designe
    pas une lane (runner CI).
    """
    monkeypatch.setattr(mod.gh_identity, "machine_hostname",
                        lambda: "7b3c06ed8710")
    monkeypatch.setattr(mod, "pem_path", lambda: Path("Z:/absente.pem"))
    with pytest.raises(subprocess.CalledProcessError):
        mod._attempt(lambda: (_ for _ in ()).throw(_rl_error()))
    err = capsys.readouterr().err
    assert "bascule IMPOSSIBLE" in err
    assert "absente.pem" in err


def test_attempt_laisse_traverser_un_echec_non_quota(mod, monkeypatch):
    forge = {"n": 0}
    monkeypatch.setattr(mod, "forge_app_token",
                        lambda: forge.__setitem__("n", forge["n"] + 1) or "tok")

    def forbidden():
        raise subprocess.CalledProcessError(
            1, ["gh"], stderr="gh: Resource not accessible by integration")

    with pytest.raises(subprocess.CalledProcessError):
        mod._attempt(forbidden)
    assert forge["n"] == 0
    assert mod._STATE["failover_done"] is False


# --- funnel call : routing ETag preserve ------------------------------------


def test_call_route_par_etag_et_compte_les_304(mod, monkeypatch):
    touches = []
    monkeypatch.setattr(mod.gh_etag, "etag_applicable",
                        lambda args: "repos/jsboige/CoursIA/x")
    monkeypatch.setattr(mod.gh_etag, "conditional_get",
                        lambda path, timeout: ({"id": 7}, True))
    out = mod.call(["api", "repos/jsboige/CoursIA/x"],
                   timeout=5, on_304=lambda: touches.append(1))
    assert out == {"id": 7}
    assert touches == [1]  # on_304 appelee exactement une fois


def test_call_chemin_direct_parse_le_json(mod, monkeypatch):
    monkeypatch.setattr(mod.gh_etag, "etag_applicable", lambda args: None)

    class Fake:
        stdout = json.dumps([{"number": 1}])

    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **k: Fake())
    assert mod.call(["pr", "list", "--json", "number"], timeout=5) == [
        {"number": 1}]


def test_call_bascule_sur_rate_limit_du_chemin_direct(mod, monkeypatch, capsys):
    monkeypatch.setattr(mod.gh_etag, "etag_applicable", lambda args: None)
    monkeypatch.setattr(mod, "forge_app_token", lambda: "tok-app")
    monkeypatch.setattr(mod.gh_identity, "machine_hostname",
                        lambda: "myia-po-2028")
    runs = {"n": 0}

    def flaky_run(*a, **k):
        runs["n"] += 1
        if runs["n"] == 1:
            raise _rl_error()

        class Fake:
            stdout = '{"ok": true}'

        return Fake()

    monkeypatch.setattr(mod.subprocess, "run", flaky_run)
    assert mod.call(["pr", "view", "9", "--json", "ok"], timeout=5) == {
        "ok": True}
    assert os.environ.get("GH_TOKEN") == "tok-app"
    assert "bascule effectuee" in capsys.readouterr().err


# --- resolution de l'app_id (endpoint public, cache) ------------------------


def test_fetch_app_id_cache_par_process(mod, monkeypatch):
    fetched = {"n": 0}

    class Resp:
        def __enter__(self):
            return self

        def __exit__(self, *a):
            return False

        def read(self):
            fetched["n"] += 1
            return json.dumps({"id": 987654, "slug": "coursia-lane-po-2028"})

    monkeypatch.setattr(mod.urllib.request, "urlopen", lambda req, timeout: Resp())
    assert mod._fetch_app_id("coursia-lane-po-2028") == 987654
    assert mod._fetch_app_id("coursia-lane-po-2028") == 987654  # cache
    assert fetched["n"] == 1
