#!/usr/bin/env python3
"""Tests de la lecture **partagee** des PRs ouvertes par la qualification (#29027).

Le tirage (`tapis_rapide.py`) lit les PRs et les garde dans son cache de lecture
partage par machine (`lecture-45j.json`). La qualification (`tapis_prise_en_charge.py`)
relisait la meme liste depuis le reseau a chaque invocation : le credit gh etait
paye deux fois pour le meme contenu, et la qualification echouait en `rate limit
exceeded` quand le seau etait court (mesure du 28/11/2026, 09:52Z, siege ai-01).

Ce que ces tests etablissent :

- le cache de lecture du tapis **suffit** : aucune lecture reseau ;
- une qualification consecutive ne paie **aucun** appel de plus ;
- un cache PRs dedie evite le reseau lui aussi ;
- un cache absent, perime ou illisible rebascule **sur le reseau** ;
- **le temoin** : la qualification prend ses PRs dans le cache partage et
  n'appelle plus `gh_bulk.lire_prs_ouvertes` -- la sentinelle refuse cet
  appel, donc le test echoue avant la correction et passe apres.

Aucun test ne touche le reseau ni le vrai depot : chaque lecture recoit un faux
`run(argv, timeout)`, et la sentinelle `forbid_shell_escape` refuse tout
processus.

Run: python -m pytest scripts/tests/test_gh_prs_cache.py
"""
from __future__ import annotations

import json
import sys
import time
from dataclasses import asdict
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, gh_prs_cache, tapis_leger_fenetre
from coordination import tapis_prise_en_charge
from coordination import tapis_qualification as tq

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")


def _pr(number: int = 1) -> dict:
    """Une PR au format de `gh_bulk.lire_prs_ouvertes`."""
    return {"title": f"PR {number}", "body": "", "created_at": "2026-11-01T00:00:00Z",
            "updated_at": "2026-11-02T00:00:00Z", "number": number, "draft": False,
            "merged_at": None, "head": {"ref": f"feature/{number}"},
            "user": {"login": "jsboige"}}


def _run_faux(appels: list[list[str]]):
    """Un `run` qui repond a la pagination des PRs, sans toucher le reseau."""
    def run(argv: list[str], timeout: int) -> str:
        appels.append(argv)
        return json.dumps([_pr(1)])
    return run


def _lire_interdite(run, depot=gh_bulk.DEPOT_GH, echeance=None):
    """La sentinelle du temoin : plus aucune lecture directe des PRs."""
    raise AssertionError(
        "lecture directe des PRs ouvertes : la qualification paie deux fois "
        "le meme contenu (temoin #29027)")


def _ecrire_cache_tapis(dossier: Path, prs: list[dict], jours: int = 45,
                         epoch: float | None = None) -> Path:
    """Le cache de lecture du tapis, ecrit comme le fait `gh_bulk.lire_tout`."""
    dossier.mkdir(parents=True, exist_ok=True)
    chemin = dossier / f"lecture-{jours}j.json"
    lecture = gh_bulk.Lecture(issues=[], prs=prs, citations={},
                              lu_a="2026-11-28T10:14:53Z", appels=4, secondes=1.0)
    chemin.write_text(json.dumps({**asdict(lecture),
                                  "_epoch": time.time() if epoch is None else epoch}),
                      encoding="utf-8")
    return chemin


# --- le cache de lecture du tapis suffit ---------------------------------------

def test_le_cache_du_tapis_suffit(tmp_path, monkeypatch):
    """Les PRs du tirage sont relues sans aucun appel reseau."""
    _ecrire_cache_tapis(tmp_path, [_pr(7), _pr(8)])
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    appels: list[list[str]] = []
    prs = gh_prs_cache.lire_prs_partagees(_run_faux(appels), dossier_cache=tmp_path)
    assert appels == []
    assert [p["number"] for p in prs] == [7, 8]


# --- une qualification consecutive ne paie rien de plus ------------------------

def test_la_seconde_qualification_ne_paie_plus_d_appel(tmp_path, monkeypatch):
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    appels: list[list[str]] = []
    run = _run_faux(appels)

    premiere = gh_prs_cache.lire_prs_partagees(run, dossier_cache=tmp_path)
    calls_apres_premiere = len(appels)
    assert calls_apres_premiere > 0  # la premiere lecture a bien lu le reseau
    assert len(premiere) == 1

    seconde = gh_prs_cache.lire_prs_partagees(run, dossier_cache=tmp_path)
    assert len(appels) == calls_apres_premiere  # aucun appel de plus
    assert [p["number"] for p in seconde] == [p["number"] for p in premiere]


# --- le cache PRs dedie evite le reseau ----------------------------------------

def test_le_cache_prs_dedie_evite_le_reseau(tmp_path, monkeypatch):
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    chemin = tmp_path / "prs-ouvertes.json"
    chemin.write_text(json.dumps({"prs": [_pr(9)], "lu_a": "2026-11-28T10:00:00Z",
                                  "_epoch": time.time()}), encoding="utf-8")
    appels: list[list[str]] = []
    prs = gh_prs_cache.lire_prs_partagees(_run_faux(appels), dossier_cache=tmp_path)
    assert appels == []
    assert [p["number"] for p in prs] == [9]


# --- les replis : absent, perime, illisible ------------------------------------

def test_un_cache_absent_rebascule_sur_le_reseau(tmp_path, monkeypatch):
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    appels: list[list[str]] = []
    prs = gh_prs_cache.lire_prs_partagees(_run_faux(appels), dossier_cache=tmp_path)
    assert len(appels) > 0
    assert len(prs) == 1


def test_un_cache_perime_rebascule_sur_le_reseau(tmp_path, monkeypatch):
    _ecrire_cache_tapis(tmp_path, [_pr(7)], epoch=time.time() - 10_000)
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    appels: list[list[str]] = []
    prs = gh_prs_cache.lire_prs_partagees(_run_faux(appels), dossier_cache=tmp_path)
    assert len(appels) > 0  # le cache perime ne vaut pas une lecture
    assert [p["number"] for p in prs] == [1]  # la lecture reseau, pas le cache perime


def test_un_cache_illisible_rebascule_sur_le_reseau(tmp_path, monkeypatch):
    (tmp_path / "lecture-45j.json").write_text("{ pas du json", encoding="utf-8")
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    appels: list[list[str]] = []
    prs = gh_prs_cache.lire_prs_partagees(_run_faux(appels), dossier_cache=tmp_path)
    assert len(appels) > 0
    assert len(prs) == 1


# --- le relais : le tirage publie, la qualification relit ----------------------

def test_le_tirage_publie_ce_que_la_qualification_relit(tmp_path, monkeypatch):
    """Le tirage paie une fois ; la qualification relit, sans payer."""
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    gh_prs_cache.publier_prs([_pr(11), _pr(12)], dossier_cache=tmp_path)
    appels: list[list[str]] = []
    prs = gh_prs_cache.lire_prs_partagees(_run_faux(appels), dossier_cache=tmp_path)
    assert appels == []
    assert [p["number"] for p in prs] == [11, 12]


def test_le_tirage_leger_publie_la_liste_il_a_paie(monkeypatch, tmp_path):
    """La voie legere publie les PRs qu'elle vient de lire.

    Le tirage garde sa lecture fraiche : il n'est pas question de lui servir
    une liste plus ancienne que celle qu'il lit lui-meme. La publication vit
    dans le module de la fenetre servie (`tapis_leger_fenetre`), qui porte la
    liste que le tirage a payee.
    """
    publiees: list[list[dict]] = []
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)
    monkeypatch.setattr(gh_prs_cache, "publier_prs",
                        lambda prs, dossier_cache=None: publiees.append(list(prs)))
    monkeypatch.setattr(tapis_leger_fenetre, "passer_et_replir",
                        lambda file, grains, lane, maintenant, prs, run=None,
                        run_commande=None, echeance=None, pool_ouvert=True,
                        repli=None: (file, [], {}, None))
    monkeypatch.setattr(tapis_leger_fenetre, "qualifier",
                        lambda file, lane, maintenant, jours, prs, run,
                        echeance=None: (file, {}, None))
    monkeypatch.setattr(tapis_leger_fenetre, "rapport",
                        lambda *a, **k: {"prs": [_pr(11), _pr(12)]})

    classe = {"prs": [_pr(11), _pr(12)], "grains": [], "conteneurs": [],
               "metas": [], "etats": []}
    tapis_leger_fenetre.servir(
        classe=classe, file=[{"numero": 1}], fenetre={}, origami={},
        lane="myia-ai-01:CoursIA-2", grains=1,
        maintenant=datetime(2026, 11, 28, 10, 0, tzinfo=UTC), jours=45,
        graine="graine", depot=Path("D:/CoursIA-2"), run=None,
        phases={"selection_s": 0.1}, secondes=0.2, budget_s=60.0)

    assert [p["number"] for p in publiees[0]] == [11, 12]


# --- LE TEMOIN : la qualification prend ses PRs du cache partage ----------------

def test_la_qualification_ne_relit_plus_les_prs_depuis_le_reseau(tmp_path, monkeypatch):
    """Le temoin de #29027 : il echoue avant la correction, passe apres.

    Avant, la qualification appelait `gh_bulk.lire_prs_ouvertes` : la
    sentinelle ci-dessous leve, et le test echoue. Apres, elle prend les PRs
    du cache partage -- zero appel, et la liste passee au qualifyur est celle
    du cache.
    """
    _ecrire_cache_tapis(tmp_path, [_pr(42)])
    monkeypatch.setattr(gh_bulk, "dossier_cache_defaut", lambda: tmp_path)

    captures: dict = {}

    def faux_qualifier(candidats, lane, maintenant, jours, prs, run, echeance=None,
                       lot=None, horloge=None, debut=None, preuve=None):
        captures["prs"] = prs
        return [], {}, [], False, 0, {"secondes": 0.0}

    monkeypatch.setattr(tq, "qualifier", faux_qualifier)
    # La sentinelle : plus aucune lecture directe des PRs ouvertes.
    monkeypatch.setattr(gh_bulk, "lire_prs_ouvertes", _lire_interdite)

    rc = tapis_prise_en_charge.main(["--issue", "1", "--lane", "myia-ai-01:CoursIA-2"])

    assert rc == 0
    assert [p["number"] for p in captures["prs"]] == [42]
