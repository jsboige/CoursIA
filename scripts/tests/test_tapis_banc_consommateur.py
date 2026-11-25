#!/usr/bin/env python3
"""Controle NEGATIF de la PORTE CONSOMMATEUR, sur les cas FIGES du banc.

Le banc (#27251) rejoue les ecarts du TIRAGE (les neuf codes) sur des cas
figes. Il ne rejouait pas la **porte consommateur**
(`scripts/check_lane_claim.py`), qui est l'organe applique AVANT toute
edition : c'est la que se joue l'exclusion d'un grain reclame par une autre
lane.

Ce fichier prouve que les deux organes **s'accordent sur la meme entree** :

- le cas fige `RECLAMEE` (un claim vivant d'une autre lane) est refuse par le
  tapis ET par la porte consommateur, qui nomme la lane bloquante ;
- un cas `SERVI` sans claim vivant est **accepte** par la porte -- c'est le
  controle POSITIF : sans lui, un refus qui refuserait tout ne prouverait rien.

Le cas fige est donc un **controle negatif** de l'exclusion par claim : la
regle doit exclure, et l'exclusion doit etre prouvee sur la meme entree que
celle que le tapis a refusee.

Hors reseau : le portillon se lit par `clc._run_check(payload, lane)`, qui ne
touche pas GitHub ; seule la recherche d'activite de la lane est neutralisee
(comme dans `test_check_lane_claim.py`).
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402

FIXTURE = (Path(__file__).resolve().parents[1] / "tests" / "fixtures"
           / "tapis_replay_cases.json")

AUTRE_LANE = "myia-ai-01:CoursIA-2"


@pytest.fixture
def sans_activite(monkeypatch):
    """La recherche d'activite de la lane enumere les PRs ouvertes : sans ce
    stub, le test appellerait le vrai `gh`."""
    monkeypatch.setattr(clc, "_gh_open_prs_with_files", lambda: [])


def _fixture() -> dict:
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def _cas(code: str, fil_vide: bool = False) -> dict:
    for cas in _fixture()["cas"]:
        if cas["attendu"]["code"] != code:
            continue
        if fil_vide and cas["fil_complet"]:
            continue
        return cas
    raise AssertionError(f"aucun cas fige au code {code}")


def _payload(cas: dict) -> dict:
    """Le cas fige, mis a la forme `gh issue view --json` que la porte
    attend : `createdAt` et `author.login` (camelCase)."""
    return {
        "number": cas["number"],
        "title": cas["title"],
        "labels": [{"name": lab} for lab in cas["labels"]],
        "comments": [{"body": c["body"], "createdAt": c["created_at"],
                      "author": {"login": c["author"]}, "url": None}
                     for c in cas["fil_complet"]],
    }


def test_le_cas_reclamee_est_refuse_par_la_porte_consommateur(sans_activite,
                                                               capsys):
    """Le claim vivant d'une autre lane doit REFUSER le passage : la porte ne
    rend pas CLEAR, et elle NOMME la lane bloquante (une levee par phrase
    d'une autre lane n'existe pas ici : seul un tier leve un refus de tiers)."""
    cas = _cas("RECLAMEE")
    rc = clc._run_check(_payload(cas), AUTRE_LANE)
    capture = capsys.readouterr()
    assert rc != 0, "la porte ne doit pas laisser passer un grain reclame"
    assert "myia-po-2027:CoursIA" in capture.out + capture.err


def test_un_cas_servable_sans_claim_vivant_passe_la_porte(sans_activite,
                                                           capsys):
    """CONTROLE POSITIF -- sans lui, le refus ci-dessus ne prouverait rien :
    une porte qui refuse TOUT passerait le test precedent. Ici la porte
    ACCEPTe un cas fige sans claim vivant."""
    cas = _cas("SERVI", fil_vide=True)
    rc = clc._run_check(_payload(cas), AUTRE_LANE)
    capture = capsys.readouterr()
    assert rc == 0, f"la porte doit laisser passer un grain libre : {capture.out}"
    assert "CLEAR" in capture.out + capture.err


def test_le_controle_ne_depend_daucun_reseau(monkeypatch, sans_activite,
                                             capsys):
    """Le portillon joue sur des entrees FIGEES : si le reseau changeait le
    verdict, le controle mesurerait autre chose que la regle."""
    def boom(*a, **k):
        raise AssertionError("le controle ne doit lire aucun reseau")
    monkeypatch.setattr(clc.subprocess, "run", boom)
    cas = _cas("RECLAMEE")
    rc = clc._run_check(_payload(cas), AUTRE_LANE)
    capsys.readouterr()
    assert rc != 0
