"""Tests de la requalification des exclusions MERGEE (banc #27242).

Le corpus est **fige** (`fixtures/requalification/corpus.json`) : chaque cas
est un issue reelle du depot, avec la PR MERGEE qui la cite et son fil
complet. Les verdicts attendus sont lus dans le corpus lui-meme -- un test ne
peut pas prescrire un verdict que le corpus ne porte pas.

Ce que ces tests verrouillent :
  - une preuve de reste **posterieure** au merge requalifie ;
  - une preuve **anterieure** au merge ne requalifie pas (controle negatif) ;
  - une issue livree, sans PR en vol, reste hors du pool ;
  - une PR en vol rend l'issue **vivante mais pas servable** ;
  - un claim vivant d'une autre lane refuse la requalification ;
  - les cases a cocher vides du **corps** ne sont jamais une preuve ;
  - les compteurs sont coherents (`servables` inclus dans `requalifiees`).
"""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from coordination.requalify_merged_exclusions import classer, rejouer

FIXTURE = Path(__file__).resolve().parent / "fixtures" / "requalification" / "corpus.json"


@pytest.fixture(scope="module")
def corpus() -> list[dict]:
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def _cas(corpus: list[dict], numero: int) -> dict:
    for c in corpus:
        if c["number"] == numero:
            return c
    raise AssertionError("cas absent du corpus : #{}".format(numero))


def test_le_corpus_porte_les_deux_temoins(corpus):
    """Le corpus porte le temoin (reste restant) et le contre-temoin (livre)."""
    numeros = {c["number"] for c in corpus}
    assert 27223 in numeros, "temoin manquant"
    assert 26911 in numeros, "contre-temoin manquant"


def test_un_reste_posterieur_au_merge_rend_l_issue_servable(corpus):
    """#27223 : le fil annonce apres le merge ce qui reste ET comment le faire."""
    verdict = classer(_cas(corpus, 27223))
    assert verdict["verdict"] == "servable"
    assert verdict["preuve"], "la preuve doit etre citee"


def test_une_phrase_de_reste_anterieure_au_merge_ne_requalifie_pas():
    """CONTROLE NEGATIF : un reste ecrit AVANT le merge decrit la tranche."""
    cas = {
        "number": 999999,
        "title": "cas de controle",
        "labels": [],
        "body": "",
        "merged_refs": [{"pr": 1, "merged_at": "2026-11-18T12:00:00Z"}],
        "prs_ouverts": [],
        "comments": [
            {"created_at": "2026-11-18T11:00:00Z", "author": "jsboige",
             "body": "Il reste la tranche 2 du plan de qualite a faire."},
            {"created_at": "2026-11-18T13:00:00Z", "author": "jsboige",
             "body": "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #1"},
        ],
    }
    verdict = classer(cas)
    assert verdict["verdict"] == "livre", verdict


def test_une_issue_livree_sans_pr_en_vol_reste_hors_du_pool(corpus):
    """#26911 : livree, fil sans reste apres le merge, aucune PR en vol."""
    verdict = classer(_cas(corpus, 26911))
    assert verdict["verdict"] == "livre"


def test_une_pr_en_vol_rend_l_issue_vivante_mais_pas_servable(corpus):
    """#27214 : une PR ouverte cite l'issue -> vivante, pas servable."""
    verdict = classer(_cas(corpus, 27214))
    assert verdict["verdict"] == "requalifiee"
    assert "PR en vol" in verdict["motif"]


def test_les_cases_a_cocher_vides_du_corps_ne_sont_pas_une_preuve(corpus):
    """#27213 : corps livre avec `- [ ]` vides -> jamais requalifie par le corps."""
    cas = _cas(corpus, 27213)
    assert "- [ ]" in cas["body"], "le temoin suppose des cases vides dans le corps"
    verdict = classer(cas)
    assert verdict["verdict"] != "servable"
    assert verdict["verdict"] == "requalifiee"  # vivant : PR en vol


def test_un_claim_vivant_d_une_autre_lane_refuse_la_requalification():
    """Un claim pose et jamais leve est un refus structurel."""
    cas = {
        "number": 999998,
        "title": "cas de controle",
        "labels": [],
        "body": "",
        "merged_refs": [{"pr": 1, "merged_at": "2026-11-18T12:00:00Z"}],
        "prs_ouverts": [],
        "comments": [
            {"created_at": "2026-11-18T13:00:00Z", "author": "jsboige",
             "body": "[CLAIMED] lane myia-po-2027:CoursIA-2 -- un grain"},
        ],
    }
    verdict = classer(cas)
    assert verdict["verdict"] == "refusee"
    assert "claim vivant" in verdict["motif"]


def test_un_epic_est_refuse(corpus):
    """Un EPIC n'est pas requalifiable : il reste ouvert par construction."""
    cas = dict(_cas(corpus, 26939))
    cas["title"] = "[EPIC] famille de test"
    verdict = classer(cas)
    assert verdict["verdict"] == "refusee"
    assert "EPIC" in verdict["motif"]


def test_les_compteurs_sont_coherents(corpus):
    """`servables` est inclus dans `requalifiees` : les deux compteurs distincts."""
    rapport = rejouer(corpus)
    assert rapport["servables"] <= rapport["requalifiees"]
    assert rapport["requalifiees"] == (rapport["compteurs"].get("servable", 0)
                                       + rapport["compteurs"].get("requalifiee", 0))
    assert rapport["corpus"] == len(corpus)


def test_le_banc_est_deterministe(corpus):
    """Meme corpus, memes verdicts : le banc est reproductible."""
    a = rejouer(corpus)
    b = rejouer(corpus)
    assert [v["verdict"] for v in a["cas"]] == [v["verdict"] for v in b["cas"]]
