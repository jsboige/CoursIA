"""La preuve de livraison par le DIFF (revue 5967171401, 19/11).

Un marqueur `[DELIVERED]` **designe** une PR a verifier ; la preuve, c'est le
diff de cette PR couvrant le perimetre declare. Meme marqueur, deux diffs,
deux verdicts : c'est le temoin demande par la revue.

**Revision du 19/11 (revue du coordinateur, DM `night-27242-glob-is-not-whole-scope`)** :
le perimetre d'une tranche livree est ecrit en **chemins explicites** (la
pratique des tranches livrees sur #27242), et un **glob ne certifie jamais la
completude** : une seule modification sous `scripts/tests/**` ne prouve pas
que le perimetre est couvert. Deux controles negatifs verrouillent la regle.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_diff as td
from coordination import tapis_qualification as tq

NOW = datetime(2026, 11, 18, 9, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"

MARQUEUR = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242 -- "
            "paths: scripts/coordination/tapis_diff.py, scripts/tests/test_tapis_diff.py")
MARQUEUR_GLOBE = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242 -- "
                   "paths: scripts/coordination/tapis_diff.py, scripts/tests/**")
COMPLET = ["scripts/coordination/tapis_diff.py", "scripts/tests/test_tapis_diff.py"]
PARTIEL = ["scripts/coordination/tapis_diff.py"]

#: L'issue porte une attribution (deux fichiers) ; la tranche livree n'en
#: declare qu'un : la livraison est complete sur SON perimetre, mais plus
#: etroite que l'issue.
ATTRIBUTION = ("[CLAIMED] lane myia-ai-01:CoursIA-2 -- paths: "
               "scripts/coordination/tapis_diff.py, scripts/tests/test_tapis_qualification.py")
TRANCHE_ETROITE = ("[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242 -- "
                    "paths: scripts/coordination/tapis_diff.py")


def _issue(body: str = MARQUEUR, autres: list[str] | None = None) -> dict:
    commentaires = [{"created_at": "2026-11-10T00:00:00Z",
                     "author": "jsboige", "body": body}]
    for i, autre in enumerate(autres or []):
        commentaires.append({"created_at": f"2026-11-1{i}T00:00:00Z",
                             "author": "jsboige", "body": autre})
    return {"number": 7, "title": "Grain 7", "body": "",
            "created_at": "2026-11-01T00:00:00Z",
            "comments": commentaires,
            "comments_total": len(commentaires), "labels": []}


def _faux_lecture(monkeypatch, issue: dict):
    """La lecture ciblee rend l'issue ; le fil complet rend son commentaire."""
    monkeypatch.setattr(tq.tapis_lot.gh_selection, "qualifier",
                        lambda run, depot, numeros=None: {7: issue})
    monkeypatch.setattr(tq.tapis_fenetre, "fil_complet",
                        lambda numero: issue["comments"])


def _run() -> str:
    return "[]"


def test_le_meme_marqueur_deux_diffs_deux_verdicts():
    """LE temoin demande : meme marqueur, deux diffs, verdict different."""
    complet = td.verdict(MARQUEUR, COMPLET)
    partiel = td.verdict(MARQUEUR, PARTIEL)
    assert complet[0] == td.COUVRE, complet[1]
    assert partiel[0] == td.TRANCHE, partiel[1]
    assert "scripts/tests/test_tapis_diff.py" in partiel[1], "le manque est dit"


def test_un_seul_fichier_sous_un_glob_qui_en_attend_plusieurs_ne_couvre_pas():
    """NEGATIF 1 (demande par la revue du 19/11).

    Un glob ne dit pas combien de fichiers il attend : une seule
    modification sous `scripts/tests/**` ne prouve pas que le perimetre est
    couvert. Le verdict est `tranche`, jamais `couvre`.
    """
    code, detail = td.verdict(MARQUEUR_GLOBE, COMPLET)
    assert code == td.TRANCHE, detail
    assert "scripts/tests/**" in detail, "le glob est dit"
    assert "ne certifie pas la completude" in detail


def test_une_livraison_complete_plus_etroite_que_l_issue_ne_couvre_pas():
    """NEGATIF 2 (demande par la revue du 19/11).

    La tranche livree est complete sur SON perimetre (le diff contient le
    fichier declare), mais l'issue porte une attribution plus large : la
    livraison ne livre pas l'issue, elle reste dans la rotation.
    """
    code, detail = td.verdict(TRANCHE_ETROITE, ["scripts/coordination/tapis_diff.py"],
                               ["scripts/coordination/tapis_diff.py",
                                "scripts/tests/test_tapis_qualification.py"])
    assert code == td.TRANCHE, detail
    assert "plus etroit que l'issue" in detail
    assert "scripts/tests/test_tapis_qualification.py" in detail, "le manque est dit"


def test_une_attribution_plus_large_que_la_tranche_laisse_l_issue_servie(monkeypatch):
    """Le meme cas, vu par la qualification : l'issue reste dans la file."""
    _faux_lecture(monkeypatch, _issue(TRANCHE_ETROITE, autres=[ATTRIBUTION]))
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: ["scripts/coordination/tapis_diff.py"])
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees


def test_un_diff_absent_ne_prouve_rien():
    """Pas de diff, pas de preuve : l'issue reste dans la rotation."""
    assert td.verdict(MARQUEUR, None)[0] == td.A_VERIFIER


def test_un_marqueur_sans_perimetre_ne_prouve_rien():
    ligne = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242"
    assert td.verdict(ligne, COMPLET)[0] == td.A_VERIFIER


def test_un_marqueur_sans_pr_designee_ne_prouve_rien():
    ligne = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- paths: a/**"
    assert td.verdict(ligne, ["a/x.py"])[0] == td.A_VERIFIER


def test_un_diff_complet_prouve_la_livraison(monkeypatch):
    """Le diff couvre le perimetre : l'issue est livree, elle sort de la file."""
    _faux_lecture(monkeypatch, _issue())
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: COMPLET)
    assert [e.numero for e in servis] == [], "une livraison prouvee n'est pas servie"
    assert ecartees[7]["code"] == "LIVREE"
    assert "couvre" in ecartees[7]["motif"]


def test_un_diff_partiel_laisse_l_issue_dans_la_rotation(monkeypatch):
    """Le diff ne couvre qu'une tranche : l'issue reste dans la rotation."""
    _faux_lecture(monkeypatch, _issue())
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: PARTIEL)
    assert [e.numero for e in servis] == [7], "l'issue revient dans la file"
    assert 7 not in ecartees
    assert any("reste dans la rotation" in n for n in servis[0].notes)


def test_sans_preuve_le_classement_reste_sur_le_marqueur(monkeypatch):
    """Pas de `preuve` : rien ne change (le classement n'est pas bascule)."""
    _faux_lecture(monkeypatch, _issue())
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run)
    assert [e.numero for e in servis] == [7]


def test_un_marqueur_sans_paths_ne_livrait_plus_l_issue(monkeypatch):
    """Un marqueur sans perimetre ne prouve rien : l'issue reste servable."""
    ligne = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242"
    _faux_lecture(monkeypatch, _issue(ligne))
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: COMPLET)
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees
