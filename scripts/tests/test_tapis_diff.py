"""La preuve de livraison par le DIFF (revue 5967171401, 19/11).

Un marqueur `[DELIVERED]` **designe** une PR a verifier ; la preuve, c'est le
diff de cette PR couvrant le perimetre declare. Meme marqueur, deux diffs,
deux verdicts : c'est le temoin demande par la revue.

**Revision du 19/11 (revue du coordinateur, DM `night-27242-glob-is-not-whole-scope`)** :
le perimetre d'une tranche livree est ecrit en **chemins explicites** (la
pratique des tranches livrees sur #27242), et un **glob ne certifie jamais la
completude** : une seule modification sous `scripts/tests/**` ne prouve pas
que le perimetre est couvert. Deux controles negatifs verrouillent la regle.

**Revision du 19/11, 2e tour (DM `night-27242-unknown-scope-stays-in-rotation`)** :
une livraison complete exige **deux** choses -- un perimetre **independant
du marqueur de livraison** (l'attribution portee par l'issue) et **l'etat de
la PR**. Deux temoins le verrouillent : l'issue **sans attribution** et la PR
**fermee sans fusion** ne livrent pas l'issue ; elle reste dans la rotation.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_diff as td
from coordination import tapis_qualification as tq
from coordination.tapis_preuve import Preuve

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

#: L'attribution **egale** au perimetre livre : une livraison complete, sur
#: une issue dont le perimetre attribue est connu et couvert.
ATTRIBUTION_EGALE = ("[CLAIMED] lane myia-ai-01:CoursIA-2 -- paths: "
                     "scripts/coordination/tapis_diff.py, scripts/tests/test_tapis_diff.py")
PERIMETRE_ATTRIBUE = ["scripts/coordination/tapis_diff.py",
                      "scripts/tests/test_tapis_diff.py"]


def _preuve(fichiers, etat: str = "OPEN", fusionne: bool = False) -> Preuve:
    """La preuve d'une livraison : les fichiers modifies ET l'etat de la PR."""
    return Preuve(tuple(fichiers), etat, fusionne)


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
    complet = td.verdict(MARQUEUR, _preuve(COMPLET), PERIMETRE_ATTRIBUE)
    partiel = td.verdict(MARQUEUR, _preuve(PARTIEL), PERIMETRE_ATTRIBUE)
    assert complet[0] == td.COUVRE, complet[1]
    assert partiel[0] == td.TRANCHE, partiel[1]
    assert "scripts/tests/test_tapis_diff.py" in partiel[1], "le manque est dit"


def test_un_seul_fichier_sous_un_glob_qui_en_attend_plusieurs_ne_couvre_pas():
    """NEGATIF 1 (demande par la revue du 19/11).

    Un glob ne dit pas combien de fichiers il attend : une seule
    modification sous `scripts/tests/**` ne prouve pas que le perimetre est
    couvert. Le verdict est `tranche`, jamais `couvre`.
    """
    code, detail = td.verdict(MARQUEUR_GLOBE, _preuve(COMPLET), PERIMETRE_ATTRIBUE)
    assert code == td.TRANCHE, detail
    assert "scripts/tests/**" in detail, "le glob est dit"
    assert "ne certifie pas la completude" in detail


def test_une_livraison_complete_plus_etroite_que_l_issue_ne_couvre_pas():
    """NEGATIF 2 (demande par la revue du 19/11).

    La tranche livree est complete sur SON perimetre (le diff contient le
    fichier declare), mais l'issue porte une attribution plus large : la
    livraison ne livre pas l'issue, elle reste dans la rotation.
    """
    code, detail = td.verdict(TRANCHE_ETROITE, _preuve(["scripts/coordination/tapis_diff.py"]),
                               ["scripts/coordination/tapis_diff.py",
                                "scripts/tests/test_tapis_qualification.py"])
    assert code == td.TRANCHE, detail
    assert "plus etroit que l'issue" in detail
    assert "scripts/tests/test_tapis_qualification.py" in detail, "le manque est dit"


def test_une_issue_sans_attribution_ne_livrait_pas_l_issue():
    """TEMOIN 3 (demande du coordinateur, 19/11).

    L'issue ne porte **aucun** marqueur d'attribution : son perimetre
    attribue est **inconnu**, pas « vide et donc satisfait ». Le diff peut
    attester une **tranche**, pas une livraison complete : l'issue reste
    dans la rotation.
    """
    code, detail = td.verdict(MARQUEUR, _preuve(COMPLET))
    assert code == td.TRANCHE, detail
    assert "attribution inconnue" in detail, detail
    assert "tranche" in detail


def test_une_attribution_globale_ne_livrait_pas_l_issue():
    """L'attribution **globale** (marqueur sans `paths:`) ne certifie rien.

    Son perimetre est l'issue entiere : un diff ne peut pas le couvrir, il
    n'atteste qu'une tranche.
    """
    code, detail = td.verdict(MARQUEUR, _preuve(COMPLET), [])
    assert code == td.TRANCHE, detail
    assert "attribution globale" in detail


def test_une_pr_fermee_sans_fusion_ne_livrait_pas_l_issue():
    """TEMOIN 4 (demande du coordinateur, 19/11).

    `/files` ne dit pas si la PR a ete integree : une PR **fermee sans
    fusion** porte un diff complet, mais le travail n'est jamais arrive sur
    `main`. La livraison n'a pas eu lieu.
    """
    code, detail = td.verdict(MARQUEUR, _preuve(COMPLET, "CLOSED", False),
                               PERIMETRE_ATTRIBUE)
    assert code == td.A_VERIFIER, detail
    assert "fermee sans fusion" in detail


def test_une_pr_fusionnee_livrait_bien_l_issue():
    """Le temoin positif de l'etat : une PR fusionnee atteste la livraison."""
    code, detail = td.verdict(MARQUEUR, _preuve(COMPLET, "CLOSED", True),
                               PERIMETRE_ATTRIBUE)
    assert code == td.COUVRE, detail


def test_un_etat_de_pr_inconnu_ne_prouve_rien():
    """Une preuve sans etat est **incomplete** : fail-CLOSED, elle n'atteste
    pas une livraison complete."""
    code, detail = td.verdict(MARQUEUR, Preuve(tuple(COMPLET)), PERIMETRE_ATTRIBUE)
    assert code == td.A_VERIFIER, detail
    assert "etat de la PR inconnu" in detail


def test_une_issue_sans_attribution_reste_dans_la_rotation(monkeypatch):
    """Le temoin 3 vu par la qualification : l'issue reste servable."""
    _faux_lecture(monkeypatch, _issue())
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: _preuve(COMPLET))
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees


def test_une_pr_fermee_sans_fusion_reste_dans_la_rotation(monkeypatch):
    """Le temoin 4 vu par la qualification : l'issue reste servable."""
    _faux_lecture(monkeypatch, _issue(MARQUEUR, autres=[ATTRIBUTION_EGALE]))
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run,
        preuve=lambda pr: _preuve(COMPLET, "CLOSED", False))
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees
    assert any("fermee sans fusion" in n for n in servis[0].notes)


def test_une_attribution_plus_large_que_la_tranche_laisse_l_issue_servie(monkeypatch):
    """Le meme cas, vu par la qualification : l'issue reste dans la file."""
    _faux_lecture(monkeypatch, _issue(TRANCHE_ETROITE, autres=[ATTRIBUTION]))
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run,
        preuve=lambda pr: _preuve(["scripts/coordination/tapis_diff.py"]))
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees


def test_un_diff_absent_ne_prouve_rien():
    """Pas de diff, pas de preuve : l'issue reste dans la rotation."""
    assert td.verdict(MARQUEUR, None)[0] == td.A_VERIFIER


def test_un_marqueur_sans_perimetre_ne_prouve_rien():
    ligne = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- PR #27242"
    assert td.verdict(ligne, _preuve(COMPLET))[0] == td.A_VERIFIER


def test_un_marqueur_sans_pr_designee_ne_prouve_rien():
    ligne = "[DELIVERED] lane myia-ai-01:CoursIA-2 -- paths: a/**"
    assert td.verdict(ligne, _preuve(["a/x.py"]))[0] == td.A_VERIFIER


def test_un_diff_complet_prouve_la_livraison(monkeypatch):
    """Le diff couvre le perimetre, l'attribution est connue et couverte, la
    PR est integree : l'issue est livree, elle sort de la file."""
    _faux_lecture(monkeypatch, _issue(MARQUEUR, autres=[ATTRIBUTION_EGALE]))
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: _preuve(COMPLET))
    assert [e.numero for e in servis] == [], "une livraison prouvee n'est pas servie"
    assert ecartees[7]["code"] == "LIVREE"
    assert "couvre" in ecartees[7]["motif"]


def test_un_diff_partiel_laisse_l_issue_dans_la_rotation(monkeypatch):
    """Le diff ne couvre qu'une tranche : l'issue reste dans la rotation."""
    _faux_lecture(monkeypatch, _issue())
    servis, ecartees, echecs, arrete, appels, chrono = tq.qualifier(
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: _preuve(PARTIEL))
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
        [7], LANE, NOW, 45, [], _run, preuve=lambda pr: _preuve(COMPLET))
    assert [e.numero for e in servis] == [7], "l'issue reste dans la rotation"
    assert 7 not in ecartees
