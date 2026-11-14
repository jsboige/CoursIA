#!/usr/bin/env python3
"""Tests du census des classes de marqueur (#23762).

Le census est un instrument de MESURE : sa seule fonction utile est de classer
la preuve qui soutient un statut de livraison. Ces tests pinent le classement,
qui est une fonction PURE -- ils ne touchent pas au reseau.

La regle de lecture : un detecteur se valide par ses faux NEGATIFS. Ici, le
risque n'est pas de rater une classe, mais d'en **inventer** une : une issue
doit tomber dans la classe que sa piece soutient, et dans aucune autre.
"""

import os
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from audit.measure_delivery_classes import (  # noqa: E402
    CLASSES,
    evidence_class,
    table,
)

ISSUE = {"number": 4242, "title": "un issue de test", "labels": [],
         "created_at": "2026-01-01T00:00:00Z", "body": "", "comments": []}


def merged_pr(body: str, pr_number: int = 100) -> dict:
    return {"pr_number": pr_number, "merged_at": "2026-01-02T00:00:00Z",
            "is_pr": True, "state": "closed", "body": body, "title": "t"}


def open_pr(body: str, pr_number: int = 101) -> dict:
    return {"pr_number": pr_number, "merged_at": None, "is_pr": True,
            "state": "open", "body": body, "title": "t"}


def test_verdict_candidate_donne_la_classe_fermant():
    assert evidence_class(ISSUE, [merged_pr("Closes #4242")], "candidate") == "fermant"


def test_attestation_soutenue_par_un_fermant():
    refs = [merged_pr("Closes #4242")]
    assert evidence_class(ISSUE, refs, "attested") == "attestation_fermant"


def test_attestation_soutenue_par_une_tranche():
    """`See #N` est une PIECE, mais une tranche : pas la preuve de l'issue."""
    refs = [merged_pr("See #4242 -- une tranche")]
    assert evidence_class(ISSUE, refs, "attested") == "attestation_tranche"


def test_attestation_sans_piece():
    """Aucune PR mergee ne declare l'issue : la seule preuve est la lane."""
    refs = [merged_pr("Closes #9999"), open_pr("See #4242")]
    assert evidence_class(ISSUE, refs, "attested") == "attestation_sans_piece"


def test_attestation_sans_piece_meme_sans_refs():
    assert evidence_class(ISSUE, [], "attested") == "attestation_sans_piece"


def test_verdict_partial_donne_la_classe_tranche():
    refs = [merged_pr("See #4242")]
    assert evidence_class(ISSUE, refs, "partial") == "tranche"


def test_verdict_no_delivery_donne_sans_preuve():
    assert evidence_class(ISSUE, [], "no_delivery") == "sans_preuve"


def test_les_verdicts_ne_qui_arant_pas_de_classe_propre_tombent_dans_autre():
    for verdict in ("epic", "container", "in_flight", "active", "retracted",
                    "attestation_revoked"):
        assert evidence_class(ISSUE, [], verdict) == "autre"


def test_un_marqueur_d_un_autre_issue_ne_soutient_pas_l_attestation():
    """La piece doit porter LE numero de l'issue (le meme contrat que
    `delivery_marker` : un `#N` qui n'est pas le nôtre ne prouve rien)."""
    refs = [merged_pr("Closes #7777")]
    assert evidence_class(ISSUE, refs, "attested") == "attestation_sans_piece"


def test_une_pr_ouverte_ne_soutient_pas_l_attestation():
    """Une PR ouverte, c'est du travail EN COURS : ce n'est pas une piece
    de livraison."""
    refs = [open_pr("Closes #4242")]
    assert evidence_class(ISSUE, refs, "attested") == "attestation_sans_piece"


def test_table_rend_les_effectifs_et_les_deux_listes():
    out = {
        "repo": "jsboige/CoursIA",
        "issues": 2,
        "rows": [
            {"number": 1, "title": "a", "verdict": "attested",
             "classe": "attestation_sans_piece", "label_actuel": True,
             "perdrait_le_label": False, "raison": ""},
            {"number": 2, "title": "b", "verdict": "partial",
             "classe": "tranche", "label_actuel": True,
             "perdrait_le_label": True, "raison": ""},
        ],
    }
    rendered = table(out)
    assert "attestation_sans_piece" in rendered
    assert "PERDRAIENT le label" in rendered
    assert "#2" in rendered


def test_les_classes_declarees_sont_celles_du_rendu():
    for name in CLASSES:
        assert name in table({"repo": "r", "issues": 0, "rows": []})


def test_collecte_partielle_signale_echec_et_conserve_succes(monkeypatch, capsys, tmp_path):
    """Un quota épuisé n'est ni une preuve absente ni un census complet."""
    import json
    from audit import measure_delivery_classes as measure

    monkeypatch.setattr(measure.cd, "list_open_issues", lambda repo: [
        {"number": 1, "title": "inaccessible", "labels": []},
        {"number": 2, "title": "lisible", "labels": []},
    ])

    def timeline(repo, number, label):
        if number == 1:
            raise RuntimeError("quota GitHub épuisé")
        return [], []

    monkeypatch.setattr(measure.cd, "timeline_facts", timeline)
    monkeypatch.setattr(measure.cd, "issue_detail", lambda repo, number: {
        "created_at": "2026-01-01T00:00:00Z", "body": "", "comments": [],
    })
    destination = tmp_path / "census.json"
    rc = measure.main(["--repo", "fixture/repo", "--sleep", "0",
                       "--json", str(destination)])
    out = json.loads(destination.read_text(encoding="utf-8"))
    rendered = capsys.readouterr().out

    assert rc == 1
    assert out["complete"] is False
    assert out["errors"] == 1
    assert out["issues"] == 2
    assert out["rows"][0]["classe"] == "erreur"
    assert out["rows"][1]["classe"] == "sans_preuve"
    assert "INCOMPLET" in rendered
    assert "#1" in rendered and "quota GitHub épuisé" in rendered
    assert "sans_preuve" in rendered


def test_collecte_complete_garde_rc_zero_et_json_lisible(monkeypatch, capsys, tmp_path):
    import json
    from audit import measure_delivery_classes as measure

    monkeypatch.setattr(measure.cd, "list_open_issues", lambda repo: [
        {"number": 2, "title": "lisible", "labels": []},
    ])
    monkeypatch.setattr(measure.cd, "timeline_facts", lambda *args: ([], []))
    monkeypatch.setattr(measure.cd, "issue_detail", lambda *args: {
        "created_at": "2026-01-01T00:00:00Z", "body": "", "comments": [],
    })
    destination = tmp_path / "census.json"
    assert measure.main(["--repo", "fixture/repo", "--sleep", "0",
                         "--json", str(destination)]) == 0
    out = json.loads(destination.read_text(encoding="utf-8"))
    assert out["complete"] is True
    assert out["errors"] == 0
    assert out["issues"] == 1
    assert out["rows"][0]["classe"] == "sans_preuve"
    assert "INCOMPLET" not in capsys.readouterr().out


@pytest.mark.parametrize("response", [
    RuntimeError("quota épuisé"),
    {"title": "corps absent"},
    {"body": None, "title": "corps illisible"},
])
def test_echec_lecture_pr_ne_devient_pas_absence_de_preuve(
        monkeypatch, capsys, tmp_path, response):
    """Le corps historique du renvoi ne remplace pas une lecture live échouée."""
    import json
    from audit import measure_delivery_classes as measure

    monkeypatch.setattr(measure.cd, "list_open_issues", lambda repo: [
        {"number": n, "title": "un travail", "labels": []} for n in (7, 8)
    ])
    monkeypatch.setattr(measure.cd, "timeline_facts", lambda repo, n, label: ([{
        "pr_number": 99 if n == 7 else 100, "is_pr": True,
        "merged_at": "2026-01-02T00:00:00Z", "state": "closed",
        "body": f"Closes #{n}",
    }], []))
    monkeypatch.setattr(measure.cd, "issue_detail", lambda *args: {
        "created_at": "2026-01-01T00:00:00Z", "body": "", "comments": [],
    })

    def pr_view(argv):
        if argv[2] == "99":
            if isinstance(response, Exception):
                raise response
            return response
        return {"body": "Closes #8", "title": "livraison de 8"}

    monkeypatch.setattr(measure.cd, "_gh_json", pr_view)
    destination = tmp_path / "census.json"
    assert measure.main(["--repo", "fixture/repo", "--sleep", "0",
                         "--json", str(destination)]) == 1
    out = json.loads(destination.read_text(encoding="utf-8"))
    assert out["complete"] is False and out["errors"] == 1
    assert out["rows"][0]["classe"] == "erreur"
    assert "PR #99" in out["rows"][0]["detail"]
    assert out["rows"][1]["verdict"] == "candidate"
    assert out["rows"][1]["classe"] == "fermant"
    rendered = capsys.readouterr().out
    assert "INCOMPLET" in rendered and "PR #99" in rendered


@pytest.mark.parametrize("body, expected", [("Closes #7", "fermant"),
                                            ("", "sans_preuve")])
def test_corps_pr_reellement_lu_soutient_le_classement(
        monkeypatch, body, expected):
    from audit import measure_delivery_classes as measure

    monkeypatch.setattr(measure.cd, "list_open_issues", lambda repo: [
        {"number": 7, "title": "un travail", "labels": []},
    ])
    monkeypatch.setattr(measure.cd, "timeline_facts", lambda *args: ([{
        "pr_number": 99, "is_pr": True, "state": "closed",
        "merged_at": "2026-01-02T00:00:00Z",
    }], []))
    monkeypatch.setattr(measure.cd, "issue_detail", lambda *args: {
        "created_at": "2026-01-01T00:00:00Z", "body": "", "comments": [],
    })
    monkeypatch.setattr(measure.cd, "_gh_json", lambda argv: {
        "body": body, "title": "corps courant",
    })
    out = measure.census("fixture/repo", sleep=0)
    assert out["complete"] is True and out["errors"] == 0
    assert out["rows"][0]["classe"] == expected
