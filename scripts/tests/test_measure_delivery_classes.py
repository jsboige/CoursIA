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
