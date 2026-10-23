#!/usr/bin/env python3
"""Tests de l'organe `approved_without_dossier` (#22089).

Ce que ces tests pinent, dans l'ordre du degat :

1. **Une approbation sur une tete depassee ne compte pas.** C'est le
   discriminant de l'issue : approuvee « quelque part » n'est pas approuvee
   « ici », et une PR absente de la liste parce qu'elle est perimee ne doit
   pas etre confondue avec une PR saine.
2. **Une PR avec dossier valide est exclue** : elle est deja dans la voie
   normale, l'organe ne doit pas la proposer une seconde fois.
3. **Tout vert = CHAINABLE, un seul rouge = WAITING avec sa cause nommee.**
   Un organe qui rend `CHAINABLE` sans regarder B.0, checks, mergeState et
   DWELL serait un zero propre.
4. **La pagination est bornee et les brouillons sont hors sujet.**

Run : python -m pytest scripts/tests/test_approved_without_dossier.py
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import approved_without_dossier as awd  # noqa: E402

HEAD = "a" * 40
OLD = "b" * 40


def _pr(number=1, head=HEAD, merge_state="CLEAN", reviews=None, draft=False):
    return {
        "number": number,
        "title": "t",
        "head": head,
        "merge_state": merge_state,
        "isDraft": draft,
        "reviews": reviews or [],
    }


def _review(login="myia-ai-01", state="APPROVED", oid=HEAD,
            submitted="2026-10-22T20:00:00Z"):
    return {"author": {"login": login}, "state": state,
            "submittedAt": submitted, "commit": {"oid": oid}}


GREEN_PROBES = {
    "dossier": {"ready": False, "verdict": "NO_DOSSIER"},
    "b0": {"blocked": False, "blocking": []},
    "checks": {"green": True, "reds": []},
    "dwell": {"ok": True, "message": "dwell ecoule"},
}


# --- 1. le discriminant : a la tete, ou pas -------------------------------


def test_approbation_a_la_tete_compte():
    assert awd.approval_verdict(_pr(reviews=[_review()])) == "at_head"


def test_approbation_sur_tete_depassee_est_absente():
    pr = _pr(reviews=[_review(oid=OLD)])
    assert awd.approval_verdict(pr) == "stale"
    assert awd.candidates([pr]) == [], (
        "une approbation sur une tete depassee ne doit pas entrer dans la liste"
    )


def test_la_derniere_review_fait_foi_pas_la_premiere():
    """Une approbation ancienne suivie d'un CHANGES_REQUESTED ne compte pas."""
    pr = _pr(reviews=[
        _review(state="APPROVED", submitted="2026-10-22T10:00:00Z"),
        _review(state="CHANGES_REQUESTED", submitted="2026-10-22T12:00:00Z"),
    ])
    assert awd.approval_verdict(pr) == "none"


def test_un_autre_approbateur_ne_compte_pas():
    pr = _pr(reviews=[_review(login="hermes-bot")])
    assert awd.approval_verdict(pr) == "none"


def test_l_ordre_des_lignes_ne_decide_pas():
    """`latestReviews` ne garantit pas l'ordre : c'est `submittedAt` qui
    tranche. Une APPROVED posterieure gagne meme placee en premier."""
    pr = _pr(reviews=[
        _review(state="APPROVED", submitted="2026-10-22T22:00:00Z"),
        _review(state="CHANGES_REQUESTED", submitted="2026-10-22T12:00:00Z"),
    ])
    assert awd.approval_verdict(pr) == "at_head"


# --- 2. une PR deja dossiersee est hors sujet -----------------------------


def test_pr_avec_dossier_valide_est_exclue():
    probes = dict(GREEN_PROBES, dossier={"ready": True, "verdict": "READY"})
    status, causes = awd.classify(_pr(), probes)
    assert status == "EXCLUDED"
    assert causes == ["dossier-valide"]


# --- 3. CHAINABLE / WAITING avec cause nommee ----------------------------


def test_tout_vert_rend_chaineable():
    status, causes = awd.classify(_pr(), GREEN_PROBES)
    assert status == "CHAINABLE"
    assert causes == []


def test_b0_bloque_rend_waiting_avec_cause():
    probes = dict(GREEN_PROBES, b0={"blocked": True, "blocking": ["x", "y"]})
    status, causes = awd.classify(_pr(), probes)
    assert status == "WAITING"
    assert causes == ["b0:2"]


def test_checks_rouges_rend_waiting_avec_les_jambes():
    probes = dict(GREEN_PROBES,
                  checks={"green": False, "reds": ["A", "B", "C", "D"]})
    status, causes = awd.classify(_pr(), probes)
    assert status == "WAITING"
    assert causes[0].startswith("checks:")
    assert "A,B,C" in causes[0], "au plus trois jambes nommees"


def test_merge_state_non_clean_rend_waiting():
    status, causes = awd.classify(_pr(merge_state="BLOCKED"), GREEN_PROBES)
    assert status == "WAITING"
    assert causes == ["mergeStateStatus:BLOCKED"]


def test_dwell_non_ecoule_rend_waiting():
    probes = dict(GREEN_PROBES, dwell={"ok": False, "message": "reste 100 min"})
    status, causes = awd.classify(_pr(), probes)
    assert status == "WAITING"
    assert "dwell" in causes


def test_dwell_saute_ne_bloque_pas_mais_ne_prouve_rien():
    """`ok=None` = mesure sautee explicitement (`--no-dwell`) : ce n'est pas
    un rouge, donc pas une cause de WAITING. Le contrat est ecrit ici pour
    qu'un futur changement soit conscient : cet etat ne prouve RIEN sur le
    plancher, il dit seulement « non mesure »."""
    probes = dict(GREEN_PROBES, dwell={"ok": None, "message": "saute"})
    assert awd.classify(_pr(), probes) == ("CHAINABLE", [])


# --- 4. pagination bornee, brouillons hors sujet --------------------------


def _node(number=1, head=HEAD, merge_state="CLEAN", reviews=None,
          draft=False):
    """Noeud GraphQL BRUT (noms de champs de l'API, pas la forme aplatie)."""
    return {
        "number": number,
        "title": "t",
        "isDraft": draft,
        "headRefOid": head,
        "mergeStateStatus": merge_state,
        "latestReviews": {"nodes": [_review()] if reviews is None
                          else reviews},
    }


def _page(nodes, has_next, cursor="c1"):
    return {"data": {"repository": {"pullRequests": {
        "pageInfo": {"hasNextPage": has_next, "endCursor": cursor},
        "nodes": nodes,
    }}}}


def test_les_brouillons_sont_exclus():
    pages = [_page([_node(number=1, draft=True), _node(number=2)], False)]
    assert [p["number"] for p in awd.parse_pages(pages)] == [2]


def test_le_curseur_suit_has_next_page():
    assert awd.page_cursor([_page([], True)]) == "c1"
    assert awd.page_cursor([_page([], False)]) is None
    assert awd.page_cursor([]) is None


def test_l_aplatissement_conserve_head_et_merge_state():
    pages = [_page([_node(number=7, merge_state="UNKNOWN")], False)]
    parsed = awd.parse_pages(pages)
    assert parsed[0]["head"] == HEAD
    assert parsed[0]["merge_state"] == "UNKNOWN"
    assert awd.approval_verdict(parsed[0]) == "at_head"


# --- _run_json contre les sorties REELLES des organes delegues (review #22102) ---
#
# Hermes a prouve que le scan « derniere ligne commencant par { » ne lit
# JAMAIS check_unaddressed_nits (31 lignes, indent=1) ni check_run_state
# (483 lignes, indent=1) : seule la premiere ligne commence par « { » (elle
# est seule), json.loads("{") echoue, _run_json rend None et les probes
# b0/checks fail-close en « unreadable » sur CHAQUE run. Ces temoins
# nourrissent _run_json avec ces formes reelles.


def _fake_subprocess(stdout: str):
    def fake_run(cmd, **kwargs):
        return subprocess.CompletedProcess(cmd, 0, stdout=stdout, stderr="")

    return fake_run


def test_run_json_lit_un_bloc_indent_multi_lignes(monkeypatch):
    # Forme reelle de check_run_state.py --json : json.dumps(..., indent=1).
    payload = {
        "head": HEAD,
        "latest": {"Build": {"conclusion": "success"}},
        "residual_reds": [],
    }
    bloc = json.dumps(payload, indent=1, ensure_ascii=False)
    assert len(bloc.splitlines()) >= 4  # bien un bloc multi-lignes
    monkeypatch.setattr(awd.subprocess, "run", _fake_subprocess(bloc))
    assert awd._run_json(["organe", "--pr", "7"]) == payload


def test_run_json_garde_le_repli_ligne_d_usage_prependee(monkeypatch):
    # Cas documente du repli : une ligne d'usage PUIS un JSON sur une ligne.
    out = "usage: organe --pr N --json\n" + json.dumps({"blocked": False})
    monkeypatch.setattr(awd.subprocess, "run", _fake_subprocess(out))
    assert awd._run_json(["organe"]) == {"blocked": False}


def test_run_json_ligne_unique_sans_usage(monkeypatch):
    # Forme reelle de check_adjoint_prevalidation.py --json : une seule ligne.
    out = json.dumps({"ready": False, "verdict": "NO_DOSSIER"})
    monkeypatch.setattr(awd.subprocess, "run", _fake_subprocess(out))
    assert awd._run_json(["organe"]) == {"ready": False, "verdict": "NO_DOSSIER"}


def test_run_json_sortie_illisible_rend_none(monkeypatch):
    monkeypatch.setattr(awd.subprocess, "run", _fake_subprocess("panic: boom"))
    assert awd._run_json(["organe"]) is None
