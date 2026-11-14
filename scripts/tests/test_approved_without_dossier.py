#!/usr/bin/env python3
"""Tests de l'organe `approved_without_dossier` (#22089).

Ce que ces tests pinent, dans l'ordre du degat :

1. **Une approbation sur une tete depassee ne compte pas** -- sauf quand elle
   ne differe de la tete courante que par des rafraichissements de base
   prouves content-free : c'est la couverture Q131, et le predicat qui la
   rend est celui de `merge_ready`, jamais une copie locale.
2. **Une PR dont la voix du coordinateur a ete perimee sort en WAITING**,
   avec son geste nomme (`approval:stale`), pas en silence.
3. **Tout vert = CHAINABLE, un seul rouge = WAITING avec sa cause nommee.**
   Un organe qui rend `CHAINABLE` sans regarder B.0, checks, mergeState et
   DWELL serait un zero propre.
4. **`unstable` est tranche par le predicat importe**, pas par une regle
   locale -- et fail-closed quand la mesure manque.
5. **La pagination est bornee, les brouillons sont hors sujet, et le mode
   REST dit la meme chose que le mode GraphQL.**

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
BASE = "d" * 40


def _pr(number=1, head=HEAD, merge_state="CLEAN", reviews=None, draft=False):
    return {
        "number": number,
        "title": "t",
        "head": head,
        "base_oid": BASE,
        "merge_state": merge_state,
        "isDraft": draft,
        "reviews": reviews or [],
    }


def _review(login="myia-ai-01", state="APPROVED", oid=HEAD,
            submitted="2026-10-22T20:00:00Z", typename="User", body=""):
    return {"author": {"login": login, "__typename": typename},
            "state": state, "body": body,
            "submittedAt": submitted, "commit": {"oid": oid}}


GREEN_PROBES = {
    "b0": {"blocked": False, "blocking": []},
    "checks": {"green": True, "reds": []},
    "dwell": {"ok": True, "message": "dwell ecoule"},
}


# --- 1. le discriminant : a la tete, couvrante, ou pas --------------------


def test_approbation_a_la_tete_compte():
    assert awd.approval_verdict(_pr(reviews=[_review()])) == "at_head"


def test_approbation_sur_tete_depassee_est_absente():
    pr = _pr(reviews=[_review(oid=OLD)])
    assert awd.approval_verdict(pr) == "stale"
    assert awd.candidates([pr]) == [], (
        "une approbation sur une tete depassee ne doit pas entrer dans la liste"
    )


def test_approbation_sur_tete_depassee_sans_runner_ne_prouve_pas_la_couverture():
    """Sans runner, la couverture Q131 n'est pas mesurable : `stale`.

    Fail-closed : l'organe ne suppose jamais qu'un rafraichissement etait
    sans conflit pour se dispenser de la preuve.
    """
    pr = _pr(reviews=[_review(oid=OLD)])
    assert awd.approval_verdict(pr, runner=None) == "stale"


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


def test_une_approbation_d_app_ne_gouverne_pas():
    """La voix du coordinateur est le login humain seul (#17437) : une App,
    meme homonyme, n'est pas une approbation."""
    pr = _pr(reviews=[_review(login="coursia-lane-ai-01", typename="Bot")])
    assert awd.approval_verdict(pr) == "none"


# --- 1 bis. la couverture Q131, deleguee au predicat de merge_ready --------


def test_approbation_rafraichie_sans_conflit_est_couvrante(monkeypatch):
    """Controle POSITIF (arbitrage ai-01) : une PR approuvee puis rafraichie
    sans conflit sort CHAINABLE.

    Le predicat est celui de `merge_ready`, et le test verifie qu'il est
    reellement appele avec la base de la PR : si l'organe recopiait la regle,
    ce temoin ne verrait aucun appel.
    """
    pr = _pr(number=31, reviews=[_review(oid=OLD)])
    seen = []

    def fake_reason(view, head, runner, gh_env):
        seen.append((view.get("baseRefOid"), head))
        return None  # « les deux tetes remontent au meme commit de contenu »

    monkeypatch.setattr(awd.merge_ready, "coordinator_approval_reason",
                        fake_reason)
    runner = object()

    assert awd.approval_verdict(pr, runner=runner) == "covering"
    assert seen == [(BASE, HEAD)], (
        "le predicat importe doit recevoir la base et la tete courante")
    assert awd.candidates([pr], runner=runner) == [pr]

    screened = awd.screen([pr], runner=runner)
    assert [s["approval"] for s in screened] == ["covering"]
    assert screened[0]["status"] is None, "a classifier sur les probes"
    status, causes = awd.classify(pr, GREEN_PROBES)
    assert (status, causes) == ("CHAINABLE", [])


def test_approbation_rafraichie_avec_conflit_sort_waiting(monkeypatch):
    """Controle NEGATIF (arbitrage ai-01) : un rafraichissement qui a resolu
    un conflit perime la lecture, et la PR sort WAITING."""
    pr = _pr(number=32, reviews=[_review(oid=OLD)])
    monkeypatch.setattr(awd.merge_ready, "coordinator_approval_reason",
                        lambda view, head, runner, gh_env:
                        "coordinator-approval-stale")
    runner = object()

    assert awd.approval_verdict(pr, runner=runner) == "stale"
    assert awd.candidates([pr], runner=runner) == []

    screened = awd.screen([pr], runner=runner)
    assert len(screened) == 1
    assert screened[0]["status"] == "WAITING"
    assert screened[0]["causes"] == ["approval:stale"]


def test_une_pr_sans_voix_du_coordinateur_n_est_pas_du_sujet():
    pr = _pr(reviews=[_review(login="hermes-bot")])
    assert awd.screen([pr]) == [], (
        "les PRs vertes non approuvees sont un autre livrable")


# --- 2. CHAINABLE / WAITING avec cause nommee ----------------------------


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


# --- 3. `unstable` : le predicat de merge_ready decide (#25059) ----------


def test_unstable_sans_runner_reste_waiting():
    """Une mesure impossible n'est pas une acceptation."""
    status, causes = awd.classify(_pr(merge_state="UNSTABLE"), GREEN_PROBES)
    assert status == "WAITING"
    assert causes == ["mergeStateStatus:UNSTABLE:unstable-not-measured"]


def test_unstable_accepte_par_le_predicat_importe_est_chaineable(monkeypatch):
    seen = []

    def fake_reason(runner, pr, head, gh_env):
        seen.append((pr, head))
        return None, "unstable-accepted:2"

    monkeypatch.setattr(awd.merge_ready, "unstable_state_reason", fake_reason)
    status, causes = awd.classify(_pr(number=7, merge_state="UNSTABLE"),
                                  GREEN_PROBES, runner=object())
    assert (status, causes) == ("CHAINABLE", [])
    assert seen == [(7, HEAD)]


def test_unstable_refuse_par_le_predicat_nomme_la_cause(monkeypatch):
    monkeypatch.setattr(awd.merge_ready, "unstable_state_reason",
                        lambda runner, pr, head, gh_env:
                        ("unstable-check-red:Build", ""))
    status, causes = awd.classify(_pr(number=8, merge_state="UNSTABLE"),
                                  GREEN_PROBES, runner=object())
    assert status == "WAITING"
    assert causes == ["mergeStateStatus:UNSTABLE:unstable-check-red:Build"]


# --- 4. pagination bornee, brouillons hors sujet -------------------------


def _node(number=1, head=HEAD, merge_state="CLEAN", reviews=None,
          draft=False, base=BASE):
    """Noeud GraphQL BRUT (noms de champs de l'API, pas la forme aplatie)."""
    return {
        "number": number,
        "title": "t",
        "isDraft": draft,
        "headRefOid": head,
        "baseRefOid": base,
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


def test_l_aplatissement_conserve_head_merge_state_et_base():
    pages = [_page([_node(number=7, merge_state="UNKNOWN")], False)]
    parsed = awd.parse_pages(pages)
    assert parsed[0]["head"] == HEAD
    assert parsed[0]["base_oid"] == BASE
    assert parsed[0]["merge_state"] == "UNKNOWN"
    assert awd.approval_verdict(parsed[0]) == "at_head"


# --- 5. mode REST : meme lecture, autre porte ----------------------------


def _rest_item(number=1, head=HEAD, state="clean", draft=False,
               base=BASE):
    return {
        "number": number,
        "title": "t",
        "draft": draft,
        "head": {"sha": head},
        "base": {"sha": base},
        "mergeable_state": state,
    }


def test_parse_rest_met_l_etat_en_majuscules_et_exclut_les_brouillons():
    parsed = awd.parse_rest([
        _rest_item(number=1, draft=True),
        _rest_item(number=2, state="unstable"),
    ])
    assert [p["number"] for p in parsed] == [2]
    assert parsed[0]["merge_state"] == "UNSTABLE"
    assert parsed[0]["base_oid"] == BASE


def test_parse_rest_unknown_ou_absent_reste_unknown():
    parsed = awd.parse_rest([_rest_item(number=3, state=None)])
    assert parsed[0]["merge_state"] == "UNKNOWN"


def test_rest_sort_la_meme_chose_que_graphql(monkeypatch):
    """Les deux portes nourrissent le meme predicat : une PR approuvee a la
    tete est candidate des deux cotes.

    En REST la liste ne porte aucune review : c'est la relecture typee par le
    runner qui fait foi. Le test la remplace par le verdict qu'elle rendrait.
    """
    rest = awd.parse_rest([_rest_item(number=5)])
    graph = awd.parse_pages([_page([_node(number=5)], False)])
    monkeypatch.setattr(awd.merge_ready, "coordinator_approval_oid",
                        lambda view, runner=None, gh_env=None: HEAD)
    assert [p["number"] for p in awd.candidates(rest, runner=object())] == [5]
    assert [p["number"] for p in awd.candidates(graph)] == [5]


# --- 5 bis. `UNKNOWN` n'est pas un verdict : on le re-mesure ---------------


def test_merge_state_inconnu_est_remesure_par_la_lecture_unitaire(monkeypatch):
    """Les deux listes (GraphQL et REST) rendent `unknown` tant que GitHub n'a
    pas calcule la fusionabilite. Sans cette re-mesure, une PR `clean` sort en
    `WAITING mergeStateStatus:UNKNOWN` et la liste nominative ne dit plus rien
    de son blocage reel (mesure du 14/11 : 5 PRs sur 8 dans ce cas)."""
    seen = []

    def fake_probe(repo, pr):
        seen.append((repo, pr))
        return "CLEAN"

    monkeypatch.setattr(awd, "probe_merge_state_rest", fake_probe)
    pr = _pr(number=9, merge_state="UNKNOWN")
    awd.resolve_merge_state("jsboige/CoursIA", pr)
    assert pr["merge_state"] == "CLEAN"
    assert seen == [("jsboige/CoursIA", 9)]


def test_un_etat_deja_mesure_n_est_pas_repaye(monkeypatch):
    monkeypatch.setattr(awd, "probe_merge_state_rest",
                        lambda repo, pr: "DIRTY")
    pr = _pr(number=10, merge_state="CLEAN")
    awd.resolve_merge_state("jsboige/CoursIA", pr)
    assert pr["merge_state"] == "CLEAN"


def test_une_re_mesure_illisible_laisse_unknown(monkeypatch):
    """Fail-closed : une mesure impossible ne devient pas une acceptation."""
    monkeypatch.setattr(awd, "probe_merge_state_rest", lambda repo, pr: None)
    pr = _pr(number=11, merge_state="UNKNOWN")
    awd.resolve_merge_state("jsboige/CoursIA", pr)
    assert pr["merge_state"] == "UNKNOWN"


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
    # Forme d'un organe qui sort son objet sur une seule ligne.
    out = json.dumps({"heads": 3, "reds": []})
    monkeypatch.setattr(awd.subprocess, "run", _fake_subprocess(out))
    assert awd._run_json(["organe"]) == {"heads": 3, "reds": []}


def test_run_json_sortie_illisible_rend_none(monkeypatch):
    monkeypatch.setattr(awd.subprocess, "run", _fake_subprocess("panic: boom"))
    assert awd._run_json(["organe"]) is None


# --- 6. probe_checks : skipped/neutral ne sont pas des rouges (#25092) ---


def test_probe_checks_ne_compte_pas_skipped_neutral_rouges(monkeypatch):
    """`skipped` et `neutral` sont des VERTES, miroir des trois organes
    canoniques : le predicate de `probe_checks` ne doit compter que
    `failure`/`timed_out`. Le predicate precedent (`!= "success"`) comptait
    skipped/neutral comme rouges et fabriquait des rouges fantomes sur des
    jambes desactivees (ex. Build Quarto / Deploy Pages d'une PR de docs)."""
    payload = {
        "head": HEAD,
        "latest": {
            "Build": {"conclusion": "success"},
            "Quarto": {"conclusion": "skipped"},
            "Deploy": {"conclusion": "skipped"},
            "Advisory": {"conclusion": "neutral"},
            "Tests": {"conclusion": "failure"},
            "Slow": {"conclusion": "timed_out"},
        },
        "residual_reds": [],
    }
    bloc = json.dumps(payload, indent=1, ensure_ascii=False)
    monkeypatch.setattr(awd.subprocess, "run", _fake_subprocess(bloc))
    result = awd.probe_checks(7, HEAD)
    assert result["green"] is False
    assert result["reds"] == ["Slow", "Tests"]