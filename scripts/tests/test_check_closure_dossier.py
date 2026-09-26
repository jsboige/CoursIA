#!/usr/bin/env python3
"""Tests du gate de fermeture d'issues check_closure_dossier.py (#17956 pt 3).

L'acceptance du dispatch, case par case :

  - dossier auto-atteste (lane = lane du Grain: livrant)      -> refuse (rc 1)
  - dossier anterieur au dernier commentaire non neutre       -> refuse (rc 1)
  - PR ouverte referencant l'issue                             -> refuse (rc 1)
  - dossier CLOSE integre                                       -> rc 0
  - dossier KEEP integre                                        -> rc 3
  - dossier absent                                              -> rc 1
  - fille citee fermee                                          -> refuse (rc 1)
  - PR citee non merged                                         -> refuse (rc 1)

Le reseau (gh) est monkeypathe au niveau de ``gh_json`` : les snapshots sont
construits a la main, seuls les controles followup/PR-citee declenchent des
appels supplementaires.
"""

import sys
import os

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_closure_dossier as ccd  # noqa: E402
from check_closure_dossier import (  # noqa: E402
    Dossier,
    evaluate,
    parse_dossier,
    render_template,
    validate_dossier,
    main,
)


def _comment(body, login="jsboige", created="2026-09-20T10:00:00Z"):
    return {"author": {"login": login}, "created_at": created, "body": body}


def _dossier_body(lane="myia-po-2025:CoursIA-2", issue=17900, verdict="CLOSE",
                  items=("critere A -> PR #17901",), residue="none",
                  open_prs=0, comments_reviewed=0):
    lines = [
        "[CLOSURE PREFLIGHT]",
        "schema: 1",
        f"lane: {lane}",
        f"issue: {issue}",
        f"verdict: {verdict}",
        "acceptance:",
        *(f"  - {item}" for item in items),
        f"residue: {residue}",
        f"open-prs: {open_prs}",
        f"comments-reviewed: {comments_reviewed}",
        "[/CLOSURE PREFLIGHT]",
    ]
    return "\n".join(lines)


def _snapshot(issue=17900, comments=(), merged_prs=None, open_prs=(),
              state="OPEN"):
    return {
        "repo": "o/r",
        "number": issue,
        "title": "Corriger le rendu SVG",
        "state": state,
        "labels": [],
        "created_at": "2026-08-01T00:00:00Z",
        "comments": list(comments),
        "merged_prs": merged_prs if merged_prs is not None else [
            {"number": 17901, "merged_at": "2026-09-19T10:00:00Z",
             "body": "Grain: DEEP/notebook-python — lane myia-po-2024:CoursIA "
                     "-- See #17900."},
        ],
        "open_prs": list(open_prs),
    }


# --- cas nominaux de l'acceptance -------------------------------------------

def test_close_integre():
    snap = _snapshot(comments=[_comment(_dossier_body())])
    verdict, errors, dossier = evaluate(snap)
    assert verdict == "CLOSE"
    assert errors == []
    assert dossier.fields["lane"] == "myia-po-2025:CoursIA-2"


def test_keep_integre(monkeypatch):
    monkeypatch.setattr(ccd, "gh_json", lambda args: {
        "number": 17910, "state": "OPEN"})
    snap = _snapshot(comments=[
        _comment(_dossier_body(verdict="KEEP", residue="followup #17910"))])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "KEEP"
    assert errors == []


def test_no_dossier():
    snap = _snapshot(comments=[_comment("un commentaire ordinaire")])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "NO-DOSSIER"
    assert any("no [CLOSURE PREFLIGHT]" in e for e in errors)


def test_auto_atteste_par_grain_de_la_pr_livrante():
    # La lane du dossier est celle du Grain: de la PR merged qui reference
    # l'issue : elle atteste son propre travail -> refuse.
    snap = _snapshot(comments=[
        _comment(_dossier_body(lane="myia-po-2024:CoursIA"))])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("self-attestation" in e for e in errors)


def test_auto_atteste_par_delivered_de_lissue():
    # Meme refus quand la lane est celle du [DELIVERED] pose sur l'issue.
    snap = _snapshot(comments=[
        _comment("[DELIVERED] lane myia-po-2026:CoursIA -- tranche livree"),
        _comment(_dossier_body(lane="myia-po-2026:CoursIA",
                               comments_reviewed=1)),
    ])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("self-attestation" in e for e in errors)


def test_stale_par_commentaire_non_neutre_posterieur():
    # Un humain reprend la discussion apres le dossier : perime.
    snap = _snapshot(comments=[
        _comment(_dossier_body(), created="2026-09-20T10:00:00Z"),
        _comment("En fait le critere B n'est pas satisfait",
                 created="2026-09-21T09:00:00Z"),
    ])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("postdates it" in e for e in errors)


def test_commentaire_neutre_posterieur_ne_perime_pas():
    # Le bloc d'un autre dossier (grammaire adjoint) est neutre : il ne
    # perime pas le dossier de fermeture.
    snap = _snapshot(comments=[
        _comment(_dossier_body(), created="2026-09-20T10:00:00Z"),
        _comment("[ADJOINT PREFLIGHT]\nschema: 1\n[/ADJOINT PREFLIGHT]",
                 created="2026-09-21T09:00:00Z"),
    ])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "CLOSE"
    assert errors == []


def test_pr_ouverte_referencant_lissue_refuse():
    # Le contrat dit open-prs: 0 ; le live en trouve une -> perime.
    snap = _snapshot(comments=[_comment(_dossier_body())], open_prs=[18050])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("open-prs is stale" in e for e in errors)


def test_fille_citee_fermee_refuse(monkeypatch):
    monkeypatch.setattr(ccd, "gh_json", lambda args: {
        "number": 17910, "state": "CLOSED"})
    snap = _snapshot(comments=[
        _comment(_dossier_body(residue="followup #17910"))])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("followup #17910 is CLOSED" in e for e in errors)


def test_pr_citee_non_merged_refuse(monkeypatch):
    def fake_gh_json(args):
        assert args[:2] == ["pr", "view"], args
        return {"state": "OPEN", "mergedAt": None}
    monkeypatch.setattr(ccd, "gh_json", fake_gh_json)
    snap = _snapshot(comments=[
        _comment(_dossier_body(items=("critere A -> PR #18002",)))])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("#18002 is not MERGED" in e for e in errors)


def test_pr_citee_deja_dans_les_merged_ne_requete_pas(monkeypatch):
    # #17901 est dans merged_prs : aucun appel gh supplementaire.
    def boom(args):
        raise AssertionError(f"appel gh inattendu: {args}")
    monkeypatch.setattr(ccd, "gh_json", boom)
    snap = _snapshot(comments=[_comment(_dossier_body())])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "CLOSE"


# --- controleurs secondaires --------------------------------------------------

def test_commentsReviewed_stale():
    # Le dossier pretend avoir lu 3 commentaires alors qu'il est le 1er : la
    # lecture n'etait pas complete -> perime.
    snap = _snapshot(comments=[_comment(_dossier_body(comments_reviewed=3))])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("comments-reviewed is stale" in e for e in errors)


def test_lane_hors_flotte_refusee():
    snap = _snapshot(comments=[
        _comment(_dossier_body(lane="some-lane:nowhere"))])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("qualifying cluster lanes" in e for e in errors)


def test_issue_fermee_hors_champ():
    snap = _snapshot(state="CLOSED", comments=[_comment(_dossier_body())])
    verdict, errors, _ = evaluate(snap)
    assert verdict == "REFUSED"
    assert any("state must be OPEN" in e for e in errors)


# --- parseur ------------------------------------------------------------------

def test_parse_dossier_sans_marqueur_fermant():
    body = _dossier_body().replace("[/CLOSURE PREFLIGHT]", "")
    dossier, errors = parse_dossier(body, 0, "jsboige")
    assert dossier is not None
    assert any("missing closing marker" in e for e in errors)


def test_parse_dossier_item_sans_fleche():
    body = _dossier_body(items=("critere sans preuve",))
    dossier, errors = parse_dossier(body, 0, "jsboige")
    assert not errors  # structurellement valide...
    errs = validate_dossier(dossier, _snapshot(comments=[_comment(body)]))
    assert any("lacks '->'" in e for e in errs)  # ...mais refuse au controle


def test_parse_dossier_champ_inconnu():
    body = _dossier_body().replace("residue: none", "residue: none\nextra: x")
    _, errors = parse_dossier(body, 0, "jsboige")
    assert any("unknown fields: extra" in e for e in errors)


def test_parse_dossier_champ_manquant():
    body = _dossier_body().replace("open-prs: 0\n", "")
    _, errors = parse_dossier(body, 0, "jsboige")
    assert any("missing fields: open-prs" in e for e in errors)


def test_parse_dossier_prose_apres_marqueur_ignoree():
    body = _dossier_body() + "\nProse humaine post-dossier : ignoree."
    dossier, errors = parse_dossier(body, 0, "jsboige")
    assert errors == []
    assert dossier.fields["verdict"] == "CLOSE"


def test_residue_waiver_syntaxe():
    body = _dossier_body(residue="waiver: arbitrage user 2026-09-26, issue #X")
    dossier, errors = parse_dossier(body, 0, "jsboige")
    assert errors == []
    errs = validate_dossier(dossier, _snapshot(comments=[_comment(body)]))
    assert not any("residue" in e for e in errs)


# --- gabarit et codes de sortie -----------------------------------------------

def test_template_rend_les_champs_mecaniques():
    snap = _snapshot(comments=[_comment("x"), _comment("y")])
    out = render_template(snap, "myia-po-2026:CoursIA-3")
    assert out.startswith("[CLOSURE PREFLIGHT]")
    assert "[/CLOSURE PREFLIGHT]" in out
    assert "lane: myia-po-2026:CoursIA-3" in out
    assert "issue: 17900" in out
    assert "open-prs: 0" in out
    assert "comments-reviewed: 2" in out
    assert "REPLACE_WITH_CLOSE_OR_KEEP" in out


def test_main_rc_close_0_keep_3_refuse_1_inconnu_2(monkeypatch, capsys):
    close_snap = _snapshot(comments=[_comment(_dossier_body())])
    keep_snap = _snapshot(comments=[
        _comment(_dossier_body(verdict="KEEP"))])
    refused_snap = _snapshot(comments=[
        _comment(_dossier_body(lane="myia-po-2024:CoursIA"))])

    def routing(repo, number=None, **kw):
        return {
            17900: close_snap,
            17901: keep_snap,
            17902: refused_snap,
        }[number]

    monkeypatch.setattr(ccd, "load_snapshot", routing)
    assert main(["17900"]) == 0
    assert main(["17901"]) == 3
    assert main(["17902"]) == 1

    def boom(*a, **kw):
        raise RuntimeError("gh: rate limit")
    monkeypatch.setattr(ccd, "load_snapshot", boom)
    assert main(["17900"]) == 2
    capsys.readouterr()  # vide la sortie pour les asserts suivants


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
