#!/usr/bin/env python3
"""Equivalence pierre par pierre : check_lane_claim.py vs claim_grammar.py (T4 #26364).

Le module pur `scripts/coordination/claim_grammar.py` est extrait byte-exact de
`scripts/check_lane_claim.py` (decoupage AST, commentaires d'incidents gardes).
Ce test est le PILIER du contrat phase 1 "construire a cote" :

  - sur un LOT REEL ENREGISTRE (14 issues, 287 commentaires, fils choisis pour
    leur historique de marqueurs riche -- incidents fondateurs #9774, #10395,
    #13022, #13336, #23720...), chaque etage de la pipeline (parse, tri,
    reduction, lint, filtrage de scope) doit rendre des resultats IDENTIQUES
    entre l'organe et le module ;
  - si l'organe change sans que le module suive (ou l'inverse), ce test ROUGIT.

Deux divergences documentees, chacune piree par un test dedie :
  1. `_unwrap_trapped_body` recalcule le chemin de `scripts/ci` (le module vit
     un niveau plus bas) -- les deux doivent resoudre le MEME fichier ;
  2. `_resolve_delivered_v2` sans `pr_states` injecte ne fetch PAS : fail-CLOSED
     (#13336) -- temoin pose, verrou garde. L'organe, lui, appelle gh.

Run: python -m pytest scripts/tests/test_claim_grammar.py -q
"""
import ast
import importlib.util
import json
import sys
from pathlib import Path

import pytest

TESTS = Path(__file__).resolve().parent
SCRIPTS = TESTS.parent
REPO = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

import check_lane_claim as clc  # noqa: E402

_SPEC = importlib.util.spec_from_file_location(
    "claim_grammar", SCRIPTS / "coordination" / "claim_grammar.py"
)
cg = importlib.util.module_from_spec(_SPEC)
sys.modules.setdefault("claim_grammar", cg)
_SPEC.loader.exec_module(cg)

FIXTURE = TESTS / "fixtures" / "claim_grammar" / "batch.json"


# --- normalisation -----------------------------------------------------------

def _norm_event(ev):
    """ClaimEvent (dict subclass) -> representation comparable et stable."""
    return json.dumps({k: v for k, v in ev.items()}, sort_keys=True, ensure_ascii=False, default=str)


def _norm_active(result):
    """Sortie de compute_active_claims -> (dict lanes, liste orphelins) normee."""
    active, leftovers = result
    # active : dict[str, ClaimEvent] -- UN evenement par lane (le dernier open)
    norm_active = {
        lane: _norm_event(ev) for lane, ev in active.items()
    }
    norm_left = [_norm_event(e) for e in leftovers]
    return json.dumps(norm_active, sort_keys=True, ensure_ascii=False), norm_left


# --- pipeline equivalente sur le lot reel enregistre -------------------------

def _batch():
    if not FIXTURE.exists():
        pytest.skip(f"fixture absent : {FIXTURE}")
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


def _pr_maps(events):
    """Une carte d'etats par branche v2, derivee des refs reellement vues."""
    refs = sorted({e["pr_ref"] for e in events if e.get("pr_ref") is not None})
    maps = [{}]
    for st in ("MERGED", "OPEN", "CLOSED"):
        maps.append({r: st for r in refs})
    return maps, refs


@pytest.mark.parametrize("payload", _batch(), ids=lambda p: f"issue-{p['number']}")
def test_equiv_parse_and_reduce(payload):
    events_old = [e for c in payload["comments"] for e in clc._parse_claim_events(c)]
    events_new = [e for c in payload["comments"] for e in cg._parse_claim_events(c)]
    assert [_norm_event(e) for e in events_old] == [_norm_event(e) for e in events_new]

    maps, _refs = _pr_maps(events_old)
    for pr_states in maps:
        act_old, left_old = _norm_active(
            clc.compute_active_claims(list(events_old), pr_states=dict(pr_states))
        )
        act_new, left_new = _norm_active(
            cg.compute_active_claims(list(events_new), pr_states=dict(pr_states))
        )
        assert act_old == act_new, f"active divergent (pr_states={pr_states})"
        assert left_old == left_new, f"orphelins divergent (pr_states={pr_states})"


def test_equiv_sort_events():
    for payload in _batch():
        assert (
            [_norm_event(e) for e in clc._sort_events(payload)]
            == [_norm_event(e) for e in cg._sort_events(payload)]
        ), f"tri divergent sur #{payload['number']}"


def test_equiv_lint(capsys):
    # le lint marche l'arbre suivi via git local : les DEUX modules le font,
    # chacun dans son propre appel -- les sorties doivent coincider au
    # caractere pres. Echantillon borne (le walk git est le seul cout).
    for payload in _batch()[:3]:
        events = [e for c in payload["comments"] for e in cg._parse_claim_events(c)]
        tracked = clc._git_tracked_files(str(REPO))
        clc._lint_claim_events(
            events, payload["number"], str(REPO), tracked, None, None, None
        )
        old_out = capsys.readouterr().err
        cg._lint_claim_events(
            events, payload["number"], str(REPO), tracked, None, None, None
        )
        new_out = capsys.readouterr().err
        assert old_out == new_out, f"lint divergent sur #{payload['number']}"
        # tracked=None : chaque module marche l'arbre git LUI-MEME et paie le
        # chemin memo (_TRACKED_FILES_MEMO) -- c'est la jambe qui a manque le
        # global AnnAssign au premier passage du generateur (NameError).
        cg._lint_claim_events(
            events, payload["number"], str(REPO), None, None, None, None
        )
        assert capsys.readouterr().err is not None


def test_equiv_filter_by_claim_scope():
    others_old, others_new = {}, {}
    for payload in _batch():
        for c in payload["comments"]:
            for ev in clc._parse_claim_events(c):
                if ev.get("lane") and ev.get("paths"):
                    others_old.setdefault(ev["lane"], ev)
                    others_new.setdefault(ev["lane"], dict(ev))
    if not others_old:
        pytest.skip("aucun claim scope dans le lot")
    mine_paths = sorted({p for ev in others_old.values() for p in (ev.get("paths") or [])})[:2]
    filtered_old = clc._filter_by_claim_scope(dict(others_old), mine_paths, None)
    filtered_new = cg._filter_by_claim_scope(dict(others_new), mine_paths, None)
    assert sorted(filtered_old) == sorted(filtered_new)
    for lane in filtered_old:
        assert _norm_event(filtered_old[lane]) == _norm_event(filtered_new[lane])


# --- divergences documentees (chacune pierre par un test) --------------------

def test_divergence_ci_dir_resolves_same_file():
    # Le module vit un niveau plus bas : parents[1]/ci doit resoudre le MEME
    # fichier scripts/ci/check_gh_comment_traps.py que parent/ci chez l'organe.
    import check_gh_comment_traps as _never_direct  # noqa: F401  (preuve d'existence)
    old_dir = clc.Path(clc.__file__).resolve().parent / "ci"
    new_dir = cg.Path(cg.__file__).resolve().parents[1] / "ci"
    assert (new_dir / "check_gh_comment_traps.py").exists()
    assert (old_dir / "check_gh_comment_traps.py").resolve() == (
        new_dir / "check_gh_comment_traps.py"
    ).resolve()


def test_divergence_delivered_v2_fail_closed_sans_injection():
    # Sans pr_states, l'organe appelle gh ; le module fail-CLOSE (#13336) :
    # temoin pose + verrou garde. La purete est prouvee par l'absence meme de
    # _fetch_pr_state dans le module.
    assert not hasattr(cg, "_fetch_pr_state")
    ev = cg.ClaimEvent(
        marker="DELIVERED", lane="myia-x:CoursIA", pr_ref=424242,
        created_at="2026-11-15T00:00:00Z",
    )
    assert cg._resolve_delivered_v2(ev, None) == "open"
    assert "module pur" in ev.get("pr_state_error", "")
    assert ev.get("pr_state") is None


def test_equiv_delivered_v2_avec_injection():
    # Avec la carte injectee, comportement strictement identique a l'organe.
    for st, expected in (("OPEN", "open"), ("MERGED", "open_locked"), ("CLOSED", "close")):
        ev_old = clc.ClaimEvent(
            marker="DELIVERED", lane="myia-x:CoursIA", pr_ref=777,
            created_at="2026-11-15T00:00:00Z",
        )
        ev_new = cg.ClaimEvent(
            marker="DELIVERED", lane="myia-x:CoursIA", pr_ref=777,
            created_at="2026-11-15T00:00:00Z",
        )
        assert clc._resolve_delivered_v2(ev_old, {777: st}) == expected
        assert cg._resolve_delivered_v2(ev_new, {777: st}) == expected
        assert ev_old.get("pr_state") == ev_new.get("pr_state")


# --- unite : les incidents fondateurs doivent tenir dans le module ----------

def _ev(body, created="2026-11-15T00:00:00Z", author="jsboige"):
    return cg._parse_claim_events(
        {"body": body, "createdAt": created, "author": {"login": author}, "url": None}
    )


def test_marker_decoration_unicode_tolerated():
    # #10906/#12711 : les decorations (dont unicode) devant le marqueur ne
    # doivent pas desamorcer la detection.
    evs = _ev("[CLAIMED] lane myia-a:CoursIA -- x\n→ [RELEASED] lane myia-a:CoursIA")
    lanes = [(e["marker"], e.get("lane")) for e in evs]
    assert ("CLAIMED", "myia-a:CoursIA") in lanes
    assert ("RELEASED", "myia-a:CoursIA") in lanes


def test_amend_remplace_le_scope_open():
    # #13022 : CLAIMED-AMEND est un evenement OPEN REMPLACANT.
    evs = _ev("[CLAIMED] lane myia-a:CoursIA -- tout\n"
              "[CLAIMED-AMEND] lane myia-a:CoursIA -- paths: a/**, b/**")
    amend = [e for e in evs if e["marker"] == "CLAIMED-AMEND"]
    assert amend and amend[0].is_open is True
    assert amend[0]["paths"] == ["a/**", "b/**"]


def test_paths_clause_derniere_occurrence():
    # #23720 : plusieurs occurrences DANS la ligne de marqueur -> la derniere
    # gagne (greedy). Une occurrence hors ligne de marqueur (prose sur la
    # ligne suivante) ne vole PAS le scope -- verifie contre l'organe.
    body = "[CLAIMED] lane myia-a:CoursIA -- paths: vieux/** -- paths: bon/**"
    assert _ev(body)[0]["paths"] == ["bon/**"]
    body2 = "[CLAIMED] lane myia-a:CoursIA -- paths: vieux/**\ntexte paths: bon/**"
    assert _ev(body2)[0]["paths"] == ["vieux/**"]
    # l'equivalence organ/module tient sur les deux formes
    for b in (body, body2):
        c = {"body": b, "createdAt": "2026-11-15T00:00:00Z",
             "author": {"login": "jsboige"}, "url": None}
        assert (_norm_event(clc._parse_claim_events(c)[0])
                == _norm_event(cg._parse_claim_events(c)[0]))


def test_payload_trap_deballe():
    # #19971 : un corps qui EST le payload JSON {"body": ...} est deballe.
    trapped = json.dumps({"body": "[CLAIMED] lane myia-a:CoursIA -- piégé"})
    evs = _ev(trapped)
    assert evs and evs[0].get("lane") == "myia-a:CoursIA"


def test_delivered_v2_gate_via_reducer():
    # #12386/#13336 : MERGED -> verrou garde (open_locked), OPEN -> open,
    # PR inconnue de la carte injectee -> close silencieux (pas d'echec).
    body = "[DELIVERED] lane myia-a:CoursIA -- PR #555 -- paths: x/**"
    events = _ev(body)
    active, _ = cg.compute_active_claims(list(events), pr_states={555: "MERGED"})
    assert "myia-a:CoursIA" in active
    active, _ = cg.compute_active_claims(list(events), pr_states={555: "OPEN"})
    assert "myia-a:CoursIA" in active
    active, _ = cg.compute_active_claims(list(events), pr_states={})
    assert "myia-a:CoursIA" not in active


def test_accolades_non_fermees_epic_wide_fail_closed():
    # #10597 : une clause paths non parsable ne resserre PAS le scope.
    evs = _ev("[CLAIMED] lane myia-a:CoursIA -- paths: search-{6,8")
    assert evs[0].get("unparseable_scope") or not evs[0].get("paths")


def _hotes_subprocess(src: str) -> list[str]:
    """Les fonctions de premier niveau qui touchent `subprocess`, lues sur l'AST.

    Le nom rendu est celui de l'hote ; `"<module>"` signale un appel au niveau
    module, qui serait le pire cas (import == effet de bord).
    """
    hotes = []
    for noeud in ast.parse(src).body:
        if isinstance(noeud, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            for enfant in ast.walk(noeud):
                if (isinstance(enfant, ast.Attribute)
                        and isinstance(enfant.value, ast.Name)
                        and enfant.value.id == "subprocess"):
                    hotes.append(noeud.name)
                    break
        elif any(isinstance(enfant, ast.Attribute)
                 and isinstance(enfant.value, ast.Name)
                 and enfant.value.id == "subprocess"
                 for enfant in ast.walk(noeud)):
            hotes.append("<module>")
    return sorted(hotes)


def test_module_sans_reseau_import():
    # Garde anti-regression de la frontiere : importer le module ne doit jamais
    # declencher d'appel reseau (aucun code au niveau module n'en fait, et ce
    # test fige l'absence d'import gh/requests).
    src = (SCRIPTS / "coordination" / "claim_grammar.py").read_text(encoding="utf-8")
    assert "import requests" not in src
    assert "import urllib" not in src
    # Frontiere subprocess : un seul hote autorise, `_git_tracked_files`, qui lit
    # l'index git LOCAL. La liste est explicite et fermee : un appel ajoute dans
    # une autre fonction rougit ce test, et un appel au niveau module aussi.
    assert _hotes_subprocess(src) == ["_git_tracked_files"], _hotes_subprocess(src)
    # Temoin negatif : le garde doit VOIR un second hote, sinon il ne mord pas
    # (l'assertion precedente seule ne distinguerait pas « une seule occurrence »
    # de « detecteur aveugle »).
    temoin = ("def a():\n    subprocess.run([])\n"
              "def b():\n    subprocess.run([])\n"
              "subprocess.run([])\n")
    assert _hotes_subprocess(temoin) == ["<module>", "a", "b"], _hotes_subprocess(temoin)
    # frontiere reseau : le module ne definit aucun fetch -- la preuve dure est
    # l'absence du symbole ET le temoin fail-closed du test de divergence.
    assert not hasattr(cg, "_fetch_pr_state")
