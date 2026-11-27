#!/usr/bin/env python3
"""#28669 -- qualification de vivacite de la branche SCOPEE du lint.

Le defaut : `_lint_claim_events` emettait `WARN: glob sans correspondance`
pour TOUT evenement `open`/`override` portant un glob mort, sans verifier que
le marqueur tient encore le verrou. Un claim superseded ou libere continuait
donc de produire son WARN a chaque appel de l'organe (mesure du lot enregistre
`scripts/tests/fixtures/claim_grammar/batch.json` : 90 des 99 globs morts
portaient un marqueur non actif).

Le correctif est le symetrique de #12327, qui qualifie deja la branche
epic-wide par `active_claims` / `others_verdict` :

  * le WARN ne parle que si le marqueur EST le claim actif de sa lane ;
  * les globs morts des marqueurs non actifs sont comptes et restitues en UNE
    ligne `INFO:` en fin de fonction -- l'organe dit ce qu'il a tu ;
  * sans `active_claims` (appelant qui n'a pas reduit), rien ne change, ce qui
    garde `test_claim_grammar.py::test_equiv_lint` byte-identique.

Run: python -m pytest scripts/tests/test_claim_lint_liveness.py -q
"""
import importlib.util
import sys
from pathlib import Path

import pytest

TESTS = Path(__file__).resolve().parent
SCRIPTS = TESTS.parent
REPO = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))

import check_lane_claim as clc  # noqa: E402

# Arbre suivi INJECTE : aucun walk git, donc une mesure hermetique. Le glob
# mort est mort par construction, quel que soit l'etat du worktree.
TRACKED = ["scripts/check_lane_claim.py"]

DEAD = "MyIA.AI.Notebooks/Compression/Compression-04b-CodecsSOTA-Pareto-CSharp.ipynb"
LIVE = "scripts/check_lane_claim.py"

LANE = "myia-po-2024:CoursIA"
OTHER = "myia-po-2028:claudish"

CLAIM = f"[CLAIMED] lane {LANE} -- tranche -- paths: {DEAD}"
AMEND = f"[CLAIMED-AMEND] lane {LANE} -- paths: {LIVE}"
RELEASE = f"[RELEASED] lane {LANE}"


def comment(body, created_at, author="jsboige"):
    return {"body": body, "createdAt": created_at,
            "author": {"login": author}, "url": None}


def events(*comments):
    """Evenements dans l'ordre CHRONOLOGIQUE des commentaires fournis."""
    return [ev for c in comments for ev in clc._parse_claim_events(c)]


def lint(evs, capsys, active_claims, my_lane="myia-ai-01:CoursIA-2"):
    clc._lint_claim_events(
        evs, 28669, tracked=TRACKED,
        active_claims=active_claims,
        others_verdict={} if active_claims is not None else None,
        my_lane=my_lane,
    )
    return capsys.readouterr().err


# --- le correctif : le marqueur perime ne parle plus -------------------------

def test_superseded_marker_dead_glob_is_silenced(capsys):
    """Le cas mesure : une lane claim avec un chemin retire, puis re-claim
    proprement. L'ancien marqueur ne doit plus WARNer -- mais l'organe doit
    dire qu'il a tu, avec le compte et la lane."""
    evs = events(
        comment(CLAIM, "2026-11-20T10:00:00Z"),
        comment(AMEND, "2026-11-21T10:00:00Z"),
    )
    active, _ = clc.compute_active_claims(evs)
    assert active[LANE].get("paths") == [LIVE]  # l'amend tient bien le verrou
    err = lint(evs, capsys, active)
    assert "glob sans correspondance" not in err
    assert "1 glob(s) mort(s)" in err
    assert "superseded" in err and "0 sans claim actif" in err
    assert LANE in err


def test_released_lane_dead_glob_is_silenced(capsys):
    """Une lane qui a libere son claim ne tient plus rien : son glob mort ne
    decrit aucun perimetre courant, et c'est l'INFO qui le compte."""
    evs = events(
        comment(CLAIM, "2026-11-20T10:00:00Z"),
        comment(RELEASE, "2026-11-23T23:51:00Z"),
    )
    active, _ = clc.compute_active_claims(evs)
    assert LANE not in active
    err = lint(evs, capsys, active)
    assert "glob sans correspondance" not in err
    assert "1 glob(s) mort(s)" in err
    assert "1 sans claim actif" in err


def test_silencing_is_per_lane_not_global(capsys):
    """La qualification est par marqueur : le glob mort d'une lane ACTIVE
    continue de WARNer pendant qu'un marqueur perime d'une autre lane est tu."""
    evs = events(
        comment(CLAIM, "2026-11-20T10:00:00Z"),
        comment(AMEND, "2026-11-21T10:00:00Z"),
        comment(f"[CLAIMED] lane {OTHER} -- paths: {DEAD}", "2026-11-22T10:00:00Z"),
    )
    active, _ = clc.compute_active_claims(evs)
    assert active[OTHER].get("paths") == [DEAD]
    err = lint(evs, capsys, active)
    assert f'WARN: glob sans correspondance : "{DEAD}" (lane {OTHER})' in err
    assert f'(lane {LANE})' not in err.split("INFO:")[0]
    assert "1 glob(s) mort(s)" in err and f"{LANE}: 1" in err


# --- les controles negatifs -------------------------------------------------

def test_live_claim_dead_glob_still_warns(capsys):
    """C'est le seul cas ou l'auteur peut encore corriger sa clause : le WARN
    doit rester, et aucune ligne de bride ne doit apparaitre."""
    evs = events(comment(CLAIM, "2026-11-20T10:00:00Z"))
    active, _ = clc.compute_active_claims(evs)
    assert active[LANE] is evs[0]
    err = lint(evs, capsys, active)
    assert f'WARN: glob sans correspondance : "{DEAD}" (lane {LANE})' in err
    assert "NON ACTIFS" not in err


def test_legacy_path_without_active_claims_is_unchanged(capsys):
    """Sans `active_claims`, l'organe n'a pas reduit : il garde son
    comportement d'origine. C'est ce chemin que `test_equiv_lint` compare
    entre l'organe et le module pur -- il doit rester byte-identique."""
    evs = events(
        comment(CLAIM, "2026-11-20T10:00:00Z"),
        comment(AMEND, "2026-11-21T10:00:00Z"),
    )
    err = lint(evs, capsys, None)
    assert f'WARN: glob sans correspondance : "{DEAD}" (lane {LANE})' in err
    assert "NON ACTIFS" not in err


def test_marker_without_lane_keeps_its_warn(capsys):
    """Un marqueur sans lane ne peut pas etre prouve non actif (il ne tient
    rien par construction, mais rien ne permet de l'affirmer) : fail-open
    vers le WARN, on ne tait que ce qu'on peut demontrer."""
    evs = events(comment(f"[CLAIMED] -- paths: {DEAD}", "2026-11-20T10:00:00Z"))
    err = lint(evs, capsys, {})
    assert 'glob sans correspondance' in err
    assert "NON ACTIFS" not in err


# --- equivalence organe / module pur, avec reduction ------------------------

def test_equivalent_to_grammar_module_when_active_claims_given(capsys):
    """`test_claim_grammar.py` ne compare les deux modules que sans
    `active_claims`. La qualification est un second etage : il doit lui aussi
    etre identique au caractere pres, sinon le module pur derive."""
    spec = importlib.util.spec_from_file_location(
        "claim_grammar", SCRIPTS / "coordination" / "claim_grammar.py")
    cg = importlib.util.module_from_spec(spec)
    sys.modules.setdefault("claim_grammar", cg)
    spec.loader.exec_module(cg)

    evs = events(
        comment(CLAIM, "2026-11-20T10:00:00Z"),
        comment(AMEND, "2026-11-21T10:00:00Z"),
        comment(f"[CLAIMED] lane {OTHER} -- paths: {DEAD}", "2026-11-22T10:00:00Z"),
    )
    active, _ = clc.compute_active_claims(evs)
    clc._lint_claim_events(evs, 28669, tracked=TRACKED, active_claims=active,
                           others_verdict={}, my_lane="myia-ai-01:CoursIA-2")
    organ = capsys.readouterr().err
    cg._lint_claim_events(evs, 28669, tracked=TRACKED, active_claims=active,
                          others_verdict={}, my_lane="myia-ai-01:CoursIA-2")
    module = capsys.readouterr().err
    assert organ == module and organ  # non vide : le temoin a bien parle
