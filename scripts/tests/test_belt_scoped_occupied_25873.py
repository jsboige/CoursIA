"""#25873 -- le belt sert une issue dont les claims d'autres lanes sont TOUS
bornés (chemins déclarés), au lieu de l'écarter en NOT_SCOPED.

Le défaut mesuré : le belt appelle la sonde SANS ``--paths``, donc la sonde ne
peut pas prouver la disjonction et rend ``NOT_SCOPED`` (exit 2) pour TOUT
claim d'une autre lane -- borné ou non. Or un claim borné ne fige que les
fichiers qu'il nomme, jamais l'issue entière : 95/352 issues étaient à tort
écartées du tapis.

Le correctif est un OPT-IN du belt (``serve_bounded=True``), PAS un changement
global : la sonde mono-issue de ``check_lane_claim.py`` (le geste de
lane-claim-protocol d'une lane avant édition) reste fail-CLOSED (``NOT_SCOPED``)
quand elle ne déclare pas de scope -- une sonde manuelle sans scope ne peut
pas prouver la disjonction, et ce comportement ne bouge pas.

Aucun test ne touche le réseau : ``_git_tracked_files`` est remplacé pour
garder les globs du claim « vivants » (sinon le fail-safe #10958 lève un scope
entièrement mort à epic-wide), et la racine de l'instantane est redirigée vers
``tmp_path``.
"""

import json
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import check_lane_claim as clc
import gh_snapshot as gs
import pick_idle_grain as pig


@pytest.fixture(autouse=True)
def _snapshot_root_isole(tmp_path, monkeypatch):
    """Racine de l'instantane redirigée : jamais le LOCALAPPDATA réel."""
    monkeypatch.setattr(gs, "snapshot_root", lambda: tmp_path / "gh-snapshot")
    yield
    clc.set_snapshot(None)


def _comment(body, created_at, author="jsboige", url=None):
    return {
        "body": body,
        "createdAt": created_at,
        "author": {"login": author},
        "url": url,
    }


def _payload(*comments, number=9764, title="t"):
    return {"number": number, "title": title, "comments": list(comments)}


def _summary(stdout: str) -> dict:
    """Le resume JSON d'un ``_run_check`` (avant la phrase-verdict)."""
    brace = (stdout or "").find("{")
    if brace == -1:
        return {}
    try:
        data, _ = json.JSONDecoder().raw_decode(stdout[brace:])
    except json.JSONDecodeError:
        return {}
    return data if isinstance(data, dict) else {}


def _faux_gh_api(responses):
    """Remplace ``_gh_api`` : rend les réponses fixées, refuse le reste."""
    def fake(path, *, params=""):
        if path in responses:
            return responses[path]
        raise RuntimeError(f"appel gh inattendu: {path} {params}")
    return fake


def _snapshot_avec_claim(monkeypatch, n: int, claim_body: str) -> dict:
    """Instantané construit par la voie de production (#22684)."""
    recent = (datetime.now(UTC) - timedelta(hours=1)).strftime(
        "%Y-%m-%dT%H:%M:%SZ")
    monkeypatch.setattr(gs, "_gh_api", _faux_gh_api({
        f"repos/jsboige/CoursIA/issues/{n}":
            {"number": n, "title": f"T{n}", "labels": [],
             "updated_at": recent, "state": "open"},
        f"repos/jsboige/CoursIA/issues/{n}/comments":
            [{"body": claim_body, "created_at": recent, "updated_at": recent,
              "user": {"login": "jsboige"}, "html_url": "u"}],
    }))
    snap = {"issues": {}, "comments": {}, "prs": {}, "checks": {}, "meta": {}}
    snap, _calls = gs.ensure_issue_payloads("jsboige/CoursIA", [n], snap, 600)
    return snap


def _claim_body_borne():
    """Un claim BORNÉ d'une autre lane (``paths:`` vivante)."""
    return clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="tranche x",
        paths_clause=clc._paths_clause(["x/**", "y/01.ipynb"]))


def _live_tracked(monkeypatch):
    monkeypatch.setattr(
        clc, "_git_tracked_files",
        lambda: ["x/a.ipynb", "y/01.ipynb", "z/deep/f.ipynb"])


# --- un claim BORNÉ d'une autre lane : le belt le sert (exit 0) -------------


def test_belt_serves_bounded_claim_with_occupied_paths(monkeypatch, capsys):
    """Acceptance 1 -- borné : servi avec les chemins occupés.

    Le belt (``serve_bounded=True``) ne déclare pas de scope (``my_paths``
    None). Un claim borné d'une autre lane occupe seulement ses fichiers :
    l'issue est servie (exit 0), le resume JSON porte ``occupied_paths`` et la
    phrase humaine name les chemins à éviter.
    """
    _live_tracked(monkeypatch)
    pl = _payload(_comment(_claim_body_borne(), "2026-08-15T00:00:00Z"),
                  number=11064, title="t")

    rc = clc._run_check(pl, "B:CoursIA", serve_bounded=True)
    out = capsys.readouterr().out

    assert rc == 0, f"borné -> servable, obtenu exit {rc}"
    summary = _summary(out)
    assert summary.get("query_scope") == "SCOPED_OCCUPIED"
    assert summary.get("occupied_paths") == {"A:CoursIA": ["x/**", "y/01.ipynb"]}
    # La phrase humaine name la lane et ses chemins (lignes du contrat).
    assert "chemins occupés par A:CoursIA" in out
    assert "x/**" in out


# --- la sonde manuelle reste fail-CLOSED (le correctif est belt-only) -------


def test_manual_probe_stays_not_scoped(monkeypatch, capsys):
    """Contrôle du scope du correctif : SANS ``serve_bounded`` (sonde
    mono-issue manuelle), le même claim borné rend ``NOT_SCOPED`` exit 2 --
    le comportement pré-existant ne change pas.
    """
    _live_tracked(monkeypatch)
    pl = _payload(_comment(_claim_body_borne(), "2026-08-15T00:00:00Z"),
                  number=11064, title="t")

    rc = clc._run_check(pl, "B:CoursIA")  # pas de serve_bounded
    out = capsys.readouterr().out

    assert rc == 2, f"sonde manuelle sans scope -> NOT_SCOPED, obtenu exit {rc}"
    # `NOT_SCOPED` part sur stderr ; le resume JSON (stdout) le qualifie par
    # `query_scope`.
    assert _summary(out).get("query_scope") == "EPIC_WIDE_NO_PATHS_DECLARED"
    assert _summary(out).get("occupied_paths") == {}


# --- un claim EPIC-WIDE d'une autre lane : le belt le retient (exit 2) -------


def test_belt_still_withholds_epic_wide_claim(monkeypatch, capsys):
    """Contrôle négatif -- epic-wide : retenu même pour le belt.

    Un claim SANS ``paths:`` n'a pas de périmètre borné : il verrouille
    l'issue entière pour toutes les lanes. Le belt ne le sert PAS (exit 2),
    et ``occupied_paths`` reste vide (règle fail-CLOSED du protocole).
    """
    _live_tracked(monkeypatch)
    body = clc._CLAIM_BODY_TMPL.format(
        lane="A:CoursIA", intention="epic-wide, sans paths", paths_clause="")
    pl = _payload(_comment(body, "2026-08-15T00:00:00Z"),
                  number=11065, title="t")

    rc = clc._run_check(pl, "B:CoursIA", serve_bounded=True)
    out = capsys.readouterr().out

    assert rc == 2, f"epic-wide -> retenu, obtenu exit {rc}"
    assert _summary(out).get("query_scope") == "EPIC_WIDE_NO_PATHS_DECLARED"
    assert _summary(out).get("occupied_paths") == {}


# --- cas mixte : un claim borne + un claim epic-wide -> le belt retient ----


def test_belt_withholds_mixed_bounded_and_epic_wide(monkeypatch, capsys):
    """Contrôle négatif (CR #25906) -- le mix borné + epic-wide est retenu.

    Une issue avec un claim BORNÉ de A et un claim EPIC-WIDE de C : le verrou
    epic-wide de C s'étend à toute l'issue. Le belt ne doit PAS la servir
    (exit 2), ni porter l'occupation de A : ``query_scope`` est
    ``EPIC_WIDE_NO_PATHS_DECLARED`` et ``occupied_paths`` est vide. Le défaut
    initial servait l'issue (``SCOPED_OCCUPIED`` exit 0) dès qu'UN claim était
    borné, en droppeant le verrou epic-wide de C (mesure à la tête :
    ``RC 0 SCOPED_OCCUPIED {'A:CoursIA': [...]} ['A:CoursIA','C:CoursIA']``).
    """
    _live_tracked(monkeypatch)
    epique = clc._CLAIM_BODY_TMPL.format(
        lane="C:CoursIA", intention="epic-wide, sans paths", paths_clause="")
    pl = _payload(
        _comment(_claim_body_borne(), "2026-08-15T00:00:00Z"),
        _comment(epique, "2026-08-15T00:05:00Z"),
        number=11067, title="t")

    rc = clc._run_check(pl, "B:CoursIA", serve_bounded=True)
    out = capsys.readouterr().out

    assert rc == 2, f"mix borne + epic-wide -> retenu, obtenu exit {rc}"
    assert _summary(out).get("query_scope") == "EPIC_WIDE_NO_PATHS_DECLARED"
    assert _summary(out).get("occupied_paths") == {}


# --- la voie batch (celle que le belt utilise en masse) porte occupied_paths -


def test_batch_result_carries_occupied_paths(monkeypatch):
    """Le mode batch du belt (``check_issues_batch(serve_bounded=True)``) rend
    ``code=FREE`` (exit 0) ET ``occupied_paths`` pour un claim borné.
    """
    _live_tracked(monkeypatch)
    n = 11066
    snap = _snapshot_avec_claim(monkeypatch, n, _claim_body_borne())
    clc.set_snapshot(snap)
    monkeypatch.setattr(clc, "_OPEN_PRS_MEMO", [])

    out = clc.check_issues_batch([str(n)], "B:CoursIA", from_json=None,
                                 serve_bounded=True)
    res = out["results"][str(n)]

    assert res["exit"] == 0, f"borné -> servable, obtenu exit {res['exit']}"
    assert res["code"] == "FREE"
    assert res["occupied_paths"] == {"A:CoursIA": ["x/**", "y/01.ipynb"]}


# --- les réducteurs du belt mapent occupied_paths sur un code SERVI ----------


def test_belt_reducer_single_maps_occupied_to_served():
    """``_summarize_claim`` (voie solo) : un resume avec ``occupied_paths``
    rend ``FREE_OCCUPIED`` (servable), PAS ``BLOCKED`` -- le test doit précéder
    ``blocking_lanes`` (non vide ici).
    """
    out = (json.dumps({
        "blocking_lanes": ["A:CoursIA"],
        "occupied_paths": {"A:CoursIA": ["x/**", "y/01.ipynb"]},
    }) + "\nSCOPED_OCCUPIED: #11064 est servable")
    code, human = pig._summarize_claim(out, 0)
    assert code == pig.CLAIM_CODE_FREE_OCCUPIED
    assert code != pig.CLAIM_CODE_BLOCKED
    assert "x/**" in human


def test_belt_reducer_batch_maps_occupied_to_served():
    """``_summarize_claim_from_batch`` (voie batch) : idem, sur le payload
    ``{results: {N: {...}}}``.
    """
    payload = {"results": {"11064": {
        "code": "FREE", "exit": 0, "human": "FREE",
        "occupied_paths": {"A:CoursIA": ["x/**", "y/01.ipynb"]},
    }}}
    code, human = pig._summarize_claim_from_batch(payload, 11064)
    assert code == pig.CLAIM_CODE_FREE_OCCUPIED
    assert code != pig.CLAIM_CODE_BLOCKED
    assert "x/**" in human


def test_belt_reducer_batch_plain_free_unchanged():
    """Contrôle négatif du réducteur batch : un ``FREE`` SANS ``occupied_paths``
    reste ``FREE`` (pas ``FREE_OCCUPIED``) -- le nouvel état n'invente pas
    d'occupation là où il n'y en a pas.
    """
    payload = {"results": {"9764": {
        "code": "FREE", "exit": 0, "human": "FREE",
        "occupied_paths": {},
    }}}
    code, _ = pig._summarize_claim_from_batch(payload, 9764)
    assert code == pig.CLAIM_CODE_FREE
