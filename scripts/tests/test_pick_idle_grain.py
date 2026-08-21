"""Tests for scripts/pick_idle_grain.py recent_delivery (#12174).

Un detecteur se valide par ses faux negatifs, pas par ses hits. Le cas
fondateur (2026-08-21) : #12014 tiree en urne grain a 16:47Z alors que
#12077, mergee a 16:19Z, avait deja livre 3 de ses 4 items -- le label
``candidate-delivered`` (workflow schedule: quotidien, dernier run 05:49Z)
n'en savait rien. Le replay ci-dessous rejoue cet etat exact.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402


class _FakeCompleted:
    def __init__(self, stdout):
        self.stdout = stdout


def _patch_gh(monkeypatch, payloads, calls):
    """payloads : liste (dans l'ordre des candidats) de listes de PRs JSON."""
    def fake_run(cmd, **kwargs):
        calls.append(cmd)
        return _FakeCompleted(json.dumps(payloads[len(calls) - 1]))
    monkeypatch.setattr(pig.subprocess, "run", fake_run)


def _pick(n=12014, updated_at="2026-08-21T05:13:00Z"):
    return {"number": n, "klass": "grain", "updated_at": updated_at,
            "title": "founding case", "age": 30, "idle": 0,
            "genre": "slides", "weight": 1.0}


def test_founding_case_12014_surfaces_12077(monkeypatch):
    """#12174 controle positif : le tirage du 2026-08-21 doit nommer #12077.

    Issue non touchee depuis 05:13Z, PR mergee 16:19:17Z -- l'ecart que le
    label quotidien ne pouvait pas voir.
    """
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "mergedAt": "2026-08-21T16:19:17Z"},
    ]], calls)
    notes = pig.recent_delivery([_pick()])
    assert 12014 in notes
    assert "#12077" in notes[12014]
    assert "16:19:17Z" in notes[12014]
    assert "05:13:00Z" in notes[12014]
    assert "confronter le body au reel" in notes[12014]


def test_query_shape_bounded_one_per_candidate(monkeypatch):
    """Cout borne : exactement une requete par candidat tire, jamais le pool.

    La commande doit chercher les PRs MERGEES referencant le numero
    (troisieme surface de grounding, cf #12174).
    """
    calls = []
    _patch_gh(monkeypatch, [[], []], calls)
    pig.recent_delivery([_pick(n=1), _pick(n=2)])
    assert len(calls) == 2
    for cmd, n in zip(calls, (1, 2)):
        assert "--state" in cmd and "merged" in cmd
        assert "--limit" in cmd and "20" in cmd
        assert "--search" in cmd
        assert cmd[cmd.index("--search") + 1] == f"{n} in:title,body"


def test_merge_older_than_update_not_annotated(monkeypatch):
    """Une fusion ANTERIEURE a la derniere activite de l'issue est deja
    digeree par le body -- pas d'annotation, sinon le signal noie."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "mergedAt": "2026-08-21T04:00:00Z"},
    ]], calls)
    notes = pig.recent_delivery([_pick(updated_at="2026-08-21T05:13:00Z")])
    assert notes == {}


def test_no_merged_pr_no_note(monkeypatch):
    calls = []
    _patch_gh(monkeypatch, [[]], calls)
    assert pig.recent_delivery([_pick()]) == {}


def test_candidate_stays_drawable(monkeypatch):
    """L'annotation informe, elle n'ecarte pas (parite candidate-delivered) :
    la fonction rend des notes, les picks passes ne sont ni filtres ni mutés."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "mergedAt": "2026-08-21T16:19:17Z"},
    ]], calls)
    picks = [_pick()]
    snapshot = dict(picks[0])
    notes = pig.recent_delivery(picks)
    assert len(picks) == 1 and picks[0] == snapshot
    assert 12014 in notes  # annote ET toujours la, tirable


def test_multiple_prs_latest_named_with_count(monkeypatch):
    """Plusieurs PRs mergees referencent le numero : la plus recente porte la
    note, le compte evite de lire 'la livraison' comme l'unique."""
    calls = []
    _patch_gh(monkeypatch, [[
        {"number": 12077, "mergedAt": "2026-08-21T16:19:17Z"},
        {"number": 12065, "mergedAt": "2026-08-20T10:00:00Z"},
    ]], calls)
    notes = pig.recent_delivery([_pick()])
    assert "#12077" in notes[12014]
    assert "(+1 autres)" in notes[12014]
    assert "#12065" not in notes[12014]


def test_gh_failure_annotated_best_effort(monkeypatch):
    """Echec gh : l'absence d'annotation ne doit pas se lire comme 'aucune
    livraison verifiee'."""
    def boom(cmd, **kwargs):
        raise pig.subprocess.TimeoutExpired(cmd, 30)
    monkeypatch.setattr(pig.subprocess, "run", boom)
    notes = pig.recent_delivery([_pick()])
    assert "indisponible" in notes[12014]
    assert "TimeoutExpired" in notes[12014]
