#!/usr/bin/env python3
"""Tests de la jambe IMPLICIT sur les chemins d'ECRITURE et de RELECTURE (#26751).

Le trou constate le 15/11 (#26597, deux PRs pour un grain) est double :

1. `--claim` n'appelait PAS `_run_check(..., check_open_pr_paths=True)` :
   poser le marqueur n'est PAS le geste de deconfliction face a une PR
   OUVERTE et SANS marqueur d'une session hors flotte (#26598, fermee
   comme doublon apres que #26734 eut livre la meme issue).
2. Une fois son claim pose, la lane recevait `CLEAR` POUR TOUJOURS
   (`mine is None` dans la condition de la jambe) : un claim pose a la
   main par-dessus une PR plus ancienne se blanchissait lui-meme a
   chaque relecture.

Ces tests pinnent les DEUX trous, plus le contrat `--from-json` (hors
reseau) qui doit survivre au changement.

Run: python -m pytest scripts/tests/test_check_lane_claim_implicit.py
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402


# --- helpers -----------------------------------------------------------------

def comment(body, created_at, author="jsboige", url=None):
    return {
        "body": body,
        "createdAt": created_at,
        "author": {"login": author},
        "url": url,
    }


def payload(*comments, number=26597, title="t", labels=None):
    d = {"number": number, "title": title, "comments": list(comments)}
    if labels is not None:
        d["labels"] = labels
    return d


# --- fixture : la PR hors flotte, SANS tag de lane lisible --------------------
#
# La forme exacte de #26598 (session hors flotte du 14/11, fermee comme
# doublon de #26734) : le corps ne porte AUCUN marqueur de lane, donc
# `extract_lane` rend None et la PR compte comme « d'une autre lane »
# (fail-closed, comme dans `--paths`).

_PR_26598 = {
    "number": 26598,
    "title": "feat(#26597): extraction du profil",
    "headRefName": "feature/26597-profil",
    "body": "See #26597",
    "files": [{"path": "scripts/ci/extract_profil.py"}],
    "additions": 1124,
    "deletions": 295,
    # #26751 -- la date de creation SERVEUR : elle dit si la PR est
    # anterieure au claim de la lane appelante.
    "created_at": "2026-11-14T09:00:00Z",
}

_CLAIM_LANE = "myia-po-2024:CoursIA-2"


def _no_epic_cap(monkeypatch):
    """Le probe de plafond EPIC (#22500) ne doit jamais partir sur le reseau.

    Un payload sans label EPIC et un titre qui ne commence pas par `EPIC`
    suffisent : `_is_umbrella_issue` rend False et le probe rend zero appel.
    Le monkeypatch ferme le filet : si la forme du payload change un jour,
    le test echoue bruyamment au lieu de faire un appel reseau.
    """
    monkeypatch.setattr(clc, "_epic_cap_parent_payload",
                        lambda number: pytest.fail("appel reseau du probe EPIC"))
    monkeypatch.setattr(clc, "_epic_cap_pool",
                        lambda: pytest.fail("appel reseau du pool EPIC"))


# --- (a) `--claim` refuse de poster au-dessus d'une PR ouverte non taguee -----

def test_claim_refused_over_an_untagged_open_pr(monkeypatch, capsys):
    # EXIGENCE 1 du body #26751 : `--claim` appelle la jambe IMPLICIT et un
    # rc=3 REFUSE de poster. Avant la correction, le marqueur partait par
    #-dessus #26598 -- c'est ce qui a produit deux PRs pour un grain.
    posted = []

    def _boom_prs():
        raise AssertionError("_gh_open_prs_with_files ne doit pas etre appele")

    monkeypatch.setattr(clc, "_gh_issue_comments",
                        lambda issue: payload(number=26597))
    monkeypatch.setattr(clc, "_gh_open_prs_with_files", lambda: [_PR_26598])
    monkeypatch.setattr(clc, "_post_comment",
                        lambda issue, body: posted.append((issue, body)))
    _no_epic_cap(monkeypatch)

    rc = clc.main(["26597", "--lane", _CLAIM_LANE,
                    "--claim", "reprise du grain"])

    assert rc == 3
    assert posted == [], "le marqueur ne doit PAS etre poste au-dessus d'une PR ouverte"
    captured = capsys.readouterr()
    assert "BLOCKED: not posting [CLAIMED]" in captured.err
    assert "IMPLICIT" in captured.out
    assert "#26598" in captured.out


# --- (b) lecture : claim pose APRES la PR ouverte -> IMPLICIT -----------------

def test_read_with_claim_after_the_untagged_pr_is_implicit(monkeypatch, capsys):
    # EXIGENCE 2 du body #26751 : la lane detient son claim, pose le 15/11,
    # alors que la PR hors flotte a ete ouverte le 14/11. Le claim a recouvre
    # une livraison en cours -> verdict IMPLICIT (rc=3), nommant la PR.
    monkeypatch.setattr(clc, "_gh_open_prs_with_files", lambda: [_PR_26598])
    p = payload(comment(
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- reprise du grain",
        "2026-11-15T08:00:00Z"), number=26597)

    rc = clc._run_check(p, _CLAIM_LANE, check_open_pr_paths=True)

    assert rc == 3
    captured = capsys.readouterr()
    assert "IMPLICIT:" in captured.out
    assert "#26598" in captured.out
    brace = captured.out.find("{")
    data, _ = json.JSONDecoder().raw_decode(captured.out[brace:])
    assert [f["number"] for f in data["implicit_occupation"]] == [26598]


# --- (c) lecture : claim pose AVANT la PR ouverte -> CLEAR, inchange ---------

def test_read_with_claim_before_the_untagged_pr_stays_clear(monkeypatch, capsys):
    # EXIGENCE 2 du body #26751 (second volet) : une PR posterieure au claim
    # reste SUBSUMEE par le claim (review 5429946072) -> CLEAR, inchange.
    monkeypatch.setattr(clc, "_gh_open_prs_with_files", lambda: [_PR_26598])
    p = payload(comment(
        "[CLAIMED] lane myia-po-2024:CoursIA-2 -- reprise du grain",
        "2026-11-13T08:00:00Z"), number=26597)

    rc = clc._run_check(p, _CLAIM_LANE, check_open_pr_paths=True)

    assert rc == 0
    captured = capsys.readouterr()
    assert "IMPLICIT" not in captured.out
    brace = captured.out.find("{")
    data, _ = json.JSONDecoder().raw_decode(captured.out[brace:])
    assert data["implicit_occupation"] == []
    assert data["my_active_claim"] is True


# --- (c-bis) une lane TIERCE lisible occupe le grain a TOUTE date ------------

# La forme de la mesure du 25/11 14:42:43Z : la PR porte un tag de lane LISIBLE
# et distinct de l'appelante, et elle a ete ouverte APRES son claim.
_PR_28250 = {
    "number": 28250,
    "title": "Add(rust,#27130): lot 2 -- 5 jumeaux Rust executes",
    "headRefName": "feature/27130-lot2-rust-graphes",
    "body": "See #26597 -- porte par lane myia-ai-01:CoursIA-2",
    "files": [{"path": "MyIA.AI.Notebooks/Search/Part1-Foundations/"
                       "Search-11-Metaheuristics-Rust.ipynb"}],
    "additions": 3100,
    "deletions": 0,
    "created_at": "2026-11-23T10:00:00Z",
}


def test_read_with_a_tagged_third_lane_pr_after_the_claim_is_implicit(
        monkeypatch, capsys):
    # Le filtre chronologique de #26751 laissait passer toute PR POSTERIEURE au
    # claim de l'appelante, y compris celle d'une AUTRE lane : rc=0,
    # `implicit_occupation: []` au-dessus de #28250. Or
    # `_find_open_prs_referencing_issue` exclut deja les PR de l'appelante :
    # une lane tierce LISIBLE occupe le grain, quelle que soit sa date.
    monkeypatch.setattr(clc, "_gh_open_prs_with_files", lambda: [_PR_28250])
    p = payload(comment(
        "[CLAIMED] lane myia-po-2028:claudish -- lot 2",
        "2026-11-22T09:00:00Z"), number=26597)

    rc = clc._run_check(p, "myia-po-2028:claudish", check_open_pr_paths=True)

    assert rc == 3
    captured = capsys.readouterr()
    assert "IMPLICIT:" in captured.out
    assert "#28250" in captured.out
    brace = captured.out.find("{")
    data, _ = json.JSONDecoder().raw_decode(captured.out[brace:])
    assert [f["number"] for f in data["implicit_occupation"]] == [28250]
    assert data["implicit_occupation"][0]["lane"] == "myia-ai-01:CoursIA-2"
    assert data["my_active_claim"] is True


def test_read_with_a_tagged_third_lane_pr_before_the_claim_is_implicit(
        monkeypatch, capsys):
    # Le cas d'avant : une lane tierce lisible ANTERIEURE au claim occupait deja
    # le grain -- il doit continuer de le faire.
    monkeypatch.setattr(clc, "_gh_open_prs_with_files", lambda: [_PR_28250])
    p = payload(comment(
        "[CLAIMED] lane myia-po-2028:claudish -- lot 2",
        "2026-11-24T09:00:00Z"), number=26597)

    rc = clc._run_check(p, "myia-po-2028:claudish", check_open_pr_paths=True)

    assert rc == 3
    captured = capsys.readouterr()
    brace = captured.out.find("{")
    data, _ = json.JSONDecoder().raw_decode(captured.out[brace:])
    assert [f["number"] for f in data["implicit_occupation"]] == [28250]


# --- (d) `--from-json` reste hors reseau ------------------------------------

def test_from_json_stays_off_network_on_the_write_path(monkeypatch, capsys, tmp_path):
    # EXIGENCE 3 du body #26751 : `--from-json` est un contrat HORS RESEAU.
    # La correction ne doit pas y introduire une lecture GitHub : ni le
    # payload (il vient du fichier), ni les PRs ouvertes (la jambe est
    # sautee, avec un WARN qui dit comment verifier a la main).
    posted = []

    def _boom(*args, **kwargs):
        raise AssertionError("le chemin --from-json ne doit pas lire le reseau")

    monkeypatch.setattr(clc, "_gh_issue_comments", _boom)
    monkeypatch.setattr(clc, "_gh_open_prs_with_files", _boom)
    monkeypatch.setattr(clc, "_post_comment",
                        lambda issue, body: posted.append((issue, body)))
    _no_epic_cap(monkeypatch)

    source = tmp_path / "issue.json"
    source.write_text(json.dumps(payload(number=26597)), encoding="utf-8")

    rc = clc.main(["26597", "--lane", _CLAIM_LANE, "--from-json", str(source),
                    "--claim", "reprise du grain"])

    assert rc == 0
    assert len(posted) == 1 and str(posted[0][0]) == "26597"
    captured = capsys.readouterr()
    assert "posted [CLAIMED]" in captured.out
    assert "hors reseau" in captured.err or "HORS RESEAU" in captured.err
