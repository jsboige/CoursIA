#!/usr/bin/env python3
"""L'adherence au tapis, mesuree par lane (issue #25082, point D).

La mesure 1 de #25082 comptait les PRs ouvertes qui traitent une issue de
la file de leur lane, sans distinguer TROIS provenances que le coordinateur
a ensuite precisees (commentaire du 07/11 16:30Z) :

1. issue de la file ASSIGNEE par le coordinateur ;
2. issue TIREE par la lane elle-meme au tapis ;
3. HORS tapis (dispatch nominatif, reparation de PR, initiative de la lane).

La provenance 2 n'innocente pas le tirage : c'est le tapis lui-meme qui ne
met pas la consolidation en tete. Elle se distingue de 1 pour qu'on sache
si une lane travaille SA file ou le tapis, et de 3 pour qu'on voie le
travail hors tapis.

Ces tests n'appellent jamais ``gh`` : les PRs et les tirages sont injectes.
"""
from __future__ import annotations

import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import belt_queues as bq  # noqa: E402

NOW = datetime(2026, 11, 7, 17, 0, tzinfo=timezone.utc)
A, B = "myia-ai-01:CoursIA-2", "myia-po-2023:CoursIA"

PREV = {"assigned_at": "2026-11-07T09:00:00Z", "lanes": {
    A: {"arc": "X", "queue": [{"number": 10}, {"number": 11}]},
    B: {"arc": "Y", "queue": [{"number": 20}]},
}}


def _pr(number, lane=A, title="Fix(x,#10): un sujet", body="", created="2026-11-07T10:00:00Z",
        closing=()):
    """Une PR ouverte, avec le tag `Grain:` qui porte la lane (le login
    GitHub est partage : le tag est la seule attribution par lane)."""
    tag = f"Grain: MED/guard -- lane {lane} -- prev: MED/guard #1" if lane else "Grain: MED/guard"
    full = (tag + "\n\n" + body) if body else tag
    return {"number": number, "title": title, "body": full, "createdAt": created,
            "closingIssuesReferences": [{"number": n} for n in closing]}


# --- la classification --------------------------------------------------------


def test_une_pr_qui_traite_une_issue_de_la_file_est_comptee_file():
    out = bq.measure_adherence(PREV, [A], open_prs=[_pr(100, title="Fix(x,#10): x")],
                                belt_draws={A: set()})
    lane = out["lanes"][A]
    assert lane["assigned"] == 1
    assert lane["self_drawn"] == 0
    assert lane["off_belt"] == 0
    assert lane["adherence"] == 1.0
    assert lane["prs"]["file"] == [100]


def test_une_pr_qui_traite_une_issue_tiree_au_tapis_est_comptee_tapis():
    out = bq.measure_adherence(PREV, [A], open_prs=[_pr(101, title="Fix(x,#77): x")],
                                belt_draws={A: {77}})
    lane = out["lanes"][A]
    assert lane["self_drawn"] == 1
    assert lane["assigned"] == 0
    assert lane["adherence"] == 1.0


def test_une_pr_hors_tapis_est_comptee_hors_tapis():
    out = bq.measure_adherence(PREV, [A], open_prs=[_pr(102, title="Fix(x,#999): x")],
                                belt_draws={A: {77}})
    lane = out["lanes"][A]
    assert lane["off_belt"] == 1
    assert lane["adherence"] == 0.0


def test_le_taux_compte_la_file_ET_le_tapis():
    """L'adherence dit si une lane travaille LE TAPIS (file ou tirage) : les
    deux provenances comptent, la troisieme non."""
    prs = [_pr(100, title="Fix(x,#10): x"), _pr(101, title="Fix(x,#77): x"),
           _pr(102, title="Fix(x,#999): x")]
    out = bq.measure_adherence(PREV, [A], open_prs=prs, belt_draws={A: {77}})
    lane = out["lanes"][A]
    assert lane["total"] == 3
    assert lane["adherence"] == round(2 / 3, 3)


def test_la_file_prime_sur_le_tapis_quand_une_pr_cite_les_deux():
    """Une PR qui cite une issue de la file ET une issue tiree au tapis est
    comptee une seule fois, dans la file : la file est la provenance la
    plus contraignante (c'est elle que le coordinateur a assignee)."""
    prs = [_pr(100, body="See #10\n\nVoir aussi #77", title="Fix(x): x")]
    out = bq.measure_adherence(PREV, [A], open_prs=prs, belt_draws={A: {77}})
    lane = out["lanes"][A]
    assert lane["assigned"] == 1
    assert lane["self_drawn"] == 0
    assert lane["total"] == 1


# --- la fenetre et l'attribution ----------------------------------------------


def test_une_pr_creee_avant_la_repartition_precedente_est_hors_fenetre():
    prs = [_pr(100, title="Fix(x,#10): x", created="2026-11-06T10:00:00Z")]
    out = bq.measure_adherence(PREV, [A], open_prs=prs, belt_draws={A: set()})
    assert out["lanes"][A]["total"] == 0
    assert out["lanes"][A]["adherence"] is None


def test_une_pr_sans_tag_de_lane_est_comptee_a_part_et_non_repartie():
    """Sans tag, la PR n'est attribuee a personne : elle est COMPTEe, jamais
    repartie au hasard sur une lane."""
    prs = [_pr(100, lane=None, title="Fix(x,#10): x")]
    out = bq.measure_adherence(PREV, [A], open_prs=prs, belt_draws={A: set()})
    assert out["lanes"][A]["total"] == 0
    assert out["sans_lane"] == 1


def test_une_pr_d_une_autre_lane_n_entraine_pas_dans_ma_ligne():
    prs = [_pr(100, lane=B, title="Fix(x,#20): x")]
    out = bq.measure_adherence(PREV, [A], open_prs=prs, belt_draws={A: set()})
    assert out["lanes"][A]["total"] == 0


def test_une_mesure_non_faite_est_distinguee_d_un_zero():
    """Aucune lecture des PRs n'est une absence de MESURE : elle est dite,
    et non convertie en « la lane n'a rien fait »."""
    out = bq.measure_adherence(PREV, [A], open_prs=None, measured=False)
    assert out["lanes"][A]["measured"] is False
    assert out["lanes"][A]["total"] == 0


def test_sans_repartition_precedente_l_adherence_n_est_pas_measurable():
    out = bq.measure_adherence(None, [A], open_prs=[], belt_draws={})
    assert out["measured"] is False
    assert out["reason"]


# --- les issues traitees par une PR ------------------------------------------


def test_la_parse_de_github_prime_sur_le_texte():
    """`closingIssuesReferences` est la parse de GitHub : elle vaut, quel que
    soit le texte."""
    pr = _pr(1, title="Fix(x): sans numero", closing=(42,))
    assert 42 in bq.pr_issue_refs(pr)


def test_le_titre_porte_le_numero_de_l_issue_traitee():
    pr = _pr(1, title="Fix(audit,#17222): les findings corriges")
    assert 17222 in bq.pr_issue_refs(pr)


def test_une_reference_non_fermante_du_body_compte():
    """`See #N` ne ferme pas, mais c'est la forme que les lanes ecrivent :
    elle doit compter comme issue traitee."""
    pr = _pr(1, title="Fix(x): sans numero", body="See #25082\n")
    assert 25082 in bq.pr_issue_refs(pr)


def test_une_pr_sans_issue_traitee_n_attribue_aucune_issue():
    pr = _pr(1, title="Fix(x): sans numero")
    assert bq.pr_issue_refs(pr) == set()


def test_la_lane_vient_du_tag_grain():
    assert bq.pr_lane(_pr(1, lane=A)) == A
    assert bq.pr_lane(_pr(1, lane=None)) is None


# --- le tableau ----------------------------------------------------------------


def test_le_tableau_affiche_la_colonne_d_adherence():
    prs = [_pr(100, title="Fix(x,#10): x")]
    board = bq.board({"picks": []}, [A], PREV, NOW,
                      fetch_issue=lambda n: {"number": n, "state": "OPEN", "comments": []},
                      open_prs=prs, belt_draws={A: set()})
    lane = board["lanes"][A]
    assert lane["adherence"]["assigned"] == 1
    texte = bq.render_board(board)
    assert "adherence" in texte
    assert "file 1" in texte


def test_le_tableau_dit_quand_l_adherence_n_est_pas_measurable():
    board = bq.board({"picks": []}, [A], PREV, NOW,
                      fetch_issue=lambda n: {"number": n, "state": "OPEN", "comments": []},
                      open_prs=None, belt_draws={}, adherence_measured=False)
    assert "NON MESUREE" in bq.render_board(board)


# --- le journal de tirage (provenance 2) --------------------------------------


def test_le_journal_de_tirage_alimente_la_provenance_tapis(monkeypatch):
    """La provenance 2 vient du journal de tirage de la lane : `mode=belt`
    seulement (un tirage pondere n'est pas un tirage au tapis), et l'issue
    RETENUE seulement -- pas les candidates montrees (#25082, revue du
    07/11 : le tapis montre jusqu'a 50 issues, la lane n'en prend qu'une)."""

    class _Rec:
        def __init__(self, lane, candidates, mode, retained=None):
            self.lane, self.candidates = lane, candidates
            self.mode, self.retained = mode, retained

    monkeypatch.setattr(bq, "_local_machine", lambda: "myia-ai-01")
    monkeypatch.setattr(bq.tj, "read_journal", lambda *a, **k: [
        _Rec(A, [77, 78], "belt", retained=78),
        _Rec(A, [99], "weighted", retained=99),
        _Rec(A, [88], "belt", retained=None),
    ])
    # 78 retenue seulement : 77 (montree) et 99 (tirage pondere) ne comptent
    # pas ; 88 n'a rien retenu.
    assert bq.belt_draw_numbers(A) == {78}


def test_une_issue_montree_mais_non_retenue_ne_compte_pas_comme_tapis():
    """Un tirage dont `candidates` contient l'issue de la PR et `retained`
    une AUTRE issue : la PR est hors_tapis, pas tapis (#25082, revue)."""
    prs = [_pr(101, title="Fix(x,#77): x")]
    out = bq.measure_adherence(PREV, [A], open_prs=prs, belt_draws={A: {78}})
    lane = out["lanes"][A]
    assert lane["prs"]["hors_tapis"] == [101]
    assert lane["self_drawn"] == 0


def test_une_lane_d_une_autre_machine_n_est_pas_mesuree_localement(monkeypatch):
    """Le journal de tirage est par machine : pour une lane distante, la
    provenance tapis est NON MESUREE (None), jamais un zero -- et ses PRs
    hors file tombent dans non_mesure, pas dans hors_tapis (#25082, revue)."""
    monkeypatch.setattr(bq, "_local_machine", lambda: "myia-ai-01")
    monkeypatch.setattr(bq.tj, "read_journal", lambda *a, **k: [])
    # B vit sur myia-po-2023 : le journal local d'ai-01 ne peut pas la voir.
    assert bq.belt_draw_numbers(B) is None

    prs = [_pr(201, lane=B, title="Fix(x,#55): x"),   # hors file, tapis ?
           _pr(202, lane=B, title="Fix(x,#20): x")]   # issue de SA file
    out = bq.measure_adherence(PREV, [A, B], open_prs=prs, belt_draws={
        A: set(), B: None})
    lane = out["lanes"][B]
    assert lane["assigned"] == 1
    assert lane["self_drawn"] is None
    assert lane["off_belt"] == 0
    assert lane["non_mesure"] == 1
    assert lane["prs"]["non_mesure"] == [201]
    assert lane["adherence"] is None


def test_le_rendu_d_une_lane_distante_reserve_le_tapis_au_journal_local():
    """`tapis 0/n (journal local)` : la reserve est dans la ligne, le zero
    nu interdit -- le tableau ne dit pas « la lane n'a rien fait du tapis »
    quand il ne peut pas le savoir."""
    prs = [_pr(201, lane=B, title="Fix(x,#55): x")]
    board = bq.board({"picks": []}, [A, B], PREV, NOW,
                     fetch_issue=lambda n: {"number": n, "state": "OPEN",
                                            "comments": []},
                     open_prs=prs, belt_draws={A: set(), B: None})
    texte = bq.render_board(board)
    assert "journal local" in texte
    assert "tapis 0/1 (journal local)" in texte
    # le zero nu de l'ancienne forme ne doit plus apparaitre pour cette lane
    assert "tapis 0 /" not in texte


def test_un_journal_illisible_ne_leve_pas(monkeypatch):
    """L'absence de journal n'est pas une erreur de mesure : la provenance 2
    est simplement vide, et la mesure le dit ailleurs."""
    import json as _json

    def _boom(*a, **k):
        raise _json.JSONDecodeError("x", "y", 0)

    monkeypatch.setattr(bq, "_local_machine", lambda: "myia-ai-01")
    monkeypatch.setattr(bq.tj, "read_journal", _boom)
    assert bq.belt_draw_numbers(A) == set()


@pytest.mark.parametrize("provenance,attendu", [
    (bq.ADHERENCE_ASSIGNED, "file"),
    (bq.ADHERENCE_SELF_DRAWN, "tapis"),
    (bq.ADHERENCE_OFF_BELT, "hors_tapis"),
    (bq.ADHERENCE_NON_MEASURED, "non_mesure"),
])
def test_les_quatre_provenances_sont_nommees(provenance, attendu):
    assert provenance == attendu
