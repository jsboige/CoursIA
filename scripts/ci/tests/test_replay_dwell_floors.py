"""Tests de `scripts/ci/replay_dwell_floors.py`.

Hors reseau : les fonctions testees sont PURES. Le controle cle est le
**controle d'emetteur** : le message du minuteur est produit par
`merge_dwell.evaluate` (l'emetteur), puis relu par le parseur de l'emetteur
aussi -- jamais par une copie de la forme. Une copie deriverait en silence et
le minuteur redeviendrait invisible, ce qui est exactement le piege documente
dans `merge_dwell`.
"""

from __future__ import annotations

import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[3]
CI_DIR = Path(__file__).resolve().parents[1]
if str(CI_DIR) not in sys.path:
    sys.path.insert(0, str(CI_DIR))

import merge_dwell  # noqa: E402
from replay_dwell_floors import (  # noqa: E402
    decide,
    dwell_floor,
    is_dwell_timer,
    job_ref,
)

HEAD_AT = datetime(2026, 11, 18, 18, 57, 52, tzinfo=timezone.utc)


def _pending_title(dwell_min: float = 120.0, age_min: float = 10.0) -> str:
    """Message du minuteur produit par l'EMETTEUR (merge_dwell.evaluate)."""
    _ok, _remaining, message = merge_dwell.evaluate(
        committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=age_min),
        dwell_min=dwell_min)
    return message


def test_plancher_brut_est_la_tete_plus_le_dwell():
    floor = dwell_floor(HEAD_AT, 120.0)
    assert floor == HEAD_AT + timedelta(minutes=120)
    assert floor.strftime("%Y-%m-%dT%H:%M:%SZ") == "2026-11-18T20:57:52Z"


def test_le_minuteur_est_reconnu_par_le_parseur_de_l_emetteur():
    assert is_dwell_timer(_pending_title()) is True


def test_un_plancher_ecoule_n_est_pas_un_minuteur():
    """Quand le plancher est passe, le message change de forme : ce n'est plus
    une attente de minuteur, et l'organe ne doit pas rejouer sur ce texte."""
    _ok, _remaining, message = merge_dwell.evaluate(
        committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=200), dwell_min=120.0)
    assert "dwell ecoule" in message
    assert is_dwell_timer(message) is False


def test_un_rouge_reel_n_est_pas_un_minuteur():
    assert is_dwell_timer("3 tests ont echoue : assertion false") is False


def test_legende_verte_ignoree():
    action, motif = decide(conclusion="success", title="", committed_at=HEAD_AT,
                           now=HEAD_AT + timedelta(hours=3))
    assert action == "ignorer"
    assert "verte" in motif


def test_rouge_reel_jamais_rejoue():
    action, motif = decide(conclusion="failure", title="3 tests ont echoue",
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3))
    assert action == "ignorer"
    assert "reel" in motif


def test_derogation_par_label_ignoree():
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           waived=True)
    assert action == "ignorer"
    assert merge_dwell.WAIVER_LABEL in motif


def test_plancher_non_passe_attente():
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=30))
    assert action == "attendre"
    assert "pas encore passe" in motif


def test_plancher_passe_rejoue():
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(minutes=121))
    assert action == "rejouer"
    assert "2026-11-18T20:57:52Z" in motif


def test_egalite_au_plancher_rejoue():
    """Le plancher passe a l'instant exact : la limite est inclusive."""
    action, _motif = decide(conclusion="failure", title=_pending_title(),
                            committed_at=HEAD_AT, now=dwell_floor(HEAD_AT, 120.0))
    assert action == "rejouer"


def test_jambe_en_cours_n_est_pas_un_rouge_reel():
    """Une jambe EN COURS porte un titre vide (GitHub ne l'ecrit qu'a la fin du
    job) : sans test de `status`, elle tombait dans « pas le minuteur » et le
    verdict devenait « rouge reel ». Mesure : #26989 (18/11 20:45:34Z)."""
    action, motif = decide(conclusion="", title="", committed_at=HEAD_AT,
                           now=HEAD_AT + timedelta(hours=3), status="in_progress")
    assert action == "attendre"
    assert "en cours" in motif
    assert "reel" not in motif


def test_jembe_en_cours_n_est_jamais_rejouee():
    """Meme au-dela du plancher : une jambe qui tourne n'est pas rejouee."""
    action, _motif = decide(conclusion="", title="", committed_at=HEAD_AT,
                            now=HEAD_AT + timedelta(hours=3), status="queued")
    assert action == "attendre"


def test_le_minuteur_reconnu_passe_meme_si_la_jambe_echoue():
    """Le cas inverse : le minuteur reste detectable sur une jambe terminee."""
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           status="completed")
    assert action == "rejouer"
    assert "2026-11-18T20:57:52Z" in motif


def test_horloge_en_arriere_ou_future_ne_passe_pas():
    """Une tete datee dans le futur (decalage de machine) ne doit pas etre
    lue comme un plancher ecoule : fail-CLOSED."""
    future = HEAD_AT + timedelta(days=1)
    action, motif = decide(conclusion="failure", title=_pending_title(),
                           committed_at=future, now=HEAD_AT + timedelta(hours=3))
    assert action == "attendre"
    assert "pas encore passe" in motif


def test_dwell_desactive_rejoue_tout():
    """`--dwell-min <= 0` desactive le plancher : la jambe n'est plus un
    minuteur, donc elle ne se rejoue pas sur le critere du plancher."""
    action, motif = decide(conclusion="failure", title=_pending_title(dwell_min=0.0),
                           committed_at=HEAD_AT, now=HEAD_AT + timedelta(hours=3),
                           dwell_min=0.0)
    assert action == "ignorer"


def test_job_ref_extrait_run_et_job():
    ref = job_ref("https://github.com/jsboige/CoursIA/actions/runs/44375592255/job/135053807477")
    assert ref == ("44375592255", "135053807477")


def test_job_ref_none_si_url_inconnue():
    assert job_ref("https://example.invalid/nope") is None


@pytest.mark.parametrize("dwell_min", [60.0, 120.0, 240.0])
def test_le_plancher_suit_le_dwell(dwell_min):
    assert dwell_floor(HEAD_AT, dwell_min) == HEAD_AT + timedelta(minutes=dwell_min)


# --------------------------------------------------------------------------
# Pagination de la liste des PR ouvertes (correction c3271)
# --------------------------------------------------------------------------

def test_open_pr_numbers_pagine_jusqu_a_epuisement(monkeypatch):
    """`--all` doit voir TOUTES les PRs ouvertes, pas la premiere page.

    Mesure du 2026-11-18 : le depot comptait 194 PRs ouvertes ; la lecture
    d'une seule page (`per_page=100`, sans pagination) n'en voyait que 100
    -- les plus recentes -- alors que l'aide de l'organe annoncait « examine
    toutes les PR ouvertes du depot ». La promesse non tenue est le defaut.
    """
    import replay_dwell_floors

    pages = {
        1: [{"number": n} for n in range(1, 101)],
        2: [{"number": n} for n in range(101, 195)],
    }
    appels = []

    def faux_gh_json(path):
        appels.append(path)
        return pages.get(int(path.split("&page=")[1]), [])

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    nums = replay_dwell_floors.open_pr_numbers("jsboige/CoursIA")
    assert len(nums) == 194
    assert nums[0] == 1 and nums[-1] == 194
    assert len(appels) == 2


def test_open_pr_numbers_ne_boucle_pas_sur_une_page_pleine(monkeypatch):
    """Une page exactement pleine force une page de plus : la page vide qui
    suit doit arreter la lecture (et non la faire boucler)."""
    import replay_dwell_floors

    appels = []

    def faux_gh_json(path):
        appels.append(path)
        page = int(path.split("&page=")[1])
        if page == 1:
            return [{"number": n} for n in range(1, 101)]
        return []

    monkeypatch.setattr(replay_dwell_floors, "gh_json", faux_gh_json)
    nums = replay_dwell_floors.open_pr_numbers("jsboige/CoursIA")
    assert len(nums) == 100
    assert len(appels) == 2
