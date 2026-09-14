#!/usr/bin/env python3
"""Tests du plancher de merge (`scripts/ci/merge_dwell.py`, mandat user 2026-09-07).

Ce que ces tests epinglent, par ordre de degat s'ils cassent :

1. **Le plancher refuse vraiment une tete jeune.** Un garde temporel qui rend
   toujours vert est indiscernable d'un garde debranche -- c'est la premiere
   chose a mesurer, avant meme la mise en forme du message.
2. **Le futur n'est pas « tres vieux ».** Une date de committer dans le futur
   (decalage d'horloge, date forgee) rend l'age negatif ; la seule facon de
   transformer ce garde en passe-plat serait de la laisser passer.
3. **Une lecture d'API muette n'est pas une derogation.** `is_waived` sur une
   reponse illisible doit LEVER, jamais renvoyer False silencieusement -- le
   zero propre que le harnais interdit de croire.
4. **Hors contexte de PR, pas de plancher.** Le gate tourne aussi sur
   `workflow_dispatch`, ou son check-run atterrit sur la branche par defaut :
   y appliquer un plancher rougirait `main` sans rien gater.

Run: python -m pytest scripts/tests/test_merge_dwell.py
"""
import sys
from datetime import datetime, timedelta, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from ci import merge_dwell  # noqa: E402

NOW = datetime(2026, 9, 7, 12, 0, 0, tzinfo=timezone.utc)


# --- 1. le plancher refuse une tete jeune -----------------------------------

def test_tete_jeune_refusee():
    ok, remaining, msg = merge_dwell.evaluate(NOW - timedelta(minutes=5), NOW, 120.0)
    assert ok is False
    assert 114 < remaining <= 115
    assert "reste 115 min" in msg


def test_tete_agee_acceptee():
    ok, remaining, msg = merge_dwell.evaluate(NOW - timedelta(minutes=121), NOW, 120.0)
    assert ok is True
    assert remaining == 0.0
    assert "dwell ecoule" in msg


def test_bord_exact_accepte():
    """A 120 min pile le plancher est ecoule -- un plancher, pas un plafond."""
    ok, _, _ = merge_dwell.evaluate(NOW - timedelta(minutes=120), NOW, 120.0)
    assert ok is True


def test_message_de_refus_nomme_le_geste_de_levee():
    """Le rouge doit dire comment il se leve, sinon il se lit comme un blocage."""
    _, _, msg = merge_dwell.evaluate(NOW - timedelta(minutes=1), NOW, 120.0)
    assert "pr-gate-stale-sweep.yml" in msg
    assert merge_dwell.WAIVER_LABEL in msg


def test_message_de_refus_porte_lheure_de_levee_absolue():
    """#15693 : l'heure de tete ET l'heure de LEVEE. « 101 min » oblige la
    lane a refaire le calcul et l'incite a agir ; un re-push reactionnaire
    remet le plancher a zero depuis la nouvelle tete. Tete 11:55 + plancher
    120 min -> leve au premier balayage suivant 13:55."""
    ok, _, msg = merge_dwell.evaluate(
        NOW.replace(hour=11, minute=55), NOW, 120.0
    )
    assert ok is False
    assert "tete du 2026-09-07T11:55:00Z" in msg
    assert "2026-09-07T13:55:00Z" in msg, "l'heure de levee, pas seulement les minutes"


# --- 2. le futur n'est pas « tres vieux » -----------------------------------

def test_tete_dans_le_futur_refusee():
    ok, remaining, _ = merge_dwell.evaluate(NOW + timedelta(minutes=30), NOW, 120.0)
    assert ok is False
    assert remaining > 120.0


# --- derogation et desactivation --------------------------------------------

def test_label_de_derogation_leve_le_plancher():
    ok, _, msg = merge_dwell.evaluate(
        NOW - timedelta(minutes=1), NOW, 120.0, waived=True
    )
    assert ok is True
    assert merge_dwell.WAIVER_LABEL in msg
    # Controle positif de la meme entree SANS derogation : sans lui, un test
    # vert ne distingue pas « le label a leve » de « le plancher ne mord pas ».
    assert merge_dwell.evaluate(NOW - timedelta(minutes=1), NOW, 120.0)[0] is False


def test_dwell_nul_desactive():
    ok, _, _ = merge_dwell.evaluate(NOW - timedelta(minutes=1), NOW, 0.0)
    assert ok is True


# --- 3. une API muette n'est pas une derogation -----------------------------

def test_is_waived_leve_sur_payload_inattendu():
    with pytest.raises(merge_dwell.DwellError):
        merge_dwell.is_waived("o/r", 1, fetch=lambda path: [])


def test_is_waived_lit_le_label():
    payload = {"labels": [{"name": "docs"}, {"name": merge_dwell.WAIVER_LABEL}]}
    assert merge_dwell.is_waived("o/r", 1, fetch=lambda path: payload) is True
    assert merge_dwell.is_waived(
        "o/r", 1, fetch=lambda path: {"labels": [{"name": "docs"}]}
    ) is False


def test_head_committed_at_leve_sans_date():
    with pytest.raises(merge_dwell.DwellError):
        merge_dwell.head_committed_at(
            "o/r", "deadbeef", fetch=lambda path: {"commit": {"committer": {}}}
        )


def test_head_committed_at_lit_la_date_du_committer():
    payload = {
        "commit": {
            "author": {"date": "2020-01-01T00:00:00Z"},
            "committer": {"date": "2026-09-07T09:48:43Z"},
        }
    }
    got = merge_dwell.head_committed_at("o/r", "abc", fetch=lambda path: payload)
    assert got == datetime(2026, 9, 7, 9, 48, 43, tzinfo=timezone.utc)


def test_parse_iso8601_refuse_une_date_vide():
    with pytest.raises(merge_dwell.DwellError):
        merge_dwell.parse_iso8601("")


# --- 4. hors contexte de PR, pas de plancher --------------------------------

def test_check_sans_numero_de_pr_ne_gate_rien():
    def boom(path):  # le reseau ne doit meme pas etre touche
        raise AssertionError("aucun appel gh attendu hors contexte de PR")

    ok, msg = merge_dwell.check("o/r", "abc", None, 120.0, fetch=boom)
    assert ok is True
    assert "non applicable" in msg


def test_check_bout_en_bout_refuse_une_tete_jeune():
    def fetch(path):
        if path.startswith("repos/o/r/pulls/"):
            return {"labels": []}
        return {"commit": {"committer": {"date": "2026-09-07T11:55:00Z"}}}

    ok, msg = merge_dwell.check("o/r", "abc", 42, 120.0, now=NOW, fetch=fetch)
    assert ok is False
    assert msg.startswith("tete du 2026-09-07T11:55:00Z")


def test_check_bout_en_bout_accepte_une_tete_agee():
    def fetch(path):
        if path.startswith("repos/o/r/pulls/"):
            return {"labels": []}
        return {"commit": {"committer": {"date": "2026-09-07T09:00:00Z"}}}

    ok, msg = merge_dwell.check("o/r", "abc", 42, 120.0, now=NOW, fetch=fetch)
    assert ok is True
    assert "dwell ecoule" in msg
