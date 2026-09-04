#!/usr/bin/env python3
"""Unit tests for the pure helper of `scripts/ci/assert_sweep_payload.py`.

PR #13370 a ajoute ce contrôle positif pour detecter un organe de
balayage mort (sortie vide ou non-JSON) -- le seul moyen de distinguer un
balayage effectif d'un fantome est de verifier le PAYLOAD (dict, cles
attendues, types des listes). La fonction `check(raw)` prend une sortie
brute de `review_coverage.py --dry-run` et renvoie un verdict.

Couvre :
  - stdout vide -> (False, "stdout vide -- ...")
  - stdout non-JSON -> (False, "stdout non-JSON (...)")
  - payload qui n'est pas un dict (liste, str, int) -> (False, ...)
  - cles requises manquantes -> (False, "cles absentes ...")
  - une cle de liste qui n'est pas une liste -> (False, ...)
  - payload complet -> (True, "balayage effectif -- ...")

Contexte : cycle 77 pool atomic epuise, META grain aligne sur les organes
recemment actifs du CI (cf #13370).
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import assert_sweep_payload as asp  # noqa: E402


# --- stdout vide / non parseable -----------------------------------------


def test_check_empty_string():
    """Une sortie totalement vide echoue (defaut : organe mort)."""
    ok, msg = asp.check("")
    assert ok is False
    assert "vide" in msg.lower()


def test_check_whitespace_only():
    """Espaces blancs seulement = stdout vide apres strip."""
    ok, msg = asp.check("   \n  \t  ")
    assert ok is False
    assert "vide" in msg.lower()


def test_check_non_json():
    """Une sortie qui n'est pas du JSON echoue."""
    ok, msg = asp.check("This is not JSON at all")
    assert ok is False
    assert "non-json" in msg.lower() or "json" in msg.lower()


def test_check_partial_json():
    """JSON casse (accolade non fermee) echoue."""
    ok, msg = asp.check('{"threshold": 0.5, "flagged": [')
    assert ok is False
    assert "non-json" in msg.lower() or "json" in msg.lower()


# --- type de payload -----------------------------------------------------


def test_check_payload_not_a_dict():
    """Une liste JSON est un payload valide cote syntaxe, mais pas cote organe."""
    ok, msg = asp.check("[1, 2, 3]")
    assert ok is False
    assert "objet" in msg.lower() or "type" in msg.lower()


def test_check_payload_is_string():
    """Une chaine JSON n'est pas un objet JSON : defaut refuse."""
    ok, msg = asp.check('"just a string"')
    assert ok is False


def test_check_payload_is_number():
    """Un nombre JSON n'est pas un objet : defaut refuse."""
    ok, msg = asp.check("42")
    assert ok is False


# --- cles requises manquantes --------------------------------------------


def test_check_missing_all_required_keys():
    """Un dict vide manque toutes les cles requises."""
    ok, msg = asp.check("{}")
    assert ok is False
    assert "absentes" in msg.lower() or "manquantes" in msg.lower()


def test_check_missing_some_keys():
    """Un dict avec seulement `threshold` echoue (5 autres cles manquent)."""
    ok, msg = asp.check('{"threshold": 0.5}')
    assert ok is False
    # 6 cles attendues, 1 presente => 5 absentes
    assert "absentes" in msg.lower()
    # Verifie qu'au moins une des cles attendues est listee comme manquante
    assert any(k in msg for k in ("dry_run", "flagged", "cleared",
                                   "skipped_draft", "skipped_base", "errors"))


def test_check_all_required_keys_present():
    """Toutes les cles requises sont la, toutes les listes sont OK."""
    payload = {
        "threshold": 0.5,
        "dry_run": True,
        "flagged": [],
        "cleared": [{"pr": 1}],
        "skipped_draft": [],
        "skipped_base": [],
        "errors": [],
    }
    import json
    ok, msg = asp.check(json.dumps(payload))
    assert ok is True
    assert "balayage effectif" in msg.lower()


def test_check_extra_keys_allowed():
    """Des cles supplementaires au-dela de REQUIRED_KEYS sont tolerees."""
    payload = {
        "threshold": 0.5,
        "dry_run": True,
        "flagged": [],
        "cleared": [],
        "skipped_draft": [],
        "skipped_base": [],
        "errors": [],
        "extra_unexpected_key": "ignored",
        "another": 42,
    }
    import json
    ok, msg = asp.check(json.dumps(payload))
    assert ok is True


# --- types des listes ----------------------------------------------------


@pytest.mark.parametrize("list_key", [
    "flagged", "cleared", "skipped_draft", "skipped_base",
])
def test_check_list_key_wrong_type(list_key):
    """Une cle qui doit etre une liste mais est un dict/str/int : echoue."""
    payload = {
        "threshold": 0.5,
        "dry_run": True,
        "flagged": [],
        "cleared": [],
        "skipped_draft": [],
        "skipped_base": [],
        "errors": [],
    }
    payload[list_key] = "not a list"  # substitue par une chaine
    import json
    ok, msg = asp.check(json.dumps(payload))
    assert ok is False
    assert list_key in msg
    assert "liste" in msg.lower() or "list" in msg.lower()


# --- verifications semantiques du verdict OK -----------------------------


def test_check_message_counts_total_items():
    """Le message OK totalise flagged + cleared + skipped_*."""
    payload = {
        "threshold": 0.75,
        "dry_run": False,
        "flagged": [1, 2, 3],
        "cleared": [4],
        "skipped_draft": [5, 6],
        "skipped_base": [],
        "errors": [{"run_id": "x"}],
    }
    import json
    ok, msg = asp.check(json.dumps(payload))
    assert ok is True
    # 3 + 1 + 2 + 0 = 6 PRs examinees
    assert "6" in msg
    # 3 flagged
    assert "3" in msg
    # 1 cleared
    assert "1" in msg
    # 1 erreur
    assert "erreur" in msg.lower()


def test_check_zero_items_is_still_ok():
    """Payload complet mais vide (0 PRs examinees) reste OK -- organe a tourne."""
    payload = {
        "threshold": 0.5,
        "dry_run": True,
        "flagged": [],
        "cleared": [],
        "skipped_draft": [],
        "skipped_base": [],
        "errors": [],
    }
    import json
    ok, msg = asp.check(json.dumps(payload))
    assert ok is True
    assert "0" in msg  # 0 PRs examinees / 0 flagged / 0 cleared


# --- tolerance whitespace ------------------------------------------------


def test_check_leading_trailing_whitespace_ok():
    """Espaces autour du JSON sont strips avant parse."""
    payload = {
        "threshold": 0.5,
        "dry_run": True,
        "flagged": [],
        "cleared": [],
        "skipped_draft": [],
        "skipped_base": [],
        "errors": [],
    }
    import json
    raw = "  \n  " + json.dumps(payload) + "  \n"
    ok, msg = asp.check(raw)
    assert ok is True


def test_check_none_input_treated_as_empty():
    """Defensif : `None` doit etre traite comme stdout vide (pas de crash)."""
    ok, msg = asp.check(None)  # type: ignore[arg-type]
    assert ok is False
    assert "vide" in msg.lower()
