"""Tests de l'organe de mesure par etape de `merge_ready` (#26799).

L'organe (`scripts/coordination/merge_ready_step_timing.py`) ne doit rien
decider : il enveloppe les etapes de `evaluate_pr` d'une horloge et rend le
decoupage. Ces tests le prouve sur un module FAKE -- aucun reseau, aucun
`gh`, aucun appel reel a `merge_ready`.
"""

from __future__ import annotations

import importlib.util
import sys
import types
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
ORGANE_PATH = HERE.parent / "coordination" / "merge_ready_step_timing.py"
_spec = importlib.util.spec_from_file_location("step_timing_sous_test", ORGANE_PATH)
organe = importlib.util.module_from_spec(_spec)
sys.modules["step_timing_sous_test"] = organe
_spec.loader.exec_module(organe)

VUE = {"headRefOid": "abc123", "baseRefName": "main", "changedFiles": 3}


def module_faux(etape_cassee: str | None = None) -> types.SimpleNamespace:
    """Un faux `merge_ready` : chaque etape est une fonction sans effet, et
    `evaluate_pr` les appelle toutes -- comme le vrai, qui les traverse
    jusqu'au premier skip."""
    mr = types.SimpleNamespace()
    for nom in organe.ETAPES:
        setattr(mr, nom, (lambda *a, **k: None))
    mr.fetch_pr_view = lambda runner, pr, env: dict(VUE)

    def evaluate_pr(vue, pr, runner, env):
        tete = vue["headRefOid"]
        appels = (
            ("fetch_pr_files", (runner, pr, vue, env)),
            ("lean_build_attestation_reason", (vue, tete, runner, env)),
            ("coordinator_approval_reason", (vue, tete, runner, env)),
            ("run_nits", (runner, pr, env)),
            ("twin_collision_reason", (runner, pr, tete, [])),
            ("slot_reservation_reason", (runner, pr, tete, [])),
            ("base_ref_liveness", (runner, env, "main")),
            ("stacked_parent_state", (runner, 1, env)),
            ("mergeable_state_and_head", (runner, pr, env)),
            ("_combined_tree", (runner, pr, tete, env)),
        )
        for nom, args in appels:
            if nom == etape_cassee:
                raise RuntimeError("boom")
            getattr(mr, nom)(*args)
        return types.SimpleNamespace(
            reason="mergeable-state:blocked", verdict="skipped",
        )

    mr.evaluate_pr = evaluate_pr
    return mr


def test_chaque_etape_appellee_est_mesuree():
    mr = module_faux()
    resultat = organe.mesurer(mr, 123, None, {})
    mesurees = {m["etape"] for m in resultat["etapes"]}
    assert mesurees == set(organe.ETAPES)
    for mesure in resultat["etapes"]:
        assert mesure["secondes"] >= 0.0


def test_le_total_et_le_motif_sont_rendus():
    mr = module_faux()
    resultat = organe.mesurer(mr, 123, None, {})
    assert resultat["pr"] == 123
    assert resultat["motif"] == "mergeable-state:blocked"
    assert resultat["verdict"] == "skipped"
    assert resultat["tete"] == "abc123"
    assert resultat["base"] == "main"
    assert resultat["fichiers"] == 3
    assert resultat["total_secondes"] >= 0.0


def test_une_etape_qui_leve_remonte_et_laisse_sa_mesure():
    """Une etape qui leve ne doit pas faire disparaitre sa mesure : le
    decoupage doit porter l'etape qui a rompu."""
    mr = module_faux(etape_cassee="run_nits")
    with pytest.raises(RuntimeError):
        organe.mesurer(mr, 123, None, {})

    # Meme propriete, verifiee directement sur l'horloge.
    mr2 = types.SimpleNamespace()
    mesures: list[dict] = []

    def cassee(*args, **kwargs):
        raise RuntimeError("boom")

    mr2.run_nits = cassee
    organe.horloger(mr2, "run_nits", mesures)
    with pytest.raises(RuntimeError):
        mr2.run_nits()
    assert len(mesures) == 1
    assert mesures[0]["etape"] == "run_nits"
    assert mesures[0]["secondes"] >= 0.0
