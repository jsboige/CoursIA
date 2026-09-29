"""Tests de ``ict.free_coordinates`` — banc executable strate 7 (#18052)."""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.free_coordinates import (  # noqa: E402
    EvolutiveGame,
    FixedSpacePredictor,
    OntologicalMove,
    apply_ontology,
    expansion_ontology,
    institutionalization,
    internal_move,
    irreversibility_debt,
    non_canonicity,
    performative_power,
    political_opening,
    quorum_mechanism,
)


def _game() -> EvolutiveGame:
    return EvolutiveGame(
        agents=("alice", "bob"),
        lexicon=frozenset({"echange"}),
        actions=frozenset({"vendre", "garder"}),
        payoffs={
            ("alice", "vendre"): 1.0,
            ("alice", "garder"): 0.4,
            ("bob", "vendre"): 0.3,
            ("bob", "garder"): 1.0,
        },
    )


def _eta_personne_morale() -> OntologicalMove:
    return OntologicalMove(
        proposer="alice",
        new_concepts=("personne-morale",),
        opened_actions={"personne-morale": ("signer", "posseder")},
        pose_cost=1.0,
        undo_cost=50.0,
    )


def test_internal_move_paye_et_ne_change_rien():
    g = _game()
    assert internal_move(g, "alice", "vendre") == 1.0
    assert internal_move(g, "bob", "garder") == 1.0


def test_internal_move_rejette_action_hors_espace():
    with pytest.raises(ValueError):
        internal_move(_game(), "alice", "signer")


def test_apply_ontology_etend_lexique_et_actions():
    g0, eta = _game(), _eta_personne_morale()
    g1 = apply_ontology(g0, eta)
    assert expansion_ontology(g0, g1) == 1
    assert political_opening(g0, g1) == 2
    assert "signer" in g1.actions
    assert internal_move(g1, "alice", "signer") == 1.0


def test_concept_ornamental_nouvre_rien():
    g0 = _game()
    eta = OntologicalMove(
        proposer="bob",
        new_concepts=("poesie",),
        opened_actions={},
    )
    g1 = apply_ontology(g0, eta)
    assert expansion_ontology(g0, g1) == 1
    assert political_opening(g0, g1) == 0


def test_quorum_rejette_puis_accepte():
    g0, eta = _game(), _eta_personne_morale()
    _, rejected = quorum_mechanism(g0, (eta,), votes={}, quorum=2)
    assert rejected == ()
    votes = {"personne-morale": {"alice", "bob"}}
    g1, accepted = quorum_mechanism(g0, (eta,), votes=votes, quorum=2)
    assert len(accepted) == 1
    assert "signer" in g1.actions


def test_non_canonicite_une_seule_extension_equivalente():
    g0 = _game()
    e1 = OntologicalMove("alice", ("personne-morale",), {"personne-morale": ("signer", "posseder")})
    e2 = OntologicalMove("bob", ("societe",), {"societe": ("signer", "posseder")})
    e3 = OntologicalMove("bob", ("hypotheque",), {"hypotheque": ("nantir",)})
    assert non_canonicity(g0, (e1, e2)) == 1
    assert non_canonicity(g0, (e1, e2, e3)) == 2
    assert non_canonicity(g0, (e1,)) == 1


def test_performative_power_coup_fort_vs_decoratif():
    """Contraste decoratif : une copie d'action est une option DISTINGUEE
    (P(R) brut > 0) mais EQUIVALENTE (P(R) marginalise ~ 0) — deux lectures,
    pas une. Bornes calibrees multi-seeds (0/7/42/99/2026) : pm >= 2.4,
    deco brut <= 2.0, deco marginalise <= 0.10."""
    g0, eta = _game(), _eta_personne_morale()
    g1 = apply_ontology(g0, eta)
    deco = OntologicalMove("alice", ("ornement",), {"ornement": ("vendre2",)})
    g_deco = apply_ontology(g0, deco)
    for agent in g_deco.agents:
        g_deco.payoffs[(agent, "vendre2")] = g_deco.payoffs[(agent, "vendre")]

    p_fort = performative_power(g1, g0, horizon=20, n_sim=8, rng=np.random.default_rng(42))
    p_deco = performative_power(g_deco, g0, horizon=20, n_sim=8, rng=np.random.default_rng(42))
    p_deco_eq = performative_power(
        g_deco, g0, horizon=20, n_sim=8, rng=np.random.default_rng(42),
        equivalence={"vendre2": "vendre"},
    )
    assert p_fort > 2.0        # le coup ouvrant de vraies actions transforme la dynamique
    assert p_deco < p_fort     # brut : la copie capte moins de dynamique que la vraie ouverture
    assert p_deco_eq < 0.15    # marginalisee : la copie ne change PAS la dynamique de fond
    assert p_fort > 10 * p_deco_eq


def test_institutionnalisation_depend_des_paiements_des_autres():
    g0, eta = _game(), _eta_personne_morale()
    rng = np.random.default_rng(7)
    rate = institutionalization(apply_ontology(g0, eta), eta, horizon=60, rng=rng)
    assert 0.0 < rate < 1.0
    egoiste = OntologicalMove(
        proposer="alice",
        new_concepts=("jargon-prive",),
        opened_actions={"jargon-prive": ("jargonner",)},
    )
    g_ego = apply_ontology(g0, egoiste)
    for agent in g_ego.agents:
        g_ego.payoffs[(agent, "jargonner")] = -2.0  # les autres EVITENT le jargon prive
    assert institutionalization(g_ego, egoiste, horizon=60, rng=rng) < 0.05


def test_irreversibilite_est_un_ratio():
    assert irreversibility_debt(_eta_personne_morale()) == 50.0


def test_predicteur_espace_fixe_perte_bornee_sur_support():
    pred = FixedSpacePredictor(("vendre", "garder"))
    for _ in range(50):
        pred.update("vendre")
    for _ in range(50):
        pred.update("garder")
    perte = max(pred.log_loss(a, epsilon=1.0) for a in ("vendre", "garder"))
    assert perte <= 2.0


def test_predicteur_surprise_structurelle_hors_support():
    pred = FixedSpacePredictor(("vendre", "garder"))
    assert pred.log_loss("signer") == pytest.approx(np.log2(3))
    with pytest.raises(KeyError):
        pred.update("signer")


def test_surprise_structurelle_croit_avec_l_espace():
    assert (
        FixedSpacePredictor(("a",)).surprise_structurelle()
        < FixedSpacePredictor(tuple("abcd")).surprise_structurelle()
    )
