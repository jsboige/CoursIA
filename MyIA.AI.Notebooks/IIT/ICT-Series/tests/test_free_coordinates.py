"""Tests de ``ict.free_coordinates`` — banc executable strate 7 (#18052)."""
from __future__ import annotations

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.free_coordinates import (  # noqa: E402
    BenchVerdict,
    EvolutiveGame,
    FixedSpacePredictor,
    OntologicalMove,
    apply_ontology,
    authority_mechanism,
    bancher_mecanisme,
    candidate_key,
    classer_proxys,
    compose_ontology,
    composition_report,
    competing_mechanisms,
    expansion_ontology,
    institutionalization,
    internal_move,
    irreversibility_debt,
    non_canonicity,
    performative_power,
    political_opening,
    quorum_mechanism,
    temoin_decoratif,
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


# ---------------------------------------------------------------------------
# Mecanismes concurrents et extensions composees (#20773)
# ---------------------------------------------------------------------------


def _eta_hypotheque() -> OntologicalMove:
    return OntologicalMove(
        proposer="bob",
        new_concepts=("hypotheque",),
        opened_actions={"hypotheque": ("nantir",)},
    )


def test_authority_lit_les_memes_votes_que_le_quorum():
    g0 = _game()
    eta = _eta_personne_morale()
    votes = {"personne-morale": {"alice", "bob"}}
    # quorum 2 : accepte ; anciennete (alice) : accepte ; anciennete (bob) : accepte
    assert candidate_key(eta) == "personne-morale"
    assert quorum_mechanism(g0, (eta,), votes=votes, quorum=2)[1] == (eta,)
    assert authority_mechanism(g0, (eta,), votes, "alice") == (eta,)
    votes_bob_seul = {"personne-morale": {"bob"}}
    # quorum 2 refuse (1 suffrage), l'autorite bob admet — divergence sur les memes votes
    assert quorum_mechanism(g0, (eta,), votes=votes_bob_seul, quorum=2)[1] == ()
    assert authority_mechanism(g0, (eta,), votes_bob_seul, "bob") == (eta,)


def test_competing_mechanisms_litige_et_politiques():
    g0 = _game()
    eta_pm = _eta_personne_morale()
    eta_jargon = OntologicalMove(
        proposer="alice",
        new_concepts=("jargon-prive",),
        opened_actions={"jargon-prive": ("jargonner",)},
    )
    votes = {
        "personne-morale": {"alice", "bob"},
        "jargon-prive": {"bob"},  # 1 suffrage : sous le quorum, soutenu par l'autorite
    }
    quorum = lambda g, p, v: quorum_mechanism(g, p, votes=v, quorum=2)[1]  # noqa: E731
    anciennete = lambda g, p, v: authority_mechanism(g, p, v, "bob")  # noqa: E731
    mechs = {"quorum": quorum, "anciennete": anciennete}
    proposals = (eta_pm, eta_jargon)

    g_and, acc_and, litiges = competing_mechanisms(g0, proposals, votes, mechs, policy="and")
    g_or, acc_or, _ = competing_mechanisms(g0, proposals, votes, mechs, policy="or")

    # le litige est exactement la candidature ou les regles divergent
    assert litiges == ("jargon-prive",)
    # conjonction : seules les candidatures admises par les deux passent
    assert acc_and == (eta_pm,)
    # disjonction : le litige passe aussi — meme votes, jeu public different
    assert acc_or == (eta_pm, eta_jargon)
    assert political_opening(g0, g_and) == 2
    assert political_opening(g0, g_or) == 3
    with pytest.raises(ValueError):
        competing_mechanisms(g0, proposals, votes, mechs, policy="tirage")


def test_composition_temoins_negatifs_disjoints_doivent_commuter():
    """Temoins negatifs (#20773) : deux extensions ouvrant des actions DISJOINTES
    commutent sur les quatre axes. Une non-commutativite mesuree sur ce cas
    serait un defaut de l'organe, pas un resultat."""
    g0 = _game()
    eta_pm = _eta_personne_morale()  # ouvre signer, posseder
    eta_hy = _eta_hypotheque()  # ouvre nantir — disjoint
    rep = composition_report(g0, eta_pm, eta_hy)
    assert rep["same_lexicon"] is True
    assert rep["same_actions"] is True
    assert rep["structural_commutativity"] is True
    assert rep["payoff_commutativity"] is True
    assert rep["payoff_conflicts"] == frozenset()
    g12, g21 = compose_ontology(g0, (eta_pm, eta_hy)), compose_ontology(g0, (eta_hy, eta_pm))
    assert g12.payoffs == g21.payoffs


def test_composition_non_commutativite_de_paiement_sur_chevauchement():
    """Deux coups ouvrant la MEME action : le langage commute (union), les
    paiements non — le premier poseur capture la coordonnee (setdefault au
    nom du proposeur). Dette d'irreversibilite de second ordre, mesuree."""
    g0 = _game()
    eta_pm = _eta_personne_morale()  # alice ouvre signer, posseder
    eta_meme = OntologicalMove(
        proposer="bob",
        new_concepts=("titre-executoire",),
        opened_actions={"titre-executoire": ("signer",)},  # chevauche signer
    )
    rep = composition_report(g0, eta_pm, eta_meme)
    assert rep["structural_commutativity"] is True  # le langage et les coups commutent
    assert rep["payoff_commutativity"] is False  # ... mais pas la distribution du pouvoir
    assert rep["payoff_conflicts"] == frozenset({("alice", "signer"), ("bob", "signer")})
    g12 = compose_ontology(g0, (eta_pm, eta_meme))
    g21 = compose_ontology(g0, (eta_meme, eta_pm))
    assert g12.payoffs[("alice", "signer")] == 1.0 and g12.payoffs[("bob", "signer")] == 0.5
    assert g21.payoffs[("bob", "signer")] == 1.0 and g21.payoffs[("alice", "signer")] == 0.5


def test_composition_irreversibilite_sadditionne_independamment_de_l_ordre():
    eta_pm, eta_hy = _eta_personne_morale(), _eta_hypotheque()
    d12 = irreversibility_debt(eta_pm) + irreversibility_debt(eta_hy)
    d21 = irreversibility_debt(eta_hy) + irreversibility_debt(eta_pm)
    assert d12 == d21 == 60.0  # 50.0 (personne morale) + 10.0 (defauts pose 1, undo 10)


# ---------------------------------------------------------------------------
# Banc unique : classer_proxys / temoin_decoratif / bancher_mecanisme
# (#23900 — reprise Hermes : branche renommage, quotient, dualite)
# ---------------------------------------------------------------------------


def test_classer_renommage_pur_est_decoratif():
    # o=0, dA brut=3, dA marginalise=0 : le renommage s'evapore sous quotient.
    # Avant la branche manquante, ce cas tombait dans '?' (review #23900 pt 4).
    assert classer_proxys(0, 3, 1, 0.0026, 0.0, d_a_t_marg=0) == "decoratif"


def test_classer_renommage_actif_ouvre_des_classes():
    assert classer_proxys(0, 3, 1, 0.5, 0.4, d_a_t_marg=2) == "nouveau (renommage actif)"
    assert (
        classer_proxys(0, 3, 1, 0.5, 0.0, d_a_t_marg=2)
        == "nouveau (renommage actif, non institutionnalise)"
    )


def test_classer_concept_ornemental_est_nomme():
    # o>0, dA=0 : un concept qui n'ouvre rien — verbiage, sorti du '?'.
    assert classer_proxys(2, 0, 1, 0.0, 0.0) == "ornamental (concept sans action ouverte)"


def test_classer_sans_d_marg_reste_compatible_avec_la_lecture_brute():
    assert classer_proxys(0, 0, 1, 0.0, 0.0) == "decoratif"
    assert classer_proxys(0, 0, 1, 0.5, 0.0) == "latent"
    # d_a_t_marg None => d_marg = d_a_t = 3 : lecture brute — le renommage
    # est indistinguable d'une ouverture, il se lit actif (c'est le point
    # du quotient : sans equivalence, pas de verdict decoratif).
    assert (
        classer_proxys(0, 3, 1, 0.0, 0.0)
        == "nouveau (renommage actif, non institutionnalise)"
    )
    assert classer_proxys(0, 3, 1, 0.5, 0.4) == "nouveau (renommage actif)"


def test_temoin_est_le_dual_exact_du_classifieur():
    # Propriete enforcee par test (mesuree empiriquement dans la review #23900
    # pt 5) : temoin vide <=> classe 'decoratif', sur TOUTE la grille.
    for o_t in (0, 1, 2):
        for d_a_t in (0, 1, 5):
            for d_marg in (None, 0, 1, 5):
                for c_t in (1, 2):
                    for p_r_marg in (0.0, 0.005, 0.05, 4.0):
                        for inst in (0.0, 0.3):
                            classe = classer_proxys(
                                o_t, d_a_t, c_t, p_r_marg, inst, d_a_t_marg=d_marg
                            )
                            temoin = temoin_decoratif(
                                o_t, d_a_t, c_t, p_r_marg, d_a_t_marg=d_marg
                            )
                            assert (classe == "decoratif") == (temoin == ()), (
                                f"dualite brisee : o={o_t} dA={d_a_t} d_marg={d_marg} "
                                f"c={c_t} p_marg={p_r_marg} -> {classe!r} vs {temoin!r}"
                            )


def test_temoin_ne_compte_pas_l_ouverture_brute_d_un_renommage():
    # dA brut=3 mais marginalise=0 : le temoin du decoratif reste PROPRE.
    assert temoin_decoratif(0, 3, 1, 0.0026, d_a_t_marg=0) == ()
    # L'ouverture brute SEULE (sans quotient) rougissait a tort :
    assert temoin_decoratif(0, 3, 1, 0.0026) != ()


def test_non_canonicite_quotiente_les_renommages():
    g0 = EvolutiveGame(
        agents=("electeur",),
        lexicon=frozenset({"a", "b", "c"}),
        actions=frozenset({"comite a", "comite b", "comite c"}),
        payoffs={("electeur", "comite a"): 2.0},
    )
    ren1 = OntologicalMove(
        proposer="electeur",
        new_concepts=(),
        opened_actions={"": ("comite a'", "comite b'", "comite c'")},
    )
    ren2 = OntologicalMove(
        proposer="electeur",
        new_concepts=(),
        opened_actions={"": ("comite a''", "comite b''", "comite c''")},
    )
    eq = {
        "comite a'": "comite a", "comite b'": "comite b", "comite c'": "comite c",
        "comite a''": "comite a", "comite b''": "comite b", "comite c''": "comite c",
    }
    # Brutes : deux schemas de noms = deux ensembles d'actions distincts.
    assert non_canonicity(g0, (ren1, ren2)) == 2
    # Sous quotient : une seule famille d'extensions, canonique.
    assert non_canonicity(g0, (ren1, ren2), eq) == 1


def _banc_vote() -> tuple:
    g0 = EvolutiveGame(
        agents=("electeur",),
        lexicon=frozenset({"a", "b", "c"}),
        actions=frozenset({"comite a", "comite b", "comite c"}),
        payoffs={
            ("electeur", "comite a"): 2.0,
            ("electeur", "comite b"): 0.3,
            ("electeur", "comite c"): 0.3,
        },
    )
    eta = OntologicalMove(proposer="electeur", new_concepts=(), opened_actions={})
    return g0, eta


def test_bancher_renommage_pur_est_decoratif_sous_quotient():
    g0, eta = _banc_vote()
    g1 = EvolutiveGame(
        agents=("electeur",),
        lexicon=frozenset({"a", "b", "c"}),
        actions=frozenset({"comite a'", "comite b'", "comite c'"}),
        payoffs={
            ("electeur", "comite a'"): 2.0,
            ("electeur", "comite b'"): 0.3,
            ("electeur", "comite c'"): 0.3,
        },
    )
    eq = {"comite a'": "comite a", "comite b'": "comite b", "comite c'": "comite c"}
    ren1 = OntologicalMove(
        proposer="electeur", new_concepts=(),
        opened_actions={"": ("comite a'", "comite b'", "comite c'")},
    )
    ren2 = OntologicalMove(
        proposer="electeur", new_concepts=(),
        opened_actions={"": ("comite a''", "comite b''", "comite c''")},
    )
    eq_cand = dict(eq)
    eq_cand.update({
        "comite a''": "comite a", "comite b''": "comite b", "comite c''": "comite c",
    })
    v = bancher_mecanisme(
        "vote renomme", g0, g1, eta, (ren1, ren2),
        equivalence=eq_cand, horizon=40, n_sim=80, rng=np.random.default_rng(4),
    )
    assert v.O_t == 0 and v.dA_t == 3 and v.dA_t_marg == 0
    assert v.C_t == 1
    assert v.P_R > 1.0  # brut : supports disjoints, le renommage se VOIT
    assert v.P_R_marg < 1e-2  # sous quotient : l'effet s'evapore
    assert v.classe == "decoratif"
    assert v.temoin == ()


def test_bancher_renommage_drifté_est_latent_et_le_temoin_rougit():
    g0, eta = _banc_vote()
    # Renommage MAIS la copie agit : le payoff porte sur une AUTRE classe.
    g1 = EvolutiveGame(
        agents=("electeur",),
        lexicon=frozenset({"a", "b", "c"}),
        actions=frozenset({"comite a'", "comite b'", "comite c'"}),
        payoffs={
            ("electeur", "comite a'"): 0.3,
            ("electeur", "comite b'"): 0.3,
            ("electeur", "comite c'"): 2.0,
        },
    )
    eq = {"comite a'": "comite a", "comite b'": "comite b", "comite c'": "comite c"}
    v = bancher_mecanisme(
        "vote renomme drift", g0, g1, eta, (eta,),
        equivalence=eq, horizon=40, n_sim=80, rng=np.random.default_rng(5),
    )
    assert v.O_t == 0 and v.dA_t_marg == 0
    assert v.P_R_marg > 1e-2  # la trajectoire change SOUS quotient
    assert v.classe == "latent"
    assert any("trajectoire" in v for v in v.temoin)


def test_bench_verdict_porte_l_ouverture_marginalisee():
    v = BenchVerdict(
        mecanisme="x", O_t=0, dA_t=3, C_t=1, P_R=11.2, P_R_marg=0.0026,
        institutionnalisation=0.0, I_R=10.0, classe="decoratif",
    )
    assert v.dA_t_marg == 0  # defaut : champ present, valeur neutre
