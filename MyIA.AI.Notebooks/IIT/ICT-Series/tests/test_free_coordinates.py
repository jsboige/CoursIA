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
    jumeaux_comportementaux,
    non_canonicity,
    performative_power,
    political_opening,
    quorum_mechanism,
    temoin_decoratif,
    verifier_equivalence,
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


def test_concept_et_alias_ne_sont_pas_une_nouvelle_classe():
    # Le concept existe, mais son action ne fait que renommer une action existante.
    for inst in (0.0, 0.5):
        assert classer_proxys(1, 1, 1, 0.0, inst, d_a_t_marg=0) == (
            "ornamental (concept sans action ouverte)"
        )
    # Sans quotient explicite, la lecture historique reste brute.
    assert classer_proxys(1, 1, 1, 0.0, 0.5) == "nouveau"
    assert classer_proxys(1, 1, 1, 0.0, 0.0) == "nouveau (non institutionnalise)"


def test_banc_concept_alias_et_action_reelle_sur_quatre_graines():
    agents = ("auteur", "tiers")
    g0 = EvolutiveGame(
        agents=agents, lexicon=frozenset({"acte"}), actions=frozenset({"acte"}),
        payoffs={(agent, action): 1.0 for agent in agents
                 for action in ("acte", "acte_alias")},
    )
    coup = OntologicalMove(
        proposer="auteur", new_concepts=("jargon",),
        opened_actions={"jargon": ("acte_alias",)},
    )
    g1 = apply_ontology(g0, coup)
    for seed in range(4):
        alias = bancher_mecanisme(
            "alias", g0, g1, coup, (coup,), equivalence={"acte_alias": "acte"},
            horizon=20, n_sim=30, rng=np.random.default_rng(seed),
        )
        nouveau = bancher_mecanisme(
            "action", g0, g1, coup, (coup,),
            horizon=20, n_sim=30, rng=np.random.default_rng(seed),
        )
        assert alias.O_t == alias.dA_t == 1
        assert alias.dA_t_marg == 0 and alias.P_R_marg == 0
        assert alias.institutionnalisation > 0
        assert alias.classe == "ornamental (concept sans action ouverte)"
        assert alias.temoin and "O_t" in alias.temoin[0]
        assert nouveau.dA_t_marg == 1 and nouveau.P_R_marg > 0
        assert nouveau.institutionnalisation > 0 and nouveau.classe == "nouveau"


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


def test_fixed_predictor_rejects_undefined_distribution():
    with pytest.raises(ValueError, match="distinctes"):
        FixedSpacePredictor(("a", "a"))
    p = FixedSpacePredictor(("a", "b"))
    with pytest.raises(ValueError, match="observation"):
        p.log_loss("a")
    for epsilon in (-1.0, float("nan"), float("inf")):
        with pytest.raises(ValueError, match="epsilon"):
            p.log_loss("a", epsilon=epsilon)
    assert p.log_loss("a", epsilon=1.0) == pytest.approx(1.0)
    p.update("a")
    assert p.log_loss("a") == pytest.approx(0.0)
    assert p.log_loss("unknown") == pytest.approx(np.log2(3))


def test_banc_lectures_brute_et_identite_partagent_tirages():
    g0, eta = _banc_vote()
    g1 = apply_ontology(g0, eta)
    result = bancher_mecanisme(
        "identite", g0, g1, eta, (eta,), equivalence={},
        horizon=8, n_sim=3, rng=np.random.default_rng(92),
    )
    assert result.P_R == pytest.approx(result.P_R_marg, abs=1e-15)


# ---------------------------------------------------------------------------
# Revue contradictoire (Concern #23778, 2026-11-01) — les gardes du quotient
# ---------------------------------------------------------------------------

def _banc_renommage(paiement_copie: float) -> tuple[EvolutiveGame, EvolutiveGame, dict[str, str]]:
    """Le banc M5a minimal : un renommage pur, copie a paiement parametre."""
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
    g1 = EvolutiveGame(
        agents=("electeur",),
        lexicon=frozenset({"a", "b", "c"}),
        actions=frozenset({"comite a'", "comite b'", "comite c'"}),
        payoffs={
            ("electeur", "comite a'"): paiement_copie,
            ("electeur", "comite b'"): 0.3,
            ("electeur", "comite c'"): 0.3,
        },
    )
    eq = {"comite a'": "comite a", "comite b'": "comite b", "comite c'": "comite c"}
    return g0, g1, eq


def test_verifier_equivalence_carte_coherente_rend_vide():
    g0, g1, eq = _banc_renommage(paiement_copie=2.0)
    assert verifier_equivalence(g0, g1, eq) == ()


def test_verifier_equivalence_carte_vide_ou_nulle_rend_vide():
    g0, g1, _ = _banc_renommage(paiement_copie=2.0)
    assert verifier_equivalence(g0, g1, None) == ()
    assert verifier_equivalence(g0, g1, {}) == ()


def test_verifier_equivalence_copie_porteuse_de_paiements_est_nommee():
    g0, g1, eq = _banc_renommage(paiement_copie=3.5)  # la copie paie PLUS cher
    violations = verifier_equivalence(g0, g1, eq)
    assert len(violations) == 1
    assert "comite a" in violations[0] and "comite a'" in violations[0]


def test_verifier_equivalence_lit_les_paiements_par_agent():
    g0, _, eq = _banc_renommage(paiement_copie=2.0)
    g0 = EvolutiveGame(
        agents=("electeur", "censeur"),
        lexicon=g0.lexicon, actions=g0.actions,
        payoffs={("electeur", "comite a"): 2.0, ("censeur", "comite a"): 1.0,
                 ("electeur", "comite b"): 0.3, ("censeur", "comite b"): 0.3,
                 ("electeur", "comite c"): 0.3, ("censeur", "comite c"): 0.3},
    )
    g1 = EvolutiveGame(
        agents=("electeur", "censeur"),
        lexicon=g0.lexicon,
        actions=frozenset({"comite a'", "comite b'", "comite c'"}),
        payoffs={("electeur", "comite a'"): 2.0,
                 ("electeur", "comite b'"): 0.3, ("censeur", "comite b'"): 0.3,
                 ("electeur", "comite c'"): 0.3, ("censeur", "comite c'"): 0.3},
    )
    # Pour l'electeur les profils concordent ; le censeur paye l'original 1.0
    # et la copie 0.0 (absente) — la fusion doit tomber sur CE fait, seul.
    violations = verifier_equivalence(g0, g1, eq)
    assert len(violations) == 1
    assert "censeur" in violations[0]


def test_jumeaux_comportementaux_renommage_pur_trois_paires():
    g0, g1, _ = _banc_renommage(paiement_copie=2.0)
    paires = jumeaux_comportementaux(g0, g1)
    # b et c paient tous deux 0.3 : ce sont des jumeaux, et la paire de c'
    # nomme un REPRESENTANT (le premier trie) — la non-unificite est un fait
    # du banc, pas un defaut du detecteur.
    assert paires == (
        ("comite a'", "comite a"),
        ("comite b'", "comite b"),
        ("comite c'", "comite b"),
    )


def test_jumeaux_comportementaux_action_vraiment_nouvelle_aucune_paire():
    g0, g1, _ = _banc_renommage(paiement_copie=9.7)  # profil inedit : pas de jumeau
    assert jumeaux_comportementaux(g0, g1) == (("comite b'", "comite b"), ("comite c'", "comite b"))


def test_jumeaux_comportementaux_meme_nom_ne_compte_pas():
    g0, _, _ = _banc_renommage(paiement_copie=2.0)
    g1 = EvolutiveGame(agents=g0.agents, lexicon=g0.lexicon, actions=g0.actions,
                       payoffs=dict(g0.payoffs))
    assert jumeaux_comportementaux(g0, g1) == ()


def _verdict_copie_porteuse(paiement_copie: float) -> tuple:
    """Le banc M5a, copie a paiement parametre, carte de noms passe telle quelle."""
    g0, g1, eq = _banc_renommage(paiement_copie=paiement_copie)
    eta = OntologicalMove(proposer="electeur", new_concepts=(), opened_actions={})
    ren1 = OntologicalMove(proposer="electeur", new_concepts=(),
                           opened_actions={"": ("comite a'", "comite b'", "comite c'")})
    v = bancher_mecanisme("copie porteuse (carte de noms)", g0, g1, eta, (ren1,),
                          equivalence=eq, horizon=40, n_sim=80,
                          rng=np.random.default_rng(7))
    return v, verifier_equivalence(g0, g1, eq)


def test_faux_decoratif_sous_eps_est_rattrape_par_la_garde():
    """Le faux decoratif MESURE : une copie qui paie 2.05 (vs 2.00) passe sous
    eps (P_R_marg ~ 6e-4) et le banc dit 'decoratif' — alors que la carte de
    noms fusionne des paiements divergents. La garde lit les paiements, pas la
    trajectoire lissée : elle nomme la carte inadmissible que eps avale."""
    v, garde = _verdict_copie_porteuse(paiement_copie=2.05)
    assert v.classe == "decoratif"           # le verdict NAIF...
    assert v.P_R_marg < 1e-2                 # ...parce que l'ecart passe sous eps
    assert len(garde) == 1                   # ...et la garde ne passe pas dessous


def test_copie_porteuse_au_dela_d_eps_bascule_en_latent_temoin_rouge():
    """Le meme cas, divergence franche (3.5) : le banc lui-meme bascule en
    'latent' et le temoin rougit — la carte trop large echoue BRUYAMMENT, la
    garde nomme la cause en plus."""
    v, garde = _verdict_copie_porteuse(paiement_copie=3.5)
    assert v.classe == "latent"
    assert any("trajectoire" in t for t in v.temoin)
    assert len(garde) == 1


def test_renommage_pur_carte_admissible_decoratif_merite():
    """Le controle : copie a paiement identique (2.0), carte coherente — le
    verdict 'decoratif' est alors TENU et la garde se tait."""
    v, garde = _verdict_copie_porteuse(paiement_copie=2.0)
    assert v.classe == "decoratif"
    assert v.temoin == ()
    assert garde == ()


def test_faux_nouveau_par_carte_oubliee_est_rattrape_par_les_jumeaux():
    """Le circuit complet du faux nouveau : carte oubliee -> le banc dit
    'nouveau', les jumeaux comportementaux designent le renommage."""
    g0, g1, _ = _banc_renommage(paiement_copie=2.0)
    eta = OntologicalMove(proposer="electeur", new_concepts=(), opened_actions={})
    ren1 = OntologicalMove(proposer="electeur", new_concepts=(),
                           opened_actions={"": ("comite a'", "comite b'", "comite c'")})
    v = bancher_mecanisme("renommage pur (carte oubliee)", g0, g1, eta, (ren1,),
                          equivalence=None, horizon=40, n_sim=80,
                          rng=np.random.default_rng(8))
    assert v.classe.startswith("nouveau")   # le verdict NAIF
    assert v.dA_t_marg == 3                 # ...compte 3 classes nouvelles
    paires = jumeaux_comportementaux(g0, g1)
    assert len(paires) == 3                 # ...toutes trois sont des renommages
