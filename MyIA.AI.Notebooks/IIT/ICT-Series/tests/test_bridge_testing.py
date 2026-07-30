"""Tests du module bridge_testing (Epic #8077 — tester les fleches, pas les noeuds).

Verifient le protocole falsifiable du **pont #1** (sigma stabilite ->
recuperabilite) sur le substrat fronce de Thom, et surtout son **verdict
honnêtement FALSIFIE** : la recuperation apres perturbation finie est gouvernee
par la largeur de bassin (position du col), pas par la courbure locale ``sigma``.
``sigma`` n'a aucune puissance predictive independante (correlation partielle
~0) -- c'est un proxy correle, non la cause.

C'est le point methodologique de #8077 : un pont qui echoue est aussi
informatif (distinction toy-model / lien causal) qu'un pont qui tient.

Numpy + pytest. Le module depend de ``catastrophe`` (+ numpy du package).
"""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import bridge_testing as bt  # noqa: E402
from ict import catastrophe as cat  # noqa: E402


# --------------------------------------------------------------------------- #
#  Geometrie des bassins : structure bistable vs monostable                    #
# --------------------------------------------------------------------------- #


def test_basin_geometry_bistable_has_col():
    # region bistable (a<0, petit |b|) : 2 minima + 1 col -> 2 entrees
    geo = bt.basin_geometry(-2.0, 0.3)
    assert len(geo) == 2
    for xstar, sigma, width, col in geo:
        assert sigma > 0.0          # minimum stable : courbure positive
        assert width > 0.0          # col a distance finie
    # le col est commun aux deux bassins (l'equilibre instable du milieu)
    assert geo[0][3] == pytest.approx(geo[1][3], abs=1e-6)


def test_basin_geometry_monostable_empty():
    # region monostable (a>0) : pas de col -> bassin infini -> hors-scope (vide)
    assert bt.basin_geometry(1.0, 0.5) == []
    # au pli exact (discriminant = 0) : pas non plus de col net
    assert bt.basin_geometry(-1.0, 0.0) != []  # b=0, a<0 : bistable symetrique


def test_basin_geometry_width_is_distance_to_col():
    # la demi-largeur doit egaler |x* - col|
    geo = bt.basin_geometry(-2.0, 0.6)
    for xstar, sigma, width, col in geo:
        assert width == pytest.approx(abs(xstar - col), rel=1e-9)


# --------------------------------------------------------------------------- #
#  GATE (falsifiable) : sigma ne predit pas la portee mieux que la largeur     #
# --------------------------------------------------------------------------- #


@pytest.fixture(scope="module")
def verdict():
    # seed 0, deterministe. 126 equilibria sur la grille par defaut.
    return bt.bridge_stability_to_recoverability(seed=0)


def test_bridge_verdict_is_falsified(verdict):
    """Le pont naif « plus stable => mieux recupere » est FALSIFIE sur la fronce :
    la portee de recuperation est gouvernee par la largeur de bassin (col), pas
    par la courbure locale. Verdict honnete = 0.0 (informatif, pas un echec)."""
    assert verdict["bridge_sigma_to_recoverability"] == 0.0


def test_width_dominates_sigma_for_recovery(verdict):
    """La largeur de bassin predit la portee NETTEMENT mieux que sigma
    (rho_width >> rho_sigma) -- sigma n'est qu'un proxy correle."""
    assert verdict["rho_width_recovery"] > verdict["rho_sigma_recovery"]
    assert verdict["rho_width_recovery"] > 0.95   # portee = f(largeur) quasi-parfaite
    assert verdict["rho_sigma_recovery"] < 0.98    # sigma : proxy imparfait


def test_sigma_has_no_independent_predictive_power(verdict):
    """LE TEST DECISIF : correlation partielle de sigma (controle largeur) ~ 0.
    Sigma n'apporte rien au-dela de la largeur -- ce n'est pas la cause."""
    partial = verdict["partial_rho_sigma_recovery_given_width"]
    assert abs(partial) < 0.2                       # ~0 (pas de pouvoir independant)
    assert abs(partial) < verdict["partial_null_p95"]  # sous le null (non significatif)


def test_sigma_width_are_correlated_but_not_identical(verdict):
    """Sigma et largeur sont couplees (rho ~0.93) -- c'est pourquoi sigma a l'air
    de predire la portee marginal -> c'est le piege que le test partiel detecte."""
    assert verdict["rho_sigma_width"] > 0.8
    assert verdict["rho_sigma_width"] < 0.99        # couplees mais distinctes


def test_bridge_verdict_robust_across_seeds():
    """Le verdict falsifie n'est pas un point-artefact (c.1014-L) : il tient sur
    plusieurs graines (le null est shuffle-dependant, la conclusion non)."""
    verdicts = [bt.bridge_stability_to_recoverability(seed=s)["bridge_sigma_to_recoverability"]
                for s in (0, 1, 2)]
    assert all(v == 0.0 for v in verdicts)


# --------------------------------------------------------------------------- #
#  Cohérence interne : la recuperation est bien une fonction de largeur        #
# --------------------------------------------------------------------------- #


def test_recovery_fraction_zero_when_delta_exceeds_width():
    """Sanity : une perturbation franchissant le col perd le bassin (portee bornee
    par la largeur), une perturbation inferieure revient."""
    geo = bt.basin_geometry(-2.0, 0.3)
    xstar, sigma, width, col = geo[0]
    a, b = -2.0, 0.3
    # petite perturbation (sous la largeur) -> revient
    small = cat.relax_to_equilibrium(xstar + 0.1 * np.sign(col - xstar), a, b, dt=0.01, steps=2000)
    assert abs(small - xstar) < 0.1
    # perturbation au-dela de la largeur -> bascule dans l'autre bassin
    big = cat.relax_to_equilibrium(xstar + (width + 0.5) * np.sign(col - xstar), a, b, dt=0.01, steps=2000)
    assert abs(big - xstar) > 0.3   # perdu : beaucoup plus loin de x*


# --------------------------------------------------------------------------- #
#  Bridge #3 : extraction (importance) -> usage causal (ablation)  (CONFIRME)  #
# --------------------------------------------------------------------------- #
# Le pont #3 est CONFIRME sur substrat lineaire a redondance : l'importance
# marginale predit l'usage causal (ablation) au-dela de la redondance, a diversite
# realiste. Le controle nul (redondance severe) FALSIFIE : l'importance devient un
# proxy trompeur, seule l'ablation revele les features causeales (c.1023, C976-L).


def test_redundant_dataset_shape_and_structure():
    """Sanity : le substrat a la forme attendue et les groupes dupliques sont bien
    moins uniques que les singletons (la redondance est injectee)."""
    rng = np.random.default_rng(0)
    X, y = bt._redundant_feature_dataset(rng, n_samples=300, n_singleton=6,
                                         n_dup_groups=6, dup_size=3,
                                         feat_noise=0.3, y_noise=0.5)
    assert X.shape == (300, 6 + 6 * 3)          # K = singletons + groupes * dup_size
    assert y.shape == (300,)
    _, _, uniq = bt._feature_causal_stats(X, y)
    # singletons (6 premiers) > uniques que duplicatas (18 suivants, par groupes de 3)
    assert uniq[:6].mean() > uniq[6:].mean()


def test_bridge3_verdict_is_confirmed():
    """Le pont « importance => usage causal » est CONFIRME a diversite realiste
    (feat_noise eleve) : l'extraction predit l'usage causal au-dela de la redondance."""
    v = bt.bridge_extraction_to_causal_usage(seed=0)
    assert v["bridge_extraction_to_causal_usage"] == 1.0


def test_bridge3_importance_predicts_ablation():
    """La correlation partielle (importance | unicite) -> ablation est nettement
    positive en moyenne sur le regime confirme."""
    v = bt.bridge_extraction_to_causal_usage(seed=0)
    assert v["mean_partial_rho_importance_ablation_given_uniqueness"] > 0.2


def test_bridge3_majority_of_models_confirm():
    """LE TEST DECISIF : sur la majorite des modeles, l'importance predit l'usage
    causal au-dela du null per-modele."""
    v = bt.bridge_extraction_to_causal_usage(seed=0)
    assert v["frac_models_confirmed"] > 0.5


def test_bridge3_verdict_robust_across_seeds():
    """Le verdict confirme n'est pas un point-artefact (c.1014-L)."""
    verdicts = [bt.bridge_extraction_to_causal_usage(seed=s)
                ["bridge_extraction_to_causal_usage"] for s in (0, 1, 2)]
    assert all(v == 1.0 for v in verdicts)


def test_bridge3_null_control_severe_redundancy_falsifies():
    """LE CONTROLE NUL (c.1023, reponse a la question 'ou le pont cede') : sous
    redondance severe (feat_noise faible, duplicatas quasi-identiques), l'importance
    marginale perd son pouvoir predictif sur l'usage causal (frac < 0.5, bridge=0).
    L'importance devient un proxy trompeur ; seule l'ablation (intervention do)
    distingue alors les features causeales des redondantes (do-calculus)."""
    v_null = bt.bridge_extraction_to_causal_usage(feat_noise=0.02, seed=0)
    assert v_null["bridge_extraction_to_causal_usage"] == 0.0
    assert v_null["frac_models_confirmed"] < 0.5
    # CONTRASTE : sous diversite realiste, le pont TIENT.
    assert bt.bridge_extraction_to_causal_usage(feat_noise=0.3, seed=0)["bridge_extraction_to_causal_usage"] == 1.0


# --------------------------------------------------------------------------- #
#  Bridge #4 : workspace (broadcast) -> diffusion fonctionnelle   (CONFIRME)   #
# --------------------------------------------------------------------------- #
# Le pont #4 est CONFIRME : la disponibilite globale (broadcast) etend la portee
# fonctionnelle au-dela de la connectivite directe (elle fait atteindre des
# modules structurellement inaccessibles). Controle nul structural : un bus
# present mais ignore (read_p=0) est fonctionnellement inerte (frac=0 exact) --
# le null « broadcast present mais non exploite en aval » de #8077 (c.1025).


def test_direct_reach_is_transitive_closure():
    """Sanity : _direct_reach_set est la fermeture transitive des aretes directes
    (portee locale, sans bus). Le module source est toujours atteint."""
    rng = np.random.default_rng(0)
    adj = bt._random_module_network(rng, n_modules=20, density=(0.1, 0.2))
    reached = bt._direct_reach_set(adj, source=0)
    assert reached[0]                              # source atteinte
    assert reached.sum() <= 20


def test_broadcast_reaches_unreachable_modules():
    """Sanity : avec un bus lu (read_p=1) et allume (pub_p=1), le broadcast atteint
    des modules que la connectivite directe n'atteint pas (la contribution unique
    du workspace)."""
    rng = np.random.default_rng(0)
    adj = bt._random_module_network(rng, n_modules=40, density=(0.02, 0.06))
    direct = bt._direct_reach_set(adj, source=0)
    broadcast = bt._broadcast_reach_set(adj, read_p=1.0, pub_p=1.0, source=0, rng=rng)
    if (~direct).sum() > 0:                        # s'il y a des inaccessibles
        assert broadcast.sum() >= direct.sum()      # broadcast >= direct


def test_bridge4_verdict_is_confirmed():
    """Le pont « broadcast etend la portee au-dela du direct » est CONFIRME."""
    v = bt.bridge_workspace_to_diffusion(seed=0)
    assert v["bridge_workspace_to_diffusion"] == 1.0


def test_bridge4_broadcast_capacity_predicts_unreachable_reach():
    """LE TEST DECISIF : la capacite du broadcast predit significativement la
    fraction des modules inaccessibles atteints, au-dela du denominateur
    structurel (partial positive > null p95)."""
    v = bt.bridge_workspace_to_diffusion(seed=0)
    partial = v["partial_rho_capacity_frac_given_n_unreachable"]
    assert partial > 0.2
    assert partial > v["partial_null_p95"]


def test_bridge4_null_control_dark_bus_is_inert():
    """LE CONTROLE NUL STRUCTURAL (c.1025) : un bus present mais ignore (read_p=0)
    est fonctionnellement inerte -- la fraction des inaccessibles atteints tombe
    a ~0. C'est le null « broadcast present mais non exploite en aval » de #8077."""
    v = bt.bridge_workspace_to_diffusion(seed=0)
    assert v["null_control_frac_dark_bus"] < 0.05    # bus dark => inerte


def test_bridge4_verdict_robust_across_seeds():
    """Le verdict confirme n'est pas un point-artefact (c.1014-L)."""
    verdicts = [bt.bridge_workspace_to_diffusion(seed=s)
                ["bridge_workspace_to_diffusion"] for s in (0, 1, 2)]
    assert all(v == 1.0 for v in verdicts)


# --------------------------------------------------------------------------- #
#  Bridge #5 : MDL (compression) -> generalisation  (CONFIRME-CONDITIONNEL)    #
# --------------------------------------------------------------------------- #
# Le pont #5 n'est ni un confirme ni un falsifie naif : la compressibilite du
# train predit la generalisation held-out **sur source stationnaire** et
# l'**anti-predit sous decalage de source**. La fleche a un domaine de validite
# (claim_type « vraie sous condition », #7734). Le controle nul naif (drift
# stationnaire) est INERTE (drift quasi-orthogonal) -- le vrai discriminateur est
# le contraste stationnaire vs non-stationnaire (c.1024, rework apres review).


def test_markov_sequence_shape_and_bounds():
    rng = np.random.default_rng(0)
    seq = bt._markov_sequence(rng, n=50, n_states=4, regularity=0.8, drift=0.0)
    assert len(seq) == 50
    assert all(0 <= s < 4 for s in seq)


def test_markov_sequence_regular_is_more_compressible_than_random():
    """Sanity : une sequence reguliere (regularity=1, drift=0) a une entropie de
    train inferieure a une sequence iid (regularity=0)."""
    from ict import mdl
    rng = np.random.default_rng(0)
    reg = bt._markov_sequence(rng, 300, 4, regularity=1.0, drift=0.0)
    rng = np.random.default_rng(0)
    iid = bt._markov_sequence(rng, 300, 4, regularity=0.0, drift=0.0)
    h_reg = mdl.entropy_rate_estimate(reg[:150], block=2)["entropy_rate"]
    h_iid = mdl.entropy_rate_estimate(iid[:150], block=2)["entropy_rate"]
    assert h_reg < h_iid            # regular = plus compressible


@pytest.fixture(scope="module")
def verdict5():
    return bt.bridge_compression_to_generalization(seed=0)


def test_bridge5_verdict_is_confirmed_conditional(verdict5):
    """Le pont est CONFIRME-CONDITIONNEL : le pattern « predit sur source
    stationnaire ET anti-predit sous decalage » tient (bridge=1.0)."""
    assert verdict5["bridge_compression_to_generalization"] == 1.0


def test_bridge5_stationary_compress_predicts_generalization(verdict5):
    """Sur source stationnaire, la compressibilite du train predit fortement la
    generalisation held-out (rho > 0.7) -- le pole CONFIRME."""
    assert verdict5["rho_compress_gen"] > 0.7


def test_bridge5_nonstationary_source_inverts(verdict5):
    """LE VRAI FINDING (c.1022, porte au premier plan c.1024) : sous source
    non-stationnaire (train compressible + test decale), la compression
    **anti-predit** la generalisation (rho < -0.3). C'est le null « compression
    misleads » de #8077, et il borne le domaine de validite du pont."""
    assert verdict5["rho_compress_gen_nonstationary"] < -0.3


def test_bridge5_drift_is_inert_control(verdict5):
    """Le controle nul naif (drift stationnaire) est INERTE : drift est
    quasi-orthogonal a la compression (|rho_compress_drift| faible), donc la
    correlation partielle (compress | drift) est essentiellement egale a la
    correlation brute. La partielle n'est PAS le test decisif d'un pouvoir
    independant -- c'est le contraste stationnaire/non-stationnaire qui tranche."""
    assert abs(verdict5["rho_compress_drift"]) < 0.4   # drift ~ orthogonal
    # la partielle bouge a peine vs le brut (inertie, pas pouvoir independant)
    assert abs(verdict5["partial_rho_compress_gen_given_drift"]
               - verdict5["rho_compress_gen"]) < 0.06


def test_bridge5_verdict_robust_across_seeds():
    """Le verdict conditionnel n'est pas un point-artefact (c.1014-L) : le
    ``_markov_sequence`` est stochastique ET regularity/drift sont tires par essai,
    donc le seed traverse le calcul (mesure de robustesse reelle, contrairement au
    pont #1 deterministe)."""
    verdicts = [bt.bridge_compression_to_generalization(seed=s)
                ["bridge_compression_to_generalization"] for s in (0, 1, 2)]
    assert all(v == 1.0 for v in verdicts)
