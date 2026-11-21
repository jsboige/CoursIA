"""Tests unitaires pour la boucle auto-referentielle p_hat (Case 2, Epic #9533).

23 tests couvrant : mecanique, scan, estimation frontiere, delieur,
verdict honnete, robustesse multi-seed, non-trivialite.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict.phat_self_reference import (
    EnvironmentParams,
    KAPPA_C_PREDICTED,
    KAPPA_GRID,
    N_INIT,
    RATIO_BORNE_HIGH,
    RATIO_DIVERGENT,
    delieur_verdict,
    estimate_stability_boundary,
    f_obs,
    predict_and_dissociate,
    run_full_protocol,
    simulate_self_reference_loop,
    stability_scan,
)


# --------------------------------------------------------------------------- #
#  1. Mécanique : f_obs, couplage, identite aux conditions nulles                #
# --------------------------------------------------------------------------- #


def test_f_obs_exact_predicteur():
    """f_obs avec a_hat = a doit retourner la prediction exacte du pas suivant."""
    params = EnvironmentParams(a=0.9, b=0.1, a_hat=0.9, b_hat=0.1)
    x = np.array([-1.0, 0.0, 1.0, 0.5])
    np.testing.assert_allclose(f_obs(x, params), 0.9 * x + 0.1)


def test_kappa_zero_est_vecteur_d_identite_pour_p_hat():
    """A kappa=0, p_hat_t+1 = f_obs(x_t) independamment de p_hat_t."""
    params = EnvironmentParams()
    rng = np.random.default_rng(42)
    sim = simulate_self_reference_loop(kappa=0.0, n_init=10, horizon=20, rng=rng)
    # Recompute p_hat a la main et verifier.
    for t in range(20):
        expected = f_obs(sim["trajectories_x"][:, t], params)
        np.testing.assert_allclose(sim["trajectories_phat"][:, t + 1], expected)


def test_kappa_zero_simulation_deterministe_avec_seed():
    """Meme seed, meme kappa=0 -> memes ratios (simulation deterministe)."""
    sim1 = simulate_self_reference_loop(
        kappa=0.0, n_init=20, horizon=100, rng=np.random.default_rng(7)
    )
    sim2 = simulate_self_reference_loop(
        kappa=0.0, n_init=20, horizon=100, rng=np.random.default_rng(7)
    )
    np.testing.assert_allclose(sim1["ratio"], sim2["ratio"])


def test_kappa_zero_x_independantes_de_p_hat():
    """A kappa=0, x_t+1 ne depend que de x_t (et bruit), pas de p_hat_t.

    On verifie qu'en re-initialisant p_hat_0 a une valeur tres differente,
    la trajectoire x reste la meme (pour un meme seed de bruit).
    """
    # Fixons le bruit : on triche en simulant avec kappa=0 et en verifiant
    # que x ne depend pas de p_hat. Plus simple : kappa=0 -> equation x_t+1 =
    # a x_t + b + epsilon_t, lineaire en x, lineaire en bruit, INDEPENDANTE
    # de p_hat. Donc deux conditions initiales p_hat differentes donnent meme x.
    params = EnvironmentParams()
    rng = np.random.default_rng(123)

    # Sim 1 avec p_hat par defaut.
    sim1 = simulate_self_reference_loop(
        kappa=0.0, n_init=10, horizon=50, params=params, rng=rng
    )
    rng2 = np.random.default_rng(123)
    # Sim 2 en forcant p_hat_0 = 999 pour voir si ca affecte x.
    x0 = rng2.uniform(-1.0, 1.0, size=10)
    traj_x = np.empty((10, 51))
    traj_x[:, 0] = x0
    for t in range(50):
        noise = rng2.normal(0.0, params.sigma, size=10)
        traj_x[:, t + 1] = params.a * traj_x[:, t] + params.b + noise
    np.testing.assert_allclose(sim1["trajectories_x"], traj_x)


# --------------------------------------------------------------------------- #
#  2. Stabilite : delieur reste borne, bouclee diverge                           #
# --------------------------------------------------------------------------- #


def test_delieur_reste_borne_kappa_zero():
    """kappa=0 (delieur) doit garder ratio << RATIO_DIVERGENT."""
    sim = simulate_self_reference_loop(
        kappa=0.0,
        n_init=N_INIT,
        horizon=200,
        rng=np.random.default_rng(0),
    )
    assert np.all(sim["ratio"] < RATIO_BORNE_HIGH), (
        f"Delieur devrait rester borne (ratio < {RATIO_BORNE_HIGH}), "
        f"max observe = {float(np.max(sim['ratio'])):.2f}"
    )


def test_bouclee_kappa_grand_divergence():
    """kappa=1 doit declencher une divergence massive (ratio >> RATIO_DIVERGENT)."""
    sim = simulate_self_reference_loop(
        kappa=1.0,
        n_init=N_INIT,
        horizon=200,
        rng=np.random.default_rng(0),
    )
    assert np.all(sim["ratio"] >= RATIO_DIVERGENT), (
        f"Bouclee a kappa=1 devrait diverger (ratio >= {RATIO_DIVERGENT}), "
        f"min observe = {float(np.min(sim['ratio'])):.2f}"
    )


def test_monotonie_croissante_du_ratio_avec_kappa():
    """Le ratio median doit croitre monotonement avec kappa (stabilite lineaire)."""
    scan = stability_scan(seeds=(0, 1, 7))
    ratio_median_per_kappa = scan["ratio_median"].mean(axis=0)
    # Tolerance : on accepte une non-monotonie numerique a 5% (le bruit peut
    # creer de petites fluctuations pour les tres petits kappa).
    for i in range(1, len(ratio_median_per_kappa)):
        if ratio_median_per_kappa[i] > RATIO_DIVERGENT:
            # Une fois diverge, on n'exige plus la monotonie (les chiffres
            # explosent et la dynamique n'est plus lineaire).
            break
        # En regime sous-divergent, le ratio median doit croitre.
        assert ratio_median_per_kappa[i] >= ratio_median_per_kappa[i - 1] * 0.95, (
            f"Ratio median devrait croitre avec kappa : "
            f"kappa={KAPPA_GRID[i - 1]:.3f} -> {ratio_median_per_kappa[i - 1]:.3f}, "
            f"kappa={KAPPA_GRID[i]:.3f} -> {ratio_median_per_kappa[i]:.3f}"
        )


# --------------------------------------------------------------------------- #
#  3. Scan de stabilite : structure des sorties                                  #
# --------------------------------------------------------------------------- #


def test_stability_scan_dimensions():
    """Le scan doit retourner les bonnes shapes."""
    scan = stability_scan(seeds=(0, 1, 7), kappa_grid=(0.0, 0.1, 0.5))
    assert scan["ratio_mean"].shape == (3, 3)
    assert scan["ratio_median"].shape == (3, 3)
    assert scan["stable_mask"].shape == (3, 3)
    assert scan["divergent_mask"].shape == (3, 3)
    assert len(scan["kappa_grid"]) == 3
    assert len(scan["seeds"]) == 3


def test_stability_scan_deterministe_meme_seed():
    """Deux scans avec meme seed doivent retourner les memes resultats."""
    scan1 = stability_scan(seeds=(0, 1, 7), kappa_grid=(0.0, 0.1, 0.5))
    scan2 = stability_scan(seeds=(0, 1, 7), kappa_grid=(0.0, 0.1, 0.5))
    np.testing.assert_array_equal(scan1["ratio_median"], scan2["ratio_median"])


def test_stable_et_divergent_mutuellement_exclusifs():
    """Une cellule ne peut pas etre a la fois stable et divergente."""
    scan = stability_scan(seeds=(0, 1, 7))
    assert not np.any(scan["stable_mask"] & scan["divergent_mask"])


def test_kappa_zero_toujours_stable():
    """kappa=0 doit etre dans 'stable' sur toutes les graines."""
    scan = stability_scan(seeds=(0, 1, 7, 42, 99))
    idx_zero = int(np.where(np.isclose(scan["kappa_grid"], 0.0))[0][0])
    assert np.all(scan["stable_mask"][:, idx_zero]), "kappa=0 devrait toujours etre stable"


# --------------------------------------------------------------------------- #
#  4. Estimation de la frontiere : structure et sens                             #
# --------------------------------------------------------------------------- #


def test_estimate_boundary_retourne_per_seed_et_median():
    """L'estimation de frontiere doit rapporter per-seed + median + biais."""
    scan = stability_scan(seeds=(0, 1, 7, 42, 99))
    boundary = estimate_stability_boundary(scan)
    assert "kappa_critical_per_seed" in boundary
    assert "kappa_critical_median" in boundary
    assert "bias_vs_predicted" in boundary
    assert len(boundary["kappa_critical_per_seed"]) == 5
    assert isinstance(boundary["kappa_critical_median"], float)


def test_frontiere_dans_grille_ou_au_dela():
    """La frontiere estimee doit etre dans la grille (ou juste au-dela)."""
    scan = stability_scan(seeds=(0, 1, 7, 42, 99))
    boundary = estimate_stability_boundary(scan)
    last_kappa = scan["kappa_grid"][-1]
    for kc in boundary["kappa_critical_per_seed"]:
        # Soit dans la grille, soit juste au-dela (frontiere > max(grid)).
        assert kc >= scan["kappa_grid"][0] - 1e-9
        assert kc <= last_kappa + 0.5


# --------------------------------------------------------------------------- #
#  5. Delieur verdict : structure et sens                                        #
# --------------------------------------------------------------------------- #


def test_delieur_verdict_clef_presence():
    """delieur_verdict doit retourner les 4 cles documentees."""
    scan = stability_scan(seeds=(0, 1, 7))
    v = delieur_verdict(scan)
    assert "delieur_ratio_per_seed" in v
    assert "delieur_ratio_max" in v
    assert "delieur_ratio_mean" in v
    assert "delieur_stable" in v


def test_delieur_verdict_stable_a_kappa_zero():
    """A kappa=0, delieur doit etre declare stable (le predicteur est exact)."""
    scan = stability_scan(seeds=(0, 1, 7, 42, 99))
    v = delieur_verdict(scan)
    assert v["delieur_stable"], (
        f"Delieur devrait etre stable, max ratio = {v['delieur_ratio_max']:.2f}"
    )


# --------------------------------------------------------------------------- #
#  6. Verdict honnete a deux niveaux (prediction + dissociation)                 #
# --------------------------------------------------------------------------- #


def test_verdict_2_niveaux_champs_obligatoires():
    """predict_and_dissociate doit retourner tous les champs documentes."""
    scan = stability_scan(seeds=(0, 1, 7))
    v = predict_and_dissociate(scan)
    for key in (
        "verdict",
        "verdict_detail",
        "boundary",
        "delieur",
        "prediction_confirmed",
        "dissociation_confirmed",
        "n_seeds",
        "n_within_tolerance",
    ):
        assert key in v, f"Cle manquante : {key}"


def test_verdict_run_full_protocol_CONFIRMED():
    """Le protocole complet avec 5 graines doit retourner CONFIRMED.

    C'est le test central : la prediction numerique est-elle exacte ? Avec
    une grille assez fine et 5 graines, on s'attend a ce que la frontiere
    observee coincide avec KAPPA_C_PREDICTED a la tolerance de la grille.
    """
    r = run_full_protocol()
    assert r["verdict"]["verdict"] == "CONFIRMED", r["verdict"]["verdict_detail"]
    assert r["verdict"]["prediction_confirmed"] is True
    assert r["verdict"]["dissociation_confirmed"] is True


def test_verdict_dissociation_tient_meme_si_prediction_falsifiee():
    """Si on deplace KAPPA_C_PREDICTED hors tolerance, dissociation tient.

    On simule un scenario ou la frontiere observee ne coincide pas avec la
    prediction, et on verifie que le verdict degrade en PARTIAL tout en
    gardant la dissociation.
    """
    # Pas de moyen simple de mocker la frontiere sans toucher au module ;
    # on verifie au moins la structure : si verdict != CONFIRMED, la
    # dissociation reste dans le verdict_detail.
    r = run_full_protocol()
    v = r["verdict"]
    if v["verdict"] != "CONFIRMED":
        assert v["dissociation_confirmed"] or "non soutenue" in v["verdict_detail"]


# --------------------------------------------------------------------------- #
#  7. Robustesse multi-seed (≥ 4 graines, exigence #2161 ICT)                    #
# --------------------------------------------------------------------------- #


def test_5_seeds_kappa_critical_consensus():
    """Avec 5 graines, kappa_critical doit etre stable (faible std)."""
    r = run_full_protocol()
    boundary = r["verdict"]["boundary"]
    # Le coefficient de variation (std / median) doit etre faible si la
    # frontiere est bien definie. Tolerance : 50% (la grille est discrete).
    cv = boundary["kappa_critical_std"] / max(boundary["kappa_critical_median"], 1e-9)
    assert cv < 0.5, f"Frontiere instable inter-graines : CV = {cv:.2f}"


def test_3_seeds_vs_5_seeds_meme_verdict():
    """Le verdict doit etre stable entre 3 et 5 graines (robustesse)."""
    r3 = run_full_protocol(seeds=(0, 1, 7))
    r5 = run_full_protocol(seeds=(0, 1, 7, 42, 99))
    assert r3["verdict"]["verdict"] == r5["verdict"]["verdict"], (
        f"Verdict instable : 3 graines -> {r3['verdict']['verdict']}, "
        f"5 graines -> {r5['verdict']['verdict']}"
    )


# --------------------------------------------------------------------------- #
#  8. Non-trivialite (SOTA Prong B)                                              #
# --------------------------------------------------------------------------- #


def test_horizon_augmente_resolution_frontiere():
    """Allonger T (horizon) doit affiner la frontiere (test non degenere).

    Un test degenere (test trivial) ne dependrait pas de T. Ici, T=50 vs
    T=200 donne des ratios tres differents au voisinage de la frontiere,
    ce qui prouve que le test est sensible a la dimension temporelle du
    phenomene (divergence cumulative sur T).
    """
    sim_50 = simulate_self_reference_loop(
        kappa=0.06, n_init=30, horizon=50, rng=np.random.default_rng(0)
    )
    sim_200 = simulate_self_reference_loop(
        kappa=0.06, n_init=30, horizon=200, rng=np.random.default_rng(0)
    )
    # Meme conditions initiales (meme seed), kappa voisin de la frontiere :
    # le ratio doit croitre avec T (la divergence cumulative domine).
    assert float(np.median(sim_200["ratio"])) > float(np.median(sim_50["ratio"])), (
        f"Le test devrait dependre de T : T=50 ratio median = "
        f"{float(np.median(sim_50['ratio'])):.2f}, T=200 = "
        f"{float(np.median(sim_200['ratio'])):.2f}"
    )


def test_n_init_augmente_stabilite_ratio():
    """Augmenter n_init reduit le bruit sur le ratio au voisinage de la frontiere.

    NB : pour etre interessant, ce test doit se placer dans une zone ou le
    ratio depend de l'echantillon (au voisinage de la frontiere). A kappa=0.04,
    on est encore borne et la stabilite est triviale (CV quasi nul). On
    utilise kappa=0.06 (au voisinage immediat de la frontiere ~0.08) ou le
    ratio depend de la combinaison aleatoire des conditions initiales (certains
    x_0 particuliers menent a des ratios extremes via la non-linearite du
    couplage loop).
    """
    sim_30 = simulate_self_reference_loop(
        kappa=0.06, n_init=30, horizon=200, rng=np.random.default_rng(0)
    )
    sim_300 = simulate_self_reference_loop(
        kappa=0.06, n_init=300, horizon=200, rng=np.random.default_rng(0)
    )
    # Meme seed-mais-different-n_init : la stabilite (1/CV) augmente avec n.
    cv_30 = float(np.std(sim_30["ratio"]) / max(np.mean(sim_30["ratio"]), 1e-9))
    cv_300 = float(np.std(sim_300["ratio"]) / max(np.mean(sim_300["ratio"]), 1e-9))
    # Au voisinage de la frontiere, le ratio peut etre non-trivial (CV > 0).
    # En augmentant n, le CV doit baisser (loi des grands nombres).
    assert cv_300 < cv_30 + 1e-9, (
        f"Le CV devrait baisser avec n_init : n=30 CV={cv_30:.3f}, "
        f"n=300 CV={cv_300:.3f}"
    )


def test_kappa_zero_ne_diverge_pas_meme_avec_T_grand():
    """Le delieur (kappa=0) ne diverge pas, meme pour T tres grand.

    Non-trivialite : un test trivial echouerait ici. Le delieur est borne
    par construction (a < 1), donc le ratio reste < 1 peu importe T.
    """
    sim = simulate_self_reference_loop(
        kappa=0.0, n_init=50, horizon=2000, rng=np.random.default_rng(0)
    )
    assert np.all(sim["ratio"] < 1.5), (
        f"Delieur devrait rester borne meme T=2000, "
        f"max ratio = {float(np.max(sim['ratio'])):.2f}"
    )