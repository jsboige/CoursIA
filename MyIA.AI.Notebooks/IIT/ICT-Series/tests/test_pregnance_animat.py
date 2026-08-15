"""Tests du module #7740 (C1) : animat a pregnance/valence incarnees.

Couvre les quatre verdicts falsifiables du banc incarne + la matrice de
dissociation (la porte scientifique #7740) + leurs controles negatifs :

1. **p_hat incarne** (mesure 1) : ``p_hat`` bat la persistance sur balistique
   (source previsible) mais pas sur statique ; sur ``erratique`` son erreur
   relative explose (le levier de dissociation).
2. **transfert incarne** (mesure 2) : un signal neutre devient APPROCHE seul
   apres co-occurrence avec une source, et un controle non-conditionne ne l'est
   pas. Controle negatif : sans conditionnement, pas de transfert.
3. **engagement d'action** (mesure 3) : un animat investi (forte ``pi``)
   collapse sa distribution d'actions (entropie << uniforme). Controle : sans
   investissement, l'entropie reste proche du max.
4. **reversibilite comportementale** (mesure 6) : l'approche acquise s'eteint
   sous presentation seule ; la valence ``pi`` acquise puis eteinte. Controle :
   sans acquisition, pas de reversibilite a observer.
5. **dissociation** : sur ``erratique``, ``p_hat`` est detruit MAIS transfert +
   reversibilite tiennent — valence et prediction sont dissociables.

Reutilises (non reinventes) : :class:`ict.learned_valence.LearnedValence`,
:func:`ict.valence.predict_source` + baselines, :func:`ict.inhibited_action.action_entropy`.
numpy + pytest, CPU uniquement.
"""

import numpy as np
import pytest

from ict.pregnance_animat import (
    AnimatConfig,
    ObjectSpec,
    PregnanceAnimat,
    build_object_trajectories,
    prediction_accuracy_test,
    phat_regime_sweep,
    embodied_transfer_test,
    action_commitment_test,
    behavioral_reversibility_test,
    free_energy_profile_test,
    predictive_information_test,
    predictive_information_regime_contrast,
    dissociation_matrix,
)


# --- Proprietes mecaniques de PregnanceAnimat ---


def test_animat_initial_state_is_neutral():
    """A l'init, aucun signal n'est valorise (pi=0), faim nulle, position connue."""
    a = PregnanceAnimat(n_objects=3, rng=np.random.default_rng(0))
    assert np.all(a.lv.valence_vector() == 0.0)
    assert a.hunger == 0.0
    assert np.allclose(a.pos, [2.0, 2.0])


def test_module_reuses_learned_valence_and_predict_source():
    """L'animat REUTILISE les fondations (non reinventees) : LearnedValence et
    predict_source proviennent de ict.learned_valence / ict.valence."""
    from ict.learned_valence import LearnedValence
    from ict.valence import predict_source
    a = PregnanceAnimat(n_objects=2, rng=np.random.default_rng(0))
    assert isinstance(a.lv, LearnedValence)
    assert callable(predict_source)


def test_conditioning_episode_raises_neutral_valence():
    """Apres un episode de co-occurrence (source + neutre tethered), la valence
    du neutre monte (acquisition Rescorla-Wagner via co-occurrence)."""
    from ict.pregnance_animat import _tethered_trajectories, _run_episode
    rng = np.random.default_rng(0)
    a = PregnanceAnimat(n_objects=3, config=AnimatConfig(), rng=rng)
    a.set_intrinsic_valences({0: 1.0})
    trajs = _tethered_trajectories("balistique", 140, 32, rng, n_objects=3,
                                   neutral_idx=1, control_idx=2)
    _run_episode(a, trajs, start=np.array([2.0, 2.0]))
    assert a.lv.valence(1) > 0.5          # neutre conditionne
    assert a.lv.valence(2) < 0.05         # controle hors-arene reste neutre


def test_hunger_grows_and_capture_satiates():
    """La faim croit avec le temps ; capturer une source la fait chuter."""
    from ict.pregnance_animat import _run_episode
    rng = np.random.default_rng(0)
    a = PregnanceAnimat(n_objects=2, config=AnimatConfig(hunger_rate=0.05, satiation=0.4), rng=rng)
    a.set_intrinsic_valences({0: 1.0})
    # source immobile au centre, animat proche : capture immediate.
    src = np.full((2, 30, 2), 16.0)
    _run_episode(a, src, start=np.array([15.0, 15.0]))
    assert len(a.captures) > 0
    # apres captures repetees, la faim a chute sous son max.
    assert a.hunger < 1.0


def test_animat_without_valence_explores():
    """Sans valence (pi=0, aucune source), l'animat explore (action = n_objects)."""
    from ict.pregnance_animat import _run_episode
    rng = np.random.default_rng(0)
    a = PregnanceAnimat(n_objects=3, config=AnimatConfig(), rng=rng)
    # aucun intrinsic, pi nul -> rien valorise -> exploration.
    src = np.full((3, 40, 2), 10.0)
    _run_episode(a, src, start=np.array([2.0, 2.0]))
    actions = np.asarray(a.actions)
    assert (actions == a.n_objects).mean() > 0.8   # majorite d'exploration


# --- Gardes de validation ---


def test_invalid_n_objects_raises():
    """n_objects=0 propage la garde de LearnedValence (n_signals >= 1)."""
    with pytest.raises(ValueError):
        PregnanceAnimat(n_objects=0)


def test_build_object_trajectories_shape():
    """Le constructeur d'environnement renvoie la forme attendue."""
    objs = [ObjectSpec(idx=0, kind="balistique", intrinsic_valence=1.0),
            ObjectSpec(idx=1, kind="erratique")]
    trajs = build_object_trajectories(objs, n_steps=50, size=32, rng=np.random.default_rng(0))
    assert trajs.shape == (2, 50, 2)


# --- Mesure 1 : p_hat incarne ---


def test_phat_beats_persistence_on_ballistic():
    """Sur balistique (vitesse constante), p_hat bat la persistance."""
    r = prediction_accuracy_test("balistique", seed=0)
    assert r["err_phat"] < r["err_persistence"]
    assert r["phat_beats_persistence"] == 1.0


def test_phat_does_not_beat_persistence_on_static():
    """Sur statique, la persistance est quasi parfaite : p_hat ne bat pas
    (controle : p_hat n'est pas magiquement toujours gagnant)."""
    r = prediction_accuracy_test("statique", seed=0)
    assert r["phat_beats_persistence"] == 0.0


def test_phat_erratic_relative_error_exceeds_ballistic():
    """Le levier de dissociation : err_phat/err_pers est plus haut sur erratique
    que sur balistique (p_hat y perd relativement)."""
    sweep = phat_regime_sweep(seed=0)
    ratio_errat = sweep["erratique"]["err_phat"] / sweep["erratique"]["err_persistence"]
    ratio_bal = sweep["balistique"]["err_phat"] / sweep["balistique"]["err_persistence"]
    assert ratio_errat > ratio_bal


# --- Mesure 2 : transfert incarne ---


def test_embodied_transfer_verdict():
    """Verdict TRANSFERT : le neutre devient approche seul, le controle non."""
    r = embodied_transfer_test(kind="balistique", seed=0)
    assert r["post_valence_neutral"] > 0.5
    assert r["control_valence_unconditioned"] < 0.05
    assert r["approach_fraction_conditioned"] > r["approach_fraction_control"]
    assert r["approach_gain"] > 0.15
    assert r["transferred"] == 1.0


def test_transfer_holds_on_erratic_regime():
    """Le transfert tient meme sur erratique : la co-occurrence (tethered)
    conditionne independamment de la previsibilite (dissociation vs p_hat)."""
    r = embodied_transfer_test(kind="erratique", seed=0)
    assert r["post_valence_neutral"] > 0.5
    assert r["transferred"] == 1.0


def test_no_transfer_without_conditioning():
    """Controle negatif : sans conditionnement (n_condition=0), pas de transfert."""
    r = embodied_transfer_test(kind="balistique", n_condition=0, seed=0)
    assert r["post_valence_neutral"] < 0.05
    assert r["transferred"] == 0.0


# --- Mesure 3 : engagement d'action ---


def test_action_commitment_verdict():
    """Verdict ENGAGEMENT : l'investi collapse son entropie d'action."""
    r = action_commitment_test(kind="balistique", seed=0)
    assert r["post_valence_signal"] > 0.2
    assert r["action_entropy_invested"] < r["action_entropy_uniform"]
    assert r["entropy_drop"] > 0.25
    assert r["committed"] == 1.0


def test_invested_entropy_below_uniform():
    """L'entropie de l'investi est strictement sous ln(n_actions) (non-uniforme)."""
    r = action_commitment_test(seed=0)
    assert r["action_entropy_invested"] < r["action_entropy_uniform"] - 0.2


# --- Mesure 6 : reversibilite comportementale ---


def test_behavioral_reversibility_verdict():
    """Verdict REVERSIBILITE : l'approche acquise s'eteint sous presentation seule."""
    r = behavioral_reversibility_test(kind="balistique", seed=0)
    assert r["acquired_valence"] > 0.5
    assert r["extinguished_valence"] < r["acquired_valence"] * 0.5
    assert r["approach_fraction_acquired"] > r["approach_fraction_extinguished"]
    assert r["approach_drop"] > 0.15
    assert r["reversible"] == 1.0


def test_no_reversibility_without_acquisition():
    """Controle negatif : sans acquisition (conditionnement court), pi reste basse
    et la 'reversibilite' n'a rien a inverser (acquired_valence < seuil)."""
    r = behavioral_reversibility_test(kind="balistique", n_condition=5, seed=0)
    assert r["acquired_valence"] < 0.3
    assert r["reversible"] == 0.0


# --- La matrice de dissociation (porte scientifique #7740) ---


def test_dissociation_matrix_observed():
    """Le verdict scientifique : la dissociation p_hat / valence est etablie."""
    dm = dissociation_matrix(seed=0)
    assert dm["_verdict"]["dissociation_observed"] == 1.0


def test_dissociation_erratic_destroys_phat_but_valence_holds():
    """Le coeur de la dissociation : erratique a err_phat relative elevee MAIS
    transfert + reversibilite + engagement tiennent (valence != prediction)."""
    dm = dissociation_matrix(seed=0)
    errat = dm["erratique"]
    bal = dm["balistique"]
    assert errat["err_phat_vs_persistence"] > bal["err_phat_vs_persistence"]
    assert errat["transferred"] == 1.0
    assert errat["committed"] == 1.0
    assert errat["reversible"] == 1.0


def test_dissociation_matrix_covers_three_regimes():
    """La matrice couvre balistique / erratique / bruite (3 regimes Croises)."""
    dm = dissociation_matrix(seed=0)
    for kind in ("balistique", "erratique", "bruite"):
        assert kind in dm
        assert "err_phat_vs_persistence" in dm[kind]
        assert "transferred" in dm[kind]


# --- Mesure 4 : profil d'energie libre incarnee (precision fixe vs adaptive) ---


def test_prediction_trace_shape_matches_episodes():
    """``prediction_trace()`` renvoie ``(T, n_objects, 2)`` -- une prediction
    lead-ahead ``q_hat`` par pas, necessaire pour apparier ``(obs[t+lead],
    q_hat[t])`` en mesure 4."""
    rng = np.random.default_rng(0)
    a = PregnanceAnimat(n_objects=3, config=AnimatConfig(size=16), rng=rng)
    obs_t = np.array([[2.0, 2.0], [5.0, 5.0], [8.0, 3.0]])  # (n_obj=3, 2)
    for t in range(12):
        a.step(obs_t, t)
    tr = a.prediction_trace()
    assert tr.shape == (12, 3, 2)
    assert np.all(np.isfinite(tr))


def test_free_energy_profile_returns_all_keys():
    """Le banc mesure 4 renvoie les ratios + les deux verdicts falsifiables."""
    r = free_energy_profile_test(seed=0)
    for key in (
        "mse_ballistic", "mse_erratic", "mse_ratio_err_over_bal",
        "F_fixed_ballistic", "F_fixed_erratic", "F_fixed_ratio_err_over_bal",
        "F_adaptive_ballistic", "F_adaptive_erratic", "F_adaptive_ratio_err_over_bal",
        "fe_fixed_monotone_with_mse", "fe_adaptive_amortizes_mse",
    ):
        assert key in r, f"cle manquante: {key}"


def test_mse_regime_effect_erratic_worse_than_ballistic():
    """Le regime erratique degrade la prediction ``q_hat`` (effet regime, mesure 1)
    -- prealable au gate FE : sans effet regime, il n'y a rien a amortir."""
    r = free_energy_profile_test(seed=0)
    assert r["mse_erratic"] > r["mse_ballistic"]


def test_fe_gate1_fixed_monotone_with_mse_holds():
    """Gate 1 incarne : en precision fixe, F et MSE rangent les regimes pareil
    (tous deux superieurs sous erratique) -- FE est un habillage du MSE en rang."""
    r = free_energy_profile_test(seed=0)
    assert r["fe_fixed_monotone_with_mse"] == 1.0


def test_fe_gate2_adaptive_amortizes_regime_explosion():
    """Gate 2 incarne : la precision adaptive amortit l'explosion de regime
    (ratio F_adaptive erratique/balistique inferieur au ratio MSE)."""
    r = free_energy_profile_test(seed=0)
    assert r["fe_adaptive_amortizes_mse"] == 1.0
    assert r["F_adaptive_ratio_err_over_bal"] < r["mse_ratio_err_over_bal"]


def test_gate2_robust_to_floor_sweep():
    """Robustesse de gate 2 (reviewer △2) : le verdict d'amortissement tient quand
    on varie le plancher scale-aware ±2x autour de son defaut (0.025, 0.05, 0.10).
    Si gate 2 ne tenait qu'a un seul point de tuning, le banc serait fragile.
    """
    for floor_frac in (0.025, 0.05, 0.10):
        r = free_energy_profile_test(seed=0, floor_frac=floor_frac)
        assert r["floor_frac"] == floor_frac
        assert r["fe_adaptive_amortizes_mse"] == 1.0, (
            f"gate 2 casse a floor_frac={floor_frac} (fragile au tuning)")
        assert r["F_adaptive_ratio_err_over_bal"] < r["mse_ratio_err_over_bal"]


def test_bare_floor_reproduces_pathology():
    """Controle negatif (reviewer △2) : un plancher quasi-absolu (floor_frac ~ bare
    estimateur 1e-6) fait EXPLOSER la surprise balistique (~142 vs ~1 a floor
    scale-aware) -- c'est la pathologie qui motive le plancher scale-aware. Sans ce
    controle, le design du floor serait une assertion non justifiee."""
    bare = free_energy_profile_test(seed=0, floor_frac=1e-7)
    aware = free_energy_profile_test(seed=0, floor_frac=0.05)
    # la surprise balistique explose sous bare floor (q_hat quasi-parfait ->
    # variance EMA effondree -> dust numerique).
    assert bare["F_adaptive_ballistic"] > 10.0 * aware["F_adaptive_ballistic"]


# --- Mesure 5 : information predictive I(q_hat ; obs) vs MSE ---


def test_predictive_information_returns_bits_and_mse():
    """Le banc M5 renvoie MI en bits + le MSE lead-ahead sur la meme trajectoire."""
    r = predictive_information_test("balistique", seed=0)
    assert r["mutual_information_bits"] >= 0.0
    assert r["mse"] > 0.0
    assert r["n_bins"] == 8
    assert r["kind"] == "balistique"


def test_mi_anticorrelated_with_mse_across_regimes():
    """La porte M5 : MI chute sous erratique (<1) TANDIS QUE MSE monte (>1) --
    preuve que MI et MSE sont deux lecteurs orthogonaux de q_hat, pas redundants.
    Anti-pattern : si MI disait la meme chose que MSE, les deux ratios iraient
    dans le meme sens."""
    c = predictive_information_regime_contrast(seed=0)
    assert c["mi_anticorrelated_with_mse"] == 1.0
    assert c["MI_ratio_err_over_bal"] < 1.0   # MI chute sous erratique
    assert c["MSE_ratio_err_over_bal"] > 1.0  # MSE monte sous erratique


def test_mi_discretization_robust():
    """Robustesse au binning : la conclusion qualitative (anti-correlation MI/MSE)
    tient sur n_bins in {4, 8, 16} (±2x autour du defaut 8). Si elle ne tenait
    qu'a un seul n_bins, la conclusion serait un artefact de discretisation."""
    for n_bins in (4, 8, 16):
        c = predictive_information_regime_contrast(seed=0, n_bins=n_bins)
        assert c["mi_anticorrelated_with_mse"] == 1.0, (
            f"anti-correlation MI/MSE casse a n_bins={n_bins} (fragile au binning)")
