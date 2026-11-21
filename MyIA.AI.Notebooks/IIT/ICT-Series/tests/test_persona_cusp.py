"""Tests du module ``ict.persona_cusp`` -- EPIC #4588 / #5104 (ICT-23).

Couvre les 3 predictions de l'Epic #5104 traduites en jumeau cusp de
Thom :

* **P0** (aplatissement par inoculation) : ``charge -> 0`` doit faire
  sortir la persona de la region bistable, meme a transgression forte.
* **P1** (hysteresis conditionnelle) : sous ``charge > 0``, un balayage
  aller-retour de la recompense doit montrer **deux sauts** ; sous
  inoculation (``charge ~ 0``), le suivi doit etre **continu**.
* **P2** (EWS Wissel/Scheffer) : variance et AR1 doivent monter avant
  la bascule (ralentissement critique), et rester plats sous inoculation.

Toutes les fonctions sont numpy-only et deterministes (graine fixee pour
les SDE). Cf. ``tests/test_catastrophe.py`` pour le pattern de tests de
la primitive cusp partagee.
"""

from __future__ import annotations

import numpy as np
import pytest

from ict import catastrophe as cat
from ict import early_warning as ews
from ict.persona_cusp import (
    _first_sustained_below,
    aaft_surrogate,
    ews_summary_persona,
    inoculation_check,
    inoculation_signature,
    in_persona_bistable_region,
    loop_tipping_points,
    persona_a_factor,
    persona_branch_along,
    persona_catastrophe_indices,
    persona_fold_b,
    persona_force,
    persona_hysteresis_loop,
    persona_potential,
    persona_ramp_sde,
    persona_sde,
    persona_stable_branch,
    ramp_ews_segment,
    relax_persona,
    surrogate_tau_band,
)


# --------------------------------------------------------------------------- #
#  P0 -- bistabilite conditionnelle a la charge semantique                     #
# --------------------------------------------------------------------------- #


def test_a_factor_sign():
    """``a = -transgression * charge`` : negatif si les deux positifs."""
    assert persona_a_factor(2.0, 0.5) == pytest.approx(-1.0)
    assert persona_a_factor(0.0, 0.5) == 0.0
    assert persona_a_factor(2.0, 0.0) == 0.0
    assert persona_a_factor(2.0, -0.5) == pytest.approx(1.0)


def test_inoculation_zero_flattens_bistability():
    """P0 : charge=0 => plus de bistabilite, meme a transgression forte."""
    # charge = 0 => a = 0 => monostable (un seul bassin)
    assert not in_persona_bistable_region(transgression=5.0, charge=0.0, reward=0.0)
    assert not in_persona_bistable_region(transgression=5.0, charge=0.0, reward=1.0)
    # charge > 0 + transgression suffisante => bistable
    assert in_persona_bistable_region(transgression=2.0, charge=1.0, reward=0.0)


def test_inoculation_check_threshold():
    """Le predicat ``inoculation_check`` est vrai sous le seuil 1e-3."""
    assert inoculation_check(0.0)
    assert inoculation_check(1e-4)
    assert not inoculation_check(1e-2)
    assert not inoculation_check(0.5)


def test_potential_equals_cusp_at_zero_charge():
    """Charge nulle => ``V(p) = p^4/4 + b p`` (pas de terme quadratique)."""
    p = np.linspace(-2.0, 2.0, 5)
    v_charge0 = persona_potential(p, transgression=3.0, charge=0.0, reward=0.5)
    v_ref = p ** 4 / 4 + 0.5 * p
    assert np.allclose(v_charge0, v_ref)


def test_force_is_negative_gradient_of_potential():
    """Cohence ``dp/dt = -dV/dp`` sur une grille de points."""
    p = np.linspace(-1.5, 1.5, 7)
    h = 1e-4
    for tr, ch, rw in [(2.0, 0.8, 0.0), (1.0, 0.5, 0.2), (0.0, 0.0, 0.5)]:
        v_plus = persona_potential(p + h, tr, ch, rw)
        v_minus = persona_potential(p - h, tr, ch, rw)
        grad_num = (v_plus - v_minus) / (2 * h)
        f = persona_force(p, tr, ch, rw)
        assert np.allclose(f, -grad_num, atol=1e-6), (tr, ch, rw)


# --------------------------------------------------------------------------- #
#  P1 -- hysteresis conditionnelle : 2 catastrophes sans inoculation, 0 avec  #
# --------------------------------------------------------------------------- #


def _rampe_recompenses(sym_max: float = 2.0, n_up: int = 60) -> np.ndarray:
    """Rampe symetrique aller-retour comme ICT-10 (perception + capture)."""
    up = np.linspace(-sym_max, sym_max, n_up)
    down = np.linspace(sym_max, -sym_max, n_up)
    return np.concatenate([up, down])


def test_hysteresis_loop_two_catastrophes_without_inoculation():
    """P1 : sous charge semantique forte, 2 catastrophes sur le lacet."""
    rewards = _rampe_recompenses(sym_max=1.5, n_up=80)
    ps = persona_hysteresis_loop(
        transgression=2.0,
        charge=0.8,  # inoculation absente
        rewards=rewards,
        dt=0.01,
        relax_steps=400,
    )
    n_cat = len(persona_catastrophe_indices(rewards, ps, threshold=0.5))
    assert n_cat == 2, f"Attendu 2 catastrophes, vu {n_cat}"


def test_hysteresis_loop_continuous_with_full_inoculation():
    """P0 dynamique : sous charge=0, suivi continu, 0 saut."""
    rewards = _rampe_recompenses(sym_max=1.5, n_up=80)
    ps = persona_hysteresis_loop(
        transgression=2.0,
        charge=0.0,  # inoculation totale
        rewards=rewards,
        dt=0.01,
        relax_steps=400,
    )
    n_cat = len(persona_catastrophe_indices(rewards, ps, threshold=0.5))
    assert n_cat == 0, f"Attendu 0 catastrophe (inoculation), vu {n_cat}"


def test_hysteresis_loop_range_monotone_when_monostable():
    """Monostable => ``p`` reste dans un intervalle borne par le balayage."""
    rewards = _rampe_recompenses(sym_max=2.0, n_up=50)
    ps = persona_hysteresis_loop(
        transgression=2.0,
        charge=0.0,  # inoculation => monostable
        rewards=rewards,
        dt=0.01,
        relax_steps=300,
    )
    # Sous monostabilite, p doit rester proche du minimum unique (p ~ -b).
    # La plage ne doit pas montrer le saut caracteristique des 2 bassins.
    assert ps.max() - ps.min() < 3.0, (
        f"Plage inattendue sous monostabilite : "
        f"min={ps.min():.3f}, max={ps.max():.3f}"
    )


def test_relax_converges_to_equilibrium():
    """La relaxation aboutit a un zero de la force (equilibre cusp)."""
    # Demarre loin du minimum attendu
    p_final = relax_persona(
        p0=2.0,
        transgression=2.0,
        charge=0.8,
        reward=0.0,
        dt=0.01,
        steps=5000,
    )
    f_final = persona_force(p_final, 2.0, 0.8, 0.0)
    assert abs(f_final) < 1e-3, f"Force residuelle {f_final}"


# --------------------------------------------------------------------------- #
#  P2 -- EWS Wissel/Scheffer avant le pli                                       #
# --------------------------------------------------------------------------- #


def test_ews_distinguish_bistable_vs_monostable():
    """P2 : les EWS (variance, AR1) sont plus eleves en regime bistable
    qu'en regime monostable (inoculation). C'est la **signature**
    Wissel/Scheffer (cf ICT-8 / ICT-20) : le ralentissement critique
    n'apparait que quand la bifurcation est proche.

    Note : on ne teste PAS ``tau > 0`` directement sur une seule
    trajectoire (signe depend de la graine + seed) ; on teste que la
    **difference** bistable - monostable est positive et marquee.
    C'est le diagnostic haut-niveau de P2.
    """
    T = 20000
    # Regime bistable (charge forte -> a < 0)
    ps_bi = persona_sde(
        transgression=2.0, charge=0.8, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    # Regime monostable par inoculation (charge = 0 -> a = 0)
    ps_mono = persona_sde(
        transgression=2.0, charge=0.0, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    sum_bi = ews_summary_persona(ps_bi, window=500, thin_factor=5, detrend_sigma=2.0)
    sum_mono = ews_summary_persona(ps_mono, window=500, thin_factor=5, detrend_sigma=2.0)
    # La variance moyenne est plus elevee en bistable (le systeme
    # "hesite" entre les 2 bassins) qu'en monostable (autour d'un seul).
    assert sum_bi["variance_mean"] > sum_mono["variance_mean"], (
        f"variance bistable {sum_bi['variance_mean']:.4f} doit etre > "
        f"variance monostable {sum_mono['variance_mean']:.4f}"
    )


def test_ews_ar1_higher_in_bistable_regime():
    """P2 (variante) : l'AR1 (autocorrelation lag-1) est plus eleve en
    regime bistable qu'en monostable -- le systeme "hesite" et la
    dynamique presente une memoire courte plus marquee."""
    T = 20000
    ps_bi = persona_sde(
        transgression=2.0, charge=0.8, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    ps_mono = persona_sde(
        transgression=2.0, charge=0.0, reward=0.05,
        p0=0.0, sigma=0.05, dt=0.01, T=T, seed=20260704,
    )
    sum_bi = ews_summary_persona(ps_bi, window=500, thin_factor=5, detrend_sigma=2.0)
    sum_mono = ews_summary_persona(ps_mono, window=500, thin_factor=5, detrend_sigma=2.0)
    # AR1 plus grand en bistable (le "bruit" est plus correle).
    assert sum_bi["ar1_mean"] > sum_mono["ar1_mean"], (
        f"AR1 bistable {sum_bi['ar1_mean']:.4f} doit etre > "
        f"AR1 monostable {sum_mono['ar1_mean']:.4f}"
    )


# --------------------------------------------------------------------------- #
#  Signature d'inoculation : courbe N_catastrophes(charge) decroissante        #
# --------------------------------------------------------------------------- #


def test_inoculation_signature_monotone_decreasing():
    """La signature ``N_catastrophes(charge)`` est decroissante : 2 sous
    charge forte, 0 sous inoculation totale. Le **diagnostic haut niveau**
    de P0/P1 d'#5104."""
    rewards = _rampe_recompenses(sym_max=1.5, n_up=60)
    sig = inoculation_signature(
        transgression=2.0,
        rewards=rewards,
        charges=(0.0, 0.3, 0.6, 0.9),
    )
    n_cat_by_charge = [sig[c]["n_catastrophes"] for c in sorted(sig)]
    # 0 sous inoculation totale, >=1 sous forte charge.
    assert n_cat_by_charge[0] == 0.0
    assert n_cat_by_charge[-1] >= 1.0
    # Monotone non-croissant.
    for i in range(len(n_cat_by_charge) - 1):
        assert n_cat_by_charge[i + 1] >= n_cat_by_charge[i], n_cat_by_charge


# --------------------------------------------------------------------------- #
#  T2 -- banc d'anticipation (#26945) : rampe, residu a la branche, nuls AAFT   #
#                                                                              #
#  Le protocole est scelle dans docs/ict/ict23-anticipation-pre-enregistrement  #
#  .md (commit anterieur au module). Ces tests verifient l'INSTRUMENT, pas un   #
#  resultat : aucun d'eux ne porte de verdict sur P-A1/P-A2.                   #
# --------------------------------------------------------------------------- #

# Facteurs du protocole : a = -2.0 * 0.6 = -1.2, pli a b_c = 0.5059644.
_A_FOLD = -1.2
_B_C = 0.5059644256269406


def test_stable_branch_is_exact_and_stable():
    """La branche rendue est un zero de V' et un minimum (V'' > 0)."""
    for b in (0.44596, 0.48, 0.50, 0.50396):
        p = persona_stable_branch(_A_FOLD, b, p_hint=1.0)
        residu = p ** 3 + _A_FOLD * p + b
        assert abs(residu) < 1e-9, f"b={b} residu={residu:.3e}"
        assert 3.0 * p * p + _A_FOLD > 0.0, f"b={b} n'est pas un minimum"
        stable_pos = [x for x, ok in cat.cusp_equilibria(_A_FOLD, b) if ok and x > 0.0]
        assert stable_pos, f"b={b} devrait avoir une racine stable positive"
        assert abs(p - max(stable_pos)) < 1e-6, (b, p, stable_pos)


def test_stable_branch_null_arm_is_unique_and_positive():
    """a > 0 : une seule racine reelle, et la branche decroit avec b."""
    bs = np.linspace(-0.524, -0.444, 500)
    ps = persona_branch_along(bs, 0.4)
    assert np.all(ps > 0.0), f"branche du nul non positive : min={ps.min():.4f}"
    # dp*/db = -1/(3 p*^2 + a) < 0 : la branche descend quand b monte.
    assert np.all(np.diff(ps) < 0.0)
    for b, p in zip(bs[::50], ps[::50]):
        assert abs(p ** 3 + 0.4 * p + b) < 1e-9
        assert len(cat.cusp_equilibria(0.4, b)) == 1, f"b={b} devrait etre monostable"


def test_ramp_constant_b_reproduces_persona_sde():
    """Rampe a b constant == banc stationnaire : meme tirage, meme trajectoire.

    C'est le test anti-regression du chemin partage : si ``persona_ramp_sde``
    changeait l'ordre des tirages ou la convention de reflexion, ``persona_sde``
    (deja utilisee par les cellules du carnet) changerait de resultat sans que
    rien ne le signale.
    """
    ps_ramp, bs = persona_ramp_sde(2.0, 0.6, 0.4, 0.4, 0.8, 0.05, 0.01, 2000, 7)
    ps_sde = persona_sde(2.0, 0.6, 0.4, 0.8, 0.05, 0.01, 2000, 7)
    assert np.array_equal(bs, np.full(2000, 0.4))
    assert np.allclose(ps_ramp, ps_sde, rtol=0.0, atol=1e-12)


def test_ramp_crosses_the_fold_at_the_analytic_index():
    """``t_cross`` est l'indice exact ou la rampe franchit ``b_c``."""
    ps, bs = persona_ramp_sde(
        2.0, 0.6, 0.44596, 0.52596, 0.804, 0.05, 0.01, 67000, 1000
    )
    t_cross = int(np.argmax(bs >= _B_C))
    assert bs[t_cross - 1] < _B_C <= bs[t_cross]
    # 0.44596 -> 0.52596 sur 67 000 pas : le franchissement tombe vers 50 254.
    assert abs(t_cross - 50254) <= 5, t_cross
    seg = ramp_ews_segment(ps, bs, 2.0, 0.6)
    assert seg["t_cross"] == t_cross


def test_lead_time_removes_every_sample_at_or_after_t_cut():
    """Aucune fenetre ne franchit ``t_cut = min(t_cross, t_jump) - lead_steps``."""
    ps, bs = persona_ramp_sde(
        2.0, 0.6, 0.44596, 0.52596, 0.804, 0.05, 0.01, 67000, 1000
    )
    seg = ramp_ews_segment(ps, bs, 2.0, 0.6)
    assert not seg["excluded"]
    t_cut = int(seg["t_cut"])
    assert t_cut <= min(int(seg["t_cross"]), int(seg["t_jump"])) - 1000
    # Les fenetres sont comptees sur ``resid[:t_cut:thin]`` uniquement.
    n_thin = len(np.arange(0, t_cut)[::10])
    assert int(seg["n_windows"]) == n_thin - 100 + 1, (
        seg["n_windows"], n_thin
    )


def test_ramp_ews_segment_excludes_too_short_a_segment():
    """Garde de faisabilite : t_cut < min_steps => excluded, aucune statistique."""
    n = 3000
    ps = np.ones(n)
    bs = np.linspace(0.0, 0.4, n)  # ne franchit jamais b_c, ne saute jamais
    seg = ramp_ews_segment(ps, bs, 2.0, 0.6)
    assert seg["excluded"] is True
    assert seg["t_jump"] is None
    assert np.isnan(seg["tau_var"]) and np.isnan(seg["tau_ar1"])
    assert int(seg["n_windows"]) == 0


def test_first_sustained_below_respects_the_hold():
    """Excursion sous le seuil : premier indice d'une duree >= ``hold``."""
    x = np.array([1.0, 1.0, 0.1, 0.1, 0.1, 1.0, 0.1, 0.1, 0.1, 0.1])
    assert _first_sustained_below(x, 0.15, 3) == 2
    assert _first_sustained_below(x, 0.15, 4) == 6
    assert _first_sustained_below(x, 0.15, 5) is None
    assert _first_sustained_below(x, 0.15, 0) is None
    assert _first_sustained_below(np.array([0.0]), 0.15, 2) is None


def test_aaft_preserves_distribution_and_amplitude_spectrum():
    """Le nul 2 garde la distribution ET le spectre : il ne detruit que l'ordre."""
    g = np.random.default_rng(0)
    x = np.cumsum(g.standard_normal(2000))  # marche aleatoire, comme le residu
    surr = aaft_surrogate(x, 5, 3)
    assert surr.shape == (5, 2000)
    for row in surr:
        assert np.allclose(np.sort(row), np.sort(x))
        assert abs(row.mean() - x.mean()) < 1e-9
        amp_x = np.abs(np.fft.rfft(x))
        amp_s = np.abs(np.fft.rfft(row))
        assert np.corrcoef(amp_x, amp_s)[0, 1] > 0.9


def test_surrogate_band_is_informative_on_white_noise():
    """Sur un bruit blanc, la bande AAFT est serree (instrument informatif)."""
    g = np.random.default_rng(1)
    band = surrogate_tau_band(g.standard_normal(20000), window=50,
                              n_surrogates=20, seed=2)
    assert band["informative"] is True
    assert band["median_abs_tau_var"] < 0.5
    assert np.isfinite(band["band_var"]) and np.isfinite(band["band_ar1"])
    assert band["tau_var"].shape == (20,)


def test_loop_tipping_points_width_matches_two_bc():
    """Largeur d'hysteresis mesuree ~ 2 b_c (le deterministe doit coller au cusp)."""
    out = loop_tipping_points(2.0, 0.6, n_points=201, relax_steps=2000)
    assert out["ok"] is True, out["jumps"]
    assert out["b_up"] > 0.0 > out["b_down"]
    assert abs(out["width"] - 2.0 * _B_C) / (2.0 * _B_C) < 0.15, out["width"]


def test_instrument_sees_a_built_in_variance_rise():
    """Controle positif de puissance : un sigma x3 rend un tau_var net > 0.5.

    Si ce test tombe, P-A1 est hors de portee de l'instrument et la tranche
    doit le dire avant de lire le bras pli (regle « controles d'abord »).
    """
    g = np.random.default_rng(0)
    n = 20000
    x = g.standard_normal(n) * np.linspace(1.0, 3.0, n)
    var = ews.rolling_variance(x[::10], 100)
    tau, _ = ews.kendall_tau(np.arange(var.shape[0], dtype=float), var)
    assert tau > 0.5, f"tau_var={tau:.3f} sur une hausse construite"


def test_t_cut_override_pairs_the_null_to_the_fold_length():
    """Le nul N1 est tronque a la longueur exacte du bras pli (appariement)."""
    n = 24000
    ps = np.ones(n)                      # aucun saut : t_cross = n
    bs = np.linspace(0.0, 0.4, n)        # ne franchit jamais b_c
    ref = ramp_ews_segment(ps, bs, 2.0, 0.6, min_steps=1000)
    assert int(ref["t_cut"]) == n - 1000
    pair = ramp_ews_segment(ps, bs, 2.0, 0.6, min_steps=1000,
                            t_cut_override=20000)
    assert int(pair["t_cut"]) == 20000
    n_thin = len(np.arange(0, 20000)[::10])
    assert int(pair["n_windows"]) == n_thin - 100 + 1
    assert pair["excluded"] is False


def _load_runner():
    """Charge ``scripts/ict23_anticipation.py`` par chemin (ce n'est pas un package)."""
    import importlib.util
    from pathlib import Path

    path = Path(__file__).resolve().parents[1] / "scripts" / "ict23_anticipation.py"
    spec = importlib.util.spec_from_file_location("ict23_anticipation_runner", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_compute_verdict_reads_clause_b_in_the_sealed_direction():
    """(B) tombe si la largeur >= 5 % de 2 b_c : tombe => HYSTERESIS CONFIRMEE.

    Sens scelle : la clause d'affaiblissement « les points coincident » est
    **tombee** quand le lacet est large. Ce test epingle la polarite du
    drapeau, qui etait inversee dans le premier passage du runner (le verdict
    sortait juste par double inversion, le drapeau consigne etait faux).
    """
    runner = _load_runner()
    green = {
        "C+var": {"green": True, "all_informative": True},
        "C0": {"green": True, "all_informative": True},
        "C+ar1": {"green": True, "all_informative": True},
        "C-lacet": {"green": True},
    }
    fold = [{"excluded": False, "informative": True}]
    base = {
        "P_A1": {"held": False},
        "P_A2": {"held": False},
        "P_A3": {"held": False},
    }

    wide = runner.compute_verdict(green, fold, dict(base, P_B={"clause_B_fallen": True}))
    assert wide["anticipation"] == "ANTICIPATION REFUTEE"
    assert wide["hysteresis"] == "HYSTERESIS CONFIRMEE"

    narrow = runner.compute_verdict(green, fold, dict(base, P_B={"clause_B_fallen": False}))
    assert narrow["hysteresis"] == "HYSTERESIS REFUTEE"

    # Lacet sans deux sauts : aucun des deux verdicts scelles n'est lisible.
    unknown = runner.compute_verdict(green, fold, dict(base, P_B={"clause_B_fallen": None}))
    assert unknown["hysteresis"].startswith("HORS DES CASES SCELLEES")

    # Un controle rouge prime sur tout resultat de fond.
    red = dict(green, C0={"green": False, "all_informative": True})
    blind = runner.compute_verdict(red, fold, dict(base, P_B={"clause_B_fallen": True}))
    assert blind["anticipation"] == "INSTRUMENT NON INFORMATIF"