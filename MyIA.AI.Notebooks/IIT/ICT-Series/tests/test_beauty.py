"""Tests du module ict.beauty (brin Schmidhuber de la jambe K, See #5090).

Verifient le gate operationnel (evenements de beaute) et le diagnostic de pli.
Trois gates falsifiables sont centraux (sans complaisance) :

* **B1 (decouverte)** : une trajectoire *bruit puis cycle deterministe* produit
  un evenement de beaute au voisinage de la transition -- la compressibilite
  locale chute brutalement quand la regle est decouverte.
* **B2 (bruit iid)** : un bruit iid ne produit **aucun** evenement (les gains
  sont de l'ordre du contrôle iid apparié -> rejetes).
* **B3 (cycle etabli)** : un cycle deterministe *depuis le debut* ne produit
  **aucun** evenement (compressible partout, pas de saut).

Ces gates ont conduit la méthodologie (cf docstring du module) : le préfixe
accumulé ``compression_progress`` est trop grossier (ratio ~1.0 meme a la
transition) et le contrôle par permutation trop faible (preserve la composition
des segments). Le détecteur retenu = fenêtre glissante locale + contrôle iid
apparié + seuil sur le biais du max.

Numpy + pytest, comme les tests existants du package.
"""

import os
import sys
import math

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict import beauty as BTY  # noqa: E402


# --------------------------------------------------------------------------- #
#  Courbe de compressibilite locale                                           #
# --------------------------------------------------------------------------- #


def test_local_compressibility_shape_and_full_windows_only():
    seq = [i % 4 for i in range(100)]
    steps, K = BTY.local_compressibility(seq, window=24)
    # fenetres pleines uniquement : steps de 24 a 100
    assert steps[0] == pytest.approx(24)
    assert steps[-1] == pytest.approx(100)
    assert steps.shape == K.shape
    assert np.all(K > 0)


def test_local_compressibility_rejects_bad_window():
    with pytest.raises(ValueError):
        BTY.local_compressibility([0, 1, 2], window=0)


def test_local_compressibility_cycle_lower_than_noise():
    # un cycle deterministe est plus compressible qu'un bruit iid local
    rng = np.random.default_rng(0)
    noise = list(rng.integers(0, 4, size=60))
    cycle = [i % 4 for i in range(60)]
    _, Kn = BTY.local_compressibility(noise, window=24)
    _, Kc = BTY.local_compressibility(cycle, window=24)
    assert Kc.mean() < Kn.mean()


def test_smooth_curve_valid_mode_shrinks_output():
    a = np.arange(20, dtype=float)
    s = BTY.smooth_curve(a, half=3)
    assert s.size == a.size - 2 * 3


def test_smooth_curve_passthrough_on_short_input():
    a = np.arange(4, dtype=float)
    s = BTY.smooth_curve(a, half=3)  # trop court pour la fenetre
    assert s.size == a.size


# --------------------------------------------------------------------------- #
#  Forme des sorties du gate operationnel                                     #
# --------------------------------------------------------------------------- #


def test_beauty_events_keys_and_types():
    rng = np.random.default_rng(7)
    seq = list(rng.integers(0, 4, size=400))
    rep = BTY.beauty_events(seq, window=60, horizon=40, n_control=10, rng=rng)
    assert set(rep) >= {
        "events", "steps", "gain", "control_mean", "control_std",
        "threshold", "n_control", "k", "n_events", "verdict",
    }
    assert rep["n_control"] == 10
    assert rep["verdict"] in ("beauty", "flat")
    assert rep["n_events"] == len(rep["events"])
    assert rep["threshold"] == pytest.approx(
        rep["control_mean"] + rep["k"] * rep["control_std"]
    )


# --------------------------------------------------------------------------- #
#  Gate B1 : une vraie decouverte produit un evenement                        #
# --------------------------------------------------------------------------- #


def test_b1_discovery_transition_produces_event():
    # Premiere moitie : bruit iid (incompressible). Seconde moitie : cycle 4
    # deterministe (tres compressible). La transition est le moment ou la
    # compressibilite locale chute brutalement -> evenement de beaute.
    rng_noise = np.random.default_rng(11)
    n_noise, n_cycle = 400, 400
    noise = list(rng_noise.integers(0, 4, size=n_noise))
    cycle = [i % 4 for i in range(n_cycle)]
    seq = noise + cycle

    rep = BTY.beauty_events(seq, window=60, horizon=40, n_control=20,
                            rng=np.random.default_rng(1))
    assert rep["n_events"] >= 1, "une transition decouverte doit produire >=1 evenement"
    # L'evenement doit tomber apres le debut de la phase cycle (>= n_noise).
    first_step = rep["events"][0][0]
    assert first_step >= n_noise, f"evenement attendu en phase cycle, recu step={first_step}"


# --------------------------------------------------------------------------- #
#  Gate B2 : un bruit iid ne produit rien                                     #
# --------------------------------------------------------------------------- #


def test_b2_iid_noise_is_flat():
    rng = np.random.default_rng(23)
    noise = list(rng.integers(0, 4, size=800))
    rep = BTY.beauty_events(noise, window=60, horizon=40, n_control=20,
                            rng=np.random.default_rng(1))
    assert rep["n_events"] == 0
    assert rep["verdict"] == "flat"


# --------------------------------------------------------------------------- #
#  Gate B3 : un cycle etabli depuis le debut ne chute pas                     #
# --------------------------------------------------------------------------- #


def test_b3_pure_cycle_from_start_is_flat():
    cycle = [i % 4 for i in range(800)]
    rep = BTY.beauty_events(cycle, window=60, horizon=40, n_control=20,
                            rng=np.random.default_rng(1))
    assert rep["n_events"] == 0
    assert rep["verdict"] == "flat"


# --------------------------------------------------------------------------- #
#  Reproductibilite                                                           #
# --------------------------------------------------------------------------- #


def test_beauty_events_reproducible_with_fixed_rng():
    rng_a = np.random.default_rng(42)
    rng_b = np.random.default_rng(42)
    seq = list(np.random.default_rng(0).integers(0, 4, size=400)) + [i % 4 for i in range(400)]
    a = BTY.beauty_events(seq, window=60, horizon=40, n_control=10, rng=rng_a)
    b = BTY.beauty_events(seq, window=60, horizon=40, n_control=10, rng=rng_b)
    assert a["events"] == b["events"]
    assert a["control_mean"] == pytest.approx(b["control_mean"])


# --------------------------------------------------------------------------- #
#  Diagnostic de pli (overlay Thom)                                           #
# --------------------------------------------------------------------------- #


def test_fold_in_compressibility_curve_returns_dict_with_fold_step_key():
    steps = np.arange(24, 124, dtype=float)
    K = np.concatenate([
        np.full(40, 28.0), np.linspace(28.0, 14.0, 20), np.full(40, 14.0),
    ])
    rep = BTY.fold_in_compressibility_curve(steps, K, smooth=3)
    assert "fold_step" in rep and "curvature" in rep and "smooth" in rep


def test_fold_in_compressibility_curve_short_curve_returns_none():
    rep = BTY.fold_in_compressibility_curve(
        np.array([24.0, 25.0, 26.0]), np.array([20.0, 19.0, 18.0]), smooth=3
    )
    assert rep["fold_step"] is None


def test_diagnose_couples_gate_and_fold():
    rng = np.random.default_rng(5)
    seq = list(rng.integers(0, 4, size=300)) + [i % 4 for i in range(300)]
    rep = BTY.diagnose(seq, window=60, horizon=40, n_control=10,
                       rng=np.random.default_rng(1))
    assert "fold" in rep and "events" in rep
    assert set(rep["fold"]) >= {"fold_step", "curvature", "smooth"}


# =========================================================================== #
#  Couche 2 -- Frontiere MDL (Levin / PowerPlay / Speed Prior), See #7258      #
# =========================================================================== #
#
# La couche 2 formalise en MDL le compression-progress de Schmidhuber (la
# beaute de la couche 1 etait empirique / zlib). Trois machineries :
#
#   - complexite de Levin ``Kt`` + Speed Prior ``2^{-Kt}`` (deterministe) ;
#   - frontiere PowerPlay (compression-progress monotone, sans abandon) ;
#   - frontiere MDL ``mdl_frontier`` + sa derivee ``mdl_compression_progress``
#     (analogue MDL de ``compressibility_gain_curve``).
#
# Gate falsifiable centrale : **B4** -- sur une transition de structure
# veritable (bruit iid -> cycle deterministe), le cycle est nettement moins
# couteux par symbole que le bruit (la machinerie MDL detecte la structure).
# Caveat honnete (cf comments #7258) : ce qui est VRAI pour une transition de
# structure ne l'est PAS pour la string de predictions d'un reseau grokkant --
# la MDL de la string recompense la memorisation. On test donc la machinerie
# sur ce qu'elle mesure correctement, sans sur-claimer le grokking.


# --------------------------------------------------------------------------- #
#  Complexite de Levin + Speed Prior                                          #
# --------------------------------------------------------------------------- #


def test_levin_complexity_formula():
    assert BTY.levin_complexity(10.0, 1024) == pytest.approx(
        10.0 + math.log2(1024)
    )
    # programme de 0 bits s'executant en 1 pas -> Kt = 0
    assert BTY.levin_complexity(0.0, 1) == pytest.approx(0.0)


def test_levin_complexity_rejects_bad_inputs():
    with pytest.raises(ValueError):
        BTY.levin_complexity(-1.0, 10)
    with pytest.raises(ValueError):
        BTY.levin_complexity(10.0, 0)


def test_speed_prior_weight_is_2pow_minus_kt_and_decreases():
    kt = BTY.levin_complexity(8.0, 16.0)
    w = BTY.speed_prior_weight(8.0, 16.0)
    assert w == pytest.approx(2.0 ** (-kt))
    # un programme plus long ou plus lent est moins probable sous Speed Prior
    assert w > BTY.speed_prior_weight(10.0, 16.0)
    assert w > BTY.speed_prior_weight(8.0, 256.0)


# --------------------------------------------------------------------------- #
#  Frontiere PowerPlay                                                        #
# --------------------------------------------------------------------------- #


def test_powerplay_frontier_accepts_monotonic_growth():
    # chaque theorie resout tout ce que la precedente resolait + une nouvelle
    theories = [(100, {"A"}), (90, {"A", "B"}), (85, {"A", "B", "C"})]
    rep = BTY.powerplay_frontier(theories)
    assert rep["total_accepted"] == 3
    assert rep["rejected"] == []
    # cumulative_solved croit de 1 en 1
    assert [f["cumulative_solved"] for f in rep["frontier"]] == [1, 2, 3]
    assert [f["new"] for f in rep["frontier"]] == [1, 1, 1]


def test_powerplay_frontier_rejects_dropped_task():
    # la 2e theorie perd la tache B -> rejetee (strict, sans abandon)
    theories = [(100, {"A", "B"}), (50, {"A"})]
    rep = BTY.powerplay_frontier(theories)
    assert rep["total_accepted"] == 1
    assert rep["rejected"][0]["index"] == 1
    assert rep["rejected"][0]["reason"] == "dropped_existing"


def test_powerplay_frontier_rejects_no_new_task():
    # la 2e theorie resout exactement la meme chose -> rejetee (pas de progres)
    theories = [(100, {"A"}), (90, {"A"})]
    rep = BTY.powerplay_frontier(theories)
    assert rep["total_accepted"] == 1
    assert rep["rejected"][0]["reason"] == "no_new"


# --------------------------------------------------------------------------- #
#  Frontiere MDL + compression-progress                                       #
# --------------------------------------------------------------------------- #


def test_mdl_frontier_returns_rows_with_keys():
    seq = [i % 4 for i in range(200)]
    rep = BTY.mdl_frontier(seq, n_points=5)
    assert "rows" in rep and len(rep["rows"]) >= 1
    r0 = rep["rows"][0]
    assert set(r0) >= {"L", "model_bits", "residual_bits",
                       "total_bits", "bits_per_symbol"}
    assert r0["bits_per_symbol"] == pytest.approx(r0["total_bits"] / r0["L"])


def test_mdl_frontier_rejects_short_sequence():
    with pytest.raises(ValueError):
        BTY.mdl_frontier([0])


def test_b4_mdl_frontier_cycle_lower_bps_than_noise():
    # Gate B4 (falsifiable) : la machinerie MDL detecte la structure -- un
    # cycle deterministe est nettement moins couteux par symbole qu'un bruit
    # iid. C'est l'analogue MDL de B1 (couche 1).
    #
    # Caveat grokking (cf comments #7258) : ce QUI EST VRAI pour une transition
    # de structure ne l'est PAS pour la string de predictions d'un reseau
    # grokkant (la MDL de la string recompense la memorisation). On test donc
    # la machinerie sur ce qu'elle mesure correctement.
    rng = np.random.default_rng(0)
    noise = list(rng.integers(0, 4, size=400))
    cycle = [i % 4 for i in range(400)]
    fn = BTY.mdl_frontier(noise, n_points=5)["rows"]
    fc = BTY.mdl_frontier(cycle, n_points=5)["rows"]
    bps_noise = float(np.mean([r["bits_per_symbol"] for r in fn]))
    bps_cycle = float(np.mean([r["bits_per_symbol"] for r in fc]))
    assert bps_cycle < bps_noise, (
        f"le cycle devrait etre moins couteux que le bruit, "
        f"recu cycle={bps_cycle:.3f} noise={bps_noise:.3f}"
    )


def test_mdl_compression_progress_returns_delta_and_max():
    rng = np.random.default_rng(1)
    seq = list(rng.integers(0, 4, size=300)) + [i % 4 for i in range(300)]
    rep = BTY.mdl_compression_progress(seq, n_points=8, horizon=2)
    assert set(rep) >= {"rows", "max_progress", "argmax_L"}
    deltas = [r["delta"] for r in rep["rows"]]
    # les `horizon` premiers points sont nan, les suivants finis
    assert np.isnan(deltas[0]) and np.isnan(deltas[1])
    assert np.all(np.isfinite(deltas[2:]))
    assert rep["argmax_L"] is not None


def test_mdl_compression_progress_rejects_bad_horizon():
    with pytest.raises(ValueError):
        BTY.mdl_compression_progress([i % 4 for i in range(20)], horizon=0)
