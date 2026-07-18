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
#  Couche 2 -- Levin / Speed Prior / PowerPlay (estimateur MDL explicite)      #
# =========================================================================== #
#  La couche 1 mesure K via zlib (BRUT, sans modele). La couche 2 la remplace
#  par le code MDL ``two_part_code`` + la ponderation de Levin Kt, et fournit le
#  detecteur ``powerplay_events`` (meme methodologie iid-appariee que
#  ``beauty_events``). Les gates falsifiables C5/C6 sont les duaux MDL de B1/B2.


def test_c1_mdl_curve_shapes_and_full_windows_only():
    seq = [i % 4 for i in range(100)]
    steps, total, model, resid = BTY.mdl_compressibility_curve(seq, window=24)
    assert steps[0] == pytest.approx(24)
    assert steps[-1] == pytest.approx(100)
    assert steps.shape == total.shape == model.shape == resid.shape
    # total_bits peut etre NEGATIF (le terme KT ``-k*log2(k+0.5)`` credite les
    # TPM parcimonieuses : un cycle deterministe -> model_bits tres negatif,
    # residu ~0). On verifie la finite + la coherence model+resid, pas la
    # signe (cf docstring de mdl_compressibility_curve).
    assert np.all(np.isfinite(total))
    assert np.allclose(total, model + resid)


def test_c2_mdl_rejects_small_window():
    with pytest.raises(ValueError):
        BTY.mdl_compressibility_curve([0, 1, 2, 3], window=3)


def test_c3_cycle_lower_mdl_than_noise():
    rng = np.random.default_rng(0)
    noise = list(rng.integers(0, 4, size=60))
    cycle = [i % 4 for i in range(60)]
    _, tn, _, _ = BTY.mdl_compressibility_curve(noise, window=24)
    _, tc, _, _ = BTY.mdl_compressibility_curve(cycle, window=24)
    # un cycle deterministe se code par une TPM de permutation (residu ~0) ->
    # total_bits nettement inferieur au bruit iid.
    assert tc.mean() < tn.mean()


def test_c4_levin_ge_total_and_speed_weight_zero_equals_total():
    seq = [i % 4 for i in range(80)]
    _, total, _, _ = BTY.mdl_compressibility_curve(seq, window=24)
    _, levin1 = BTY.levin_speed_prior_curve(seq, window=24, speed_weight=1.0)
    _, levin0 = BTY.levin_speed_prior_curve(seq, window=24, speed_weight=0.0)
    # Levin = total + speed_weight*log2(n_train) >= total ; weight=0 retombe sur total.
    assert np.all(levin1 >= total - 1e-9)
    assert np.allclose(levin0, total)


def test_c5_mdl_discovery_transition_produces_event():
    # Dual MDL de B1 : bruit iid puis cycle deterministe -> chute brusque du
    # code MDL (residu -> 0 sur le cycle) -> evenement PowerPlay au voisinage
    # de la transition. NB : l'estimateur MDL est plus bruité que zlib sur
    # courtes fenetres (variance d'estimation de la TPM) ; il faut une fenetre
    # plus large (window=80) pour stabiliser le controle iid (verifie
    # empiriquement : a window=40 le pic reel reste sous le seuil iid).
    rng_noise = np.random.default_rng(11)
    n_noise, n_cycle = 400, 400
    noise = list(rng_noise.integers(0, 4, size=n_noise))
    cycle = [i % 4 for i in range(n_cycle)]
    seq = noise + cycle
    rep = BTY.powerplay_events(seq, window=80, horizon=40, n_control=12,
                               rng=np.random.default_rng(1))
    assert rep["n_events"] >= 1, "une transition decouverte doit produire >=1 evenement PowerPlay"
    assert rep["method"] == "mdl"
    first_step = rep["events"][0][0]
    assert first_step >= n_noise, f"evenement attendu en phase cycle, recu step={first_step}"


def test_c6_iid_noise_is_flat():
    # Dual MDL de B2 : un bruit iid ne produit rien (pas de chute systematique
    # du code MDL -> sous le seuil iid). window=80 (cf C5) pour stabiliser.
    rng = np.random.default_rng(23)
    noise = list(rng.integers(0, 4, size=800))
    rep = BTY.powerplay_events(noise, window=80, horizon=40, n_control=12,
                               rng=np.random.default_rng(1))
    assert rep["n_events"] == 0
    assert rep["verdict"] == "flat"


def test_c7_powerplay_keys_and_types():
    rng = np.random.default_rng(7)
    seq = list(rng.integers(0, 4, size=400))
    rep = BTY.powerplay_events(seq, window=40, horizon=25, n_control=8, rng=rng)
    assert set(rep) >= {
        "events", "steps", "gain", "control_mean", "control_std",
        "threshold", "n_control", "k", "n_events", "verdict",
        "method", "speed_weight",
    }
    assert rep["method"] == "mdl"
    assert rep["verdict"] in ("powerplay", "flat")
    assert rep["n_events"] == len(rep["events"])
    assert rep["threshold"] == pytest.approx(
        rep["control_mean"] + rep["k"] * rep["control_std"]
    )


def test_c8_powerplay_reproducible_with_fixed_rng():
    rng_noise = np.random.default_rng(11)
    n_noise, n_cycle = 400, 400
    noise = list(rng_noise.integers(0, 4, size=n_noise))
    seq = noise + [i % 4 for i in range(n_cycle)]
    a = BTY.powerplay_events(seq, window=80, horizon=40, n_control=8,
                             rng=np.random.default_rng(1))
    b = BTY.powerplay_events(seq, window=80, horizon=40, n_control=8,
                             rng=np.random.default_rng(1))
    assert a["events"] == b["events"]
    assert a["control_mean"] == pytest.approx(b["control_mean"])
