"""Tests unitaires de ``ict.meta_proxy`` (ICT #7395, c.752).

Couvre les trois fonctions publiques du module :

* :func:`proxy_signature` -- validation des composantes, robustesse
  aux trajectoires courtes, rejet des entrees invalides.
* :func:`obstruction_vector` -- identite (sig_a == sig_b -> vecteur
  nul), antisymetrie approximative (swap de signe), insensibilite a
  l'echelle, tolerance NaN/Inf.
* :func:`cross_substrat_obstruction` -- verdict ``STABLE`` quand les
  substrats ont meme signature, verdict ``NOISE`` quand ils divergent
  fortement, ``INCONCLUSIVE`` en zone grise, rejet si < 2 substrats.

Methodologie : proxys mockes (callables deterministes) ; pas d'appel
aux ``ict.spectral`` / ``ict.sensitivity`` reels -- on reserve ces
derniers aux notebooks (test integration, Papermill execute).
"""

from __future__ import annotations

import math

import numpy as np
import pytest

from ict.meta_proxy import (
    ProxyFn,
    cross_substrat_obstruction,
    obstruction_vector,
    proxy_signature,
)


# --------------------------------------------------------------------------- #
#  Helpers                                                                     #
# --------------------------------------------------------------------------- #
def _mock_spectral(states, n_symbols):
    """Proxy spectral deterministe : retourne la moitie de n_symbols."""
    return 0.5 * float(n_symbols)


def _mock_sens_mean(states, n_symbols):
    """Proxy sensitivity moyenne deterministe : 1.5 * log(n_symbols)."""
    return 1.5 * math.log(max(n_symbols, 2))


def _mock_sens_max(states, n_symbols):
    """Proxy sensitivity max deterministe : 3.0 constant."""
    return 3.0


def _mock_spectral_alt(states, n_symbols):
    """Variante : spectral = 0.5 + 0.01*n_symbols (legerement plus grand)."""
    return 0.5 + 0.01 * float(n_symbols)


def _chain(n: int, length: int) -> list:
    return [(i % n) for i in range(length)]


def _signature_a():
    """Signature stable (substrat A) : n_symbols=10."""
    return proxy_signature(
        _chain(10, 200),
        10,
        spectral_fn=_mock_spectral,
        sensitivity_mean_fn=_mock_sens_mean,
        sensitivity_max_fn=_mock_sens_max,
    )


def _signature_b():
    """Signature stable (substrat B) : meme proxys, meme n_symbols."""
    return proxy_signature(
        _chain(10, 200),
        10,
        spectral_fn=_mock_spectral,
        sensitivity_mean_fn=_mock_sens_mean,
        sensitivity_max_fn=_mock_sens_max,
    )


# --------------------------------------------------------------------------- #
#  proxy_signature                                                             #
# --------------------------------------------------------------------------- #
class TestProxySignature:
    """Cas de base + cas limites."""

    def test_basic_fields_present(self):
        sig = _signature_a()
        assert sig["n_states"] == 10
        assert sig["n_transitions"] == 199
        for k in ("spectral_gap", "sensitivity_mean", "sensitivity_max"):
            assert k in sig
            assert isinstance(sig[k], float)
            assert math.isfinite(sig[k])

    def test_deterministic_for_same_input(self):
        sig1 = proxy_signature(
            _chain(8, 100),
            8,
            spectral_fn=_mock_spectral,
            sensitivity_mean_fn=_mock_sens_mean,
            sensitivity_max_fn=_mock_sens_max,
        )
        sig2 = proxy_signature(
            _chain(8, 100),
            8,
            spectral_fn=_mock_spectral,
            sensitivity_mean_fn=_mock_sens_mean,
            sensitivity_max_fn=_mock_sens_max,
        )
        assert sig1 == sig2

    def test_spectral_value_matches_mock(self):
        sig = _signature_a()
        # _mock_spectral(10) = 0.5 * 10 = 5.0
        assert sig["spectral_gap"] == pytest.approx(5.0)

    def test_sensitivity_mean_matches_mock(self):
        sig = _signature_a()
        # 1.5 * log(10) ≈ 3.453
        assert sig["sensitivity_mean"] == pytest.approx(1.5 * math.log(10))

    def test_sensitivity_max_matches_mock(self):
        sig = _signature_a()
        assert sig["sensitivity_max"] == 3.0

    def test_rejects_empty_states(self):
        with pytest.raises(ValueError, match="states vide"):
            proxy_signature(
                [],
                5,
                spectral_fn=_mock_spectral,
                sensitivity_mean_fn=_mock_sens_mean,
                sensitivity_max_fn=_mock_sens_max,
            )

    def test_rejects_single_state_trajectory(self):
        with pytest.raises(ValueError, match="au moins 2 elements"):
            proxy_signature(
                [3],
                5,
                spectral_fn=_mock_spectral,
                sensitivity_mean_fn=_mock_sens_mean,
                sensitivity_max_fn=_mock_sens_max,
            )

    def test_rejects_n_symbols_lt_2(self):
        with pytest.raises(ValueError, match="n_symbols doit etre"):
            proxy_signature(
                _chain(1, 50),
                1,
                spectral_fn=_mock_spectral,
                sensitivity_mean_fn=_mock_sens_mean,
                sensitivity_max_fn=_mock_sens_max,
            )

    def test_uses_alternative_spectral(self):
        """Variation du proxy spectral -> variation de la signature."""
        sig_default = proxy_signature(
            _chain(10, 200),
            10,
            spectral_fn=_mock_spectral,
            sensitivity_mean_fn=_mock_sens_mean,
            sensitivity_max_fn=_mock_sens_max,
        )
        sig_alt = proxy_signature(
            _chain(10, 200),
            10,
            spectral_fn=_mock_spectral_alt,
            sensitivity_mean_fn=_mock_sens_mean,
            sensitivity_max_fn=_mock_sens_max,
        )
        # spectral_gap differe (5.0 vs 0.6)
        assert sig_default["spectral_gap"] == pytest.approx(5.0)
        assert sig_alt["spectral_gap"] == pytest.approx(0.6)
        # Autres proxys inchanges
        assert sig_default["sensitivity_mean"] == sig_alt["sensitivity_mean"]
        assert sig_default["sensitivity_max"] == sig_alt["sensitivity_max"]


# --------------------------------------------------------------------------- #
#  obstruction_vector                                                          #
# --------------------------------------------------------------------------- #
class TestObstructionVector:
    """Identite, antisymetrie, insensibilite a l'echelle, tolerance NaN."""

    def test_identical_signatures_zero_norm(self):
        sig = _signature_a()
        vec = obstruction_vector(sig, sig)
        # Toutes les composantes doivent etre nulles
        for k in ("spectral_gap", "sensitivity_mean", "sensitivity_max"):
            assert vec[k] == pytest.approx(0.0, abs=1e-9)
        assert vec["norm_l2"] == pytest.approx(0.0, abs=1e-9)

    def test_antisymmetry_sign_flip(self):
        sig_a = _signature_a()
        sig_b = _signature_b()
        # On modifie sig_b pour avoir un delta > 0 sur spectral_gap
        sig_b_modif = dict(sig_b)
        sig_b_modif["spectral_gap"] = 8.0
        vec_ab = obstruction_vector(sig_a, sig_b_modif)
        vec_ba = obstruction_vector(sig_b_modif, sig_a)
        # (a - b) vs (b - a) : signes opposes
        assert vec_ab["spectral_gap"] == pytest.approx(-vec_ba["spectral_gap"], abs=1e-9)
        # norm_l2 identique
        assert vec_ab["norm_l2"] == pytest.approx(vec_ba["norm_l2"], abs=1e-9)

    def test_scale_invariance(self):
        """Multiplier les DEUX signatures par le meme facteur ne change pas le vecteur."""
        sig_a = _signature_a()
        sig_b = _signature_b()
        vec_1 = obstruction_vector(sig_a, sig_b)
        # Scale uniforme des deux signatures -> meme delta_norm (le facteur s'elimine)
        sig_a_scaled = {k: (v * 10.0 if isinstance(v, float) else v) for k, v in sig_a.items()}
        sig_b_scaled = {k: (v * 10.0 if isinstance(v, float) else v) for k, v in sig_b.items()}
        vec_2 = obstruction_vector(sig_a_scaled, sig_b_scaled)
        assert vec_2["norm_l2"] == pytest.approx(vec_1["norm_l2"], abs=1e-9)
        for k in ("spectral_gap", "sensitivity_mean", "sensitivity_max"):
            assert vec_2[k] == pytest.approx(vec_1[k], abs=1e-9)

    def test_scale_invariance_breaks_on_asymmetric_scaling(self):
        """Scaler une seule signature -> le vecteur change (anti-pattern)."""
        sig_a = _signature_a()
        sig_b = _signature_b()
        vec_baseline = obstruction_vector(sig_a, sig_b)
        sig_a_scaled = {k: (v * 10.0 if isinstance(v, float) else v) for k, v in sig_a.items()}
        vec_asym = obstruction_vector(sig_a_scaled, sig_b)
        # La norme L2 ne coincide plus -> le scale-asymetrique produit un motif
        assert not math.isclose(vec_asym["norm_l2"], vec_baseline["norm_l2"], abs_tol=1e-6)

    def test_nan_input_is_filtered(self):
        """sig_a contient NaN -> la cle correspondante est filtree a 0."""
        sig_a = _signature_a()
        sig_b = _signature_b()
        sig_a_nan = dict(sig_a)
        sig_a_nan["spectral_gap"] = float("nan")
        vec = obstruction_vector(sig_a_nan, sig_b)
        # spectral_gap compense : (0 - sig_b) / (0 + |sig_b|) = -1.0
        assert vec["spectral_gap"] == pytest.approx(-1.0, abs=1e-6)

    def test_inf_input_is_filtered(self):
        sig_a = _signature_a()
        sig_b = _signature_b()
        sig_b_inf = dict(sig_b)
        sig_b_inf["sensitivity_max"] = float("inf")
        vec = obstruction_vector(sig_a, sig_b_inf)
        # sensitivity_max compense : (sig_a - 0) / (sig_a + 0) = +1.0
        assert vec["sensitivity_max"] == pytest.approx(1.0, abs=1e-6)

    def test_custom_keys_subset(self):
        """Le parametre keys filtre les composantes du vecteur."""
        sig_a = _signature_a()
        sig_b = _signature_b()
        vec = obstruction_vector(sig_a, sig_b, keys=("spectral_gap",))
        assert "spectral_gap" in vec
        assert "sensitivity_mean" not in vec
        assert "sensitivity_max" not in vec
        assert "norm_l2" in vec

    def test_rejects_empty_keys(self):
        with pytest.raises(ValueError, match="keys vide"):
            obstruction_vector(_signature_a(), _signature_b(), keys=())


# --------------------------------------------------------------------------- #
#  cross_substrat_obstruction                                                  #
# --------------------------------------------------------------------------- #
class TestCrossSubstratObstruction:
    """Verdict falsifiable : STABLE / NOISE / INCONCLUSIVE."""

    def test_identical_signatures_stable(self):
        """3 substrats a signature identique -> verdict STABLE."""
        sig = _signature_a()
        subs = {"gray_scott": sig, "axelrod": sig, "grokking": sig}
        out = cross_substrat_obstruction(subs)
        assert out["verdict"] == "STABLE"
        assert out["n_substrats"] == 3
        assert out["mean_norm_l2"] == pytest.approx(0.0, abs=1e-9)
        assert out["max_norm_l2"] == pytest.approx(0.0, abs=1e-9)
        # 3 substrats -> C(3,2) = 3 paires
        assert len(out["pairwise_norms"]) == 3
        assert out["substrats"] == ["gray_scott", "axelrod", "grokking"]

    def test_orthogonal_signatures_noise(self):
        """Substrats tres divergents -> verdict NOISE."""
        sig_a = _signature_a()
        sig_b = _signature_b()
        # sig_b a un spectral_gap enorme vs sig_a
        sig_b_divergent = dict(sig_b)
        sig_b_divergent["spectral_gap"] = 100.0
        sig_b_divergent["sensitivity_mean"] = 100.0
        sig_c_divergent = dict(sig_b_divergent)
        sig_c_divergent["sensitivity_max"] = 100.0
        subs = {"gray_scott": sig_a, "axelrod": sig_b_divergent, "grokking": sig_c_divergent}
        out = cross_substrat_obstruction(subs)
        assert out["verdict"] == "NOISE"
        assert out["mean_norm_l2"] > 0.30

    def test_moderate_divergence_inconclusive(self):
        """Divergence moderee -> INCONCLUSIVE (entre seuils)."""
        sig_a = _signature_a()
        # Variation de 20% sur spectral_gap (5.0 -> 6.0) -> delta_norm
        # = (6 - 5) / (6 + 5) ≈ 0.0909 -> composante > 0.05 (STABLE)
        # mais < 0.30 (NOISE) -> INCONCLUSIVE
        sig_b_modif = dict(sig_a)
        sig_b_modif["spectral_gap"] = 6.0
        subs = {"a": sig_a, "b": sig_b_modif}
        out = cross_substrat_obstruction(subs)
        assert out["verdict"] == "INCONCLUSIVE"
        assert 0.05 < out["mean_norm_l2"] < 0.30

    def test_custom_thresholds(self):
        """Seuils ajustables : STABLE accepte si mean_norm < 0.20."""
        sig_a = _signature_a()
        sig_b_modif = dict(sig_a)
        sig_b_modif["spectral_gap"] = 6.0
        subs = {"a": sig_a, "b": sig_b_modif}
        # Seuils par defaut (0.05/0.30) -> INCONCLUSIVE
        out_default = cross_substrat_obstruction(subs)
        assert out_default["verdict"] == "INCONCLUSIVE"
        # Seuils elargis -> STABLE
        out_loose = cross_substrat_obstruction(
            subs, stable_threshold=0.20, noise_threshold=0.80
        )
        assert out_loose["verdict"] == "STABLE"

    def test_rejects_single_substrat(self):
        with pytest.raises(ValueError, match="necessite"):
            cross_substrat_obstruction({"only": _signature_a()})

    def test_rejects_empty(self):
        with pytest.raises(ValueError, match="necessite"):
            cross_substrat_obstruction({})

    def test_pairwise_count(self):
        """N substrats -> C(N, 2) paires."""
        sig = _signature_a()
        # 4 substrats -> 6 paires
        subs = {f"s{i}": sig for i in range(4)}
        out = cross_substrat_obstruction(subs)
        assert len(out["pairwise_norms"]) == 6
        assert out["n_substrats"] == 4
