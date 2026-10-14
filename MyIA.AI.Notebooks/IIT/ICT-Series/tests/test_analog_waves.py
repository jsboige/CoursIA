"""Tests du monde jouet cognition analogique par ondes (module ICT-40).

Verifient les proprietes structurelles des quatre mecanismes distilles du
preprint Miller-Brincat-Roy 2026 : gating ephaptique par phase, stencil
Spatial Computing et selectivite mixte emergente, calcul analogique par
superposition (temoin analytique exact), transition de sous-espace par
onde voyageuse, effondrement de coherence inter-regionale en regime
anesthesique. Determinisme par graine.

Numpy + scipy + pytest."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ict.analog_waves import (  # noqa: E402
    combine,
    express,
    make_grid,
    mixed_selectivity_index,
    modulation_depth,
    object_weight_maps,
    pattern_distance_matrix,
    phase_locking_value,
    principal_angle,
    regional_fields,
    spike_phase_tuning,
    stencil_from_wave,
    sum_amplitude_vs_phase,
    traveling_stencil,
    wave_field,
)


# ---------------------------------------------------------------------------
# 1. Gating ephaptique par phase
# ---------------------------------------------------------------------------

class TestSpikePhaseTuning:

    def test_champ_fort_module_le_tir(self):
        _, rate = spike_phase_tuning(field_amp=0.8, seed=0)
        assert modulation_depth(rate) > 0.3

    def test_champ_faible_presque_plat(self):
        _, rate = spike_phase_tuning(field_amp=0.01, n_trials=200_000, seed=0)
        assert modulation_depth(rate) < 0.05

    def test_pic_dans_la_phase_excicatrice(self):
        """Le cosinus ajoute du potentiel : le taux max doit tomber pres de phi=0."""
        centers, rate = spike_phase_tuning(field_amp=0.8, seed=0)
        peak = centers[np.argmax(rate)]
        assert min(abs(peak), abs(peak - 2 * np.pi)) < 2 * np.pi / 12

    def test_determinisme(self):
        a = spike_phase_tuning(0.5, seed=7)[1]
        b = spike_phase_tuning(0.5, seed=7)[1]
        np.testing.assert_array_equal(a, b)


# ---------------------------------------------------------------------------
# 2. Spatial Computing : stencil et selectivite mixte
# ---------------------------------------------------------------------------

class TestStencilAndMixedSelectivity:

    def setup_method(self):
        self.x, self.y = make_grid(24, 48)
        self.weights = object_weight_maps(24, 48, 2, corr_len=4.0, seed=1)
        self.stencil_a = stencil_from_wave(self.x, self.y, 0.3, 0.0)
        self.stencil_b = stencil_from_wave(self.x, self.y, 1.2, np.pi / 2)

    def test_stencil_dans_unit_interval(self):
        for s in (self.stencil_a, self.stencil_b):
            assert s.min() >= 0.0 and s.max() <= 1.0

    def test_suppression_reduit_l_expression(self):
        obj = np.array([1.0, 0.0])
        free = express(self.weights, obj, np.zeros_like(self.stencil_a), noise=0.0)
        gated = express(self.weights, obj, self.stencil_a, noise=0.0)
        assert gated.sum() <= free.sum()
        assert (gated <= free + 1e-12).all()

    def test_stencils_differents_mixed_selectite_emergente(self):
        """Deux contextes (stencils) : des voxels changent de preference d'objet."""
        objects = np.eye(2)
        resp_a = np.stack([express(self.weights, o, self.stencil_a) for o in objects])
        resp_b = np.stack([express(self.weights, o, self.stencil_b) for o in objects])
        msi = mixed_selectivity_index(np.stack([resp_a, resp_b]))
        assert msi > 0.05

    def test_meme_stencil_pas_de_mixite(self):
        """Contexte identique : la preference ne peut pas changer (poids fixes)."""
        objects = np.eye(2)
        resp_a = np.stack([express(self.weights, o, self.stencil_a) for o in objects])
        resp_a2 = np.stack([express(self.weights, o, self.stencil_a) for o in objects])
        assert mixed_selectivity_index(np.stack([resp_a, resp_a2])) == 0.0


# ---------------------------------------------------------------------------
# 3. Calcul analogique : superposition
# ---------------------------------------------------------------------------

class TestAnalogSuperposition:

    def test_temoin_analytique_fig6(self):
        """Somme de deux sinus : amplitude 2|cos(dphi/2)| exacte a la tolerance pres."""
        for dphi in np.linspace(0.0, np.pi, 7):
            t = np.linspace(0.0, 3.0, 3000)
            s = np.sin(2 * np.pi * t) + np.sin(2 * np.pi * t + dphi)
            measured = (s.max() - s.min()) / 2.0
            assert measured == pytest.approx(sum_amplitude_vs_phase(dphi), rel=1e-3)

    def test_quatre_combinaisons_distinguees(self):
        """Somme de deux ondes de contexte : 4 patrons bien separes (Fig. 7)."""
        x, y = make_grid(24, 48)
        waves_order = [wave_field(x, y, 0.4, p) for p in (0.0, np.pi)]
        waves_mode = [wave_field(x, y, 1.5, p) for p in (0.0, np.pi)]
        combos = [combine(o, m) for o in waves_order for m in waves_mode]
        dist = pattern_distance_matrix(np.stack(combos))
        off = dist[~np.eye(4, dtype=bool)]
        assert off.min() > 0.05

    def test_leffett_dun_contexte_depend_de_lautre(self):
        """Stencils rectifies : l'effet du mode sur le patron somme depend
        du contexte d'ordre — mixite non lineaire de la superposition,
        la signature du calcul analogique de la Fig. 7."""
        from ict.analog_waves import stencil_from_wave as sfw

        x, y = make_grid(24, 48)
        s_order = [sfw(x, y, 0.4, p) for p in (0.0, np.pi)]
        s_mode = [sfw(x, y, 1.5, p) for p in (0.0, np.pi)]
        combos = [o + m for o in s_order for m in s_mode]
        d = pattern_distance_matrix(np.stack(combos))
        # l'ecart induit par le mode n'est pas le meme selon l'ordre.
        # Valeur mesuree ~0.016 : effet reel mais modeste a egalite des
        # longueurs d'onde (la somme est lineaire ; seule la rectification
        # clip du stencil rend l'interaction non lineaire) — le notebook
        # rapporte la valeur honnetement.
        assert abs(d[0, 1] - d[2, 3]) > 0.01
        # et les quatre combinaisons restent toutes distinctes
        assert d[~np.eye(4, dtype=bool)].min() > 0.02


# ---------------------------------------------------------------------------
# 4. Onde voyageuse : transition de sous-espace
# ---------------------------------------------------------------------------

class TestTravelingWaveTransition:

    def setup_method(self):
        self.x, self.y = make_grid(24, 48)
        self.pat_from = stencil_from_wave(self.x, self.y, 0.2, 0.0)
        self.pat_to = stencil_from_wave(self.x, self.y, 1.4, np.pi / 2)
        self.weights = object_weight_maps(24, 48, 2, corr_len=4.0, seed=1)

    def test_le_front_interpole_monotonement(self):
        mid = traveling_stencil(self.x, self.y, 0.55, pattern_from=self.pat_from,
                                pattern_to=self.pat_to)
        before = traveling_stencil(self.x, self.y, 0.0, pattern_from=self.pat_from,
                                   pattern_to=self.pat_to)
        after = traveling_stencil(self.x, self.y, 1.4, pattern_from=self.pat_from,
                                  pattern_to=self.pat_to)
        d0 = np.linalg.norm(before - self.pat_to)
        dm = np.linalg.norm(mid - self.pat_to)
        d1 = np.linalg.norm(after - self.pat_to)
        assert d0 > dm > d1

    def test_transition_de_sous_espace_mesurable(self):
        """Les deux stencils cibles definissent des sous-espaces de codage
        partiellement orthogonaux : angle strictement entre 15 et 90 degres.

        L'angle doit se mesurer sur le SIGNAL (patterns sans bruit), pas sur
        des nuages d'echantillons bruites : cf test_langle_nuage_bruite_sature.
        """
        mixtures = np.array(
            [[1.0, 0.0], [0.75, 0.25], [0.5, 0.5], [0.25, 0.75], [0.0, 1.0]]
        )
        sub_from = np.stack(
            [express(self.weights, m, self.pat_from, noise=0.0).ravel() for m in mixtures]
        )
        sub_to = np.stack(
            [express(self.weights, m, self.pat_to, noise=0.0).ravel() for m in mixtures]
        )
        angle = principal_angle(sub_from, sub_to)
        assert 15.0 < angle < 90.0

    def test_le_balayage_emporte_la_reponse(self):
        """Sans bruit, la distance cosinus au point de depart croit
        strictement le long du balayage."""
        obj = np.array([1.0, 0.4])
        reps = []
        for t in np.linspace(0.0, 1.4, 25):
            st = traveling_stencil(self.x, self.y, t, pattern_from=self.pat_from,
                                   pattern_to=self.pat_to)
            reps.append(express(self.weights, obj, st, noise=0.0).ravel())
        reps = np.stack(reps)
        unit = reps / np.linalg.norm(reps, axis=1, keepdims=True)
        d = 1.0 - unit @ unit[0]
        assert d[6] < d[12] < d[-1]

    def test_angle_nul_pour_meme_nuage(self):
        rng = np.random.default_rng(0)
        cloud = rng.normal(size=(40, 6))
        assert principal_angle(cloud, cloud) < 5.0

    def test_langle_nuage_bruite_sature_par_dimension(self):
        """Garde-fou documente (notebook ICT-40) : deux nuages de bruit
        independants en haute dimension donnent deja ~90 degres — l'angle
        entre nuages bruites n'est PAS une mesure de transition."""
        rng = np.random.default_rng(5)
        a = rng.normal(size=(60, 4608))
        b = rng.normal(size=(60, 4608))
        assert principal_angle(a, b) > 80.0


# ---------------------------------------------------------------------------
# 5. Anesthesie : effondrement de coherence
# ---------------------------------------------------------------------------

class TestAnesthesiaDecoherence:

    def test_regime_organise_fort_plv(self):
        n = 12
        offsets = np.linspace(0.0, 2 * np.pi, n, endpoint=False)
        fields = regional_fields(n_regions=n, freq=10.0, phase_offsets=offsets,
                                 jitter=0.002, seed=3)
        assert phase_locking_value(fields) > 0.8

    def test_regime_anesthesique_plv_effondre(self):
        rng = np.random.default_rng(11)
        offsets = rng.uniform(0.0, 2 * np.pi, 12)
        fields = regional_fields(n_regions=12, freq=2.0, phase_offsets=offsets,
                                 jitter=0.15, amplitude=2.0, seed=4)
        assert phase_locking_value(fields) < 0.5

    def test_leffondrement_est_robuste_au_seed(self):
        rng = np.random.default_rng(21)
        for seed in (5, 6, 7):
            offsets = rng.uniform(0.0, 2 * np.pi, 10)
            fields = regional_fields(n_regions=10, freq=2.0, phase_offsets=offsets,
                                     jitter=0.15, seed=seed)
            assert phase_locking_value(fields) < 0.6
