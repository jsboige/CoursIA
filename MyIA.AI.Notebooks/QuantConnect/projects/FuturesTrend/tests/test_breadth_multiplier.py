#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Tests CPU exécutables pour le breadth multiplier (Carver #13, REPAIR-8 c.1115).

Couvre les invariants documentés dans `breadth_multiplier` de
`breadth_multiplier.py` (la fonction pure module-level). Le test ne
requiert **pas** QC Cloud : il importe uniquement `breadth_multiplier`
(pur numpy) et exerce la formule livrée.

Pré-requis : `numpy` (>= 1.21). Le runner GH Actions par défaut ne porte
PAS numpy — voir MEMORY `scipy-matplotlib-pip-install-ci-runner.md`.

Tell c.15069 strict filet `delivered` : ce test protège le caractère
sign-invariant que seul une docstring ne protégeait pas avant REPAIR-7
c.1113 (préflight adjoint po-2025 habilité n°3
`msg-20260911T063424-qnc0q9`).

REPAIR-8 c.1115 : avant ce REPAIR, le test dupliquait byte-pour-byte la
formule dans une fonction `_breadth_multiplier_standalone`. Le REPAIR-8
supprime cette duplication et importe directement la fonction de
production depuis `breadth_multiplier.py` (pur numpy, sans dépendance
QCAlgorithm). Tout changement futur qui ferait diverger la formule de
l'invariant doit rougir ici AVANT d'atteindre QC Cloud.
"""

import math
import os
import sys
import unittest

import numpy as np

# Make the FuturesTrend/ package importable without invoking
# `from main_carver13 import *` (which would drag in AlgorithmImports and
# require the QC Cloud runtime).
_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
if _PROJ_ROOT not in sys.path:
    sys.path.insert(0, _PROJ_ROOT)

from breadth_multiplier import breadth_multiplier  # noqa: E402


class TestBreadthMultiplierSignInvariance(unittest.TestCase):
    """Le multiplicateur est sign-invariant : abs() efface le signe."""

    def test_10_10_eq_10_neg10(self):
        """[10, 10] et [10, -10] rendent le meme breadth = sqrt(2)."""
        b_pos = breadth_multiplier([10.0, 10.0])
        b_mix = breadth_multiplier([10.0, -10.0])
        self.assertAlmostEqual(b_pos, b_mix, places=12)
        # Valeur theorique : sum(|f|)/sqrt(sum(f^2)) = 20/sqrt(200) = sqrt(2)
        self.assertAlmostEqual(b_pos, math.sqrt(2.0), places=12)

    def test_signed_book_all_pairs(self):
        """Pour tout [a, b], breadth([a, b]) == breadth([a, -b])."""
        rng = np.random.default_rng(seed=20260911)
        for _ in range(50):
            a, b = rng.uniform(-20, 20, size=2)
            b1 = breadth_multiplier([a, b])
            b2 = breadth_multiplier([a, -b])
            self.assertAlmostEqual(b1, b2, places=10)

    def test_full_book_sign_invariance(self):
        """Pour un livre de 19 forecasts (taille univers Carver), le
        breadth ne depend pas des signes."""
        rng = np.random.default_rng(seed=42)
        f = rng.uniform(-20, 20, size=19)
        b1 = breadth_multiplier(list(f))
        b2 = breadth_multiplier(list(-f))
        self.assertAlmostEqual(b1, b2, places=10)


class TestBreadthMultiplierInverseConcentration(unittest.TestCase):
    """Le multiplicateur mesure une LARGEUR effective (inverse concentration)."""

    def test_single_dominant_minimum_breadth(self):
        """Un seul forecast non nul : breadth = 1.0 (MINIMUM = concentration MAX)."""
        b = breadth_multiplier([10.0, 0.0, 0.0, 0.0])
        self.assertAlmostEqual(b, 1.0, places=12)

    def test_zero_array_returns_baseline(self):
        """Aucun forecast : retour = 1.0 (baseline, pas d'amplification)."""
        self.assertEqual(breadth_multiplier([0.0, 0.0, 0.0]), 1.0)
        self.assertEqual(breadth_multiplier([]), 1.0)

    def test_uniform_4_magnitudes_clipped_to_2(self):
        """4 magnitudes egales : breadth = 2 (clipe au max du clip [1, 2]).

        Formule : sum(|f|)/sqrt(sum(f^2)) = 4*10/sqrt(4*100) = 40/20 = 2.0.
        """
        b = breadth_multiplier([10.0, 10.0, 10.0, 10.0])
        self.assertAlmostEqual(b, 2.0, places=12)

    def test_uniform_19_magnitudes(self):
        """19 magnitudes egales : raw breadth = sqrt(19) ~ 4.36, CLIPE a 2.0.

        C'est precisement ce que dit le clip [1, 2] : le multiplicateur
        n'amplifie JAMAIS au-dela de 2x, meme quand la largeur effective
        est bien superieure. La forme clip est le 'soft cap on gross
        leverage' documente dans `breadth_multiplier`.
        """
        b = breadth_multiplier([10.0] * 19)
        self.assertAlmostEqual(b, 2.0, places=12)
        # Sanity check : la valeur NON clippee serait sqrt(19)
        self.assertGreater(math.sqrt(19), 2.0)

    def test_two_equal_returns_sqrt2(self):
        """2 magnitudes egales : breadth = sqrt(2) (PAS clip, < 2)."""
        b = breadth_multiplier([10.0, 10.0])
        self.assertAlmostEqual(b, math.sqrt(2.0), places=12)


class TestBreadthMultiplierClipBoundaries(unittest.TestCase):
    """Le clip [1, 2] borne le multiplicateur dans les deux directions."""

    def test_clip_lower_bound(self):
        """Une magnitude nulle a cote d'autres : jamais en dessous de 1.0."""
        # 1 dominant parmi 19 : raw = 10/sqrt(100) = 1.0, deja au plancher
        b = breadth_multiplier([10.0] + [0.0] * 18)
        self.assertAlmostEqual(b, 1.0, places=12)

    def test_clip_upper_bound_uniform_3(self):
        """3 magnitudes egales : raw = 3/sqrt(3) = sqrt(3) ~ 1.73 (< 2, pas clip).

        Cas intermediaire : on verifie que le clip NE S'ACTIVE PAS quand
        la largeur effective reste sous 2.
        """
        b = breadth_multiplier([10.0, 10.0, 10.0])
        self.assertAlmostEqual(b, math.sqrt(3.0), places=12)
        self.assertLess(b, 2.0)


class TestBreadthMultiplierPreservesSignInWeight(unittest.TestCase):
    """Le multiplicateur est sign-invariant MAIS le poids final preserve
    le signe via `forecast / abs_sum` (cf. `_rebalance`)."""

    def test_weight_sign_preserved(self):
        """Pour un livre mixte [+a, -b], le signe du poids est preserve
        par la formule poids = signe(forecast) * (|forecast|/abs_sum) * breadth."""
        forecasts = [10.0, -5.0]
        breadth = breadth_multiplier(forecasts)
        abs_sum = sum(abs(v) for v in forecasts)
        weights = [
            (math.copysign(1.0, f)) * (abs(f) / abs_sum) * breadth
            for f in forecasts
        ]
        # Signe preserve
        self.assertGreater(weights[0], 0.0)
        self.assertLess(weights[1], 0.0)
        # breadth applique symetriquement (meme valeur pour les deux) ;
        # on compare le rapport des magnitudes (car le signe est preserve)
        self.assertAlmostEqual(
            abs(weights[0]) / abs(weights[1]),
            (10.0 / 5.0),
            places=10,
        )


if __name__ == "__main__":
    # PYTHONIOENCODING utf-8 (Tell c.1067 strict)
    os.environ.setdefault("PYTHONIOENCODING", "utf-8")
    unittest.main(verbosity=2)
