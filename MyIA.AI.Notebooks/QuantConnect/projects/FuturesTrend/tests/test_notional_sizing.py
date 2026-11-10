#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Tests CPU pour le dimensionnement des futures au notionnel (#23824).

Couvre `target_contracts` et `contract_delta` de `notional_sizing.py`, la
fonction pure appelée par la branche `fix` de `main_carver13`. Le test ne
requiert pas QC Cloud : il importe uniquement `notional_sizing`.

Le cas central est le multiplicateur : à poids, valeur de portefeuille et
prix égaux, un contrat de multiplicateur 1000 porte mille fois le notionnel
d'un contrat de multiplicateur 1, et la cible en contrats doit être divisée
d'autant. C'est précisément ce que `set_holdings` ne fait pas (il dimensionne
sur la marge initiale).
"""

import os
import sys
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
if _PROJ_ROOT not in sys.path:
    sys.path.insert(0, _PROJ_ROOT)

from notional_sizing import contract_delta, target_contracts  # noqa: E402


class TestTargetContractsMultiplier(unittest.TestCase):
    """La cible en contrats est divisée par le multiplicateur."""

    def test_multiplier_1_50_1000(self):
        """10 % de 2 000 000 à prix 100 : 2000, 40 et 2 contrats."""
        self.assertEqual(target_contracts(0.10, 2_000_000.0, 100.0, 1.0), 2000)
        self.assertEqual(target_contracts(0.10, 2_000_000.0, 100.0, 50.0), 40)
        self.assertEqual(target_contracts(0.10, 2_000_000.0, 100.0, 1000.0), 2)

    def test_notional_matches_target_value(self):
        """Le notionnel des contrats retenus est au plus à un contrat de la cible."""
        cases = [
            (0.25, 2_000_000.0, 4512.25, 50.0),    # indice actions
            (-0.18, 2_000_000.0, 71.43, 1000.0),   # pétrole, côté vendeur
            (0.07, 100_000.0, 112.5, 1000.0),      # obligation, petit compte
        ]
        for weight, tpv, price, mult in cases:
            qty = target_contracts(weight, tpv, price, mult)
            gap = abs(qty * price * mult - weight * tpv)
            self.assertLessEqual(gap, 0.5 * price * mult + 1e-6)

    def test_sign_follows_weight(self):
        """Un poids négatif donne une position vendeuse de même taille."""
        long_qty = target_contracts(0.12, 2_000_000.0, 80.0, 1000.0)
        short_qty = target_contracts(-0.12, 2_000_000.0, 80.0, 1000.0)
        self.assertEqual(long_qty, 3)
        self.assertEqual(short_qty, -3)


class TestTargetContractsRounding(unittest.TestCase):
    """Arrondi au contrat entier le plus proche (demi à pair)."""

    def test_small_account_rounds_to_zero(self):
        """À 100 000, 5 % d'un contrat de 450 000 de notionnel arrondit à 0."""
        self.assertEqual(target_contracts(0.05, 100_000.0, 4500.0, 100.0), 0)

    def test_half_to_even(self):
        """1,5 contrat arrondit à 2, 2,5 à 2, -0,5 à 0 (round de Python)."""
        self.assertEqual(target_contracts(0.15, 1_000.0, 100.0, 1.0), 2)
        self.assertEqual(target_contracts(0.25, 1_000.0, 100.0, 1.0), 2)
        self.assertEqual(target_contracts(-0.05, 1_000.0, 100.0, 1.0), 0)


class TestTargetContractsGuards(unittest.TestCase):
    """Pas de notionnel calculable : aucune position."""

    def test_zero_weight(self):
        self.assertEqual(target_contracts(0.0, 2_000_000.0, 100.0, 50.0), 0)

    def test_price_not_positive(self):
        self.assertEqual(target_contracts(0.10, 2_000_000.0, 0.0, 50.0), 0)
        self.assertEqual(target_contracts(0.10, 2_000_000.0, -1.0, 50.0), 0)

    def test_multiplier_not_positive(self):
        self.assertEqual(target_contracts(0.10, 2_000_000.0, 100.0, 0.0), 0)


class TestContractDelta(unittest.TestCase):
    """Écart à envoyer entre la position détenue et la cible."""

    def test_open_close_and_flip(self):
        self.assertEqual(contract_delta(5, 0.0), 5)
        self.assertEqual(contract_delta(0, 5.0), -5)
        self.assertEqual(contract_delta(-3, 4.0), -7)

    def test_holding_is_rounded_not_truncated(self):
        """Une position lue 2,9999999 compte pour 3 contrats, pas 2."""
        self.assertEqual(contract_delta(3, 2.9999999), 0)
        self.assertEqual(contract_delta(-3, -2.9999999), 0)


if __name__ == "__main__":
    unittest.main()
