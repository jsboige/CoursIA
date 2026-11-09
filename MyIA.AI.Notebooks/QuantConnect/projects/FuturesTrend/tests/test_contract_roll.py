#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Tests CPU pour la règle de roulement des futures continus (#23841).

Couvre `roll_orders` et `aggregate_quantity` de `contract_roll.py`, la
fonction pure appelée par la branche `roll` de `main_carver13`. Le test ne
requiert pas QC Cloud : il importe uniquement `contract_roll`.

Le cas central est celui mesuré sur le run `bcf50b4b` : une position courte
de 2 contrats reste sur l'ancien contrat quand le mapping passe au suivant.
Sans roulement, l'algorithme ouvre une seconde position sur le nouveau
contrat ; avec la règle, l'ancienne est fermée et la cible est portée par le
seul contrat mappé.
"""

import os
import sys
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
if _PROJ_ROOT not in sys.path:
    sys.path.insert(0, _PROJ_ROOT)

from contract_roll import aggregate_quantity, roll_orders  # noqa: E402


class TestRollAtMappingChange(unittest.TestCase):
    """Le changement de mapping ferme l'ancien contrat et reporte la cible."""

    def test_short_rolled_to_new_contract(self):
        # Instance mesurée : -2 sur CL19M20, mapping passé à CL22N20, cible -2.
        orders = roll_orders(-2, {"CL19M20": -2.0}, "CL22N20")
        self.assertEqual(orders, [("CL19M20", 2), ("CL22N20", -2)])

    def test_aggregate_equals_target_after_roll(self):
        holdings = {"CL19M20": -2.0}
        orders = roll_orders(-2, holdings, "CL22N20")
        after = dict(holdings)
        for contract, qty in orders:
            after[contract] = after.get(contract, 0) + qty
        self.assertEqual(aggregate_quantity(after), -2)
        self.assertEqual(after["CL19M20"], 0)

    def test_roll_with_resize(self):
        # Long 3 sur l'ancien contrat, cible 5 : fermer 3, ouvrir 5.
        orders = roll_orders(5, {"ESH6": 3.0}, "ESM6")
        self.assertEqual(orders, [("ESH6", -3), ("ESM6", 5)])

    def test_roll_to_flat(self):
        # La cible tombe à 0 au moment du changement : seule la fermeture part.
        orders = roll_orders(0, {"ZNH6": 4.0}, "ZNM6")
        self.assertEqual(orders, [("ZNH6", -4)])

    def test_two_stale_contracts_and_mapped(self):
        # Doublon déjà construit (état du run sans roulement) : on le résorbe.
        holdings = {"CL21K20": 1.0, "CL19M20": -2.0, "CL22N20": -2.0}
        orders = roll_orders(-2, holdings, "CL22N20")
        self.assertEqual(orders, [("CL21K20", -1), ("CL19M20", 2)])


class TestNoRoll(unittest.TestCase):
    """Sans contrat périmé, la règle redonne le delta de `notional_sizing`."""

    def test_only_mapped_held(self):
        self.assertEqual(roll_orders(4, {"GCZ5": 1.0}, "GCZ5"), [("GCZ5", 3)])

    def test_nothing_held(self):
        self.assertEqual(roll_orders(-3, {}, "6EZ5"), [("6EZ5", -3)])

    def test_at_target(self):
        self.assertEqual(roll_orders(2, {"NQZ5": 2.0}, "NQZ5"), [])

    def test_zero_holdings_ignored(self):
        # Un contrat périmé à 0 ne produit pas d'ordre.
        self.assertEqual(roll_orders(1, {"YMH6": 0.0}, "YMM6"), [("YMM6", 1)])


class TestRounding(unittest.TestCase):
    """Les quantités sont arrondies, jamais tronquées."""

    def test_float_holding_rounded(self):
        orders = roll_orders(0, {"ZBH6": 2.9999999}, "ZBM6")
        self.assertEqual(orders, [("ZBH6", -3)])

    def test_aggregate_rounds(self):
        self.assertEqual(aggregate_quantity({"a": 2.9999999, "b": -1.0000001}), 2)


if __name__ == "__main__":
    unittest.main()
