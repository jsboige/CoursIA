#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Tests CPU executables pour la regle de netting des ordres pendants (#23962).

Couvre les invariants documentes dans `open_order_netting.py` (module pur,
sans dependance QCAlgorithm). Le test n'exige PAS QC Cloud : il importe
uniquement `open_order_netting`, suivant le patron `test_carry_forecast.py`
(la regle de production est importee, jamais dupliquee dans le test).

Les trois cas nommes par l'item 2 de l'issue sont testes tels quels :
ordre pendant compte une seule fois, remplissage partiel rachetant
l'exces, ordre annule quittant l'ensemble vivant. Les deux modes (NET /
CANCEL) le sont aussi, l'item 1 demandant de mesurer les deux remedes.
"""

import os
import sys
import unittest

# Make the FuturesTrend/ package importable without importing
# main_carver13 (which would drag in AlgorithmImports and require the
# QC Cloud runtime).
_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
if _PROJ_ROOT not in sys.path:
    sys.path.insert(0, _PROJ_ROOT)

from open_order_netting import (  # noqa: E402
    CANCEL,
    NET,
    OpenOrder,
    naive_gap,
    open_order_remainder,
    reconcile_orders,
    would_resubmit,
)


class TestOpenOrderRemainder(unittest.TestCase):
    """open_order_remainder : somme signee des restes, par contrat."""

    def test_somme_les_restantes_dun_meme_contrat(self):
        orders = [
            OpenOrder("SI27F16", -2),
            OpenOrder("SI27F16", -3, filled_quantity=-1),
            OpenOrder("SI28F16", +4),
        ]
        # SI27F16 : -2 + (-3 - (-1)) = -2 + -2 = -4 ; SI28F16 filtre.
        self.assertEqual(open_order_remainder(orders, "SI27F16"), -4)
        self.assertEqual(open_order_remainder(orders, "SI28F16"), +4)
        self.assertEqual(open_order_remainder(orders, "SI29F16"), 0)

    def test_restante_nulle_jelee_par_le_filtrage_du_module(self):
        # Un ordre entierement rempli (reste 0) ne doit rien ajouter ;
        # reconcile_orders l'ignore deja, la somme brute reste coherente.
        orders = [OpenOrder("SI27F16", -2, filled_quantity=-2)]
        self.assertEqual(open_order_remainder(orders, "SI27F16"), 0)


class TestWouldResubmit(unittest.TestCase):
    """would_resubmit : le predicte du compteur passif (item 3)."""

    def test_meme_sens_est_une_reduplication(self):
        self.assertTrue(would_resubmit(naive=-2, remainder=-2))
        self.assertTrue(would_resubmit(naive=+2, remainder=+2))

    def test_sens_oppose_nest_pas_une_reduplication(self):
        # Un reste oppose au gap naif est un etat partiel legitime que le
        # nouvel ordre doit traverser, pas un doublon.
        self.assertFalse(would_resubmit(naive=+2, remainder=-2))

    def test_zero_ne_compte_jamais(self):
        self.assertFalse(would_resubmit(naive=0, remainder=-2))
        self.assertFalse(would_resubmit(naive=+2, remainder=0))


class TestReconcileNetMode(unittest.TestCase):
    """Mode NET : gap naif moins reste vivant, par contrat."""

    def test_ordre_pendant_compte_une_seule_fois(self):
        # Item 2, cas nominal : cible -2, rien de tenu, un ordre de vente
        # -2 encore vivant. Le code actuel calcule naive_gap = -2 et
        # RENVOIE l'ordre a chaque rebalance ; le netting voit que le
        # marche doit deja -2 et n'envoie rien.
        decision = reconcile_orders(
            target_qty=-2,
            holdings={"SI27F16": 0},
            mapped="SI27F16",
            open_orders=[OpenOrder("SI27F16", -2)],
            mode=NET,
        )
        self.assertEqual(naive_gap(-2, 0), -2)
        self.assertEqual(decision.orders, [])
        self.assertEqual(decision.cancels, [])
        self.assertEqual(decision.resubmissions_avoided, 1)

    def test_remplissage_partiel_rachete_lexces(self):
        # Item 2, cas remplissage partiel : ordre -5 dont -2 remplis, la
        # position tient deja les -2 remplis, cible -2. Le code actuel
        # calcule naive_gap = 0 (aveugle au reste -3) ; le netting voit
        # que si l'ordre restant se remplit, la position passe a -5, et
        # envoie +3 pour ramener a la cible.
        decision = reconcile_orders(
            target_qty=-2,
            holdings={"SI27F16": -2},
            mapped="SI27F16",
            open_orders=[OpenOrder("SI27F16", -5, filled_quantity=-2)],
            mode=NET,
        )
        self.assertEqual(
            decision.orders, [("SI27F16", +3)]
        )
        self.assertEqual(decision.resubmissions_avoided, 0)

    def test_ordre_annule_quitte_lensemble_vivant(self):
        # Item 2, cas annulation : l'ordre annule ne figure plus dans les
        # ordres ouverts, sa reste disparait, le gap se recalcule sur les
        # positions seules. Ici position -2, cible -2 : rien a faire.
        decision = reconcile_orders(
            target_qty=-2,
            holdings={"SI27F16": -2},
            mapped="SI27F16",
            open_orders=[],  # l'ordre -5/-2 remplis a ete annule
            mode=NET,
        )
        self.assertEqual(decision.orders, [])
        self.assertEqual(decision.cancels, [])
        self.assertEqual(decision.resubmissions_avoided, 0)

    def test_instance_mesuree_si27f16(self):
        # L'instance mesuree de l'issue (#23841, projet 38722439) : le
        # contrat stale SI27F16 est en livraison, sa clôture non remplie
        # depuis le 21 janvier, la cible est portee par le contrat mappe
        # SI28F16. Le code actuel renvoie l'achat de clôture a chaque
        # rebalance ; le netting l'etouffe.
        decision = reconcile_orders(
            target_qty=0,
            holdings={"SI27F16": -2, "SI28F16": 0},
            mapped="SI28F16",
            open_orders=[OpenOrder("SI27F16", +2)],
            mode=NET,
        )
        self.assertEqual(decision.orders, [])
        self.assertEqual(decision.resubmissions_avoided, 1)

    def test_reste_oppose_elargit_lordre(self):
        # Reste oppose au gap naif : l'ordre neuf doit financer le reste
        # vivant en sens inverse, pas seulement la difference cible /
        # position. Cible +2, rien de tenu, une vente -2 encore vivante :
        # si elle se remplit, la position passe a -2, l'ordre net doit
        # donc porter +4.
        decision = reconcile_orders(
            target_qty=+2,
            holdings={"SI27F16": 0},
            mapped="SI27F16",
            open_orders=[OpenOrder("SI27F16", -2)],
            mode=NET,
        )
        self.assertEqual(decision.orders, [("SI27F16", +4)])

    def test_stale_dabord_mappe_ensuite(self):
        # Convention d'ordre de contract_roll.roll_orders : contrats
        # stales d'abord, contrat mappe en dernier.
        decision = reconcile_orders(
            target_qty=-2,
            holdings={"SI27F16": -2, "SI28F16": 0},
            mapped="SI28F16",
            open_orders=[],
            mode=NET,
        )
        self.assertEqual(
            decision.orders, [("SI27F16", +2), ("SI28F16", -2)]
        )

    def test_stale_zero_avec_reste_vivant_compense(self):
        # Angle mort mesure par la review Hermes du 01/11 : contrat stale
        # a position NULLE mais porteur d'un ordre vivant — l'ensemble
        # juge est l'union holdings ∪ contrats des ordres vivants, pas
        # holdings seul. Position deja liquidee par un rebalance
        # anterieur, l'ordre de cloture -2 pas encore annule : le NET
        # emet l'ordre compensateur +2 au lieu de laisser l'ordre vivre.
        decision = reconcile_orders(
            target_qty=0,
            holdings={"SI27F16": 0, "SI28F16": 0},
            mapped="SI28F16",
            open_orders=[OpenOrder("SI27F16", -2)],
            mode=NET,
        )
        self.assertEqual(decision.orders, [("SI27F16", +2)])
        self.assertEqual(decision.cancels, [])
        self.assertEqual(decision.resubmissions_avoided, 0)

    def test_ordre_integrallement_rempli_hors_holdings_ignore(self):
        # Cas H : un ordre integralement rempli encore present dans
        # l'ensemble vivant, sur un contrat absent des holdings. Le
        # filtre order.remaining != 0 de reconcile_orders (le mecanisme
        # reel, distinct de celui de open_order_remainder) l'ignore :
        # ni ordre, ni annulation, le contrat n'entre pas dans l'union.
        decision = reconcile_orders(
            target_qty=0,
            holdings={"SI28F16": 0},
            mapped="SI28F16",
            open_orders=[OpenOrder("SI27F16", -2, filled_quantity=-2)],
            mode=NET,
        )
        self.assertEqual(decision.orders, [])
        self.assertEqual(decision.cancels, [])


class TestReconcileCancelMode(unittest.TestCase):
    """Mode CANCEL : annuler puis decider frais sur les positions."""

    def test_annule_puis_recalcule_a_partir_des_positions(self):
        # Meme etat que le cas nominal NET, mais en mode CANCEL : le
        # contrat a des ordres vivants -> il passe dans les annulations,
        # et l'ordre envoye est le gap naif (decision fraiche, jamais
        # empilee derriere un prix perime).
        decision = reconcile_orders(
            target_qty=-2,
            holdings={"SI27F16": 0},
            mapped="SI27F16",
            open_orders=[OpenOrder("SI27F16", -2)],
            mode=CANCEL,
        )
        self.assertEqual(decision.cancels, ["SI27F16"])
        self.assertEqual(decision.orders, [("SI27F16", -2)])

    def test_sans_ordre_vivant_aucune_annulation(self):
        decision = reconcile_orders(
            target_qty=-2,
            holdings={"SI27F16": -2},
            mapped="SI27F16",
            open_orders=[],
            mode=CANCEL,
        )
        self.assertEqual(decision.cancels, [])
        self.assertEqual(decision.orders, [])

    def test_annulation_par_contrat_pas_par_ordre(self):
        # Deux ordres vivants sur le meme contrat -> une seule entree
        # d'annulation pour ce contrat (l'annulation est demandee par
        # contrat dans le wiki QC).
        decision = reconcile_orders(
            target_qty=0,
            holdings={"SI27F16": -4},
            mapped="SI28F16",
            open_orders=[
                OpenOrder("SI27F16", +2),
                OpenOrder("SI27F16", +2),
            ],
            mode=CANCEL,
        )
        self.assertEqual(decision.cancels, ["SI27F16"])
        self.assertEqual(decision.orders, [("SI27F16", +4)])

    def test_stale_zero_avec_reste_vivant_annule(self):
        # Meme etat que le cas NET (contrat stale a position nulle,
        # ordre vivant -2), mode CANCEL : le contrat entre dans les
        # annulations — la decision fraiche ne laisse pas survivre un
        # ordre qu'elle pretend remplacer — et aucun ordre n'est envoye.
        decision = reconcile_orders(
            target_qty=0,
            holdings={"SI27F16": 0, "SI28F16": 0},
            mapped="SI28F16",
            open_orders=[OpenOrder("SI27F16", -2)],
            mode=CANCEL,
        )
        self.assertEqual(decision.cancels, ["SI27F16"])
        self.assertEqual(decision.orders, [])


if __name__ == "__main__":
    unittest.main()
