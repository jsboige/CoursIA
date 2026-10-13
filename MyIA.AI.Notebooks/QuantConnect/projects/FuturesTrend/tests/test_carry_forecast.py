#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Tests CPU executables pour la jambe carry Carver #11 (semis #17320, tranche 2).

Couvre les invariants documentes dans `carry_forecast.py` (module pur
numpy, sans dependance QCAlgorithm). Le test n'exige PAS QC Cloud :
il importe uniquement `carry_forecast`, suivant le patron
`test_breadth_multiplier.py` (REPAIR-8 c.1115 : la formule de production
est importee, jamais dupliquee dans le test).

Formule de reference : article QuantConnect #16001 "Combined Carry and
Trend" (strategie #11 de Carver 2023), alpha.py `update` et
`calculate_carry_forecasts`.

Pre-requis : `numpy` (>= 1.21). Le runner GH Actions par defaut ne porte
PAS numpy — voir MEMORY `scipy-matplotlib-pip-install-ci-runner.md`.
"""

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

from carry_forecast import (  # noqa: E402
    CARRY_FORECAST_CAP,
    CARRY_FORECAST_SCALAR,
    CARRY_SMOOTHING_SPANS,
    TRADING_DAYS_PER_YEAR,
    annualized_raw_carry,
    blend_forecasts,
    carry_forecasts,
    daily_price_risk,
    risk_adjusted_carry,
)
from carry_forecast import _ewma_adjusted  # noqa: E402  (invariant interne: constantes)


class TestAnnualizedRawCarry(unittest.TestCase):
    """annualized_raw_carry : (near - further) / |gap d'expiry en annees|."""

    def test_exemple_article_dollar_par_an(self):
        # Exemple de l'article #16001 : contrats mensuels a $100/$99/$98.
        # Acheter le $99 vaut $100 a l'expiry -> carry attendu $1 par mois,
        # soit (99 - 98) annualise sur 1 mois = 1 * 12 = 12 $/an.
        # Jours en unite "days" : 30 jours d'ecart entre les expiries.
        value = annualized_raw_carry(
            near_price=99.0, further_price=98.0,
            near_expiry_day=0.0, further_expiry_day=30.0,
        )
        self.assertAlmostEqual(value, 12.0, places=9)

    def test_ecart_trois_mois(self):
        # 90 jours d'ecart -> 3 mois -> 0.25 an -> (100 - 99)/0.25 = 4.0.
        value = annualized_raw_carry(
            near_price=100.0, further_price=99.0,
            near_expiry_day=0.0, further_expiry_day=90.0,
        )
        self.assertAlmostEqual(value, 4.0, places=9)

    def test_contango_negatif(self):
        # further > near (contango) -> carry negatif.
        value = annualized_raw_carry(
            near_price=98.0, further_price=100.0,
            near_expiry_day=0.0, further_expiry_day=30.0,
        )
        self.assertAlmostEqual(value, -24.0, places=9)

    def test_meme_expiry_none(self):
        # Gap nul (meme expiry) -> division par zero gardée : None.
        self.assertIsNone(annualized_raw_carry(
            near_price=99.0, further_price=98.0,
            near_expiry_day=100.0, further_expiry_day=100.0,
        ))

    def test_prix_invalide_none(self):
        self.assertIsNone(annualized_raw_carry(0.0, 98.0, 0.0, 30.0))
        self.assertIsNone(annualized_raw_carry(99.0, None, 0.0, 30.0))

    def test_ordre_expiries_inverse(self):
        # L'annualisation est en |mois| : l'ordre near/further inverse le
        # SIGNE du carry (via les prix) mais pas la duree.
        a = annualized_raw_carry(99.0, 98.0, 0.0, 30.0)
        b = annualized_raw_carry(99.0, 98.0, 30.0, 0.0)
        self.assertAlmostEqual(a, b, places=9)


class TestCarryForecasts(unittest.TestCase):
    """carry_forecasts : lissage EWMA par span, scalaire 30, cap +/-20."""

    def test_serie_constante(self):
        # Une constante reste elle-meme (EWMA ajustee exacte) ;
        # chaque span rend c * 30 capé.
        c = 0.1
        series = [c] * max(CARRY_SMOOTHING_SPANS)
        forecasts = carry_forecasts(series)
        self.assertEqual(len(forecasts), len(CARRY_SMOOTHING_SPANS))
        for f in forecasts:
            self.assertAlmostEqual(f, c * CARRY_FORECAST_SCALAR, places=9)

    def test_cap_atteint(self):
        # c * 30 > 20 -> capé à +20 (symétriquement à -20).
        forecasts = carry_forecasts([1.0] * max(CARRY_SMOOTHING_SPANS))
        self.assertTrue(all(f == CARRY_FORECAST_CAP for f in forecasts))
        forecasts_neg = carry_forecasts([-1.0] * max(CARRY_SMOOTHING_SPANS))
        self.assertTrue(all(f == -CARRY_FORECAST_CAP for f in forecasts_neg))

    def test_min_periods_span_manquant(self):
        # Serie de 4 points : aucun span (min 5) n'a l'historique -> liste vide,
        # miroir du `if smoothed_carry_forecast.empty: continue` de l'article.
        self.assertEqual(carry_forecasts([0.5, 0.5, 0.5, 0.5]), [])

    def test_historique_partiel(self):
        # Serie de 20 points : seuls les spans 5 et 20 produisent un forecast.
        forecasts = carry_forecasts([0.1] * 20)
        self.assertEqual(len(forecasts), 2)

    def test_choc_recent_domine_ancien(self):
        # Un point ancien isole n'influence plus une longue queue constante :
        # le forecast converge vers la constante (decroissance geometrique).
        series = [5.0] + [0.2] * 199
        forecasts = carry_forecasts(series, spans=(5,))
        self.assertAlmostEqual(forecasts[0], 0.2 * CARRY_FORECAST_SCALAR, places=6)

    def test_signe_conserve(self):
        # Backwardation (carry positif) -> forecast positif ; contango -> negatif.
        pos = carry_forecasts([0.3] * 60)
        neg = carry_forecasts([-0.3] * 60)
        self.assertTrue(all(f > 0 for f in pos))
        self.assertTrue(all(f < 0 for f in neg))


class TestEwmaInvariant(unittest.TestCase):
    """_ewma_adjusted : semantique pandas ewm(span, adjust=True)."""

    def test_constante_exacte(self):
        for span in (5, 20):
            self.assertAlmostEqual(_ewma_adjusted([3.7] * 50, span), 3.7, places=12)

    def test_poids_geometriques(self):
        # Sur 2 points [x0, x1], alpha=2/(span+1) :
        # y = ((1-a)*x0 + x1) / (1 + (1-a))  — poids (1-a)^1 et (1-a)^0.
        span = 5
        alpha = 2.0 / (span + 1.0)
        expected = ((1 - alpha) * 1.0 + 2.0) / (1.0 + (1 - alpha))
        self.assertAlmostEqual(_ewma_adjusted([1.0, 2.0], span), expected, places=12)

    def test_serie_vide_none(self):
        self.assertIsNone(_ewma_adjusted([], 5))


class TestDailyPriceRisk(unittest.TestCase):
    """daily_price_risk : EWMA(|retours daily|) * dernier prix."""

    def test_retours_constants(self):
        # Croissance monotone de +1% par bar : |retour| constant 0.01,
        # EWMA d'une constante = la constante -> risque = 0.01 * dernier prix.
        prices = [100.0 * 1.01 ** k for k in range(41)]
        expected = 0.01 * prices[-1]
        self.assertAlmostEqual(daily_price_risk(prices), expected, places=9)

    def test_risque_nul_none(self):
        # Prix parfaitement plat -> risque nul -> None (garde division).
        self.assertIsNone(daily_price_risk([50.0] * 50))

    def test_historique_trop_court_none(self):
        self.assertIsNone(daily_price_risk([100.0]))
        self.assertIsNone(daily_price_risk([]))

    def test_prix_invalide_none(self):
        self.assertIsNone(daily_price_risk([100.0, 0.0, 101.0]))


class TestRiskAdjustedCarry(unittest.TestCase):
    """risk_adjusted_carry : (near-further) annualise / risque annualise."""

    def test_ratio_dimensionless(self):
        # Prix alternant autour de 100 (|retour| ~1%) : risque quotidien
        # en price terms ~= 0.01*100 = 1 $ ; annualise ~ sqrt(256)=16 $/an.
        # raw_carry = 16 $/an -> ratio ~ 1.0 (aux variations de l'alternance).
        prices = [100.0]
        for _ in range(40):
            prices.append(prices[-1] * 1.01)
            prices.append(prices[-1] / 1.01)
        annual_risk = daily_price_risk(prices) * np.sqrt(TRADING_DAYS_PER_YEAR)
        raw = 2.0 * annual_risk
        self.assertAlmostEqual(
            risk_adjusted_carry(raw, prices), 2.0, places=9
        )

    def test_none_se_propage(self):
        prices = [100.0, 101.0, 100.5, 102.0] * 10
        self.assertIsNone(risk_adjusted_carry(None, prices))
        self.assertIsNone(risk_adjusted_carry(12.0, [100.0]))


class TestBlendForecasts(unittest.TestCase):
    """blend_forecasts : 60/40 Carver avec renormalisation de jambe."""

    def test_blend_60_40(self):
        self.assertAlmostEqual(blend_forecasts(10.0, 5.0, 0.4), 8.0, places=12)
        self.assertAlmostEqual(blend_forecasts(-10.0, 10.0, 0.4), -2.0, places=12)

    def test_carry_absent_renormalise_sur_trend(self):
        # Aucun span pret -> la jambe carry ne contribue pas ; le poids
        # se renormalise sur la jambe disponible (article #16001, fenetre
        # pre-min_periods), PAS un trend affaibli a 0.6x.
        self.assertEqual(blend_forecasts(10.0, None, 0.4), 10.0)

    def test_poids_aux_bornes(self):
        self.assertAlmostEqual(blend_forecasts(10.0, 5.0, 0.0), 10.0, places=12)
        self.assertAlmostEqual(blend_forecasts(10.0, 5.0, 1.0), 5.0, places=12)

    def test_poids_invalide_leve(self):
        with self.assertRaises(ValueError):
            blend_forecasts(10.0, 5.0, 1.5)
        with self.assertRaises(ValueError):
            blend_forecasts(10.0, 5.0, -0.1)


if __name__ == "__main__":
    unittest.main()
