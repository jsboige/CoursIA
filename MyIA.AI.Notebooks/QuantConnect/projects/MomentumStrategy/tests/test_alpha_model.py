# -*- coding: utf-8 -*-
"""Tests CPU de ``SectorMomentumAlpha`` (variante Framework, #20264).

Exercent la methode ``update`` du fichier committe ``alpha_model.py`` avec des
doublures minimales des objets Lean : portefeuille, titres, historique,
indicateurs, insights. L'import de production passe par un stub du module
``AlgorithmImports`` installe dans ``sys.modules`` le temps de l'import
uniquement (``unittest.mock.patch.dict``), comme dans
``AdaptiveAssetAllocation/tests/test_alpha_model.py``.

Pre-requis : pytest, numpy, pandas. Aucune dependance QC/Lean, aucun reseau.

Execution ::

    python -m pytest tests/test_alpha_model.py -v

(depuis ``MyIA.AI.Notebooks/QuantConnect/projects/MomentumStrategy``)
"""
from __future__ import annotations

import importlib.util
import os
import sys
import types
from collections import namedtuple
from datetime import datetime, timedelta
from unittest.mock import patch

import numpy as np
import pandas as pd
import pytest

SECTORS = ["XLK", "XLF", "XLE", "XLV", "XLI", "XLY", "XLP", "XLU", "XLB", "XLRE", "XLC"]
FakeInsight = namedtuple("FakeInsight", "symbol period direction weight source_model")


def _make_algorithm_imports_stub():
    stub = types.ModuleType("AlgorithmImports")

    class _AlphaModel:
        def __init__(self):
            pass

    class _Insight:
        @staticmethod
        def price(symbol, period, direction, weight=None, source_model=None):
            return FakeInsight(symbol, period, direction, weight, source_model)

    class _Enum:
        def __init__(self, **kwargs):
            self.__dict__.update(kwargs)

    stub.AlphaModel = _AlphaModel
    stub.Insight = _Insight
    stub.InsightDirection = _Enum(UP="up", FLAT="flat", DOWN="down")
    stub.Resolution = _Enum(DAILY="daily")
    stub.timedelta = timedelta
    return stub


_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
with patch.dict(sys.modules, {"AlgorithmImports": _make_algorithm_imports_stub()}):
    _spec = importlib.util.spec_from_file_location(
        "momentum_alpha_model_under_test", os.path.join(_PROJ_ROOT, "alpha_model.py"))
    alpha_module = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(alpha_module)

UP, FLAT = "up", "flat"
LOOKBACK = 252
# Barres manquantes mesurees sur la tranche de cloture d'une demi-seance :
# 44 recues sur 257 demandees (#20264).
HALF_SESSION_MISSING = 257 - 44


class Sym(str):
    """Symbole Lean minimal : hachable, ``value`` = ticker."""

    @property
    def value(self):
        return str(self)


SYMBOLS = {t: Sym(t) for t in SECTORS + ["SPY"]}


class Holding:
    def __init__(self, invested=False, average_price=0.0):
        self.invested = invested
        self.average_price = average_price


class Security:
    def __init__(self, price):
        self.price = price


class Indicator:
    def __init__(self, value):
        self.is_ready = True
        self.current = types.SimpleNamespace(value=value)


def _prices(drifts, n=600, seed=11):
    """Cours journaliers : derive fixee par ticker, bruit gaussien reproductible."""
    rng = np.random.RandomState(seed)
    dates = pd.bdate_range("2021-01-04", periods=n)
    out = {}
    for t, d in drifts.items():
        rets = d + 0.01 * rng.randn(n)
        out[t] = pd.Series(100 * np.cumprod(1 + rets), index=dates)
    return out


POSITIVE_DRIFTS = {
    "XLK": 0.0016, "XLF": 0.0012, "XLE": 0.0010, "XLV": 0.0008, "XLI": 0.0004,
    "XLY": 0.0003, "XLP": 0.0002, "XLU": 0.0001, "XLB": -0.0002, "XLRE": -0.0004,
    "XLC": -0.0006,
}
NEGATIVE_DRIFTS = {t: -0.0010 for t in SECTORS}


class Algo:
    """Algorithme minimal : temps, historique, portefeuille, titres.

    ``missing`` retire ce nombre de barres a chaque reponse d'historique, comme
    la tranche de cloture d'une demi-seance americaine.
    """

    def __init__(self, now, prices, warming_up=False, missing=0,
                 spy_price=110.0, sma200=100.0, sma20=100.0):
        self.time = now
        self.is_warming_up = warming_up
        self._prices = prices
        self._missing = missing
        self.history_calls = []
        self.portfolio = {s: Holding() for s in SYMBOLS.values()}
        self.securities = {SYMBOLS[t]: Security(float(p.iloc[-1])) for t, p in prices.items()}
        self.securities[SYMBOLS["SPY"]] = Security(spy_price)
        self._sma = {200: Indicator(sma200), 20: Indicator(sma20)}

    def history(self, symbol, count, resolution):
        self.history_calls.append(count)
        closes = self._prices[str(symbol)].iloc[-count:]
        closes = closes.iloc[self._missing:] if self._missing else closes
        return pd.DataFrame({"close": closes.values}, index=closes.index)

    def sma(self, symbol, period, resolution):
        return self._sma[period]


def _alpha(algo):
    alpha = alpha_module.SectorMomentumAlpha(
        SECTORS, top_n=4, lookback=LOOKBACK, skip_days=21, vol_window=63,
        stop_loss_pct=-0.10)
    changes = types.SimpleNamespace(
        added_securities=[types.SimpleNamespace(symbol=s) for s in SYMBOLS.values()])
    alpha.on_securities_changed(algo, changes)
    return alpha


def _by_ticker(insights):
    return {str(i.symbol): i for i in insights}


def test_flat_insights_carry_zero_weight():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS))
    insights = _by_ticker(_alpha(algo).update(algo, None))
    ups = [t for t, i in insights.items() if i.direction == UP]
    flats = [t for t, i in insights.items() if i.direction == FLAT]
    assert len(ups) == 4
    assert len(flats) == len(SECTORS) - 4
    for t in flats:
        assert insights[t].weight == 0
    for t in ups:
        assert insights[t].weight == pytest.approx(0.25)


def test_history_survives_a_half_session_answer():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS), missing=HALF_SESSION_MISSING)
    insights = _alpha(algo).update(algo, None)
    assert set(algo.history_calls) == {2 * (LOOKBACK + 5)}
    assert len(insights) == len(SECTORS)


def test_history_keeps_the_most_recent_bars():
    prices = _prices(POSITIVE_DRIFTS)
    algo = Algo(datetime(2023, 7, 3), prices)
    alpha = _alpha(algo)
    _, raw = alpha._momentum_score(algo, SYMBOLS["XLK"])
    closes = prices["XLK"].iloc[-(LOOKBACK + 5):]
    expected = closes.iloc[-21] / closes.iloc[0] - 1
    assert raw == pytest.approx(expected)


def test_history_shorter_than_lookback_gives_no_score():
    # Ligne trop jeune (XLC cote depuis 2018) : meme en demandant le double,
    # l'historique rendu reste sous `lookback` barres, donc pas de score.
    short = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS, n=LOOKBACK - 1))
    assert _alpha(short)._momentum_score(short, SYMBOLS["XLK"]) is None
    exact = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS, n=LOOKBACK))
    assert _alpha(exact)._momentum_score(exact, SYMBOLS["XLK"]) is not None


def test_stop_loss_flat_lives_as_long_as_a_monthly_insight():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS))
    alpha = _alpha(algo)
    alpha.update(algo, None)
    xlk = SYMBOLS["XLK"]
    assert "XLK" in alpha.entry_prices
    algo.portfolio[xlk] = Holding(invested=True, average_price=alpha.entry_prices["XLK"])
    algo.securities[xlk] = Security(alpha.entry_prices["XLK"] * 0.85)
    algo.time = datetime(2023, 7, 10)
    insights = alpha.update(algo, None)
    assert len(insights) == 1
    stop = insights[0]
    assert stop.symbol == xlk and stop.direction == FLAT
    assert stop.weight == 0
    assert stop.period == alpha.period
    assert "XLK" not in alpha.entry_prices


def test_arm_stop_uses_current_price_for_a_new_line():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS))
    alpha = _alpha(algo)
    alpha._arm_stop(algo, "XLK", SYMBOLS["XLK"])
    assert alpha.entry_prices["XLK"] == algo.securities[SYMBOLS["XLK"]].price


def test_arm_stop_uses_average_price_for_a_held_line_without_entry():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS))
    alpha = _alpha(algo)
    algo.portfolio[SYMBOLS["XLK"]] = Holding(invested=True, average_price=42.0)
    alpha._arm_stop(algo, "XLK", SYMBOLS["XLK"])
    assert alpha.entry_prices["XLK"] == 42.0
    algo.portfolio[SYMBOLS["XLK"]] = Holding(invested=True, average_price=50.0)
    alpha._arm_stop(algo, "XLK", SYMBOLS["XLK"])
    assert alpha.entry_prices["XLK"] == 42.0


def test_risk_off_keeps_only_staples_and_utilities():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS),
                spy_price=90.0, sma200=100.0, sma20=100.0)
    alpha = _alpha(algo)
    insights = _by_ticker(alpha.update(algo, None))
    for t in SECTORS:
        if t in ("XLP", "XLU"):
            assert insights[t].direction == UP and insights[t].weight == 0.5
        else:
            assert insights[t].direction == FLAT and insights[t].weight == 0
    assert set(alpha.entry_prices) == {"XLP", "XLU"}


def test_defensive_fallback_arms_staples_and_utilities():
    algo = Algo(datetime(2023, 7, 3), _prices(NEGATIVE_DRIFTS))
    alpha = _alpha(algo)
    insights = _by_ticker(alpha.update(algo, None))
    for t in SECTORS:
        if t in ("XLP", "XLU"):
            assert insights[t].direction == UP and insights[t].weight == 0.5
        else:
            assert insights[t].direction == FLAT and insights[t].weight == 0
    assert set(alpha.entry_prices) == {"XLP", "XLU"}


def test_one_emission_per_month():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS))
    alpha = _alpha(algo)
    assert len(alpha.update(algo, None)) == len(SECTORS)
    algo.time = datetime(2023, 7, 5)
    assert alpha.update(algo, None) == []
    algo.time = datetime(2023, 8, 1)
    assert len(alpha.update(algo, None)) == len(SECTORS)


def test_warm_up_emits_nothing():
    algo = Algo(datetime(2023, 7, 3), _prices(POSITIVE_DRIFTS), warming_up=True)
    assert _alpha(algo).update(algo, None) == []
