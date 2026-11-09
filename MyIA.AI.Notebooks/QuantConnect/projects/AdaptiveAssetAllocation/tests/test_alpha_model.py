# -*- coding: utf-8 -*-
"""Tests CPU de ``AdaptiveAssetAllocationAlpha`` (variante Framework, #20264).

Exercent la methode ``update`` du fichier committe ``alpha_model.py`` avec des
doublures minimales des objets Lean : tranche de donnees, historique, insights.
L'import de production passe par un stub du module ``AlgorithmImports`` installe
dans ``sys.modules`` le temps de l'import uniquement (``unittest.mock.patch.dict``),
comme dans ``BitcoinRegimeGate-QC/tests/test_execution_settled.py``.

Pre-requis : pytest, numpy, pandas. Aucune dependance QC/Lean, aucun reseau.

Execution ::

    python -m pytest tests/test_alpha_model.py -v

(depuis ``MyIA.AI.Notebooks/QuantConnect/projects/AdaptiveAssetAllocation``)
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

TICKERS = ["SPY", "EFA", "EEM", "VNQ", "GLD", "DBC", "TLT", "IEF", "TIP", "HYG"]
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
    stub.pd = pd
    return stub


_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
with patch.dict(sys.modules, {"AlgorithmImports": _make_algorithm_imports_stub()}):
    _spec = importlib.util.spec_from_file_location(
        "aaa_alpha_model_under_test", os.path.join(_PROJ_ROOT, "alpha_model.py"))
    alpha_module = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(alpha_module)

UP, FLAT = "up", "flat"


class Sym(str):
    """Symbole Lean minimal : hachable, ``value`` = ticker."""

    @property
    def value(self):
        return str(self)


SYMBOLS = {t: Sym(t) for t in TICKERS}


class Bars:
    def __init__(self, symbols):
        self._symbols = set(symbols)

    def contains_key(self, symbol):
        return symbol in self._symbols


class Slice:
    def __init__(self, bar_symbols=()):
        self.bars = Bars(bar_symbols)


def _prices(n=300, seed=7):
    """Cours journaliers : derives fixees par ticker, bruit gaussien reproductible.

    ``VNQ`` reproduit ``SPY`` avec un levier 2 et un bruit faible : correlation
    proche de 1, volatilite double, donc poids de variance minimale negatif.
    """
    rng = np.random.RandomState(seed)
    drifts = {"SPY": 0.0012, "EFA": -0.0004, "EEM": -0.0006, "VNQ": 0.0, "GLD": 0.0010,
              "DBC": -0.0008, "TLT": 0.0008, "IEF": -0.0002, "TIP": -0.0003, "HYG": -0.0005}
    rets = {t: drifts[t] + 0.01 * rng.randn(n) for t in TICKERS}
    rets["VNQ"] = 2 * rets["SPY"] + 0.0005 * rng.randn(n)
    dates = pd.bdate_range("2023-01-02", periods=n)
    return {t: pd.Series(100 * np.cumprod(1 + rets[t]), index=dates) for t in TICKERS}


class Algo:
    def __init__(self, now, prices, warming_up=False):
        self.time = now
        self.is_warming_up = warming_up
        self._prices = prices
        self.history_calls = []

    def history(self, symbols, count, resolution):
        self.history_calls.append(count)
        frames = []
        for s in symbols:
            close = self._prices[str(s)].iloc[-count:]
            frames.append(pd.DataFrame({"close": close.values},
                                       index=pd.MultiIndex.from_product([[s], close.index])))
        return pd.concat(frames)


def _alpha(**kwargs):
    a = alpha_module.AdaptiveAssetAllocationAlpha(TICKERS, **kwargs)
    a.symbols = dict(SYMBOLS)
    return a


def _by_ticker(insights):
    return {str(i.symbol): i for i in insights}


def test_empty_slice_does_not_consume_month():
    a = _alpha()
    algo = Algo(datetime(2024, 2, 1, 0, 0), _prices())
    assert a.update(algo, Slice()) == []
    assert a._last_month == -1
    algo.time = datetime(2024, 2, 1, 16, 0)
    assert len(a.update(algo, Slice([SYMBOLS["SPY"]]))) == len(TICKERS)
    assert a._last_month == 2


def test_out_of_universe_bar_does_not_consume_month():
    a = _alpha()
    algo = Algo(datetime(2024, 2, 1, 16, 0), _prices())
    assert a.update(algo, Slice([Sym("QQQ")])) == []
    assert a._last_month == -1


def test_one_emission_per_month():
    a = _alpha()
    algo = Algo(datetime(2024, 2, 1, 16, 0), _prices())
    assert a.update(algo, Slice([SYMBOLS["IEF"]]))
    algo.time = datetime(2024, 2, 2, 16, 0)
    assert a.update(algo, Slice([SYMBOLS["IEF"]])) == []
    algo.time = datetime(2024, 3, 1, 16, 0)
    assert a.update(algo, Slice([SYMBOLS["IEF"]]))


def test_warm_up_emits_nothing():
    a = _alpha()
    algo = Algo(datetime(2024, 2, 1, 16, 0), _prices(), warming_up=True)
    assert a.update(algo, Slice([SYMBOLS["SPY"]])) == []
    assert a._last_month == -1


def test_every_ticker_receives_a_weighted_insight():
    a = _alpha()
    out = _by_ticker(a.update(Algo(datetime(2024, 2, 1, 16, 0), _prices()), Slice([SYMBOLS["SPY"]])))
    assert set(out) == set(TICKERS)
    assert all(i.weight is not None for i in out.values())
    ups = [i for i in out.values() if i.direction == UP]
    flats = [i for i in out.values() if i.direction == FLAT]
    assert 1 <= len(ups) <= 4
    assert all(i.weight > 0 for i in ups)
    assert all(i.weight == 0 for i in flats)
    assert sum(i.weight for i in ups) == pytest.approx(1.0)


def test_clipped_minimum_variance_weight_is_flat():
    """VNQ est retenu par le momentum mais son poids de variance minimale est negatif."""
    prices = _prices()
    a = _alpha()
    algo = Algo(datetime(2024, 2, 1, 16, 0), prices)
    closes = pd.DataFrame({t: s.iloc[-131:].values for t, s in prices.items()})
    momentum = closes.iloc[-1] / closes.iloc[-a.lookback_momentum] - 1
    assert "VNQ" in momentum.nlargest(a.top_n).index
    out = _by_ticker(a.update(algo, Slice([SYMBOLS["SPY"]])))
    assert out["VNQ"].direction == FLAT and out["VNQ"].weight == 0
    assert out["SPY"].direction == UP and out["SPY"].weight > 0


def test_period_is_expressed_in_daily_bars():
    for bars in (30, 45):
        a = _alpha(insight_bars=bars)
        out = a.update(Algo(datetime(2024, 2, 1, 16, 0), _prices()), Slice([SYMBOLS["SPY"]]))
        assert {i.period for i in out} == {timedelta(days=bars)}


def test_history_request_covers_a_short_half_session_answer():
    """La requete est doublee ; seules les 131 seances les plus recentes servent."""
    prices = _prices()
    a = _alpha()
    algo = Algo(datetime(2024, 2, 1, 16, 0), prices)
    full = _by_ticker(a.update(algo, Slice([SYMBOLS["SPY"]])))
    assert algo.history_calls == [2 * 131]

    short = {t: s.iloc[-131:] for t, s in prices.items()}
    b = _alpha()
    same = _by_ticker(b.update(Algo(datetime(2024, 2, 1, 16, 0), short), Slice([SYMBOLS["SPY"]])))
    assert {t: (i.direction, round(i.weight, 12)) for t, i in full.items()} == \
        {t: (i.direction, round(i.weight, 12)) for t, i in same.items()}
