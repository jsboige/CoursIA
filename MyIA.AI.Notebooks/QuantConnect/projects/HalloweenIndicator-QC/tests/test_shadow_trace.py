# -*- coding: utf-8 -*-
"""Tests CPU de la trace d'ombre de HalloweenIndicator-QC (#27482).

Exercent les méthodes de production de ``main.py`` (``initialize``,
``on_data``, ``_trace``, ``on_end_of_algorithm``) sur une instance de
``HalloweenIndicatorAlgorithm`` dont les collaborateurs Lean sont remplacés par
des doublures minimales. L'algorithme n'est jamais dupliqué.

Le module ``AlgorithmImports`` est remplacé par un stub dans ``sys.modules`` le
temps de l'import seulement (``unittest.mock.patch.dict``), comme dans
``BitcoinRegimeGate-QC/tests/test_execution_settled.py``.

Pré-requis : pytest. Aucune dépendance QC/Lean, aucun réseau.

Exécution ::

    python -m pytest tests/test_shadow_trace.py -v

(depuis ``MyIA.AI.Notebooks/QuantConnect/projects/HalloweenIndicator-QC``)
"""
from __future__ import annotations

import importlib.util
import os
import sys
import types
from collections import namedtuple
from datetime import datetime
from unittest.mock import patch

import pytest


def _make_algorithm_imports_stub():
    stub = types.ModuleType("AlgorithmImports")

    class _Enum:
        def __init__(self, **kwargs):
            self.__dict__.update(kwargs)

    class _Names:
        """Enum Lean dont seuls les noms servent : chaque membre vaut son nom."""

        def __getattr__(self, name):
            return name.lower()

    stub.QCAlgorithm = object
    stub.OrderStatus = _Enum(FILLED="filled", PARTIALLY_FILLED="partially_filled",
                             INVALID="invalid")
    stub.BrokerageName = _Names()
    stub.AccountType = _Names()
    stub.Resolution = _Names()
    stub.PortfolioTarget = lambda symbol, weight: (symbol, weight)
    return stub


_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
with patch.dict(sys.modules, {"AlgorithmImports": _make_algorithm_imports_stub()}):
    _spec = importlib.util.spec_from_file_location(
        "halloween_main", os.path.join(_PROJ_ROOT, "main.py"))
    _main = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_main)

HalloweenIndicatorAlgorithm = _main.HalloweenIndicatorAlgorithm

Sym = namedtuple("Sym", "value")
SPY, BIL, BND = Sym("SPY"), Sym("BIL"), Sym("BND")


class _Holding:
    def __init__(self, symbol, quantity=0):
        self.symbol = symbol
        self.invested = quantity != 0


class _Portfolio(dict):
    total_portfolio_value = 100000.0
    total_fees = 0.0

    def __missing__(self, symbol):
        return _Holding(symbol)


class _Bar:
    def __init__(self, fill_forward):
        self.is_fill_forward = fill_forward


class _Bars(dict):
    def contains_key(self, symbol):
        return symbol in self


class _Slice:
    def __init__(self, symbols, fill_forward=()):
        self.bars = _Bars({s: _Bar(s in fill_forward) for s in symbols})


class _Security:
    def __init__(self):
        self.leverage = None

    def set_leverage(self, leverage):
        self.leverage = leverage


class _Rules:
    def __getattr__(self, name):
        return lambda *args: (name, args)


def _algorithm(mode="strategy", params=None):
    algo = HalloweenIndicatorAlgorithm()
    values = {"mode": mode, "start": "2016-01-01", "end": "2026-11-27"}
    values.update(params or {})
    algo.get_parameter = lambda name, default=None: values.get(name, default)
    for name in ("set_start_date", "set_end_date", "set_cash", "set_brokerage_model"):
        setattr(algo, name, lambda *args: None)
    algo.settings = types.SimpleNamespace(seed_initial_prices=False)
    symbols = {"SPY": SPY, "BIL": BIL, "BND": BND}
    algo.add_equity = lambda ticker, resolution: types.SimpleNamespace(symbol=symbols[ticker])
    algo.benchmarks = []
    algo.set_benchmark = algo.benchmarks.append
    algo.securities = {SPY: _Security(), BIL: _Security(), BND: _Security()}
    algo.scheduled = []
    algo.schedule = types.SimpleNamespace(
        on=lambda date_rule, time_rule, action: algo.scheduled.append(action))
    algo.date_rules = _Rules()
    algo.time_rules = _Rules()
    algo.plots = []
    algo.plot = lambda chart, series, value: algo.plots.append((chart, series, value))
    algo.logs = []
    algo.log = algo.logs.append
    algo.stats = {}
    algo.set_runtime_statistic = algo.stats.__setitem__
    algo.portfolio = _Portfolio()
    algo.time = datetime(2026, 11, 24, 9, 30)
    algo.initialize()
    return algo


def _equity_points(algo):
    return [p for p in algo.plots if p[0] == "shadow" and p[1].startswith("e")]


@pytest.mark.parametrize("mode", ["strategy", "spy", "6040", "inverse"])
def test_benchmark_is_spy_in_every_mode(mode):
    algo = _algorithm(mode)
    assert algo.benchmarks == [SPY]


def test_window_has_no_default():
    with pytest.raises(TypeError):
        _algorithm(params={"start": None})


def test_first_trace_plots_initial_value():
    algo = _algorithm()
    algo._trace()
    assert [p[1] for p in algo.plots] == ["e0", "fees", "turnover"]
    assert algo.shadow_skips == 0


def test_published_close_plots_next_point():
    algo = _algorithm()
    algo._trace()
    algo.on_data(_Slice([SPY, BIL]))
    algo._trace()
    assert [p[1] for p in _equity_points(algo)] == ["e0", "e1"]


def test_fill_forward_spy_skips_the_point():
    algo = _algorithm()
    algo._trace()
    algo.on_data(_Slice([SPY], fill_forward={SPY}))
    algo._trace()
    assert len(_equity_points(algo)) == 1
    assert algo.shadow_skips == 1
    assert "SPY" in algo.logs[-1]


def test_fill_forward_held_asset_skips_the_point():
    algo = _algorithm()
    algo.portfolio[BIL] = _Holding(BIL, quantity=100)
    algo._trace()
    algo.on_data(_Slice([SPY, BIL], fill_forward={BIL}))
    algo._trace()
    assert len(_equity_points(algo)) == 1
    assert "BIL" in algo.logs[-1]


def test_fill_forward_unheld_asset_does_not_skip():
    algo = _algorithm()
    algo.portfolio[SPY] = _Holding(SPY, quantity=100)
    algo.portfolio[BIL] = _Holding(BIL, quantity=0)
    algo._trace()
    algo.on_data(_Slice([SPY, BIL], fill_forward={BIL}))
    algo._trace()
    assert len(_equity_points(algo)) == 2
    assert algo.shadow_skips == 0


def test_no_close_since_last_trace_skips_the_point():
    algo = _algorithm()
    algo._trace()
    algo._trace()
    assert len(_equity_points(algo)) == 1
    assert "aucune barre de SPY" in algo.logs[-1]


def test_series_rotation_counts_only_plotted_points():
    algo = _algorithm()
    algo._trace()
    algo.on_data(_Slice([SPY], fill_forward={SPY}))
    algo._trace()
    algo.on_data(_Slice([SPY]))
    algo._trace()
    assert [p[1] for p in _equity_points(algo)] == ["e0", "e1"]


def test_end_of_algorithm_reports_skips():
    algo = _algorithm()
    algo._trace()
    algo._trace()
    algo.on_end_of_algorithm()
    assert algo.stats["Shadow skips FF"] == "1"
    assert algo.stats["invalid_orders"] == "0"
