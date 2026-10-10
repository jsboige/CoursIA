# -*- coding: utf-8 -*-
"""Tests CPU du bras d'execution "settled" de BitcoinRegimeGate-QC (#20006).

Exercent les METHODES DE PRODUCTION de ``main.py`` (``initialize``,
``rebalance``, ``on_data``, ``on_order_event``, ``on_end_of_algorithm``) sur une
instance de production de ``BitcoinRegimeGate`` dont les collaborateurs Lean sont
remplaces par des doublures minimales. L'algorithme n'est jamais duplique : les
methodes testees sont celles du fichier committe.

L'import de production est rendu possible par un stub du module
``AlgorithmImports`` installe dans ``sys.modules`` le temps de l'import
uniquement (``unittest.mock.patch.dict``), donc sans polluer les autres tests
(convention repo : ``projects/ML-Chronos-Foundation/validate_19622_port.py``).

Pre-requis : pytest. Aucune dependance QC/Lean, aucun reseau.

Execution ::

    python -m pytest tests/test_execution_settled.py -v

(depuis ``MyIA.AI.Notebooks/QuantConnect/projects/BitcoinRegimeGate-QC``)
"""
from __future__ import annotations

import importlib.util
import os
import sys
import types
from collections import namedtuple
from datetime import datetime, timedelta
from unittest.mock import patch

import pytest


# --------------------------------------------------------------------------
# Stub du module AlgorithmImports (runtime Lean indisponible).
# --------------------------------------------------------------------------
def _make_algorithm_imports_stub():
    stub = types.ModuleType("AlgorithmImports")

    class _Base:
        """Doublure avec garde sur la propriete native Execution de QCAlgorithm."""

        @property
        def execution(self):
            return None

        @execution.setter
        def execution(self, value):
            raise TypeError("Execution attend un IExecutionModel, pas un mode texte")

    class _OrderStatus:
        FILLED = "filled"
        PARTIALLY_FILLED = "partially_filled"
        INVALID = "invalid"
        CANCELED = "canceled"

    class _Enum:
        def __init__(self, **kwargs):
            self.__dict__.update(kwargs)

    stub.QCAlgorithm = _Base
    stub.FeeModel = _Base
    stub.BrokerageModelSecurityInitializer = _Base
    stub.OrderStatus = _OrderStatus
    stub.timedelta = timedelta
    # Enum QC utilisees par initialize (mode "gate").
    stub.BrokerageName = _Enum(INTERACTIVE_BROKERS_BROKERAGE="ib")
    stub.AccountType = _Enum(MARGIN="margin")
    stub.Resolution = _Enum(DAILY="daily")
    stub.Market = _Enum(BITFINEX="bitfinex")
    return stub


_HERE = os.path.dirname(os.path.abspath(__file__))
_PROJ_ROOT = os.path.dirname(_HERE)
# Stub isole : present dans sys.modules seulement pendant l'exec du module.
with patch.dict(sys.modules, {"AlgorithmImports": _make_algorithm_imports_stub()}):
    _spec = importlib.util.spec_from_file_location(
        "btc_main", os.path.join(_PROJ_ROOT, "main.py"))
    btc_main = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(btc_main)

BitcoinRegimeGate = btc_main.BitcoinRegimeGate
OrderStatus = btc_main.OrderStatus


# --------------------------------------------------------------------------
# Doublures minimales des collaborateurs Lean.
# --------------------------------------------------------------------------
Sym = namedtuple("Sym", "value")
QQQ = Sym("QQQ")
SHY = Sym("SHY")
BTC = Sym("BTCUSD")
SPY = Sym("SPY")
IEF = Sym("IEF")


class _Holding:
    def __init__(self, symbol, quantity=0.0):
        self.symbol = symbol
        self.quantity = quantity
        self.invested = quantity != 0.0
        self.holdings_value = quantity * 100.0


class _Portfolio(dict):
    def __init__(self):
        super().__init__()
        self.total_portfolio_value = 100000.0
        self.total_fees = 0.0

    def __missing__(self, key):
        holding = _Holding(key, 0.0)
        self[key] = holding
        return holding


class _Security:
    def __init__(self, price):
        self.price = price


class _Current(namedtuple("_Current", "value")):
    pass


class _Indicator:
    def __init__(self, ready, value):
        self.is_ready = ready
        self.current = _Current(value)


class _Order:
    def __init__(self, symbol):
        self.symbol = symbol


class _Transactions:
    def __init__(self):
        self.open_orders = []

    def get_open_orders(self):
        return list(self.open_orders)


class _OrderEvent:
    def __init__(self, status, symbol, fill_quantity=0.0, fill_price=0.0):
        self.status = status
        self.symbol = symbol
        self.fill_quantity = fill_quantity
        self.fill_price = fill_price


class _Bars:
    def __init__(self, keys):
        self._keys = set(keys)

    def contains_key(self, key):
        return key in self._keys


class _Slice:
    """Barre de donnees minimale : seuls les symboles presents importent."""

    def __init__(self, symbols):
        self.bars = _Bars(symbols)


def _make(mode="gate", execution="base"):
    """Instance de production, collaborateurs Lean remplaces."""
    alg = BitcoinRegimeGate()
    alg.mode = mode
    alg._execution_mode = execution
    alg.is_warming_up = False
    alg.sma_window = 50
    alg.roc_window = 20
    alg.frequency = "weekly"
    alg.start_value = 100000.0
    alg.closes = 0
    alg.traded = 0.0
    alg.order_counts = {}
    alg.gross_sum = 0.0
    alg.n_switches = 0
    alg.n_to_qqq = 0
    alg.n_to_shy = 0
    alg._ref_month = -1
    alg._pending_target = None
    alg._decision_time = None
    alg.n_deferred = 0
    alg.n_invalid = 0
    alg.n_canceled = 0
    alg.acquire_count = 0
    alg.delay_seconds = 0.0
    alg.cash_closes = 0
    alg.qqq, alg.shy, alg.btc = QQQ, SHY, BTC
    alg.shadow_symbol = QQQ
    alg.ref_symbols = {}
    alg.portfolio = _Portfolio()
    alg.securities = {QQQ: _Security(400.0), SHY: _Security(85.0),
                      BTC: _Security(60000.0)}
    # Regime risque actif par defaut : BTC 60000 > SMA 50000, ROC +0.05 -> QQQ.
    alg.sma = _Indicator(True, 50000.0)
    alg.roc = _Indicator(True, 0.05)
    alg.transactions = _Transactions()
    alg.time = datetime(2020, 1, 6, 8, 0)
    # Enregistreurs d'appels (remplacent les methodes Lean sur l'instance).
    alg.liquidated = []
    alg.submitted = []
    alg.debugs = []
    alg.logs = []
    alg.stats = {}
    alg.plots = []
    alg.liquidate = lambda symbol=None: alg.liquidated.append(symbol)
    alg.set_holdings = lambda symbol, weight=None: alg.submitted.append((symbol, weight))
    alg.debug = lambda msg: alg.debugs.append(msg)
    alg.log = lambda msg: alg.logs.append(msg)
    alg.set_runtime_statistic = lambda name, value: alg.stats.__setitem__(name, value)
    alg.plot = lambda *args, **kwargs: alg.plots.append(args)
    return alg


# --------------------------------------------------------------------------
# Stub isole : aucun residu dans sys.modules apres l'import.
# --------------------------------------------------------------------------
def test_algorithm_imports_stub_not_leaked():
    assert "AlgorithmImports" not in sys.modules


# --------------------------------------------------------------------------
# initialize : analyse des parametres (borne).
# --------------------------------------------------------------------------
class _Sec:
    def __init__(self, ticker):
        self.symbol = Sym(ticker)


class _Rule:
    def __call__(self, *args, **kwargs):
        return self


class _Schedule:
    def __init__(self):
        self.calls = []

    def on(self, date_rule, time_rule, handler):
        self.calls.append((date_rule, time_rule, handler))


def _make_initializable(params):
    alg = BitcoinRegimeGate()
    p = dict(params)
    alg.get_parameter = lambda name, default=None: p[name] if name in p else default
    alg.set_start_date = lambda *a, **k: None
    alg.set_end_date = lambda *a, **k: None
    alg.set_cash = lambda *a, **k: None
    alg.set_brokerage_model = lambda *a, **k: None
    alg.set_security_initializer = lambda *a, **k: None
    alg.set_warm_up = lambda *a, **k: None
    alg.add_equity = lambda ticker, res, **k: _Sec(ticker)
    alg.add_crypto = lambda ticker, res, market=None: _Sec(ticker)
    alg.sma = lambda symbol, window, res: _Indicator(False, 0.0)
    alg.roc = lambda symbol, window, res: _Indicator(False, 0.0)
    alg.schedule = _Schedule()
    alg.date_rules = types.SimpleNamespace(week_start=_Rule(), month_start=_Rule())
    alg.time_rules = types.SimpleNamespace(at=_Rule())
    return alg


def test_initialize_defaults_execution_to_base():
    alg = _make_initializable({})
    alg.initialize()
    assert alg._execution_mode == "base"
    assert alg.mode == "gate"
    assert alg.frequency == "weekly"
    assert alg.sma_window == 50 and alg.roc_window == 20


def test_initialize_parses_execution_settled():
    alg = _make_initializable({"execution": "settled"})
    alg.initialize()
    assert alg._execution_mode == "settled"


def test_initialize_rejects_unknown_execution():
    alg = _make_initializable({"execution": "turbo"})
    with pytest.raises(ValueError):
        alg.initialize()


def test_initialize_rejects_unknown_mode():
    alg = _make_initializable({"mode": "turbo"})
    with pytest.raises(ValueError):
        alg.initialize()


# --------------------------------------------------------------------------
# base : defaut, paire liquidation puis allocation, inchange.
# --------------------------------------------------------------------------
def test_base_default_pairs_liquidate_then_allocate():
    alg = _make(execution="base")
    alg.portfolio[SHY] = _Holding(SHY, 100.0)  # detient SHY, decision -> QQQ
    alg.rebalance()
    assert alg.liquidated == [None]            # base : liquidate() du portefeuille
    assert alg.submitted == [(QQQ, 1.0)]
    assert alg.n_switches == 1
    assert alg._pending_target is None         # aucun etat settled engage


def test_base_on_data_has_no_deferred_acquisition():
    alg = _make(execution="base")
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == []
    assert alg.acquire_count == 0


def test_base_order_event_unchanged_by_settled_counters():
    alg = _make(execution="base")
    alg.on_order_event(_OrderEvent(OrderStatus.FILLED, QQQ, 10.0, 400.0))
    assert alg.order_counts == {"QQQ": 1}
    assert alg.traded == pytest.approx(10.0 * 400.0 / 100000.0)
    alg.on_order_event(_OrderEvent(OrderStatus.INVALID, SHY))
    alg.on_order_event(_OrderEvent(OrderStatus.CANCELED, SHY))
    assert alg.n_invalid == 0                  # base ne compte pas les issues settled
    assert alg.n_canceled == 0


def test_base_runtime_statistics_omit_settled_keys():
    alg = _make(execution="base")
    alg.on_end_of_algorithm()
    assert "Execution" not in alg.stats
    assert not any(k.startswith("Settled") for k in alg.stats)


# --------------------------------------------------------------------------
# settled : transitions.
# --------------------------------------------------------------------------
def test_settled_initial_cash_acquisition_deferred_to_later_bar():
    alg = _make(execution="settled")
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()                            # rien a liquider (aucune position)
    assert alg.liquidated == []
    assert alg.submitted == []                 # aucune allocation immediate
    assert alg._pending_target == QQQ
    assert alg.n_switches == 1
    # Meme barre que la decision -> pas d'acquisition (barre ulterieure exigee).
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == []
    # Barre ulterieure, barre cible presente -> acquisition.
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == [(QQQ, 1.0)]
    assert alg._pending_target is None
    assert alg.acquire_count == 1
    assert alg.logs                          # delai decision->soumission journalise


def test_settled_switch_liquidates_other_only_then_buys_later():
    alg = _make(execution="settled")
    alg.portfolio[SHY] = _Holding(SHY, 100.0)  # detient SHY, decision -> QQQ
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    assert alg.liquidated == [SHY]             # seule la jambe opposee est liquidee
    assert alg.submitted == []                 # aucun achat immediat
    assert alg._pending_target == QQQ
    # Vente non remplie (SHY encore detenu) -> acquisition bloquee.
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == []
    # Vente remplie : SHY a zero, aucun ordre ouvert -> acquisition a une barre ulterieure.
    alg.portfolio[SHY] = _Holding(SHY, 0.0)
    alg.time = datetime(2020, 1, 8, 16, 0)
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == [(QQQ, 1.0)]


def test_settled_target_already_held_no_action():
    alg = _make(execution="settled")
    alg.portfolio[QQQ] = _Holding(QQQ, 100.0)
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    assert alg.liquidated == []
    assert alg.submitted == []
    assert alg._pending_target is None
    assert alg.n_switches == 0


def test_settled_open_orders_defer_decision():
    alg = _make(execution="settled")
    alg.transactions.open_orders = [_Order(QQQ)]
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    assert alg.n_deferred == 1
    assert alg._pending_target is None
    assert alg.submitted == []
    assert alg.liquidated == []


def test_settled_partial_fill_blocks_acquisition_without_duplicate():
    alg = _make(execution="settled")
    alg.portfolio[SHY] = _Holding(SHY, 100.0)
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    assert alg.liquidated == [SHY]
    # Remplissage partiel : SHY garde une quantite et un ordre SHY reste ouvert.
    alg.portfolio[SHY] = _Holding(SHY, 60.0)
    alg.transactions.open_orders = [_Order(SHY)]
    alg.on_order_event(_OrderEvent(OrderStatus.PARTIALLY_FILLED, SHY, 40.0, 85.0))
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == []                 # aucun achat (ni callback, ni on_data)
    # Decision repetee le meme jour -> aucune nouvelle soumission.
    alg.rebalance()
    assert alg.liquidated == [SHY]             # toujours une seule liquidation
    assert alg.submitted == []


def test_settled_canceled_liquidation_blocks_purchase_and_counted():
    alg = _make(execution="settled")
    alg.portfolio[SHY] = _Holding(SHY, 100.0)
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    alg.transactions.open_orders = []          # la liquidation n'est plus ouverte
    alg.on_order_event(_OrderEvent(OrderStatus.CANCELED, SHY))
    assert alg.n_canceled == 1
    # SHY non nul -> acquisition bloquee, aucun retry intrabar (meme semaine).
    for day in (7, 8, 9):
        alg.time = datetime(2020, 1, day, 16, 0)
        alg.on_data(_Slice([QQQ]))
    assert alg.submitted == []
    assert alg._pending_target == QQQ          # toujours en attente (bloque)


def test_settled_canceled_liquidation_reattempt_next_decision():
    alg = _make(execution="settled")
    alg.portfolio[SHY] = _Holding(SHY, 100.0)
    alg.time = datetime(2020, 1, 6, 8, 0)      # lundi
    alg.rebalance()
    assert alg.liquidated == [SHY]
    alg.on_order_event(_OrderEvent(OrderStatus.CANCELED, SHY))
    assert alg.n_canceled == 1
    # Intrabar : aucun retry de la liquidation.
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))
    assert alg.liquidated == [SHY]
    assert alg.submitted == []
    # Decision hebdomadaire suivante : reattempt de la liquidation.
    alg.time = datetime(2020, 1, 13, 8, 0)
    alg.rebalance()
    assert alg.liquidated == [SHY, SHY]
    assert alg._decision_time == datetime(2020, 1, 13, 8, 0)
    # La vente aboutit, puis acquisition a une barre ulterieure.
    alg.portfolio[SHY] = _Holding(SHY, 0.0)
    alg.time = datetime(2020, 1, 14, 16, 0)
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == [(QQQ, 1.0)]


def test_settled_invalid_liquidation_reattempt_next_decision():
    alg = _make(execution="settled")
    alg.portfolio[SHY] = _Holding(SHY, 100.0)
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    alg.on_order_event(_OrderEvent(OrderStatus.INVALID, SHY))
    assert alg.n_invalid == 1
    # Meme jour : aucun reattempt.
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    assert alg.liquidated == [SHY]
    # Semaine suivante : reattempt.
    alg.time = datetime(2020, 1, 13, 8, 0)
    alg.rebalance()
    assert alg.liquidated == [SHY, SHY]


def test_settled_reversal_after_failed_sale_clears_pending():
    alg = _make(execution="settled")
    alg.portfolio[SHY] = _Holding(SHY, 100.0)
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()                            # cible QQQ, pending QQQ
    assert alg._pending_target == QQQ
    alg.transactions.open_orders = []
    alg.on_order_event(_OrderEvent(OrderStatus.CANCELED, SHY))
    assert alg.n_canceled == 1
    # Regime retourne a SHY : cible = SHY = detenue seule -> intention obsolete effacee.
    alg.roc = _Indicator(True, -0.05)          # risk_on False -> target SHY
    alg.time = datetime(2020, 1, 13, 8, 0)
    alg.rebalance()
    assert alg._pending_target is None
    assert alg._decision_time is None
    assert alg.submitted == []                 # aucune allocation
    assert alg.liquidated == [SHY]             # aucune nouvelle liquidation
    # Aucune acquisition residuelle.
    alg.time = datetime(2020, 1, 14, 16, 0)
    alg.on_data(_Slice([SHY]))
    assert alg.submitted == []


def test_settled_rejected_purchase_counted_no_retry():
    alg = _make(execution="settled")
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()                            # cible QQQ en attente
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))                 # acquisition soumise
    assert len(alg.submitted) == 1
    alg.on_order_event(_OrderEvent(OrderStatus.INVALID, QQQ))
    assert alg.n_invalid == 1
    # Barres suivantes jusqu'a la prochaine decision -> aucun retry.
    for day in (8, 9, 10):
        alg.time = datetime(2020, 1, day, 16, 0)
        alg.on_data(_Slice([QQQ]))
    assert len(alg.submitted) == 1
    # Prochaine decision hebdomadaire : re-armement.
    alg.time = datetime(2020, 1, 13, 8, 0)
    alg.rebalance()
    assert alg._pending_target == QQQ


def test_settled_repeated_bar_and_decision_no_double_order():
    alg = _make(execution="settled")
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()                            # cible QQQ en attente
    alg.rebalance()                            # decision repetee, meme jour
    assert alg.n_switches == 1                 # non recompte
    assert alg._pending_target == QQQ
    assert alg.submitted == []
    # Barre ulterieure : acquisition une seule fois malgre barre repetee.
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))
    alg.on_data(_Slice([QQQ]))
    assert alg.submitted == [(QQQ, 1.0)]
    assert alg.acquire_count == 1


def test_settled_missing_target_bar_blocks_acquisition():
    alg = _make(execution="settled")
    alg.time = datetime(2020, 1, 6, 8, 0)
    alg.rebalance()
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([SHY]))                 # barre cible (QQQ) absente
    assert alg.submitted == []
    assert alg._pending_target == QQQ


def test_settled_cash_closes_counted():
    alg = _make(execution="settled")
    alg.time = datetime(2020, 1, 7, 16, 0)
    alg.on_data(_Slice([QQQ]))                 # portefeuille vide -> seance cash
    assert alg.cash_closes == 1
    alg.portfolio[QQQ] = _Holding(QQQ, 100.0)
    alg.on_data(_Slice([QQQ]))                 # detenu -> plus une seance cash
    assert alg.cash_closes == 1


def test_settled_runtime_statistics_present():
    alg = _make(execution="settled")
    alg.n_deferred, alg.n_canceled, alg.n_invalid = 3, 1, 2
    alg.acquire_count, alg.delay_seconds = 2, 2 * 86400.0
    alg.cash_closes = 5
    alg._pending_target = SHY
    alg.on_end_of_algorithm()
    assert alg.stats["Execution"] == "settled"
    assert alg.stats["Settled decisions differees"] == "3"
    assert alg.stats["Settled ordres annules"] == "1"
    assert alg.stats["Settled ordres invalides"] == "2"
    assert alg.stats["Settled acquisitions (soumissions)"] == "2"
    assert alg.stats["Settled seances en liquidites"] == "5"
    assert alg.stats["Settled pending target (fin)"] == "SHY"
    assert alg.stats["Settled delai decision->soumission (j)"] == "1.0"


# --------------------------------------------------------------------------
# References detenues : isolees du bras settled.
# --------------------------------------------------------------------------
def test_references_spy_isolated_from_settled_arm():
    alg = _make(mode="spy", execution="settled")
    alg.ref_symbols = {"SPY": SPY}
    alg.shadow_symbol = SPY
    alg.time = datetime(2020, 1, 2, 16, 0)
    alg.on_data(_Slice([SPY]))
    assert alg.submitted == [(SPY, 1.0)]       # reequilibrage de reference inchange
    assert alg._pending_target is None
    assert alg.acquire_count == 0
    assert alg.logs == []


def test_references_sixty40_isolated_from_settled_arm():
    alg = _make(mode="sixty40", execution="settled")
    alg.ref_symbols = {"SPY": SPY, "IEF": IEF}
    alg.shadow_symbol = SPY
    alg.time = datetime(2020, 1, 2, 16, 0)
    alg.on_data(_Slice([SPY]))
    assert alg.submitted == [(SPY, 0.6), (IEF, 0.4)]
    assert alg._pending_target is None
    assert alg.acquire_count == 0


if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-v"]))
