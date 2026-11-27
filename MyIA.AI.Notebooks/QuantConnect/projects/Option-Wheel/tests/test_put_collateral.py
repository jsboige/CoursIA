"""Tests unitaires du dimensionnement des puts, sans moteur LEAN."""

import importlib.util
import sys
from collections import namedtuple
from pathlib import Path
from types import ModuleType, SimpleNamespace
from unittest.mock import patch

import pytest

ContractId = namedtuple("ContractId", "StrikePrice OptionRight")
Contract = namedtuple("Contract", "ID")


class Portfolio(dict):
    Cash = 1_000_000
    MarginRemaining = 1_000_000
    TotalPortfolioValue = 1_000_000
    Invested = False


@pytest.fixture
def wheel():
    imports = ModuleType("AlgorithmImports")
    imports.QCAlgorithm = object
    imports.Symbol = Contract
    # AlgorithmImports expose aussi System.Decimal dans LEAN.
    imports.Decimal = object
    imports.OptionRight = SimpleNamespace(PUT="put", CALL="call")
    imports.SecurityType = SimpleNamespace(Option="option")
    source = Path(__file__).resolve().parents[1] / "main.py"
    spec = importlib.util.spec_from_file_location("wheel_collateral_main", source)
    module = importlib.util.module_from_spec(spec)
    with patch.dict(sys.modules, {"AlgorithmImports": imports}):
        spec.loader.exec_module(module)
    algo = module.WheelStrategyAlgorithm()
    algo.Portfolio = Portfolio()
    algo.Securities = {}
    algo.max_exposure_fraction = 0.8
    algo.disable_margin = True
    return algo


def contract(algo, strike, right="put", multiplier=100):
    symbol = Contract(ContractId(strike, right))
    algo.Securities[symbol] = SimpleNamespace(
        SymbolProperties=SimpleNamespace(ContractMultiplier=multiplier)
    )
    return symbol


@pytest.mark.parametrize(
    ("cash", "margin", "strike", "multiplier", "quantity"),
    [
        (1_000_000, 1_000_000, 520, 100, 15),
        (104_000, 1_000_000, 520, 100, 2),
        (103_999, 1_000_000, 520, 100, 1),
        (1_000_000, 51_999, 520, 100, 0),
        (1_000_000, 1_000_000, 520, 50, 30),
    ],
)
def test_quantity_bounded_by_cash_and_exposure(wheel, cash, margin, strike, multiplier, quantity):
    wheel.Portfolio.Cash = cash
    wheel.Portfolio.MarginRemaining = margin
    assert wheel._put_quantity(contract(wheel, strike, multiplier=multiplier)) == quantity


def test_only_short_puts_reserve_put_collateral(wheel):
    for strike, right, quantity in [(500, "put", -2), (530, "put", 1), (540, "call", -1)]:
        wheel.Portfolio[contract(wheel, strike, right)] = SimpleNamespace(
            Quantity=quantity, Type="option"
        )
    assert wheel._put_quantity(contract(wheel, 520)) == 13
    wheel.Portfolio.Cash = 150_000
    assert wheel._put_quantity(contract(wheel, 520)) == 0


@pytest.mark.parametrize(("cash", "orders"), [(51_999, []), (1_000_000, [-15])])
def test_put_submission_uses_computed_quantity(wheel, cash, orders):
    symbol = contract(wheel, 520)
    submitted = []
    wheel.Portfolio.Cash = cash
    wheel._vix_value = None
    wheel._equity = SimpleNamespace(Symbol="SPY", Price=550)
    wheel.otm_threshold = 0.05
    wheel.IsMarketOpen = lambda _: True
    wheel._get_target_contract = lambda *_: symbol
    wheel.log_portfolio_state = lambda *_: None
    wheel.MarketOrder = lambda _, quantity: submitted.append(quantity)
    wheel.OnData(None)
    assert submitted == orders
