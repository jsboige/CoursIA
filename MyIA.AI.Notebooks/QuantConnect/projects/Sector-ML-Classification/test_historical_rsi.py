"""Témoins déterministes de la feature RSI historique, sans moteur QC simulé."""
import ast
import os
from pathlib import Path
from types import SimpleNamespace
import unittest

import numpy as np
import pandas as pd


def load_features():
    path = Path(os.environ.get("SECTOR_MAIN", Path(__file__).with_name("main.py")))
    tree = ast.parse(path.read_text(encoding="utf-8"))
    cls = next(node for node in tree.body if isinstance(node, ast.ClassDef))
    method = next(node for node in cls.body
                  if isinstance(node, ast.FunctionDef)
                  and node.name == "get_features_historical")
    module = ast.Module(body=[method], type_ignores=[])
    namespace = {"np": np, "pd": pd}
    exec(compile(ast.fix_missing_locations(module), str(path), "exec"), namespace)
    return namespace[method.name]


class HistoricalRsiTests(unittest.TestCase):
    def setUp(self):
        self.features = load_features()
        self.owner = SimpleNamespace(SMA_LONG=50, SMA_SHORT=20)
        self.dates = pd.date_range("2020-01-01", periods=80)

    def evaluate(self, values, date=None):
        prices = pd.Series(values, index=self.dates)
        spy = pd.Series(np.arange(100.0, 180.0), index=self.dates)
        return self.features(self.owner, prices, spy, date or self.dates[-1])

    def test_rising_prices(self):
        self.assertAlmostEqual(self.evaluate(np.arange(100.0, 180.0))[5], 1.0)

    def test_falling_prices(self):
        self.assertAlmostEqual(self.evaluate(np.arange(180.0, 100.0, -1))[5], -1.0)

    def test_flat_prices_use_neutral_convention(self):
        self.assertAlmostEqual(self.evaluate(np.full(80, 100.0))[5], 0.0)

    def test_balanced_gains_and_losses(self):
        values = 100 + np.arange(80) % 2
        self.assertAlmostEqual(self.evaluate(values)[5], 0.0)

    def test_unequal_gains_and_losses(self):
        # Sept hausses de 2 et sept baisses de 1 : RSI = 100 * 2 / 3.
        changes = np.tile([2.0, -1.0], 40)
        values = 100 + np.cumsum(changes)
        self.assertAlmostEqual(self.evaluate(values)[5], 1.0 / 3.0)

    def test_future_prices_do_not_change_features(self):
        values = np.arange(100.0, 180.0)
        cutoff = self.dates[59]
        before = self.evaluate(values, cutoff)
        values[60:] = np.arange(20) * 1000.0 + 1
        np.testing.assert_allclose(before, self.evaluate(values, cutoff))

    def test_bounded_finite_rsi(self):
        rng = np.random.default_rng(42)
        for _ in range(30):
            values = 100 * np.exp(np.cumsum(rng.normal(0, 0.02, 80)))
            result = self.evaluate(values)
            self.assertEqual(len(result), 11)
            self.assertTrue(np.isfinite(result).all())
            self.assertGreaterEqual(result[5], -1.0)
            self.assertLessEqual(result[5], 1.0)


if __name__ == "__main__":
    unittest.main()
