"""Integration test: verify the accounting of backtest_pairs_trading
from MyIA.AI.Notebooks/QuantConnect/projects/ETF-Pairs/quantbook.ipynb
on synthetic data where the strategy actually trades (issue #20355).

The function is extracted from cell 10 of the notebook and executed as is.
The tests check behaviour, not source text:

- the portfolio value does not jump on the day a pair is opened
  (signed accounting: the long leg debits cash, the short sale credits it);
- a round trip leaves cash equal to the initial capital plus the realized
  P&L of both legs, with no phantom credit of the short notional;
- the ETF2 leg carries -hedge_ratio times the ETF1 quantity, so the
  position follows the spread ETF1 - hr * ETF2;
- on a mean-reverting synthetic spread the backtest opens trades and
  returns finite, plausible ratio-scale metrics.

Run from repo root:
    python -m pytest tests/integration/test_etf_pairs_backtest.py -q
"""
import json
import unittest
import warnings
from pathlib import Path

import numpy as np
import pandas as pd

warnings.filterwarnings('ignore')

REPO_ROOT = Path(__file__).resolve().parents[2]
NB_PATH = REPO_ROOT / 'MyIA.AI.Notebooks' / 'QuantConnect' / 'projects' / 'ETF-Pairs' / 'quantbook.ipynb'

LOOKBACK = 50
WARMUP = LOOKBACK + 50


def extract_function(nb_path: Path) -> str:
    """Extract backtest_pairs_trading function source from cell 10 of the notebook."""
    nb = json.load(open(nb_path, 'r', encoding='utf-8'))
    cell = nb['cells'][10]
    src = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
    end = src.find('# Sélectionner les top 3 paires')
    if end < 0:
        raise ValueError('Cannot find function end marker in cell 10')
    return src[:end]


def make_mean_reverting_closes(n_days: int = 1000, seed: int = 7, hedge: float = 0.5) -> pd.DataFrame:
    """Two prices whose spread A - hedge * B is a strongly mean-reverting AR(1)."""
    rng = np.random.default_rng(seed)
    dates = pd.bdate_range('2021-01-01', periods=n_days)
    b = 100 * np.cumprod(1 + rng.normal(0.0002, 0.01, n_days))
    noise = np.zeros(n_days)
    for i in range(1, n_days):
        noise[i] = 0.8 * noise[i - 1] + rng.normal(0, 1.5)
    a = hedge * b + 50 + noise
    return pd.DataFrame({'A': a, 'B': b}, index=dates)


def make_jump_closes(hedge: float, n_days: int = 160) -> pd.DataFrame:
    """Flat noisy prices, then one spread shock that opens a single pair, then a return to the mean.

    Day WARMUP + 5: A jumps up (z-score far above 1.5 -> short A, long B).
    Day WARMUP + 10: A comes back (|z| < 0.5 -> the pair is closed).
    B moves between entry and exit so that both legs carry a P&L.
    """
    rng = np.random.default_rng(3)
    dates = pd.bdate_range('2021-01-01', periods=n_days)
    b = 80 + rng.normal(0, 0.05, n_days)
    a = hedge * b + 40 + rng.normal(0, 0.05, n_days)
    entry, exit_ = WARMUP + 5, WARMUP + 10
    a[entry:exit_] += 3.0          # spread shock
    b[entry + 1:exit_ + 1] += 1.0  # B rises after entry: the long B leg earns
    a[entry + 1:exit_ + 1] += hedge * 1.0
    return pd.DataFrame({'A': a, 'B': b}, index=dates)


# Module-level globals (set by setUpModule)
backtest_pairs_trading = None
func_src = None


def setUpModule():
    global backtest_pairs_trading, func_src
    if not NB_PATH.exists():
        raise unittest.SkipTest(f'Notebook not found: {NB_PATH}')
    func_src = extract_function(NB_PATH)
    ns = {'np': np, 'pd': pd}
    exec(func_src, ns)
    backtest_pairs_trading = ns['backtest_pairs_trading']


def portfolio_path(result) -> np.ndarray:
    """Rebuild the portfolio value path (ratio) from the cumulative returns."""
    return np.concatenate([[1.0], result['cum'].values])


class TestBacktestAccounting(unittest.TestCase):

    def test_function_source_has_no_cash_dollar_literal(self):
        self.assertRegex(func_src, r'cash\s*=\s*1\.0\b', 'cash must be normalized to ratio 1.0')
        self.assertNotRegex(func_src, r'cash\s*=\s*1_000_000', 'cash must not be 1M dollars')
        self.assertRegex(func_src, r'notional\s*=\s*0\.0[0-9]', 'notional must be a small ratio (e.g. 0.05)')

    def test_function_computes_cum_returns_as_cumprod(self):
        self.assertIn('.cumprod()', func_src, 'cum_returns must be computed via .cumprod()')

    def test_single_round_trip_is_exact(self):
        """One pair opened and closed: no jump at entry, final value = 1 + P&L of both legs."""
        hr = 0.5
        closes = make_jump_closes(hr)
        pairs = [{'pair': 'A-B', 'hedge_ratio': hr}]
        # z_entry=4: the price noise alone never opens a pair, only the shock does.
        result = backtest_pairs_trading(closes, pairs, z_entry=4.0, lookback=LOOKBACK)
        self.assertEqual(result['n_trades'], 1, 'the shock must open exactly one pair')

        pv = portfolio_path(result)
        entry, exit_ = WARMUP + 5, WARMUP + 10
        # pv[k] is the value after day WARMUP + k - 1
        k_entry = entry - WARMUP + 1
        # No jump on the entry day: the value moves only by the (tiny) price noise
        # since the previous close, far below the 5% notional.
        self.assertLess(abs(pv[k_entry] - pv[k_entry - 1]), 0.002,
                        f'value jumped by {pv[k_entry] - pv[k_entry - 1]:+.4f} on the entry day')

        # Expected P&L, recomputed independently: short A (qty1 < 0), long B (qty2 = -hr * qty1).
        p1_in, p2_in = closes['A'].iloc[entry], closes['B'].iloc[entry]
        qty1 = -0.05 / p1_in
        qty2 = -hr * qty1
        exit_day = None
        for d in range(entry + 1, len(closes)):
            hist = closes['A'].iloc[d - LOOKBACK:d] - hr * closes['B'].iloc[d - LOOKBACK:d]
            z = (closes['A'].iloc[d] - hr * closes['B'].iloc[d] - hist.mean()) / hist.std()
            if abs(z) < 0.5:
                exit_day = d
                break
        self.assertIsNotNone(exit_day, 'the pair must be closed before the end of the series')
        self.assertGreaterEqual(exit_day, exit_ - 1)
        p1_out, p2_out = closes['A'].iloc[exit_day], closes['B'].iloc[exit_day]
        pnl = qty1 * (p1_out - p1_in) + qty2 * (p2_out - p2_in)
        self.assertAlmostEqual(result['final_value'], 1.0 + pnl, places=10,
                               msg='round trip must leave cash = 1 + realized P&L (no phantom short credit)')
        # The former accounting debited only the long leg at entry and credited the notional
        # of both legs at exit: about +5% of phantom gain per round trip. Stay far from it.
        self.assertLess(abs(result['final_value'] - 1.0), 0.03)

    def test_hedge_leg_follows_the_spread(self):
        """The ETF2 quantity is -hr times the ETF1 quantity: the position P&L is qty1 * d(spread)."""
        closes = make_mean_reverting_closes()
        # Spy on the quantities chosen at each entry, without touching the notebook.
        src_spy = func_src.replace(
            "n_trades += 1",
            "n_trades += 1\n                _spy.append((qty1, qty2))",
        )
        self.assertNotEqual(src_spy, func_src, 'n_trades increment not found in the function')
        for hr in (0.5, 2.0, -0.3):
            spy_ns = {'np': np, 'pd': pd, '_spy': []}
            exec(src_spy, spy_ns)
            spy_ns['backtest_pairs_trading'](closes, [{'pair': 'A-B', 'hedge_ratio': hr}], lookback=LOOKBACK)
            self.assertTrue(spy_ns['_spy'], f'no entry recorded for hr={hr}')
            for q1, q2 in spy_ns['_spy']:
                self.assertAlmostEqual(q2, -hr * q1, places=12,
                                       msg=f'qty2 must equal -hr * qty1 (hr={hr})')

    def test_metrics_are_plausible_with_trades(self):
        closes = make_mean_reverting_closes()
        pairs = [{'pair': 'A-B', 'hedge_ratio': 0.5}]
        result = backtest_pairs_trading(closes, pairs, lookback=LOOKBACK)

        self.assertGreater(result['n_trades'], 10, 'the mean-reverting spread must generate trades')
        pv = portfolio_path(result)
        # 5% notional on one pair: no single day may move the portfolio by more than a few percent.
        self.assertLess(np.max(np.abs(np.diff(pv))), 0.02, 'daily value jump too large: accounting artefact')
        self.assertLess(abs(result['cagr']), 0.5, f'CAGR {result["cagr"]:.1%} is implausible for 5% notional')
        self.assertGreater(result['vol'], 0.0, 'trades must produce a non-zero volatility')
        self.assertLess(result['vol'], 0.2, f'Vol {result["vol"]:.1%} is implausible for 5% notional')
        self.assertGreater(result['final_value'], 0.5)
        self.assertLess(result['final_value'], 2.0)
        self.assertTrue(np.isfinite(result['sharpe']), f'Sharpe {result["sharpe"]} must be finite')
        self.assertLessEqual(result['max_dd'], 0.0)

    def test_no_pair_gives_flat_result(self):
        """The notebook's own configuration selects no pair: the result must be flat, not an error."""
        closes = make_mean_reverting_closes()
        result = backtest_pairs_trading(closes, [], lookback=LOOKBACK)
        self.assertEqual(result['n_trades'], 0)
        self.assertEqual(result['final_value'], 1.0)
        self.assertEqual(result['sharpe'], 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
