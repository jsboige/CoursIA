"""Integration test: verify the corrected backtest_pairs_trading function
from MyIA.AI.Notebooks/QuantConnect/projects/ETF-Pairs/quantbook.ipynb produces
plausible metrics (CAGR, Vol, Sharpe) on synthetic data.

This is the test that would have caught the bug fixed in PR for issue #20355:
the original code produced CAGR=1094%, Vol=4.2e7%, Sharpe=0.000 because
- cash was never debited at position entry
- cum_returns held absolute portfolio values instead of cumulative returns

The corrected function:
- normalizes cash/notional as a ratio (1.0 = 100% of initial portfolio)
- debits engaged notional at entry, credits notional + P&L at exit
- computes cum_returns from daily returns via (1+r).cumprod()
- returns ratio-scale metrics: CAGR, Vol, Sharpe, MaxDD, final_value

Run from repo root:
    python tests/integration/test_etf_pairs_backtest.py
"""
import json
import sys
import unittest
import warnings
from pathlib import Path

import numpy as np
import pandas as pd

warnings.filterwarnings('ignore')

REPO_ROOT = Path(__file__).resolve().parents[2]
NB_PATH = REPO_ROOT / 'MyIA.AI.Notebooks' / 'QuantConnect' / 'projects' / 'ETF-Pairs' / 'quantbook.ipynb'


def extract_function(nb_path: Path) -> str:
    """Extract backtest_pairs_trading function source from cell 10 of the notebook."""
    nb = json.load(open(nb_path, 'r', encoding='utf-8'))
    cell = nb['cells'][10]
    src = ''.join(cell['source']) if isinstance(cell['source'], list) else cell['source']
    end = src.find('# Sélectionner les top 3 paires')
    if end < 0:
        raise ValueError('Cannot find function end marker in cell 10')
    return src[:end]


def make_synthetic_closes(n_days: int = 1260, seed: int = 123) -> pd.DataFrame:
    """Build synthetic cointegrated ETF-like daily prices."""
    np.random.seed(seed)
    dates = pd.bdate_range('2021-01-01', periods=n_days)

    ret1 = np.random.normal(0.0003, 0.012, n_days)
    etf1 = pd.Series(100 * (1 + pd.Series(ret1)).cumprod(), index=dates)
    hedge = 0.5
    noise = np.zeros(n_days)
    for i in range(1, n_days):
        noise[i] = 0.85 * noise[i - 1] + np.random.normal(0, 2.0)
    etf2 = pd.Series(hedge * etf1 + noise, index=dates)

    qqq = pd.Series(100 * (1 + pd.Series(np.random.normal(0.0004, 0.018, n_days))).cumprod(), index=dates)
    iwm = pd.Series(100 * (1 + pd.Series(np.random.normal(0.0002, 0.016, n_days))).cumprod(), index=dates)
    efa = pd.Series(100 * (1 + pd.Series(np.random.normal(0.0002, 0.013, n_days))).cumprod(), index=dates)
    agg = pd.Series(100 * (1 + pd.Series(np.random.normal(0.0001, 0.004, n_days))).cumprod(), index=dates)

    return pd.DataFrame({
        'ETF1': etf1, 'ETF2': etf2, 'QQQ': qqq, 'IWM': iwm, 'EFA': efa, 'AGG': agg,
    })


def make_fake_pairs_results(closes: pd.DataFrame) -> list:
    """Pretend Engle-Granger found these as cointegrated."""
    return [
        {'pair': 'ETF2-ETF1', 'pvalue': 0.001, 'hedge_ratio': 0.5, 'half_life': 15, 'correlation': 0.85},
        {'pair': 'AGG-ETF1', 'pvalue': 0.002, 'hedge_ratio': -0.3, 'half_life': 45, 'correlation': -0.3},
        {'pair': 'QQQ-IWM', 'pvalue': 0.003, 'hedge_ratio': 0.6, 'half_life': 50, 'correlation': 0.7},
    ]


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


class TestBacktestAccounting(unittest.TestCase):

    def test_function_source_has_no_cash_dollar_literal(self):
        self.assertRegex(func_src, r'cash\s*=\s*1\.0\b', 'cash must be normalized to ratio 1.0')
        self.assertNotRegex(func_src, r'cash\s*=\s*1_000_000', 'cash must not be 1M dollars')
        self.assertRegex(func_src, r'notional\s*=\s*0\.0[0-9]', 'notional must be a small ratio (e.g. 0.05)')

    def test_function_debits_cash_at_entry(self):
        # Le debit cash ne porte que sur la jambe longue (la short est
        # financee par le produit de la vente) -- c'est la correction du
        # bug mark-to-market du short : ne pas immobiliser 2x le notionnel
        # a l'entree d'une paire (une jambe longue + une jambe short).
        self.assertRegex(
            func_src,
            r'cash\s*-=\s*cash_debit',
            'cash must be debited by cash_debit (long leg only) at position entry',
        )

    def test_function_credits_notional_plus_pnl_at_exit(self):
        self.assertRegex(func_src, r'cash\s*\+=\s*\S*cost\S*', 'cash must be credited notional at exit')

    def test_function_long_leg_only_cash_debit(self):
        # Le debit cash a l'entree = |qty_long * price_long| UNIQUEMENT,
        # pas |qty|*price| des deux jambes (ce qui immobiliserait 2x le
        # notionnel et creuserait le portefeuille de ~10% par paire).
        self.assertIn('cash_debit = abs(qty1 * current_prices[etf1])', func_src)
        self.assertIn('cash_debit = abs(qty2 * current_prices[etf2])', func_src)

    def test_function_computes_cum_returns_as_cumprod(self):
        self.assertIn('.cumprod()', func_src, 'cum_returns must be computed via .cumprod()')

    def test_metrics_are_plausible(self):
        closes = make_synthetic_closes()
        pairs = make_fake_pairs_results(closes)
        result = backtest_pairs_trading(closes, pairs)

        # The original bug produced CAGR=1094%, Vol=4.2e7%, Sharpe=0.000.
        self.assertLess(abs(result['cagr']), 1.0, f'CAGR {result["cagr"]:.1%} is absurd (>= 100%)')
        self.assertGreaterEqual(result['vol'], 0.0, f'Vol {result["vol"]:.1%} cannot be negative')
        self.assertLess(result['vol'], 5.0, f'Vol {result["vol"]:.1%} is absurd (>= 500%)')
        self.assertGreater(result['final_value'], 0.0, f'final_value {result["final_value"]} must be > 0')
        self.assertLess(result['final_value'], 100.0, f'final_value {result["final_value"]} is absurd (>= 100x)')
        self.assertTrue(np.isfinite(result['sharpe']), f'Sharpe {result["sharpe"]} must be finite')


if __name__ == '__main__':
    unittest.main(verbosity=2)
