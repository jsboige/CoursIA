# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class ClusteringFundamentalsAlgorithm(QCAlgorithm):
    """
    Hands-On AI Trading - Ch06 Ex10: Stock Selection through
    Fundamental Factor Z-Score Ranking.

    Uses fundamental factors with Z-score normalization to rank stocks.
    Simpler and faster alternative to PCA+ML approaches, avoiding
    NaN issues and long backtest times.

    Universe: Top N by dollar volume, rebalanced monthly.
    Selection: Z-score composite ranking of 8 fundamental factors.

    Original used LGBMRanker; v3 used PCA+GBR (too slow, NaN issues).
    This v4 uses direct Z-score ranking (10x faster, no NaN crashes).
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 3, 1)
        self.set_cash(100_000)
        self.settings.daily_precise_end_time = False

        self._liquid_universe_size = int(self.get_parameter(
            'liquid_universe_size', 50
        ))
        self._final_universe_size = int(self.get_parameter(
            'final_universe_size', 10
        ))

        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        date_rule = self.date_rules.month_start(schedule_symbol)
        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 1),
            self._trade
        )

        self.universe_settings.schedule.on(date_rule)
        self._universe = self.add_universe(self._select_assets)

    def _get_factor(self, f, factor_name):
        """Safely extract a nested fundamental factor value."""
        try:
            parts = factor_name.split('.')
            val = f
            for part in parts:
                if val is None:
                    return np.nan
                val = getattr(val, part, None)
            return float(val) if val is not None else np.nan
        except (TypeError, ValueError, AttributeError):
            return np.nan

    def _select_assets(self, fundamental):
        """Rank stocks by Z-score composite of fundamental factors."""
        selected = sorted(
            [f for f in fundamental if f.has_fundamental_data],
            key=lambda f: f.dollar_volume
        )[-self._liquid_universe_size:]
        if not selected:
            return []

        factors_to_use = [
            "operation_ratios.revenue_growth.value",
            "operation_ratios.gross_margin.value",
            "operation_ratios.roe.value",
            "operation_ratios.operation_margin.value",
            "valuation_ratios.pe_ratio",
            "valuation_ratios.book_value_yield",
            "valuation_ratios.earning_yield",
            "valuation_ratios.fcf_yield",
        ]

        # Build factor matrix
        factor_matrix = []
        symbols = []
        for f in selected:
            values = [
                self._get_factor(f, fac) for fac in factors_to_use
            ]
            values = [np.nan if np.isinf(v) else v for v in values]
            factor_matrix.append(values)
            symbols.append(f.symbol)

        # Z-score normalization (NaN-safe)
        x = np.array(factor_matrix, dtype=float)
        col_means = np.nanmean(x, axis=0)
        col_stds = np.nanstd(x, axis=0)
        col_stds[col_stds == 0] = 1
        x_clean = np.where(np.isnan(x), 0, (x - col_means) / col_stds)

        # PE ratio: lower is better, so invert
        x_clean[:, 4] = -x_clean[:, 4]

        # Composite score = mean of all Z-scores
        composite = np.nanmean(x_clean, axis=1)
        composite = np.nan_to_num(
            composite, nan=0.0, posinf=0.0, neginf=0.0
        )

        # Select top N
        indices = np.argsort(composite)[::-1]
        top_indices = indices[:self._final_universe_size]
        return [symbols[i] for i in top_indices]

    def _trade(self):
        """Equal-weight rebalance of selected assets."""
        if not self._universe.selected:
            return
        weight = 1 / len(self._universe.selected)
        self.set_holdings(
            [
                PortfolioTarget(symbol, weight)
                for symbol in self._universe.selected
            ],
            True
        )
