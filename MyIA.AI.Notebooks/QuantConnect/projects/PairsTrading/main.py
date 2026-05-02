# region imports
from AlgorithmImports import *
import numpy as np
from scipy import stats
import pandas as pd
# endregion


class PairsTrading(QCAlgorithm):
    """
    Pairs Trading Strategy (Statistical Arbitrage)
    ================================================
    Edge: Exploit mean-reversion in cointegrated ETF pairs
    Reference: Gatev, Goetzmann & Rouwenhorst (2006), Vidyamurthy (2004)

    Mechanism:
    1. Track spread between cointegrated ETF pairs
    2. Compute rolling z-score of the spread
    3. Entry: z-score > 2 or < -2 (spread deviated significantly)
    4. Exit: z-score crosses 0 (spread reverted to mean)
    5. Stop-loss: z-score > 4 (spread blowout, cointegration broken)

    Pairs (selected for structural cointegration):
    - XLF/XLK: Financials vs Technology (sector pair)
    - GLD/GDX: Gold vs Gold Miners (commodity chain)
    - EWA/EWC: Australia vs Canada (commodity-linked economies)

    Signal:
    - Long the underperformer, short the overperformer
    - Equal dollar-neutral positions
    - Rolling 60-day window for z-score

    Backtest: 2010-2026
    Expected Sharpe: 0.5-1.0 (depends on cointegration stability)
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        # Define pairs
        self.pair_configs = [
            {"long": "XLF", "short": "XLK", "name": "Financials-Tech"},
            {"long": "GLD", "short": "GDX", "name": "Gold-Miners"},
            {"long": "EWA", "short": "EWC", "name": "Australia-Canada"},
        ]

        # Add all symbols
        self.symbols = {}
        all_tickers = set()
        for pair in self.pair_configs:
            all_tickers.add(pair["long"])
            all_tickers.add(pair["short"])

        for ticker in all_tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.set_data_normalization_mode(DataNormalizationMode.ADJUSTED)
            self.symbols[ticker] = equity.symbol

        # Parameters
        self.lookback = 60             # Rolling window for z-score
        self.entry_zscore = 2.0        # Entry threshold
        self.exit_zscore = 0.0         # Exit threshold (mean reversion)
        self.stop_zscore = 4.0         # Stop-loss threshold
        self.weight_per_pair = 0.15    # 15% per leg per pair (30% per pair)

        # Track active positions
        self.active_trades = {i: None for i in range(len(self.pair_configs))}

        # Daily check
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("XLF", 30),
            self.check_pairs
        )

        self.set_warmup(self.lookback + 30, Resolution.DAILY)

    def compute_spread_zscore(self, pair_config):
        long_sym = self.symbols[pair_config["long"]]
        short_sym = self.symbols[pair_config["short"]]

        history = self.history(
            [long_sym, short_sym],
            self.lookback + 5,
            Resolution.DAILY
        )

        if history.empty:
            return None, None

        try:
            long_prices = history.loc[long_sym]["close"]
            short_prices = history.loc[short_sym]["close"]
        except (KeyError, TypeError):
            return None, None

        # Align on common dates to avoid shape mismatch
        common_idx = long_prices.index.intersection(short_prices.index)
        long_prices = long_prices.loc[common_idx]
        short_prices = short_prices.loc[common_idx]

        if len(long_prices) < self.lookback or len(short_prices) < self.lookback:
            return None, None

        # Log price ratio as spread
        spread = np.log(long_prices.values) - np.log(short_prices.values)

        # Rolling z-score
        spread_mean = np.mean(spread[-self.lookback:])
        spread_std = np.std(spread[-self.lookback:])

        if spread_std < 1e-8:
            return None, None

        current_zscore = (spread[-1] - spread_mean) / spread_std

        return current_zscore, spread_std

    def check_pairs(self):
        if self.is_warming_up:
            return

        for i, pair in enumerate(self.pair_configs):
            zscore, spread_vol = self.compute_spread_zscore(pair)

            if zscore is None:
                continue

            long_sym = self.symbols[pair["long"]]
            short_sym = self.symbols[pair["short"]]

            if self.active_trades[i] is None:
                # No position: check for entry
                if zscore > self.entry_zscore:
                    # Spread too high: short the spread (short long, buy short)
                    self.set_holdings(long_sym, -self.weight_per_pair)
                    self.set_holdings(short_sym, self.weight_per_pair)
                    self.active_trades[i] = "short_spread"
                    self.debug(f"{pair['name']}: SHORT spread (z={zscore:.2f})")

                elif zscore < -self.entry_zscore:
                    # Spread too low: long the spread (buy long, short short)
                    self.set_holdings(long_sym, self.weight_per_pair)
                    self.set_holdings(short_sym, -self.weight_per_pair)
                    self.active_trades[i] = "long_spread"
                    self.debug(f"{pair['name']}: LONG spread (z={zscore:.2f})")

            else:
                # Have position: check for exit or stop
                trade_dir = self.active_trades[i]

                should_exit = False

                # Exit: z-score reverted to mean
                if trade_dir == "short_spread" and zscore <= self.exit_zscore:
                    should_exit = True
                elif trade_dir == "long_spread" and zscore >= self.exit_zscore:
                    should_exit = True

                # Stop-loss: spread blowout
                if abs(zscore) > self.stop_zscore:
                    should_exit = True
                    self.debug(f"{pair['name']}: STOP-LOSS (z={zscore:.2f})")

                if should_exit:
                    self.liquidate(long_sym)
                    self.liquidate(short_sym)
                    self.active_trades[i] = None
                    self.debug(f"{pair['name']}: EXIT (z={zscore:.2f})")

    def on_data(self, data):
        pass
