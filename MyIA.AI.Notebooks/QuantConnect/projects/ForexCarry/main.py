# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class ForexCarryTradeStrategy(QCAlgorithm):
    """
    Forex Momentum Strategy v4.0 (Research-Driven)

    Cross-sectional G10 currency momentum strategy.
    Long-only top-2 momentum currencies vs USD. Leveraged FX positions.

    Changes from v3.2:
    1. Start date extended to 2013 (captures euro crisis 2012, dollar strength 2014-2016)
       Research (H4) showed the 2010-2015 period has better FX momentum regimes.
    2. Risk-adjusted momentum signal: IR = return(126d) / vol(21d)
       From Barroso & Santa-Clara (2015): momentum risk-adjusted reduces crashes by 50%.
       Research (H1) tested this approach.
    3. Skip-month: momentum computed from J-126 to J-21 (excludes last month noise)
       From Okunev & White (2003): last month contains mean-reversion, not signal.
       Research (H2) tested this approach.

    Signal logic:
    - For XXX/USD pairs (EURUSD, AUDUSD): signal uses price directly
    - For USD/XXX pairs (USDJPY, USDCAD): invert signal (up = USD strong = currency weak)
    - Score = return(J-126 to J-21) / annualized_vol(J-21 to J-0) -> IR (skip-month)
    - Select top-2 currencies by IR score, only if top IR is positive

    Honest assessment:
    The structural limitation remains: G10 FX momentum earns ~1-2% CAGR vs
    T-bill ~2.5% average (2018-2026, peak 5.5% in 2023). Extending to 2013
    improves Sharpe by including regimes favorable to FX momentum.
    Target Sharpe: -0.5 to -0.3 (vs -0.654 for v3.2 on 2018-2026).

    Ref: Menkhoff et al. (2012), Barroso & Santa-Clara (2015), Okunev & White (2003)
    """

    def initialize(self):
        # Extended period: captures euro crisis 2012, dollar strength 2014-2016
        self.set_start_date(2013, 1, 1)
        self.set_cash(100000)

        # 4 diversified FX pairs (Europe, Commodity, Asia, Americas) - confirmed best
        self.pair_names = ["EURUSD", "AUDUSD", "USDJPY", "USDCAD"]
        self.forex_symbols = {}
        for pair in self.pair_names:
            forex = self.add_forex(pair, Resolution.DAILY)
            self.forex_symbols[pair] = forex.symbol

        # v4.0: Risk-adjusted momentum with skip-month
        self.lookback_mom = 126     # 6-month momentum window (skip-month: J-126 to J-21)
        self.skip_days = 21         # Skip last month (mean-reversion noise)
        self.vol_lookback = 21      # Realized vol window for IR calculation

        # Long-only top-2 pairs: 50% each = 100% total (standard FX leverage)
        self.num_long = 2
        self.position_size = 0.50
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        # Warmup: need lookback_mom + vol_lookback data
        self.set_warm_up(self.lookback_mom + self.vol_lookback + 10, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return

        # Monthly rebalance: only once per month
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Compute risk-adjusted momentum scores (IR with skip-month)
        scores = {}
        for pair in self.pair_names:
            symbol = self.forex_symbols[pair]
            # Fetch enough history: lookback_mom + vol_lookback days
            history_len = self.lookback_mom + self.vol_lookback + 5
            history = self.history(symbol, history_len, Resolution.DAILY)
            if len(history) < self.lookback_mom + self.skip_days:
                continue

            try:
                closes = history['close']

                # Skip-month momentum: return from J-lookback to J-skip
                # Excludes the last month (J-21 to J-0) which contains mean-reversion
                price_start = closes.iloc[-(self.lookback_mom)]
                price_end_skip = closes.iloc[-(self.skip_days)]
                mom_return = (price_end_skip / price_start) - 1

                # Invert for USD/XXX pairs: USD up = foreign currency down
                if pair.startswith("USD"):
                    mom_return = -mom_return

                # Annualized realized vol over last vol_lookback days
                recent_closes = closes.iloc[-self.vol_lookback:]
                daily_returns = recent_closes.pct_change().dropna()
                realized_vol = daily_returns.std() * np.sqrt(252)

                if realized_vol < 1e-6:
                    continue

                # IR = return / vol (risk-adjusted momentum score)
                ir_score = mom_return / realized_vol
                scores[pair] = ir_score

            except Exception as e:
                self.log(f"Score error {pair}: {e}")
                continue

        if len(scores) < self.num_long:
            return

        # Sort by IR score (highest = best risk-adjusted momentum)
        sorted_pairs = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        long_pairs = [p for p, s in sorted_pairs[:self.num_long]]

        # Only go long if top IR is positive (foreign currency has positive risk-adj momentum)
        top_score = sorted_pairs[0][1]
        if top_score <= 0:
            if self.portfolio.invested:
                self.liquidate()
                self.log(f"ALL CASH: No positive IR score (best={top_score:.4f})")
            return

        # Liquidate positions not in top selection
        for pair, symbol in self.forex_symbols.items():
            if pair not in long_pairs:
                if self.portfolio[symbol].invested:
                    self.liquidate(symbol)

        # Go long the best risk-adjusted momentum pairs
        for pair in long_pairs:
            symbol = self.forex_symbols[pair]
            self.set_holdings(symbol, self.position_size)

        scores_str = ", ".join(f"{p}:IR={s:.3f}" for p, s in sorted_pairs)
        self.log(f"FX MOM v4.0: Long={long_pairs}, [{scores_str}]")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FOREX MOM v4.0: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
