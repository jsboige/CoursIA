# region imports
from AlgorithmImports import *
import numpy as np
# endregion


class ForexCarryTradeStrategy(QCAlgorithm):
    """
    Forex Momentum + Risk Filter Strategy v2

    Pure FX momentum (3+12 month composite) with SPY risk-on/off filter.
    Goes long high-momentum currencies vs USD, short low-momentum.
    Cash when SPY below SMA200 (risk-off).

    Ref: Menkhoff et al. (2012), Asness et al. (2013)
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
        self.set_cash(100000)

        # FX pairs vs USD
        self.pair_names = ["EURUSD", "GBPUSD", "AUDUSD", "NZDUSD", "USDCAD", "USDJPY", "USDCHF"]
        self.forex_symbols = {}
        for pair in self.pair_names:
            forex = self.add_forex(pair, Resolution.DAILY)
            self.forex_symbols[pair] = forex.symbol

        # Risk filter: SPY
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.spy_sma = self.sma(self.spy, 200, Resolution.DAILY)

        # Parametres
        self.lookback_short = 63   # 3 mois
        self.lookback_long = 252   # 12 mois
        self.num_long = 2
        self.num_short = 2
        self.position_size = 0.15  # 15% par paire
        self.rebalance_month = -1

        self.set_benchmark("SPY")
        self.set_warm_up(self.lookback_long + 10, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not self.spy_sma.is_ready:
            return

        # Rebalancement mensuel
        if self.time.month == self.rebalance_month:
            return
        self.rebalance_month = self.time.month

        # Risk filter: cash si SPY < SMA200
        spy_above_sma = self.securities[self.spy].price > self.spy_sma.current.value
        if not spy_above_sma:
            if self.portfolio.invested:
                self.liquidate()
                self.log(f"RISK OFF: SPY < SMA200, all cash")
            return

        # Calculer les scores momentum composites
        scores = {}
        for pair in self.pair_names:
            symbol = self.forex_symbols[pair]
            history = self.history(symbol, self.lookback_long, Resolution.DAILY)
            if len(history) < self.lookback_long:
                continue

            try:
                closes = history['close']
                current = closes.iloc[-1]
                # Momentum 3 mois (poids 60%)
                mom_3m = (current / closes.iloc[-self.lookback_short]) - 1
                # Momentum 12 mois (poids 40%)
                mom_12m = (current / closes.iloc[0]) - 1

                # Pour les paires USD/XXX, inverser le signe
                # (hausse = USD fort = devise faible)
                if pair.startswith("USD"):
                    mom_3m = -mom_3m
                    mom_12m = -mom_12m

                score = mom_3m * 0.6 + mom_12m * 0.4
                scores[pair] = score
            except:
                continue

        if len(scores) < self.num_long + self.num_short:
            return

        # Trier par score
        sorted_pairs = sorted(scores.items(), key=lambda x: x[1], reverse=True)

        long_pairs = [p for p, s in sorted_pairs[:self.num_long]]
        short_pairs = [p for p, s in sorted_pairs[-self.num_short:]]

        # Liquider positions non selectionnees
        for pair, symbol in self.forex_symbols.items():
            if pair not in long_pairs and pair not in short_pairs:
                if self.portfolio[symbol].invested:
                    self.liquidate(symbol)

        # Appliquer
        for pair in long_pairs:
            symbol = self.forex_symbols[pair]
            self.set_holdings(symbol, self.position_size)

        for pair in short_pairs:
            symbol = self.forex_symbols[pair]
            self.set_holdings(symbol, -self.position_size)

        self.log(f"FX MOM: Long={long_pairs}, Short={short_pairs}")

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"FOREX MOMENTUM v2: Final=${final:,.2f}, Return={(final-100000)/100000:.2%}")
