from AlgorithmImports import *

class TrendFilteredMeanReversion(QCAlgorithm):
    """
    Trend-Filtered Mean Reversion v1.0 (current best: MaxDD 11.4%)

    Buy short-term pullbacks in a confirmed uptrend.
    Edge: RSI(2) extreme oversold in bull regime = high probability bounce.

    Rules:
    - Regime: SPY > SMA200 (bull market only)
    - Entry: RSI(2) < 10
    - Exit: Close > SMA5 OR RSI(2) > 70 OR 5-day time stop
    - Position: 100% SPY

    Reference: Connolly & Rapach (2008), Larry Connors RSI(2) strategy

    Résultats mesurés (ce fichier, v1.0, fenêtre codée 2015-01-01 -> 2024-12-31) :
    backtest QC Cloud du 2026-11-12, projet 39308942, backtest 05c344893b49fb8f28b303efb85f14cb,
    modèle de courtage déclaré ci-dessous (frais inclus), journalier.
      Sharpe -0 (QC arrondit au millième : valeur négative, inférieure à 0.0005 en valeur absolue),
      CAGR 2.99 %, MaxDD 11.4 %, PSR 0.006 %, beta 0.112, volatilité annuelle 4.9 %.
      84 trades clos (8.4 par an), taux de réussite 70.2 % (59/84), gain moyen 1.16 %,
      perte moyenne -1.52 %, durée moyenne 4.4 jours, position ouverte ~10 % des jours calendaires.
    Témoin SPY achat-conservation, même fenêtre et même modèle de courtage (projet 39308949) :
      Sharpe 0.535, CAGR 12.99 %, MaxDD 33.5 %, PSR 3.08 %.

    Historique (chiffres non datés et sans projet cité, annoncés sur « 2015-2026 », non re-mesurés) :
    v1.0: RSI(2) < 10, SPY only         - Sharpe -0.016, CAGR 3.4%, MaxDD 11.4%, ~9 trades/yr (BEST)
    v2.0: RSI(2) < 20, SPY only         - Sharpe -0.002, CAGR 3.4%, MaxDD 16.2%, ~31 trades/yr (too many)
    v3.0: RSI(3) < 15, SPY only         - Sharpe -0.050, CAGR 3.2%, MaxDD 10.3%, ~12 trades/yr
    v4.0: RSI(2) < 10, SPY+QQQ+IWM     - Sharpe -0.129, CAGR 2.7%, MaxDD 14.4%, 550 trades REJECTED

    Root cause: the strategy is out of the market ~90% of the time (measured above).
    Cash drag vs risk-free rate = Sharpe at zero despite a positive CAGR.
    H4 FAILED: QQQ+IWM added noise, 550 trades (too many), Sharpe degraded from -0.016 to -0.129.
    Structural ceiling: RSI(2)<10 mean reversion on ETFs has too few quality signals in bull market.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)

        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.set_benchmark(self.spy)

        # Indicators
        self.sma200 = self.sma(self.spy, 200, Resolution.DAILY)
        self.sma5 = self.sma(self.spy, 5, Resolution.DAILY)
        self.rsi2 = self.rsi(self.spy, 2)

        # Position tracking
        self.entry_day = 0
        self.day_count = 0
        self.time_stop = 5

        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.set_warm_up(200, Resolution.DAILY)

    def on_data(self, data):
        if self.is_warming_up:
            return
        if not data.contains_key(self.spy):
            return

        self.day_count += 1

        price = self.securities[self.spy].price
        in_bull = price > self.sma200.current.value
        rsi_val = self.rsi2.current.value

        # Exit logic (check first to allow same-bar exit and re-entry)
        if self.portfolio[self.spy].invested:
            days_held = self.day_count - self.entry_day
            should_exit = (
                price > self.sma5.current.value or
                rsi_val > 70 or
                days_held >= self.time_stop
            )
            if should_exit:
                self.liquidate(self.spy)
                self.log(f"EXIT: RSI(2)={rsi_val:.1f}, Price={price:.2f}, DaysHeld={days_held}")
                return

        # Entry logic: bull regime + extreme oversold
        if not self.portfolio[self.spy].invested:
            if in_bull and rsi_val < 10:
                self.set_holdings(self.spy, 1.0)
                self.entry_day = self.day_count
                self.log(f"ENTRY: RSI(2)={rsi_val:.1f}, Price={price:.2f}")
