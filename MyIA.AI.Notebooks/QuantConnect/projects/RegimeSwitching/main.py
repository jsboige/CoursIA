# region imports
from AlgorithmImports import *
import numpy as np
from datetime import datetime
# endregion


class RegimeSwitching(QCAlgorithm):
    """
    Regime-Switching Strategy (Mean-Reversion <-> Momentum)
    ========================================================
    Edge: Apply momentum in bull markets, mean-reversion in bear/sideways
    Reference: Price Action Lab (2024), Regime-Switching Factor Models

    iter3 improvements (ECE Item 4, Maisonnave concepts):
    - Anti-micro-rebalancing threshold: skip trades when position delta < 5%
    (The 3-day beta-annealing ramp and the causal forward-filter announced
    here were never implemented; removed from this list in #23221.)

    #23221 fixes (parameter `fix`, default on):
    - room: in the mean-reversion branch, the defensive basket only takes the
      room left by the risky positions targeted or kept (a risky ETF whose RSI
      is between 30 and 50 stays held). Before, GLD/IEF were added on top of
      them, up to a gross exposure of 2.0 on a margin account (1.981 measured).
    - same day: a risky ETF that exits on RSI > 50 while the basket of the day
      targets it again (SPY in a sideways regime) is no longer liquidated:
      set_holdings alone resizes it. Before, both orders filled at the same
      close and set_holdings sold the difference a second time, down to a
      short position (2018-11-30).

    iter2 improvements:
    - Monthly rebalancing + regime-change trigger (was daily -> 3428 trades)
    - IEF instead of TLT (TLT destroys value 2015-2026)
    - Risk-adjusted momentum (return/vol) instead of raw return
    - Trailing stop-loss -10% on equity positions
    - Reduced equity in sideways (30% vs 40%)

    Source: ECE student concepts (Maisonnave, Gr01 H.4b), adapted for partner course.
    Issue #238 - Integrate ECE student concepts into QC strategies.

    Universe: SPY, QQQ, IEF, GLD
    Backtest: 2015-01-01 -> 2024-12-31 (start_date / end_date parameters)
    """

    def initialize(self):
        # Protocole #23221 : `mode` choisit la strategie (defaut), une reference
        # detenue (spy : SPY 100 % ; 6040 : SPY 60 % / BND 40 %) ou le diagnostic
        # ew4 (SPY, QQQ, IEF, GLD a poids egal). `fix` : on (defaut, les deux
        # correctifs), room (place de la poche defensive seule) ou off (code
        # d'origine).
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040", "ew4"):
            raise ValueError(
                f"unknown mode parameter: {self._mode} (strategy | spy | 6040 | ew4)"
            )
        fix = self.get_parameter("fix", "on").lower()
        if fix not in ("on", "room", "off"):
            raise ValueError(f"unknown fix parameter: {fix} (on | room | off)")
        self._fix_room = fix in ("on", "room")
        self._fix_same_day = fix == "on"
        start = self.get_parameter("start_date", "2015-01-01")
        end = self.get_parameter("end_date", "2024-12-31")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Universe (IEF replaces TLT - better risk-off 2015-2026)
        self.risky = ["SPY", "QQQ"]
        self.defensive = ["IEF", "GLD"]
        self.all_tickers = self.risky + self.defensive

        self.symbols = {}
        for ticker in self.all_tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.set_data_normalization_mode(DataNormalizationMode.ADJUSTED)
            self.symbols[ticker] = equity.symbol

        # Regime detection indicators (on SPY as market proxy)
        spy_symbol = self.symbols["SPY"]
        self.sma50 = self.sma(spy_symbol, 50, Resolution.DAILY)
        self.sma200 = self.sma(spy_symbol, 200, Resolution.DAILY)

        # RSI for mean-reversion signals
        self.rsi_indicators = {}
        for ticker in self.risky:
            indicator = RelativeStrengthIndex(14, MovingAverageType.WILDERS)
            self.register_indicator(self.symbols[ticker], indicator, Resolution.DAILY)
            self.rsi_indicators[ticker] = indicator

        # Parameters
        self.momentum_lookback = 63   # 3-month momentum
        self.vol_lookback = 63        # 3-month volatility for risk-adjusted momentum
        self.rsi_oversold = 30
        self.rsi_exit = 50
        self.stop_loss_pct = -0.10    # Trailing stop-loss -10%

        # Anti-micro-rebalancing threshold (Maisonnave concept)
        self.rebalance_threshold = 0.05  # Skip trades when position delta < 5%

        self.target_weights = {}      # Last target weight sent per symbol

        # State
        self.current_regime = None
        self.last_rebalance = self.start_date
        self.equity_high_water = {}   # For trailing stop

        # BND n'est pas dans l'univers de la strategie : seul le mode 6040 l'abonne.
        self.bnd = (self.add_equity("BND", Resolution.DAILY).symbol
                    if self._mode == "6040" else None)

        if self._mode == "strategy":
            # Monthly rebalance
            self.schedule.on(
                self.date_rules.month_start("SPY", 1),
                self.time_rules.after_market_open("SPY", 30),
                self.monthly_rebalance
            )

            # Daily regime check (only triggers rebalance on regime change)
            self.schedule.on(
                self.date_rules.every_day("SPY"),
                self.time_rules.after_market_open("SPY", 31),
                self.check_regime_change
            )

            # Daily stop-loss check
            self.schedule.on(
                self.date_rules.every_day("SPY"),
                self.time_rules.after_market_open("SPY", 45),
                self.check_stop_loss
            )
        else:
            # References : meme jour et meme heure que le reequilibrage mensuel.
            self.schedule.on(
                self.date_rules.month_start("SPY", 1),
                self.time_rules.after_market_open("SPY", 30),
                self._rebalance_reference
            )

        # Trace `shadow` (#18923) : valeur du portefeuille a l'ouverture de
        # chaque seance de SPY, hors prechauffage, dans e0..e4. La meme lecture
        # mesure l'exposition brute (somme des valeurs absolues des positions
        # rapportee a la valeur du portefeuille).
        self._closes = 0
        self._gross_max = 0.0
        self._gross_max_day = ""
        self._gross_over = 0
        self._gross_months = []
        self.schedule.on(
            self.date_rules.every_day("SPY"),
            self.time_rules.after_market_open("SPY", 0),
            self._trace
        )

        self.set_warmup(210, Resolution.DAILY)

    def detect_regime(self):
        if not self.sma50.is_ready or not self.sma200.is_ready:
            return "unknown"

        spy_price = self.securities[self.symbols["SPY"]].price
        sma50_val = self.sma50.current.value
        sma200_val = self.sma200.current.value

        if spy_price > sma200_val and sma50_val > sma200_val:
            return "bull"
        elif spy_price < sma200_val and sma50_val < sma200_val:
            return "bear"
        else:
            return "sideways"

    def check_regime_change(self):
        if self.is_warming_up:
            return

        regime = self.detect_regime()
        if regime == "unknown":
            return

        # Only rebalance on regime CHANGE (not every day)
        if regime != self.current_regime and self.current_regime is not None:
            self.debug(f"Regime change: {self.current_regime} -> {regime}")
            self.current_regime = regime
            self.execute_strategy(regime)

        if self.current_regime is None:
            self.current_regime = regime

    def monthly_rebalance(self):
        if self.is_warming_up:
            return

        regime = self.detect_regime()
        if regime == "unknown":
            return

        self.current_regime = regime
        self.execute_strategy(regime)

    def execute_strategy(self, regime):
        if regime == "bull":
            self.apply_momentum_strategy()
        else:
            self.apply_mean_reversion_strategy(regime)

        # Reset high-water marks after rebalance
        for ticker in self.risky:
            sym = self.symbols[ticker]
            if self.portfolio[sym].invested:
                self.equity_high_water[ticker] = self.securities[sym].price

    # ----------------------------------------------------------------
    # Anti-micro-rebalancing (Maisonnave concept)
    # ----------------------------------------------------------------

    def set_holdings_with_threshold(self, symbol, target_weight):
        """
        Anti-micro-rebalancing: only trade if position delta exceeds threshold.

        Avoids unnecessary trades from tiny weight adjustments, reducing
        transaction costs and improving net returns.
        """
        current_weight = 0.0
        if self.portfolio[symbol].invested:
            current_weight = (
                self.portfolio[symbol].holdings_value
                / self.portfolio.total_portfolio_value
            )

        delta = abs(target_weight - current_weight)
        if delta < self.rebalance_threshold and current_weight > 0:
            return  # Skip micro-rebalance

        self.target_weights[symbol] = target_weight
        self.set_holdings(symbol, target_weight)

    def apply_momentum_strategy(self):
        history = self.history(
            [self.symbols[t] for t in self.risky],
            self.momentum_lookback + 5,
            Resolution.DAILY
        )

        if history.empty:
            return

        # Risk-adjusted momentum: return / volatility
        risk_adj_mom = {}
        for ticker in self.risky:
            try:
                prices = history.loc[self.symbols[ticker]]["close"]
                if len(prices) >= self.momentum_lookback:
                    raw_return = prices.iloc[-1] / prices.iloc[-self.momentum_lookback] - 1
                    daily_returns = prices.pct_change().dropna()
                    vol = daily_returns.std() * np.sqrt(252)
                    if vol > 0.01:
                        risk_adj_mom[ticker] = raw_return / vol
                    else:
                        risk_adj_mom[ticker] = raw_return
            except (KeyError, TypeError):
                continue

        if not risk_adj_mom:
            return

        best = max(risk_adj_mom, key=risk_adj_mom.get)
        other = [t for t in self.risky if t != best]

        # Liquidate defensive positions
        for ticker in self.defensive:
            if self.portfolio[self.symbols[ticker]].invested:
                self.liquidate(self.symbols[ticker])

        self.set_holdings_with_threshold(self.symbols[best], 0.70)
        if other:
            self.set_holdings_with_threshold(self.symbols[other[0]], 0.30)

    def apply_mean_reversion_strategy(self, regime):
        oversold = []
        for ticker in self.risky:
            if ticker in self.rsi_indicators and self.rsi_indicators[ticker].is_ready:
                rsi_val = self.rsi_indicators[ticker].current.value
                if rsi_val < self.rsi_oversold:
                    oversold.append(ticker)

        exited = set()
        if oversold:
            weight_per_asset = 0.3 / len(oversold)
            for ticker in oversold:
                self.set_holdings_with_threshold(self.symbols[ticker], weight_per_asset)

            remaining = 0.7
            nominal = {"GLD": remaining * 0.5, "IEF": remaining * 0.5}
            targeted = set(oversold)
        else:
            if regime == "bear":
                nominal = {"GLD": 0.50, "IEF": 0.50}
            else:
                # Sideways: reduced equity (30% vs previous 40%)
                nominal = {"GLD": 0.35, "IEF": 0.35, "SPY": 0.30}

            # Exit risky if RSI recovered above exit threshold
            for ticker in self.risky:
                if ticker in self.rsi_indicators and self.rsi_indicators[ticker].is_ready:
                    if self.rsi_indicators[ticker].current.value > self.rsi_exit:
                        if self.portfolio[self.symbols[ticker]].invested:
                            if self._fix_same_day and ticker in nominal:
                                # Vise de nouveau ce jour : set_holdings le
                                # redimensionne, sans vente prealable (#23221).
                                continue
                            self.liquidate(self.symbols[ticker])
                            exited.add(ticker)
            targeted = set()

        if self._fix_room:
            nominal = self._fit_to_room(nominal, oversold, targeted, exited)
        for ticker, weight in nominal.items():
            self.set_holdings_with_threshold(self.symbols[ticker], weight)

    def _fit_to_room(self, nominal, oversold, targeted, exited):
        """Ramene le panier defensif a la place laissee par la poche risquee (#23221).

        Poche risquee : les titres survendus achetes ce jour (0,3 repartis) et les
        titres risques conserves, a leur poids courant. Un titre risque est conserve
        quand il est detenu sans etre ni vendu (RSI > 50), ni vise par ce
        reequilibrage (survendu, ou SPY dans le panier de range). Sans ce calcul,
        GLD et IEF s'ajoutaient a un QQQ conserve a 70 % : exposition brute 1,7.
        """
        tpv = self.portfolio.total_portfolio_value
        pocket = 0.3 if oversold else 0.0
        for ticker in self.risky:
            sym = self.symbols[ticker]
            if ticker in targeted or ticker in exited or ticker in nominal:
                continue
            if self.portfolio[sym].invested and tpv > 0:
                pocket += self.portfolio[sym].holdings_value / tpv
        room = max(0.0, 1.0 - pocket)
        total = sum(nominal.values())
        scale = min(1.0, room / total) if total > 0 else 0.0
        return {ticker: weight * scale for ticker, weight in nominal.items()}

    def check_stop_loss(self):
        if self.is_warming_up:
            return

        for ticker in self.risky:
            sym = self.symbols[ticker]
            if not self.portfolio[sym].invested:
                continue

            current_price = self.securities[sym].price

            # Update high-water mark
            if ticker not in self.equity_high_water:
                self.equity_high_water[ticker] = current_price
            else:
                self.equity_high_water[ticker] = max(
                    self.equity_high_water[ticker], current_price
                )

            # Check trailing stop
            drawdown = (current_price / self.equity_high_water[ticker]) - 1
            if drawdown < self.stop_loss_pct:
                self.liquidate(sym)
                self.debug(f"STOP-LOSS {ticker}: {drawdown:.2%} from high")
                del self.equity_high_water[ticker]

    def _trace(self):
        if self.is_warming_up:
            return
        tpv = self.portfolio.total_portfolio_value
        self.plot("shadow", f"e{self._closes % 5}", tpv)
        self._closes += 1
        if tpv <= 0:
            return
        gross = sum(abs(h.holdings_value) for h in self.portfolio.values()) / tpv
        if gross > self._gross_max:
            self._gross_max = gross
            self._gross_max_day = str(self.time.date())
        if gross > 1.005:
            self._gross_over += 1
            month = self.time.strftime("%Y-%m")
            if month not in self._gross_months:
                self._gross_months.append(month)

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._mode == "spy":
            targets = {self.symbols["SPY"]: 1.0}
        elif self._mode == "6040":
            targets = {self.symbols["SPY"]: 0.6, self.bnd: 0.4}
        else:
            targets = {s: 0.25 for s in self.symbols.values()}
        # Un seul set_holdings multi-cibles, ordres en attente retires d'abord :
        # les quantites se calculent sur la position finale.
        self.transactions.cancel_open_orders()
        self.set_holdings([PortfolioTarget(s, w) for s, w in targets.items()],
                          liquidate_existing_holdings=True)

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("gross_max", f"{self._gross_max:.3f}")
        self.set_runtime_statistic("gross_max_day", self._gross_max_day)
        self.set_runtime_statistic("gross_over_1005", str(self._gross_over))
        months = self._gross_months
        self.set_runtime_statistic(
            "gross_months",
            f"{len(months)} ({months[0]} .. {months[-1]})" if months else "0")

    def on_data(self, data):
        pass
