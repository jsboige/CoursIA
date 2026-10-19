# region imports
from AlgorithmImports import *
# endregion


class EMACrossIndexAlgorithm(QCAlgorithm):
    """Dual EMA crossover on SPY (S&P 500 index ETF) - v2.0.

    Research findings (research.ipynb):
    - EMA 20/60 selected over 20/50: robustness IS/OOS = 1.55 (best of grid search)
    - Slow=60 captures quarterly trends, reduces whipsaws vs slow=50
    - Cooldown 3d after exit: eliminates immediate re-entry on false signals (+4.6% Sharpe)
    - Trailing stop rejected: degrades Sharpe OR changes strategy nature (too many trades)
    - QQQ rejected: correlation 0.92-0.95 with SPY, no real diversification benefit
    - Volume filter rejected: SPY is hyper-liquid, volume not directional signal for ETFs

    Signal: long when EMA(20) > EMA(60), flat otherwise. Exit on cross-down.
    Beta ~ 0.42 (signal-driven, not beta loading).
    """

    def initialize(self):
        # Mesure contre references detenues (#21392, protocole de #21329) :
        # `strategy` (defaut) garde la decision du code ; `spy` (SPY detenu) et
        # `6040` (SPY 60 %, BND 40 %) sont les deux references.
        self._mode = self.get_parameter("mode", "strategy").lower()
        if self._mode not in ("strategy", "spy", "6040"):
            raise ValueError(
                f"parametre mode inconnu : {self._mode} (strategy | spy | 6040)"
            )

        # Les parametres start_date et end_date (%Y%m%d) ouvrent la mesure hors
        # echantillon ; sans eux, la fenetre reste celle-ci.
        start_date_param = self._parse_date_param("start_date")
        end_date_param = self._parse_date_param("end_date")
        if start_date_param is not None:
            self.set_start_date(start_date_param)
        else:
            self.set_start_date(2015, 1, 1)
        if end_date_param is not None:
            self.set_end_date(end_date_param)
        else:
            self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        if self._mode != "strategy":
            self.settings.seed_initial_prices = True
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.set_benchmark(self.spy)

        # EMA parameters (v2.0: slow changed from 50 to 60)
        # Justification: EMA 20/60 has IS/OOS robustness = 1.55, OOS Sharpe = 1.325 (2010-2015)
        # confirming the signal is structural, not overfitted to the 2015-2026 bull market
        self.fast_period = 20
        self.slow_period = 60

        # Cooldown after exit: 3 days to avoid immediate re-entry on false signals
        # Justification: eliminates 1 whipsaw trade over 11 years, +4.6% Sharpe improvement
        self.cooldown_days = 3
        self.cooldown_counter = 0

        # Indicators
        self.ema_fast = self.ema(self.spy, self.fast_period, Resolution.DAILY)
        self.ema_slow = self.ema(self.spy, self.slow_period, Resolution.DAILY)

        self.set_warm_up(self.slow_period + 10, Resolution.DAILY)

        # References : memes indicateurs et meme prechauffage, aucune decision
        # (on_data sort tout de suite), reequilibrage au debut de chaque mois.
        if self._mode != "strategy":
            self._ref_bnd = (
                self.add_equity("BND", Resolution.DAILY).symbol
                if self._mode == "6040"
                else None
            )
            self.schedule.on(
                self.date_rules.month_start(self.spy),
                self.time_rules.after_market_open(self.spy, 1),
                self._rebalance_reference,
            )

        # Trace journaliere `shadow` (contrat #18923) : valeur du portefeuille a
        # l'ouverture de chaque seance de SPY, repartie sur e0..e4. Les trois
        # modes la prennent au meme instant, sur la cloture de la veille.
        self._closes = 0
        self.schedule.on(
            self.date_rules.every_day(self.spy),
            self.time_rules.after_market_open(self.spy, 0),
            self._trace,
        )

    def _rebalance_reference(self):
        if self.is_warming_up:
            return
        if self._ref_bnd is None:
            self.set_holdings([PortfolioTarget(self.spy, 1.0)])
        else:
            self.set_holdings([
                PortfolioTarget(self.spy, 0.6),
                PortfolioTarget(self._ref_bnd, 0.4),
            ])

    def _parse_date_param(self, name):
        raw = self.get_parameter(name)
        if raw is None or str(raw).strip() == "":
            return None
        return datetime.strptime(str(raw).strip(), "%Y%m%d")

    def _trace(self):
        if self.is_warming_up:
            return
        self.plot("shadow", f"e{self._closes % 5}", self.portfolio.total_portfolio_value)
        self._closes += 1

    def on_data(self, data):
        if self.is_warming_up or self._mode != "strategy":
            return
        if not self.ema_fast.is_ready or not self.ema_slow.is_ready:
            return
        if not data.contains_key(self.spy) or data[self.spy] is None:
            return

        fast_val = self.ema_fast.current.value
        slow_val = self.ema_slow.current.value
        invested = self.portfolio[self.spy].invested

        # Decrement cooldown counter
        if self.cooldown_counter > 0:
            self.cooldown_counter -= 1

        # Long signal: fast EMA crosses above slow EMA (and not in cooldown)
        if fast_val > slow_val and not invested and self.cooldown_counter == 0:
            self.set_holdings(self.spy, 0.95, tag="EMA Cross Long")

        # Exit: fast EMA crosses below slow EMA
        elif fast_val < slow_val and invested:
            self.liquidate(self.spy, tag="EMA Cross Exit")
            self.cooldown_counter = self.cooldown_days
