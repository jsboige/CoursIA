# region imports
from AlgorithmImports import *
# endregion

# Parametres de mesure (#20054), tous optionnels : sans eux, l'algorithme garde sa
# forme d'origine (2015-01-01 -> 2024-12-31, EMA 20/50, SMA200, stop 10 %).
# - start / end : dates au format AAAA-MM-JJ ;
# - fast / slow / trail : periodes des EMA et stop suiveur (fraction, 0 = coupe) ;
# - filter : 0 coupe le filtre SMA200 a l'entree ;
# - fee_mult : multiplie les frais du modele de courtier Binance (1 = identite).
# Compteurs publies en statistiques d'execution, et graphique "shadow" : une valeur
# par jour, tracee dans e0..e4 (equity) et b0..b4 (cloture BTCUSDT) en alternance,
# pour que le graphique garde une valeur par barre journaliere.


class _ScaledFeeModel(FeeModel):
    """Frais du modele de courtier Binance, mis a l'echelle."""

    def __init__(self, multiplier):
        super().__init__()
        self._multiplier = multiplier
        self._base = BinanceFeeModel()

    def get_order_fee(self, parameters):
        fee = self._base.get_order_fee(parameters)
        if fee is None:
            return fee
        amount = float(fee.value.amount) * self._multiplier
        return OrderFee(CashAmount(amount, fee.value.currency))


class EMACrossCryptoAlgorithm(QCAlgorithm):
    """Dual EMA crossover on BTCUSDT (Binance Cash) with risk management.

    Entry: EMA fast > EMA slow AND BTC > SMA200 (bull market filter).
    Exit: EMA cross (fast < slow) OR trailing stop triggered.
    Position size: 80% of available USDT (reduced from 95%).
    Trailing stop: 10% from peak price.

    Research findings (research.ipynb):
    - SMA200 filter is the most powerful MaxDD reducer (~10-15 pts reduction)
    - Trailing stop 10% adds further protection against rapid crashes
    - Position cap 80% reduces exposure proportionally
    - EMA 20/50 remains optimal (no improvement from alternatives)
    - Scale-out and dynamic vol sizing add complexity without clear benefit
    """

    def initialize(self):
        start = self.get_parameter("start")
        end = self.get_parameter("end")
        if start:
            self.set_start_date(*map(int, start.split("-")))
        else:
            self.set_start_date(2015, 1, 1)
        if end:
            self.set_end_date(*map(int, end.split("-")))
        else:
            self.set_end_date(2024, 12, 31)  # Extended from 2020: +3 years for robustness validation (includes 2017 bull & 2018 crash)
        self.set_account_currency("USDT")
        self.set_cash(10000)
        self.btc = self.add_crypto("BTCUSDT", Resolution.DAILY, Market.BINANCE).symbol
        self.set_benchmark(self.btc)
        self.set_brokerage_model(BrokerageName.BINANCE, AccountType.CASH)
        self.fee_mult = float(self.get_parameter("fee_mult") or 1)
        if self.fee_mult != 1.0:
            self.securities[self.btc].set_fee_model(_ScaledFeeModel(self.fee_mult))

        # EMA parameters (unchanged from v1 - 20/50 is optimal)
        self.fast_period = int(self.get_parameter("fast") or 20)
        self.slow_period = int(self.get_parameter("slow") or 50)

        # Risk management parameters
        self.position_size = 0.80       # Reduced from 0.95 - limits exposure
        trail = self.get_parameter("trail")
        self.trailing_stop_pct = float(trail) if trail else 0.10   # 10% trailing stop from peak
        self.sma200_period = 200        # Bull market filter
        self.use_filter = (self.get_parameter("filter") or "1") != "0"

        # Indicators
        self.ema_fast = self.ema(self.btc, self.fast_period, Resolution.DAILY)
        self.ema_slow = self.ema(self.btc, self.slow_period, Resolution.DAILY)
        self.sma200 = self.SMA(self.btc, self.sma200_period, Resolution.DAILY)

        # Trailing stop tracking
        self.peak_price = 0.0

        # Compteurs de mesure (#20054)
        self.closes = 0
        self.days_invested = 0
        self.n_entries = 0
        self.n_cross_exits = 0
        self.n_stop_exits = 0
        self.n_rebuys_after_stop = 0
        self.last_stop_bar = None
        self.first_bar = None
        self.first_ready = None

        warmup_days = self.sma200_period + 10
        self.set_warm_up(warmup_days, Resolution.DAILY)

    def on_data(self, data):
        if data.bars.contains_key(self.btc) and self.first_bar is None:
            self.first_bar = self.time
        if self.is_warming_up:
            return
        if data.bars.contains_key(self.btc):
            # Graphique shadow : une valeur par barre journaliere, avant toute decision.
            self.plot("shadow", f"e{self.closes % 5}", self.portfolio.total_portfolio_value)
            self.plot("shadow", f"b{self.closes % 5}", float(data.bars[self.btc].close))
            self.closes += 1
            if self.portfolio[self.btc].invested:
                self.days_invested += 1
        if not self.ema_fast.is_ready or not self.ema_slow.is_ready or not self.sma200.is_ready:
            return
        if not data.contains_key(self.btc) or data[self.btc] is None:
            return
        if self.first_ready is None:
            self.first_ready = self.time

        fast_val = self.ema_fast.current.value
        slow_val = self.ema_slow.current.value
        sma200_val = self.sma200.current.value
        price = float(data[self.btc].close)
        invested = self.portfolio[self.btc].invested

        # Update trailing stop peak
        if invested and price > self.peak_price:
            self.peak_price = price

        # --- EXIT LOGIC ---

        # 1. Trailing stop (checked first - protects against rapid crashes)
        if invested and self.peak_price > 0 and self.trailing_stop_pct > 0:
            drawdown_from_peak = (price - self.peak_price) / self.peak_price
            if drawdown_from_peak <= -self.trailing_stop_pct:
                qty = self.portfolio[self.btc].quantity
                if qty > 0:
                    self.market_order(self.btc, -qty,
                                      tag=f"Trailing Stop {drawdown_from_peak*100:.1f}%")
                    self.peak_price = 0.0
                    self.n_stop_exits += 1
                    self.last_stop_bar = self.closes
                return

        # 2. EMA cross exit: fast crosses below slow
        if fast_val < slow_val and invested:
            qty = self.portfolio[self.btc].quantity
            if qty > 0:
                self.market_order(self.btc, -qty, tag="EMA Cross Exit")
                self.peak_price = 0.0
                self.n_cross_exits += 1

        # --- ENTRY LOGIC ---

        # Long signal: fast EMA > slow EMA AND BTC above SMA200 (bull market)
        elif fast_val > slow_val and not invested:
            # SMA200 filter: only enter in structural bull market
            if self.use_filter and price < sma200_val:
                return  # Skip entry if BTC is below its 200-day SMA

            usdt_available = self.portfolio.cash_book["USDT"].amount
            qty = round((usdt_available * self.position_size) / price, 5)
            if qty > 0 and usdt_available > 10:
                self.market_order(self.btc, qty, tag="EMA Cross Long")
                self.peak_price = price
                self.n_entries += 1
                if self.last_stop_bar is not None and self.closes - self.last_stop_bar <= 2:
                    self.n_rebuys_after_stop += 1

    def on_end_of_algorithm(self):
        stats = {
            "Bars": self.closes,
            "Days invested": self.days_invested,
            "Entries": self.n_entries,
            "Cross exits": self.n_cross_exits,
            "Stop exits": self.n_stop_exits,
            "Rebuys within 2 days of stop": self.n_rebuys_after_stop,
            "First bar": f"{self.first_bar:%Y-%m-%d}" if self.first_bar else "none",
            "First ready": f"{self.first_ready:%Y-%m-%d}" if self.first_ready else "none",
            "Params": (f"fast={self.fast_period} slow={self.slow_period} "
                       f"trail={self.trailing_stop_pct} filter={int(self.use_filter)} "
                       f"fee_mult={self.fee_mult}"),
        }
        for key, value in stats.items():
            self.set_runtime_statistic(key, str(value))
