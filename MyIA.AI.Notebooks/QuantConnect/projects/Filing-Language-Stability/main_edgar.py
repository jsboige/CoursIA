# region imports
from AlgorithmImports import *
# endregion

from datetime import datetime

from edgar_cloud_data import EDGAR_SIGNALS


BASKET = ("AAPL", "MSFT", "KO", "WMT", "GE")


class PercentFeeModel(FeeModel):
    """Commission explicite en proportion du notionnel de chaque ordre."""

    def __init__(self, percent):
        super().__init__()
        self.percent = percent

    def get_order_fee(self, parameters):
        security = parameters.security
        order = parameters.order
        notional = abs(order.quantity) * float(security.price)
        return OrderFee(
            CashAmount(
                self.percent * notional,
                security.quote_currency.symbol,
            )
        )


class FilingLanguageStabilityEdgarAlgorithm(QCAlgorithm):
    """Test OOS du signal EDGAR contre le meme panier sans signal.

    Parametres QC : ``mode=signal|equal|spy``, ``top_k`` (defaut 2) et
    ``fee_bps`` (defaut 5). ``edgar_cloud_data.py`` est genere depuis le CSV
    reproductible puis charge uniquement dans le projet Cloud : les donnees
    derivees et les textes SEC restent hors Git.
    """

    def initialize(self):
        self.set_start_date(2022, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.set_benchmark("SPY")

        self.mode = self.get_parameter("mode", "signal").lower()
        if self.mode not in ("signal", "equal", "spy"):
            raise ValueError("mode doit etre 'signal', 'equal' ou 'spy'")
        self.top_k = int(self.get_parameter("top_k", 2))
        if not 1 <= self.top_k <= len(BASKET):
            raise ValueError("top_k doit etre compris entre 1 et 5")
        self.fee_bps = float(self.get_parameter("fee_bps", 5.0))

        self.set_security_initializer(self._security_initializer)
        self.spy = self.add_equity("SPY", Resolution.DAILY).symbol
        self.equities = {
            ticker: self.add_equity(ticker, Resolution.DAILY).symbol
            for ticker in BASKET
        }
        self.signal_history = sorted(
            (
                datetime.strptime(available_at, "%Y-%m-%dT%H:%M:%S"),
                ticker,
                float(similarity),
            )
            for available_at, ticker, similarity in EDGAR_SIGNALS
        )
        oos_start = datetime(2022, 1, 1)
        self.eligible_tickers = sorted(
            {
                ticker
                for available_at, ticker, _ in self.signal_history
                if available_at < oos_start
            }
        )
        self.signal_cursor = 0
        self.latest_similarity = {}
        self.signal_points = 0
        self.rebalances = 0
        self.set_warm_up(5, Resolution.DAILY)
        self.schedule.on(
            self.date_rules.month_start(self.spy),
            self.time_rules.after_market_open(self.spy, 5),
            self._rebalance,
        )

    def _security_initializer(self, security):
        if security.type == SecurityType.EQUITY:
            security.set_fee_model(PercentFeeModel(self.fee_bps / 10000.0))

    def on_data(self, data):
        while self.signal_cursor < len(self.signal_history):
            available_at, ticker, similarity = self.signal_history[self.signal_cursor]
            if available_at > self.time:
                break
            self.latest_similarity[ticker] = similarity
            self.signal_points += 1
            self.signal_cursor += 1

    def _selected_tickers(self):
        if self.mode == "spy":
            return []
        if self.mode == "equal":
            return list(self.eligible_tickers)
        ranked = sorted(
            self.latest_similarity.items(),
            key=lambda item: item[1],
            reverse=True,
        )
        return [ticker for ticker, _ in ranked[: self.top_k]]

    def _rebalance(self):
        if self.is_warming_up:
            return
        selected = self._selected_tickers()
        if self.mode == "spy":
            targets = [PortfolioTarget(self.spy, 1.0)]
        elif selected:
            weight = 1.0 / len(selected)
            targets = [
                PortfolioTarget(self.equities[ticker], weight)
                for ticker in selected
            ]
        else:
            return
        self.set_holdings(targets, True)
        self.rebalances += 1

    def on_end_of_algorithm(self):
        self.set_runtime_statistic("EDGAR mode", self.mode)
        self.set_runtime_statistic("EDGAR signal points", str(self.signal_points))
        self.set_runtime_statistic("EDGAR rebalances", str(self.rebalances))
        if self.mode == "signal" and self.signal_points == 0:
            self.error("INCONCLUSIVE: aucun point EDGAR charge")
