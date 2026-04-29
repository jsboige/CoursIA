#region imports
from AlgorithmImports import *
from sklearn.tree import DecisionTreeRegressor
from sklearn.preprocessing import StandardScaler
#endregion
# Macro Factor Rotation (AI Stocks-Bonds Rotation)
# Source: QC Strategy Library - AI Stocks-Bonds Rotation
# Concept: DecisionTreeRegressor predicts 21-day forward returns using FRED macro factors
# (VIX, Yield Curve Spread, Fed Funds Rate) across SPY, GLD, BND, BTC.
# Monthly rebalance with 4-year training lookback.
# Imported from QC Cloud Project ID: 29687828


class AIStocksBondsRotationAlgorithm(QCAlgorithm):

    def initialize(self):
        self.set_start_date(2013, 1, 1)
        self.settings.daily_precise_end_time = False
        self.settings.seed_initial_prices = True

        self._bitcoin = self.add_crypto(
            "BTCUSD", market=Market.BITFINEX, leverage=2,
        ).symbol
        self._equities = [
            self.add_equity(ticker).symbol
            for ticker in ["SPY", "GLD", "BND"]
        ]
        self._symbols = self._equities + [self._bitcoin]

        self._factors = [
            self.add_data(Fred, ticker, Resolution.DAILY).symbol
            for ticker in ["VIXCLS", "T10Y3M", "DFF"]
        ]

        self._model = DecisionTreeRegressor(
            max_depth=12, random_state=1,
        )
        self._scaler = StandardScaler()
        self._max_bitcoin_weight = self.get_parameter(
            "max_bitcoin_weight", 0.1,
        )

        lookback_years = self.get_parameter("lookback_years", 4)
        self._lookback = timedelta(lookback_years * 365)

        self.schedule.on(
            self.date_rules.month_start(self._equities[0]),
            self.time_rules.after_market_open(self._equities[0], 1),
            self._rebalance,
        )

        self.set_warm_up(timedelta(35))

    def _rebalance(self):
        if self.is_warming_up:
            return

        factors = (
            self.history(self._factors, self._lookback, Resolution.DAILY)
            ["value"].unstack(0).dropna()
        )
        labels = (
            self.history(
                self._symbols, self._lookback, Resolution.DAILY,
                data_normalization_mode=DataNormalizationMode.TOTAL_RETURN,
            )
            ["close"].unstack(0).dropna()
            .pct_change(21).shift(-21).dropna()
        )

        prediction_by_symbol = pd.Series()

        for symbol in self._symbols:
            if symbol not in labels.columns:
                continue
            asset_labels = labels[symbol].dropna()
            if len(asset_labels) == 0:
                continue
            idx = factors.index.intersection(asset_labels.index)
            if len(idx) == 0:
                continue

            self._model.fit(
                self._scaler.fit_transform(factors.loc[idx]),
                asset_labels.loc[idx],
            )

            prediction = self._model.predict(
                self._scaler.transform([factors.iloc[-1]]),
            )[0]

            if prediction > 0:
                prediction_by_symbol.loc[symbol] = prediction
        if len(prediction_by_symbol) == 0:
            return

        weight_by_symbol = (
            1.5 * prediction_by_symbol / prediction_by_symbol.sum()
        )

        if (
            self._bitcoin in weight_by_symbol
            and weight_by_symbol.loc[self._bitcoin] > self._max_bitcoin_weight
        ):
            weight_by_symbol.loc[self._bitcoin] = self._max_bitcoin_weight
            if len(weight_by_symbol) > 1:
                equities = [
                    s for s in self._equities if s in weight_by_symbol
                ]
                equity_weights = weight_by_symbol.loc[equities]
                weight_by_symbol.loc[equities] = (
                    1.5 * equity_weights / equity_weights.sum()
                )

        targets = [
            PortfolioTarget(symbol, weight)
            for symbol, weight in weight_by_symbol.items()
        ]
        self.set_holdings(targets, True)

    def on_warmup_finished(self):
        self._rebalance()
