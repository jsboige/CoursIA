# region imports
from AlgorithmImports import *

from sklearn.tree import DecisionTreeRegressor
from sklearn.preprocessing import StandardScaler
# endregion
# https://www.quantconnect.com/strategies/72
# Monthly Macro Factor Cross-Asset Rotation by Derek Melchin
# 1Y OOS Sharpe 1.23, 5Y CAGR 33.45%, 5Y Drawdown 27.60%, 71% Win Rate, 163 Followers
# Macro factor driven cross-asset rotation: SPY, GLD, BND, BTCUSD
# Uses VIX, 10Y-3M yield curve, fed funds rate as ML features
# DecisionTreeRegressor with monthly retraining, 150% gross exposure, BTC capped 10%
# Source: QC Strategy Library #72, cloned 2026-04-05, QC Project ID: 29687828


class AIStocksBondsRotationAlgorithm(QCAlgorithm):

    def initialize(self):
        self.set_start_date(self.end_date - timedelta(10*365))
        self.settings.daily_precise_end_time = False
        self.settings.seed_initial_prices = True
        # Add securities
        self._bitcoin = self.add_crypto("BTCUSD", market=Market.BITFINEX, leverage=2).symbol
        self._equities = [self.add_equity(ticker).symbol for ticker in ['SPY', 'GLD', 'BND']]
        self._symbols = self._equities + [self._bitcoin]
        # Add FRED data
        self._factors = [
            self.add_data(Fred, ticker, Resolution.DAILY).symbol
            for ticker in ['VIXCLS', 'T10Y3M', 'DFF']
        ]
        # ML model setup
        self._model = DecisionTreeRegressor(max_depth=12, random_state=1)
        self._scaler = StandardScaler()
        # Parameters
        self._max_bitcoin_weight = self.get_parameter("max_bitcoin_weight", 0.1)
        lookback_years = self.get_parameter("lookback_years", 4)
        self._lookback = timedelta(lookback_years * 365)
        # Schedule monthly rebalancing
        self.schedule.on(
            self.date_rules.month_start(self._equities[0]),
            self.time_rules.after_market_open(self._equities[0], 1),
            self._rebalance
        )
        self.set_warm_up(timedelta(35))

    def _rebalance(self):
        if self.is_warming_up:
            return
        # Get historical factor data
        factors = self.history(
            self._factors,
            self._lookback,
            Resolution.DAILY
        )["value"].unstack(0).dropna()

        # Calculate 21-day forward returns as labels
        labels = self.history(
            self._symbols,
            self._lookback,
            Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.TOTAL_RETURN
        )["close"].unstack(0).dropna().pct_change(21).shift(-21).dropna()

        # Train model and make predictions
        prediction_by_symbol = pd.Series()
        for symbol in self._symbols:
            asset_labels = labels[symbol].dropna()
            idx = factors.index.intersection(asset_labels.index)

            # Fit model
            self._model.fit(
                self._scaler.fit_transform(factors.loc[idx]),
                asset_labels.loc[idx]
            )
            # Predict
            prediction = self._model.predict(self._scaler.transform([factors.iloc[-1]]))[0]
            if prediction > 0:
                prediction_by_symbol.loc[symbol] = prediction
        # Calculate weights
        weight_by_symbol = (
            1.5 * prediction_by_symbol / prediction_by_symbol.sum()
        )
        # Cap Bitcoin weight
        if (self._bitcoin in weight_by_symbol
            and weight_by_symbol.loc[self._bitcoin] > self._max_bitcoin_weight):
            weight_by_symbol.loc[self._bitcoin] = self._max_bitcoin_weight
            if len(weight_by_symbol) > 1:
                equities = [s for s in self._equities if s in weight_by_symbol]
                equity_weights = weight_by_symbol.loc[equities]
                weight_by_symbol.loc[equities] = (
                    1.5 * equity_weights
                    / equity_weights.sum()
                )
        # Execute trades
        targets = [
            PortfolioTarget(symbol, weight)
            for symbol, weight in weight_by_symbol.items()
        ]
        self.set_holdings(targets, True)

    def on_warmup_finished(self):
        self._rebalance()
