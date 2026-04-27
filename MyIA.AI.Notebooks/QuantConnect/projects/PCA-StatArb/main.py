# region imports
from AlgorithmImports import *

from sklearn.decomposition import PCA
import statsmodels.api as sm
# endregion


class PCAStatArbitrageAlgorithm(QCAlgorithm):
    """
    Hands-On AI Trading - Ch06 Ex13: PCA Statistical Arbitrage
    Mean Reversion.

    Uses principal component analysis and linear regression to perform
    statistical arbitrage. Calculates 3 principal components from the
    most liquid 100 stocks, fits OLS for each stock using PCs as
    independent variables, then derives portfolio weights based on
    z-score of residuals (mean reversion signal).

    Universe: Top 100 by dollar volume, price > $5.
    Rebalance: Monthly.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2026, 3, 1)
        self.set_cash(1_000_000)
        self.settings.minimum_order_margin_portfolio_percentage = 0

        self._num_components = self.get_parameter("num_components", 3)
        self._lookback = self.get_parameter("lookback_days", 60)
        self._z_score_threshold = self.get_parameter(
            "z_score_threshold", 1.5
        )
        self._universe_size = self.get_parameter("universe_size", 100)

        schedule_symbol = Symbol.create(
            "SPY", SecurityType.EQUITY, Market.USA
        )
        date_rule = self.date_rules.month_start(schedule_symbol)
        self.universe_settings.schedule.on(date_rule)
        self.universe_settings.data_normalization_mode = \
            DataNormalizationMode.RAW
        self._universe = self.add_universe(self._select_assets)

        self.schedule.on(
            date_rule,
            self.time_rules.after_market_open(schedule_symbol, 1),
            self._trade
        )

        chart = Chart('Explained Variance Ratio')
        self.add_chart(chart)
        for i in range(self._num_components):
            chart.add_series(
                Series(f"Component {i}", SeriesType.LINE, "")
            )

    def _select_assets(self, fundamental):
        return [
            f.symbol
            for f in sorted(
                [f for f in fundamental if f.price > 5],
                key=lambda f: f.dollar_volume
            )[-self._universe_size:]
        ]

    def _trade(self):
        tradeable_assets = [
            symbol
            for symbol in self._universe.selected
            if (self.securities[symbol].price and
                symbol in self.current_slice.quote_bars)
        ]
        # Get historical data with scaled raw normalization.
        history = self.history(
            tradeable_assets, self._lookback, Resolution.DAILY,
            data_normalization_mode=DataNormalizationMode.SCALED_RAW
        ).close.unstack(level=0)

        weights = self._get_weights(history)

        # Mean reversion: enter opposite to residual direction.
        self.set_holdings(
            [
                PortfolioTarget(symbol, -weight)
                for symbol, weight in weights.items()
            ],
            True
        )

    def _get_weights(self, history):
        """Derive portfolio weights from PCA residual z-scores."""
        sample = np.log(history.dropna(axis=1))
        sample -= sample.mean()

        model = PCA().fit(sample)

        for i in range(self._num_components):
            self.plot(
                'Explained Variance Ratio', f"Component {i}",
                model.explained_variance_ratio_[i]
            )

        factors = np.dot(
            sample, model.components_.T
        )[:, :self._num_components]
        factors = sm.add_constant(factors)

        model_by_ticker = {
            ticker: sm.OLS(sample[ticker], factors).fit()
            for ticker in sample.columns
        }

        resids = pd.DataFrame(
            {
                ticker: m.resid
                for ticker, m in model_by_ticker.items()
            }
        )

        zscores = (
            (resids - resids.mean()) / resids.std()
        ).iloc[-1]

        selected = zscores[zscores < -self._z_score_threshold]

        weights = selected * (1 / selected.abs().sum())
        return weights.sort_values()
