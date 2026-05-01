# region imports
from AlgorithmImports import *
from alpha_models import ValueAlpha, QualityAlpha, LowVolAlpha, MomentumFactorAlpha
from portfolio_construction import MeanVariancePCM
from risk_management import SectorCapRiskModel
from execution import TWAPExecutionModel
# endregion


class CompositeC2EquityFactor(QCAlgorithm):
    """
    C4.2 - Equity Factor Composite (v12)

    25 stocks, sector_cap 0.18, 65% max exposure, weekly rebalance.
    Portfolio drawdown cap at 18% + trailing stop 4%.
    """

    def initialize(self):
        self.set_start_date(2015, 1, 1)
        self.set_end_date(2025, 1, 1)
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)

        # Universe: large-cap US equities via Fine selection
        self.universe_settings.resolution = Resolution.DAILY
        self.universe_settings.leverage = 1.0

        # Add SPY for benchmark
        self.add_equity("SPY", Resolution.DAILY)

        # Fine fundamental universe: top 500 by market cap, liquid
        self.add_universe_selection(
            FineFundamentalUniverseSelectionModel(
                self._select_coarse,
                self._select_fine
            )
        )

        # Alpha Models: 4-factor ensemble
        self.set_alpha(CompositeAlphaModel(
            ValueAlpha(),
            QualityAlpha(),
            LowVolAlpha(),
            MomentumFactorAlpha()
        ))

        # PCM: Mean-Variance with sector cap
        sector_cap = float(self.get_parameter("sector_cap", 0.18))
        max_exposure = float(self.get_parameter("max_exposure", 0.65))
        self.set_portfolio_construction(MeanVariancePCM(
            sector_cap=sector_cap,
            rebalance=timedelta(days=7),
            max_exposure=max_exposure
        ))

        # Risk: Portfolio drawdown cap + trailing stop
        trail = float(self.get_parameter("trail_stop", 0.04))
        self.set_risk_management(SectorCapRiskModel(
            max_sector_pct=float(self.get_parameter("max_sector_pct", 0.10)),
            max_beta=float(self.get_parameter("max_beta", 0.8)),
            trail_pct=trail
        ))

        # Execution: TWAP
        self.set_execution(TWAPExecutionModel(
            num_slices=6,
            slice_interval_minutes=10
        ))

        self.set_benchmark("SPY")
        self.set_warm_up(252, Resolution.DAILY)

    def _select_coarse(self, coarse):
        """Select top 200 by dollar volume, price > $10."""
        filtered = [c for c in coarse
                    if c.has_fundamental_data and c.price > 10]
        sorted_by_volume = sorted(filtered,
                                  key=lambda x: x.dollar_volume,
                                  reverse=True)
        return [c.symbol for c in sorted_by_volume[:200]]

    def _select_fine(self, fine):
        """Select top 25 by market cap from the coarse-filtered universe."""
        sorted_by_mcap = sorted(fine,
                                key=lambda x: x.market_cap,
                                reverse=True)
        selected = sorted_by_mcap[:25]

        # Cache fundamental data for alpha models
        # (security.fundamental_data doesn't exist in LEAN)
        self.fundamental_cache = {}
        for f in selected:
            try:
                vr = f.valuation_ratios
                opr = f.operation_ratios
                self.fundamental_cache[f.symbol] = {
                    'price_to_book': getattr(vr, 'price_to_book', None),
                    'price_to_earnings': getattr(vr, 'price_to_earnings', None),
                    'return_on_equity': getattr(opr, 'return_on_equity', None),
                    'debt_to_equity': getattr(opr, 'debt_to_equity', None),
                }
            except Exception:
                pass

        return [f.symbol for f in selected]

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"C4.2 EQUITY FACTOR COMPOSITE: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
