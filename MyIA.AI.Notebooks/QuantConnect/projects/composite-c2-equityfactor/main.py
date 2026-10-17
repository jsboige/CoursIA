# region imports
from AlgorithmImports import *
import numpy as np
from alpha_models import ValueAlpha, QualityAlpha, LowVolAlpha, MomentumFactorAlpha
from portfolio_construction import MeanVariancePCM
from risk_management import SectorCapRiskModel
from execution import TWAPExecutionModel
# endregion


def _ratio(field):
    """Morningstar ratio as a float, None when NaN.

    Multi-period fields (roe, total_debt_equity_ratio) carry their latest
    value in .value; plain ratios (pb_ratio, pe_ratio) are numbers. Zero is
    kept: a debt-free company has a debt-to-equity of 0, and the alphas
    already drop P/B, P/E and ROE at or below 0.
    """
    value = float(getattr(field, 'value', field))
    return value if np.isfinite(value) else None


class CompositeC2EquityFactor(QCAlgorithm):
    """
    C4.2 - Equity Factor Composite (v12)

    25 stocks, sector_cap 0.18, 65% max exposure, weekly rebalance.
    Portfolio drawdown cap at 18% + trailing stop 4%.
    """

    def initialize(self):
        self.set_start_date(2018, 1, 1)
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

        # Alpha Models: 4-factor ensemble. alphas=momentum keeps the momentum
        # factor alone: the control of #21137.
        # References kept for the emission counters of #21141.
        if (self.get_parameter("alphas") or "all") == "momentum":
            self.alpha_models = [MomentumFactorAlpha()]
            self.set_alpha(self.alpha_models[0])
        else:
            self.alpha_models = [
                ValueAlpha(owner=self),
                QualityAlpha(owner=self),
                LowVolAlpha(),
                MomentumFactorAlpha()
            ]
            self.set_alpha(CompositeAlphaModel(*self.alpha_models))
        # Fundamental fields read with a usable value, per field (#21141).
        # The cache exists before the first selection: Value and Quality read
        # it through their owner reference.
        self.fundamental_cache = {}
        self.fund_seen = 0
        self.fund_nonnull = {}

        # PCM: Mean-Variance with sector cap
        sector_cap = float(self.get_parameter("sector_cap", 0.18))
        max_exposure = float(self.get_parameter("max_exposure", 0.65))
        # pcm_mode=symbol reproduces the PCM before #21137 (last insight per
        # symbol: the momentum factor, emitted last, overwrites the others).
        self.pcm = MeanVariancePCM(
            sector_cap=sector_cap,
            rebalance=timedelta(days=7),
            max_exposure=max_exposure,
            by_sleeve=((self.get_parameter("pcm_mode") or "sleeve") == "sleeve"),
            algorithm=self
        )
        self.set_portfolio_construction(self.pcm)

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
        # (security.fundamental_data doesn't exist in LEAN).
        # Lean names (#21141): pb_ratio, pe_ratio, roe, total_debt_equity_ratio.
        # The former names (price_to_book, return_on_equity...) do not exist:
        # getattr(..., None) returned None and Value/Quality never emitted.
        # A wrong name now raises at the first selection instead.
        self.fundamental_cache = {}
        for f in selected:
            vr = f.valuation_ratios
            opr = f.operation_ratios
            self.fundamental_cache[f.symbol] = {
                'price_to_book': _ratio(vr.pb_ratio),
                'price_to_earnings': _ratio(vr.pe_ratio),
                'return_on_equity': _ratio(opr.roe),
                'debt_to_equity': _ratio(opr.total_debt_equity_ratio),
            }
        for fields in self.fundamental_cache.values():
            self.fund_seen += 1
            for name, value in fields.items():
                if value is not None:
                    self.fund_nonnull[name] = self.fund_nonnull.get(name, 0) + 1

        return [f.symbol for f in selected]

    def on_end_of_algorithm(self):
        final = self.portfolio.total_portfolio_value
        self.log(f"C4.2 EQUITY FACTOR COMPOSITE: Final=${final:,.2f}, "
                 f"Return={(final - 100000) / 100000:.2%}")
        # Diagnostics for #21141: insights emitted per alpha (UP/total),
        # and fundamental fields read with a value (non-null/read).
        for alpha in self.alpha_models:
            up, flat = alpha.emitted["up"], alpha.emitted["flat"]
            self.set_runtime_statistic(f"Emitted {alpha.name}", f"{up}/{up + flat}")
        for name in ('price_to_book', 'price_to_earnings', 'return_on_equity', 'debt_to_equity'):
            self.set_runtime_statistic(
                f"Field {name}", f"{self.fund_nonnull.get(name, 0)}/{self.fund_seen}")
        # Calls where getattr(algorithm, 'fundamental_cache') saw nothing
        # (missed/calls), for the alphas that read the cache (#21141).
        for alpha in self.alpha_models:
            probe = getattr(alpha, 'cache_probe', None)
            if probe is not None:
                self.set_runtime_statistic(
                    f"Cache {alpha.name}", f"{probe['algo_missing']}/{probe['calls']}")
        # Diagnostics for #21137: insights reaching the PCM, per alpha.
        self.set_runtime_statistic("PCM calls", str(self.pcm.calls))
        for source in sorted(set(self.pcm.reached) | set(self.pcm.reached_active)):
            self.set_runtime_statistic(
                f"PCM {source}",
                f"{self.pcm.reached_active.get(source, 0)}/{self.pcm.reached.get(source, 0)}")
