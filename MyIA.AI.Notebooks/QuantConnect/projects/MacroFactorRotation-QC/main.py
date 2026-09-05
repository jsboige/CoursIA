# region imports
from AlgorithmImports import *

from sklearn.tree import DecisionTreeRegressor
from sklearn.preprocessing import StandardScaler

import asg_helpers
# endregion
# ============================================================================
# Bras "baseline" (mode="baseline", defaut) - QC Strategy Library #72 clone :
# https://www.quantconnect.com/strategies/72
# Monthly Macro Factor Cross-Asset Rotation by Derek Melchin
# 1Y OOS Sharpe 1.23, 5Y CAGR 33.45%, 5Y Drawdown 27.60%, 71% Win Rate
# Rotation multi-actifs SPY/GLD/BND/BTCUSD pilotee par VIX, courbe 10Y-3M et
# fed funds ; DecisionTreeRegressor avec reentrainement mensuel, 150 %
# d'exposition brute, BTC plafonne a 10 %. Source: QC Strategy Library #72,
# clone 2026-04-05. La logique de decision d'origine est preservee a
# l'identique (seul un parametre optionnel trading_start permet d'aligner
# la fenetre d'experimentation, voir issue #14722).
#
# Bras "asg" (mode="asg") - QC research #21132, issue #14722 :
# https://www.quantconnect.com/research/21132/sizing-market-exposure-with-aggregate-sales-growth/
# "Sizing Market Exposure With Aggregate Sales Growth" (Derek Melchin,
# juillet 2026), d'apres Garfinkel, Hribar & Hsiao (2025), "Aggregate Sales
# Growth and Stock Market Returns" (SSRN 5066654).
# Mecanique mensuelle exacte de l'article :
#   - actions ordinaires americaines primaires (ST00000001, country USA),
#     secteurs Financial Services et Real Estate exclus ;
#   - ASG = moyenne, ponderee par capitalisation, de la croissance annuelle
#     du chiffre d'affaires winsorisee 1 % / 99 % en coupe ;
#   - regression OLS a fenetre croissante du rendement excédentaire mensuel
#     de SPY sur l'ASG retardée d'un mois (convention d'indexation
#     pd.Period(now)-1 + shift(1, freq="M"), np.polynomial.polynomial.polyfit) ;
#   - prevision forecast = alpha + beta * ASG courante ;
#   - exposition SPY w = clip(forecast / (gamma * variance), 0, 1.5) avec
#     gamma = 3 et variance des 120 derniers rendements excédentaires
#     mensuels ; reliquat 1 - w place en BIL (T-bills 13 semaines).
# Les fonctions pures correspondantes (winsorisation, agregation, OLS,
# variance, bornes) sont extraites dans asg_helpers.py et testees
# localement dans tests/test_asg_helpers.py.
#
# Experimentation alignee #14722 (les deux bras, parametres passes au
# backtest) : start_date=20070101, end_date=20250101, trading_start=20180101,
# capital 100 000 USD, brokerage par defaut QC (frais/fills identiques),
# benchmark SPY. Periode
# d'entrainement/warmup 2007-01 -> 2017-12 : le bras ASG accumule ses series
# mensuelles (au moins 130 valeurs d'ASG et au moins 129 rendements
# excedentaires au premier echange, borne conservative valable meme si le
# warm-up de 35 jours ignorait les evenements de janvier et fevrier 2007)
# et sa variance 120 mois est PLEINE des le premier echange de janvier 2018
# (fenetre de l'article + marge, amendement audit pre-PR), le
# bras baseline n'echange pas. Periode OOS 2018-01 -> 2025-01
# ou les deux bras echangent. Sans ces parametres, le comportement par
# defaut reproduit la baseline d'origine.
# ============================================================================


class MacroFactorRotationAlgorithm(QCAlgorithm):

    def initialize(self):
        self._mode = self.get_parameter("mode", "baseline").lower()
        if self._mode not in ("baseline", "asg"):
            raise ValueError(
                f"parametre mode inconnu : {self._mode} (baseline | asg)"
            )
        self._trading_start = self._parse_date_param("trading_start")

        # Brokerage par defaut (les deux bras) : la strategy multi-actifs
        # equities + crypto ne passe sous aucun broker reel unique (IBKR
        # rejette les targets Crypto - "Unsupported security type: Crypto",
        # bug latent du clone local #14722 - , Binance rejette les equities).
        # Le projet cloud d'origine (32730301, metriques de l'issue) tourne
        # lui-meme sans set_brokerage_model : mode par defaut, frais QC
        # identiques pour les deux bras de l'experimentation alignee.
        start_date_param = self._parse_date_param("start_date")
        end_date_param = self._parse_date_param("end_date")
        # Ordre d'origine preserve : sans parametre, start = end_date par
        # defaut - 10 ans, puis end fixe au 2025-01-01 (baseline #72).
        self.set_start_date(
            start_date_param
            if start_date_param is not None
            else self.end_date - timedelta(10 * 365)
        )
        if end_date_param is not None:
            self.set_end_date(end_date_param)
        else:
            self.set_end_date(2025, 1, 1)  # Fixed end date for reproducibility
        self.set_cash(100_000)
        self.settings.daily_precise_end_time = False
        self.settings.seed_initial_prices = True
        self.set_benchmark("SPY")

        if self._mode == "asg":
            self._initialize_asg()
        else:
            self._initialize_baseline()

    def _parse_date_param(self, name):
        raw = self.get_parameter(name)
        if raw is None or str(raw).strip() == "":
            return None
        return datetime.strptime(str(raw).strip(), "%Y%m%d")

    def _may_trade(self):
        """Porte d'alignement #14722 : avant trading_start, on n'echange pas."""
        return self._trading_start is None or self.time >= self._trading_start

    # ------------------------------------------------------------------
    # Bras baseline : rotation macro DecisionTree (logique d'origine #72)
    # ------------------------------------------------------------------
    def _initialize_baseline(self):
        # Multi-asset strategy (equities + crypto): no single brokerage supports both.
        # IBKR rejects crypto, Binance rejects equities. Default brokerage allows both
        # with realistic fills per asset type. For production, split into sub-strategies.
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
            self._rebalance_baseline
        )
        self.set_warm_up(timedelta(35))

    def _rebalance_baseline(self):
        if self.is_warming_up:
            return
        if not self._may_trade():
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
            if symbol not in labels.columns:
                continue
            asset_labels = labels[symbol].dropna()
            if len(asset_labels) == 0:
                continue
            idx = factors.index.intersection(asset_labels.index)
            if len(idx) == 0:
                continue

            # Fit model
            self._model.fit(
                self._scaler.fit_transform(factors.loc[idx]),
                asset_labels.loc[idx]
            )
            # Predict
            prediction = self._model.predict(self._scaler.transform([factors.iloc[-1]]))[0]
            if prediction > 0:
                prediction_by_symbol.loc[symbol] = prediction
        if len(prediction_by_symbol) == 0:
            return
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
        if self._mode == "baseline":
            self._rebalance_baseline()

    # ------------------------------------------------------------------
    # Bras ASG : sizing d'exposition par Aggregate Sales Growth (#21132)
    # ------------------------------------------------------------------
    def _initialize_asg(self):
        self._spy = self.add_equity("SPY", Resolution.DAILY, leverage=3).symbol
        self._bil = self.add_equity("BIL", Resolution.DAILY, leverage=3).symbol
        # Etat accumule mois par mois (fenetre croissante de l'article).
        self._firm_data = {}
        self._asg = pd.Series(dtype=float)
        self._excess_returns = pd.Series(dtype=float)
        self._prev_event_price = None
        self._gamma = asg_helpers.GAMMA
        # Selection d'univers programmee au debut de chaque mois (00:00),
        # rebalance programme le meme jour a 08:00 : la coupe fondamentale
        # est donc toujours fraiche et connue avant la decision.
        date_rule = self.date_rules.month_start("SPY")
        self.universe_settings.schedule.on(date_rule)
        self._universe = self.add_universe(self._select_assets)
        self.schedule.on(date_rule, self.time_rules.at(8, 0), self._rebalance_asg)
        self.set_warm_up(timedelta(35))

    def _select_assets(self, fundamentals: List[Fundamental]) -> List[Symbol]:
        # Univers #21132 : actions ordinaires americaines primaires,
        # Financial Services et Real Estate exclus. L'univers ne selectionne
        # aucun titre (retour vide) : il sert uniquement a collecter la coupe
        # fondamentale point-in-time du mois.
        self._firm_data = {
            f.symbol: (f.operation_ratios.revenue_growth.one_year, f.market_cap)
            for f in fundamentals
            if (f.company_reference.country_id == "USA"
                and f.security_reference.is_primary_share
                and f.security_reference.security_type == "ST00000001"
                and f.asset_classification.morningstar_sector_code
                    not in (MorningstarSectorCode.FINANCIAL_SERVICES,
                            MorningstarSectorCode.REAL_ESTATE))
        }
        return []

    def _rebalance_asg(self):
        if self.is_warming_up:
            return
        # Convention d'indexation de l'article : a l'evenement de debut du
        # mois M, les donnees du mois complete M-1 sont enregistrees sous
        # l'index Period(M-1).
        month = pd.Period(self.time, freq="M") - 1
        # 1) Rendement excédentaire mensuel de SPY du mois complete :
        #    close de fin de mois -> close de fin de mois (prix a 08:00 =
        #    dernier close du mois precedent), moins taux sans risque
        #    mensuel courant (mecanique de l'article).
        price = self.securities[self._spy].price
        if self._prev_event_price:
            rf_monthly = (
                self.risk_free_interest_rate_model.get_interest_rate(self.time)
                / 12
            )
            self._excess_returns[month] = (
                price / self._prev_event_price - 1 - rf_monthly
            )
        self._prev_event_price = price
        # 2) ASG du mois : coupe fondamentale fraiche (point-in-time),
        #    winsorisation 1/99 et ponderation par capitalisation.
        if self._firm_data:
            firms = pd.DataFrame.from_dict(
                self._firm_data, orient="index", columns=["growth", "market_cap"]
            )
            asg_value = asg_helpers.aggregate_sales_growth(
                firms["growth"], firms["market_cap"]
            )
            if asg_value is not None:
                self._asg[month] = asg_value
        # 3) Avant trading_start (periode d'entrainement/warmup #14722) :
        #    accumuler sans echanger.
        if not self._may_trade():
            return
        # 4) OLS a fenetre croissante (lag d'un mois via shift), prevision,
        #    variance 120 mois, exposition bornee clip(., 0, 1.5).
        fit = asg_helpers.fit_expanding_ols(
            self._asg,
            self._excess_returns,
            min_observations=asg_helpers.MIN_FIT_OBSERVATIONS,
        )
        variance = asg_helpers.trailing_variance(
            self._excess_returns,
            window=asg_helpers.VARIANCE_WINDOW,
            min_observations=asg_helpers.MIN_VARIANCE_OBSERVATIONS,
        )
        forecast = asg_helpers.forecast_excess_return(fit, self._asg.get(month))
        w_star = asg_helpers.solve_exposure(
            forecast, variance, gamma=self._gamma
        )
        # 5) SPY a w_star, reliquat en BIL (negatif = financement du levier).
        self.set_holdings([
            PortfolioTarget(self._spy, w_star),
            PortfolioTarget(self._bil, 1 - w_star),
        ])
