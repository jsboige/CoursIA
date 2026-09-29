# region imports
from AlgorithmImports import *

import itertools
# endregion


class LowBetaIndustriesAlgorithm(QCAlgorithm):
    """Banc de mesure de l'anomalie bas-beta, trois bras sur le meme harnais (issue #17500).

    Parametre `arm` :
      - `article` : port fidele de QC research #18469 (Melchin, "Low Beta Portfolios
        Across Industries"). Long-only, |beta| OLS 60 j, mediane globale, poids de rang.
      - `bab`     : BAB neutre par industrie d'Asness, Frazzini, Pedersen (FAJ 2014),
        beta de Frazzini-Pedersen (JFE 2014), jambes a beta 1, industries equiponderees.
      - `spy`     : buy-and-hold SPY (reference).

    Les trois bras partagent la fenetre, le capital, l'univers et le modele de frais.
    Chaque bras trace ses rendements mensuels (graphique "Monthly") pour que les tests
    statistiques (alpha CAPM, rendement en exces du BAB) se fassent hors plateforme.
    """

    def initialize(self):
        # Reglages identiques a l'article (debut, capital, seeder, marge minimale d'ordre).
        self.set_start_date(2010, 1, 2)
        self.set_end_date(2026, 8, 31)
        self.set_cash(10_000_000)
        self.settings.automatic_indicator_warm_up = True
        self.settings.minimum_order_margin_portfolio_percentage = 0.0001
        self.set_security_initializer(BrokerageModelSecurityInitializer(self.brokerage_model, FuncSecuritySeeder(self.get_last_known_prices)))
        self._arm = self.get_parameter('arm', 'article')
        self._beta_period = self.get_parameter('beta_period', 60)
        self._assets_per_industry = self.get_parameter('assets_per_industry', 50)
        self._spy = self.add_equity('SPY', Resolution.DAILY)
        self._targets = []

        # Parametres du bras BAB : ceux des papiers, aucun n'est regle sur les resultats.
        self._bab_scale = self.get_parameter('bab_scale', 0.5)  # echelle du portefeuille (le Sharpe n'en depend pas)
        self._vol_window = 252        # AFP 2014 p. 27 : ecart-type quotidien sur un an
        self._corr_window = 1260      # AFP 2014 p. 27 : correlation sur cinq ans...
        self._corr_horizon = 3        # ... de rendements a trois jours
        self._min_vol_obs = 120       # FP 2014 section 3.1 : au moins 6 mois pour la volatilite
        self._min_corr_obs = 750      # FP 2014 section 3.1 : au moins 3 ans pour la correlation
        self._shrink = 0.6            # Vasicek : beta = 0.6 * beta_ts + 0.4 * 1
        self._min_industry_names = 4  # garde-fou : une industrie a moins de 4 betas valides est ignoree
        self._cache_rows = self._corr_window + self._corr_horizon + 40
        self._returns = pd.DataFrame()  # log-rendements quotidiens (dates x symboles)

        if self._arm in ('article', 'bab'):
            self.universe_settings.resolution = Resolution.DAILY
            self.universe_settings.schedule.on(self.date_rules.month_start(self._spy.symbol))
            if self._arm == 'article':
                self.add_universe(self._select_assets)
            else:
                self.add_universe(self._select_bab)
            self.schedule.on(self.date_rules.month_start(self._spy.symbol, 2), self.time_rules.midnight, self._rebalance)
        elif self._arm != 'spy':
            raise ValueError(f"arm inconnu : {self._arm}")

        # Mesure mensuelle, identique dans les trois bras.
        self._month = None
        self._month_value = None
        self._month_spy = None
        self._net_samples = []
        self._gross_samples = []
        self.schedule.on(self.date_rules.every_day(self._spy.symbol), self.time_rules.midnight, self._sample)

    def on_data(self, data):
        if self._arm == 'spy' and not self.portfolio.invested and data.contains_key(self._spy.symbol):
            self.set_holdings(self._spy.symbol, 1)

    # ------------------------------------------------------------------ bras article

    def _select_assets(self, fundamentals):
        # Select the most liquid assets of each industry group.
        selected = self._liquid_by_industry(fundamentals)
        # Get the absolute beta of each asset.
        self._beta_by_symbol = self._beta([f.symbol for f in selected]).abs()
        # Get the median beta.
        median_beta = np.median(self._beta_by_symbol.values)
        # Select the assets in each industry have that a beta below the median.
        weights_by_industry = {}
        symbols = []
        for industry_code, industry_assets in itertools.groupby(selected, lambda f: f.asset_classification.morningstar_industry_group_code):
            # Get the beta of each asset in the industry.
            industry_beta_by_symbol = self._beta_by_symbol[[f.symbol for f in industry_assets if f.symbol in self._beta_by_symbol]]
            # Select assets with a beta below the median.
            low_betas = industry_beta_by_symbol[industry_beta_by_symbol < median_beta]
            if low_betas.empty:
                continue
            symbols.extend(list(low_betas.index))
            # Weight assets by their beta rank: lower beta => larger positive position.
            beta_ranks = low_betas.sort_values().rank(method='first', ascending=False)
            weights_by_industry[industry_code] = beta_ranks / beta_ranks.sum()

        # Create the portfolio targets. Give equal weight to each industry. Liquidate assets we no longer want.
        self._targets = [PortfolioTarget(symbol, 0) for symbol, holding in self.portfolio.items() if holding.invested and symbol not in symbols]
        for industry_assets in weights_by_industry.values():
            self._targets.extend([PortfolioTarget(symbol, weight/len(weights_by_industry)) for symbol, weight in industry_assets.items()])
        return symbols

    def _beta(self, symbols):  # Source: https://stackoverflow.com/questions/39501277/efficient-python-pandas-stock-beta-calculation-on-many-dataframes
        returns = self.history([self._spy.symbol] + symbols, self._beta_period, Resolution.DAILY, fill_forward=False).close.unstack(0).dropna(axis=1).pct_change().dropna()
        symbols = [s for s in symbols if s in returns.columns]
        df = returns[[self._spy.symbol] + symbols]
        # first column is the market
        X = df.values[:, [0]]
        # prepend a column of ones for the intercept
        X = np.concatenate([np.ones_like(X), X], axis=1)
        # matrix algebra
        b = np.linalg.pinv(X.T.dot(X)).dot(X.T).dot(df.values[:, 1:])
        return pd.Series(b[1], df.columns[1:], name='Beta')

    def _rebalance(self):
        if self._targets:
            # Rebalance the portfolio.
            self.set_holdings(self._targets)
            self._targets = []

    # ------------------------------------------------------------------ univers commun

    def _liquid_by_industry(self, fundamentals):
        """Les `assets_per_industry` actions les plus liquides de chaque industry group Morningstar (code de l'article)."""
        fundamentals = sorted([f for f in fundamentals if f.asset_classification.morningstar_industry_group_code], key=lambda f: (f.asset_classification.morningstar_industry_group_code, f.dollar_volume))
        selected = []
        for _, industry_group_fundamentals in itertools.groupby(fundamentals, lambda f: f.asset_classification.morningstar_industry_group_code):
            selected.extend(list(industry_group_fundamentals)[-self._assets_per_industry:])  # We already sorted by dollar volume above.
        return selected

    # ------------------------------------------------------------------ bras BAB

    def _select_bab(self, fundamentals):
        selected = self._liquid_by_industry(fundamentals)
        industry_by_symbol = {f.symbol: f.asset_classification.morningstar_industry_group_code for f in selected}
        betas = self._fp_betas(list(industry_by_symbol))

        by_industry = {}
        for symbol, beta in betas.items():
            by_industry.setdefault(industry_by_symbol[symbol], []).append((symbol, beta))
        legs = []
        beta_l = []
        beta_h = []
        for members in by_industry.values():
            if len(members) < self._min_industry_names:
                continue
            b = pd.Series({s: v for s, v in members})
            # Poids de rang (FP 2014 eq. 16) : z = rang du beta, k = 2 / sum|z - zbar|.
            dz = b.rank(method='average')
            dz = dz - dz.mean()
            k = 2.0 / dz.abs().sum()
            w_high = (k * dz).clip(lower=0)
            w_low = (-k * dz).clip(lower=0)
            b_low = float((w_low * b).sum())
            b_high = float((w_high * b).sum())
            if b_low <= 0 or b_high <= 0:
                continue
            # Jambe basse levee a beta 1, jambe haute reduite a beta 1 (BAB ex ante neutre au marche).
            legs.append((w_low / b_low, w_high / b_high))
            beta_l.append(b_low)
            beta_h.append(b_high)

        if not legs:
            self._targets = []
            return [symbol for symbol, holding in self.portfolio.items() if holding.invested]

        # Industries equiponderees (AFP 2014, colonne "Equal Weighted" de la Table 3).
        scale = self._bab_scale / len(legs)
        weights = {}
        for long_w, short_w in legs:
            for s, w in long_w[long_w > 0].items():
                weights[s] = weights.get(s, 0.0) + scale * w
            for s, w in short_w[short_w > 0].items():
                weights[s] = weights.get(s, 0.0) - scale * w

        self._targets = [PortfolioTarget(symbol, 0) for symbol, holding in self.portfolio.items() if holding.invested and symbol not in weights]
        self._targets.extend([PortfolioTarget(s, w) for s, w in weights.items()])

        self.plot('BAB', 'industries', len(legs))
        self.plot('BAB', 'names', len(weights))
        self.plot('BAB', 'beta_low', float(np.mean(beta_l)))
        self.plot('BAB', 'beta_high', float(np.mean(beta_h)))
        return list(weights)

    def _fp_betas(self, symbols):
        """Beta ex ante d'AFP 2014 : rho(5 ans, rendements a 3 j) * sigma_i / sigma_m (1 an), contracte vers 1."""
        self._update_returns(symbols)
        spy = self._spy.symbol
        if self._returns.empty or spy not in self._returns.columns:
            return pd.Series(dtype=float)
        cols = [s for s in symbols if s in self._returns.columns and s != spy]
        r = self._returns[[spy] + cols]

        vol = r.iloc[-self._vol_window:]
        sigma = vol.std()
        vol_ok = vol[cols].notna().sum() >= self._min_vol_obs

        r3 = r.iloc[-(self._corr_window + self._corr_horizon - 1):].rolling(self._corr_horizon).sum().iloc[self._corr_horizon - 1:]
        rho = r3[cols].corrwith(r3[spy])
        corr_ok = r3[cols].notna().sum() >= self._min_corr_obs

        beta_ts = rho * sigma[cols] / sigma[spy]
        ok = vol_ok & corr_ok & beta_ts.notna()
        return (self._shrink * beta_ts[ok] + (1 - self._shrink)).astype(float)

    def _update_returns(self, symbols):
        """Tient a jour le cache de log-rendements quotidiens.

        On cache des rendements, pas des prix : les prix ajustes d'une requete d'historique
        dependent de la date de la requete, leurs rapports non. Chaque rendement est donc
        calcule a l'interieur d'une seule requete.
        """
        spy = self._spy.symbol
        wanted = [spy] + [s for s in symbols if s != spy]
        known = [s for s in wanted if s in self._returns.columns]
        new = [s for s in wanted if s not in self._returns.columns]
        frames = []
        if known:
            frames.append(self._log_returns(known, 45))
        for i in range(0, len(new), 250):
            frames.append(self._log_returns(new[i:i + 250], self._cache_rows + 1))
        for frame in frames:
            if frame is not None and not frame.empty:
                self._returns = frame if self._returns.empty else self._returns.combine_first(frame)
        keep = [s for s in wanted if s in self._returns.columns]
        self._returns = self._returns[keep].iloc[-self._cache_rows:]

    def _log_returns(self, symbols, bars):
        history = self.history(symbols, bars, Resolution.DAILY, fill_forward=False)
        if history.empty:
            return None
        close = history.close.unstack(0)
        return np.log(close).diff().iloc[1:]

    # ------------------------------------------------------------------ mesure mensuelle

    def _sample(self):
        """Echantillon quotidien (valeurs de cloture de la veille) et bilan a chaque changement de mois."""
        value = self.portfolio.total_portfolio_value
        spy_price = self.securities[self._spy.symbol].price
        month = (self.time.year, self.time.month)
        if self._month is not None and month != self._month and self._month_value and self._month_spy:
            self.plot('Monthly', 'ret', value / self._month_value - 1)
            self.plot('Monthly', 'spy', spy_price / self._month_spy - 1)
            if self._net_samples:
                self.plot('Monthly', 'netexp', float(np.mean(self._net_samples)))
                self.plot('Monthly', 'gross', float(np.mean(self._gross_samples)))
            self._net_samples = []
            self._gross_samples = []
        if month != self._month:
            self._month = month
            self._month_value = value
            self._month_spy = spy_price
        if value > 0:
            values = [h.holdings_value for h in self.portfolio.values() if h.invested]
            self._net_samples.append(float(sum(values)) / value)
            self._gross_samples.append(float(sum(abs(v) for v in values)) / value)
