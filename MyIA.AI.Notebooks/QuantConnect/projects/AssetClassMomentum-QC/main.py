#region imports
from AlgorithmImports import *

import numpy as np
import pandas as pd
from datetime import datetime
#endregion
# v2.0 — Consolidation article QC research #21050 (issue #14091, EPIC #11698) :
# "Cross-Asset ETF Momentum with a Correlation-Based Short Hedge" (Derek Melchin, 2026-07).
# Source primaire : Pauchlyová & Vojtko (2025), "Refining ETF Asset Momentum Strategy",
# Quantpedia / SSRN 5095447 — https://ssrn.com/abstract=5095447
# v1 (baseline 2018-2025, tranche 3 #1621) : clone QC Strategy Library — 5 ETFs,
# momentum 12 m, top-3, SANS gestion du risque → Needs-improvement (Sharpe 0.22 /
# MaxDD 28.1 % / PSR 3.8 %). L'article apporte l'élément distinctif manquant :
# univers 13 ETFs, momentum multi-horizon 3/6/9/12 m, top-4, et un hedge court
# -30 % sur le pire ETF activé UNIQUEMENT quand la corrélation moyenne 20 j
# dépasse la corrélation moyenne 250 j (régime défavorable).

class AssetClassMomentumAlgorithm(QCAlgorithm):

    def initialize(self):
        # Dates paramétrables pour les runs Dev / OOS / Full (backtests QC Cloud).
        start = self.get_parameter("start_date", "2016-01-01")
        end = self.get_parameter("end_date", "2026-07-01")
        self.set_start_date(datetime.strptime(start, "%Y-%m-%d"))
        self.set_end_date(datetime.strptime(end, "%Y-%m-%d"))
        self.set_cash(100000)
        self.set_brokerage_model(BrokerageName.INTERACTIVE_BROKERS_BROKERAGE, AccountType.MARGIN)
        self.settings.automatic_indicator_warm_up = True

        # Univers 13 ETFs (article #21050) : actions US large/small/étr. émergentes,
        # immobilier, tech, crédit investissement, durations 7-10 ans, TIPS, or,
        # énergie, panier commodités, euro.
        # `self.universe` est réservé par QCAlgorithm.Universe — préfixer autrement.
        self.tickers = ["SPY", "IWM", "EFA", "EEM", "IYR", "QQQ",
                        "LQD", "IEF", "TIP", "GLD", "USO", "DBC", "FXE"]
        # Momentum multi-horizon : moyenne des ROC 3/6/9/12 mois (63/126/189/252 j).
        self.lookbacks = [63, 126, 189, 252]
        for ticker in self.tickers:
            equity = self.add_equity(ticker, Resolution.DAILY)
            equity.rocp = [self.rocp(equity.symbol, lb, Resolution.DAILY)
                           for lb in self.lookbacks]

        self.num_long = 4           # top-4 longs, 25 % chacun
        self.short_weight = -0.30   # short -30 % du pire ETF si hedge actif
        self.corr_short_window = 20
        self.corr_long_window = 250
        self.schedule.on(self.date_rules.month_start("SPY"),
                         self.time_rules.at(8, 0),
                         self._rebalance)

    def _avg_pairwise_correlation(self, window):
        # Corrélation moyenne des 78 paires de l'univers (triangle supérieur
        # de la matrice de corrélation des rendements quotidiens) sur `window` jours.
        hist = self.history(list(self.securities.keys()), window + 1, Resolution.DAILY)
        closes = hist["close"].unstack(level=0)
        rets = closes.pct_change().dropna()
        corr = rets.corr().values
        iu = np.triu_indices(len(corr), k=1)
        return float(corr[iu].mean())

    def _rebalance(self):
        # Score de momentum = moyenne des 4 ROC ; top-4 en long équipondéré.
        scored = sorted(self.securities.values(),
                        key=lambda s: sum(ind.current.value for ind in s.rocp))
        targets = [PortfolioTarget(s.symbol, 1.0 / self.num_long)
                   for s in scored[-self.num_long:]]
        # Hedge court GATED (article #21050) : corr moyenne 20 j > corr moyenne 250 j
        # → -30 % sur l'ETF au momentum le plus faible, sinon 100 % long-only.
        if (self._avg_pairwise_correlation(self.corr_short_window)
                > self._avg_pairwise_correlation(self.corr_long_window)):
            targets.append(PortfolioTarget(scored[0].symbol, self.short_weight))
        self.set_holdings(targets, liquidate_existing_holdings=True)
