# QuantConnect Algorithmic Trading Projects

Strategies de trading algorithmique backtestees sur QuantConnect Cloud, avec notebooks de recherche standalone (yfinance/pandas).

## Performance Summary

### Strategies avancees (signaux complexes)

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Niveau |
|--------|-------------|--------|------|--------|---------|--------|
| [EMA-Cross-Crypto](EMA-Cross-Crypto/) | EMA 20/50 crossover BTCUSDT | **1.304** | 44.8% | 49.8% | 2020-2026 | Debutant |
| [EMA-Cross-Stocks](EMA-Cross-Stocks/) | EMA 20/50 multi-stock (AAPL/MSFT/GOOGL/AMZN/NVDA) | **0.872** | 25.7% | 35.7% | 2015-2026 | Debutant |
| [OptionsIncome](OptionsIncome/) | Covered Call SPY + VIX filter | **0.791** | 15.9% | 7.5% | 2023-2025 | Avance |
| [SectorMomentum](SectorMomentum/) | Dual Momentum SPY/TLT/GLD (Antonacci) | **0.555** | 13.0% | 22.8% | 2015-2026 | Intermediaire |
| [RegimeSwitching](RegimeSwitching/) | Regime detection + asset rotation | **0.553** | 11.7% | 33.0% | 2008-2026 | Avance |
| [FamaFrench](FamaFrench/) | Factor ETF rotation (VLUE/MTUM/SIZE/QUAL/USMV) | **0.540** | 12.1% | 24.2% | 2015-2026 | Intermediaire |
| [AdaptiveAssetAllocation](AdaptiveAssetAllocation/) | Momentum + min-variance multi-asset | **0.518** | 8.0% | 18.8% | 2008-2026 | Avance |
| [Crypto-MultiCanal](Crypto-MultiCanal/) | ZigZag multi-channel (macro/meso/micro) BTCUSDT | **0.486** | 7.6% | 16.8% | 2020-2026 | Avance |
| [AllWeather](AllWeather/) | Portfolio multi-asset Dalio (SPY/TLT/IEF/GLD) | **0.482** | 8.2% | 20.7% | 2015-2026 | Debutant |
| [MomentumStrategy](MomentumStrategy/) | Rotation momentum 11 ETFs sectoriels | **0.459** | 11.5% | 30.0% | 2015-2026 | Intermediaire |
| [RiskParity](RiskParity/) | Risk parity multi-asset portfolio | **0.399** | 7.8% | 20.9% | 2015-2026 | Intermediaire |
| [EMA-Cross-Index](EMA-Cross-Index/) | EMA 20/50 crossover SPY | **0.384** | 8.2% | 24.3% | 2015-2026 | Debutant |
| [DualMomentum](DualMomentum/) | Absolute + relative momentum ETFs | **0.350** | 9.2% | 33.6% | 2015-2026 | Intermediaire |
| [FuturesTrend](FuturesTrend/) | Donchian breakout ETFs (trend following) | **0.301** | 8.0% | 12.9% | 2018-2026 | Intermediaire |
| [MeanReversion](MeanReversion/) | RSI multi-asset mean reversion | **0.294** | 7.5% | 16.5% | 2015-2026 | Intermediaire |
| [TurnOfMonth](TurnOfMonth/) | Anomalie calendaire (Turn of Month) | 0.128 | 4.8% | 23.7% | 2015-2026 | Debutant |
| [VIX-TermStructure](VIX-TermStructure/) | Contango/backwardation VIX (SVXY) | 0.051 | 3.6% | 35.2% | 2010-2026 | Avance |
| [PairsTrading](PairsTrading/) | Statistical arbitrage equity pairs | -0.361 | 0.9% | 15.1% | 2010-2026 | Intermediaire |
| [ForexCarry](ForexCarry/) | FX momentum G7 currencies | -0.669 | 0.7% | 12.3% | 2018-2026 | Intermediaire |
| [ETF-Pairs](ETF-Pairs/) | Cointegration-based ETF pairs | -0.706 | -4.7% | 35.0% | 2020-2026 | Intermediaire |

### Strategies ESGF (org educative, backtests manuels)

| Projet | Description | Sharpe | Langue |
|--------|-------------|--------|--------|
| [Multi-Layer-EMA](Multi-Layer-EMA/) | Multi-layer EMA strategy | **1.891** | Python |
| [BTC-MACD-ADX](BTC-MACD-ADX/) | MACD + ADX filter BTC | **1.224** | C# |
| [BTC-ML](BTC-ML/) | Machine learning BTC prediction | - | Python |
| [Option-Wheel](Option-Wheel/) | Wheel strategy (sell puts/calls) | - | Python |

*Sharpe et metriques issus des backtests QC Cloud. Periodes variables selon la strategie.*

## Description des strategies

### EMA Crossover (Debutant)

Strategies simples basees sur le croisement de moyennes mobiles exponentielles (EMA 20/50) :

- **EMA-Cross-Crypto** : Long BTCUSDT quand EMA20 > EMA50, flat sinon. Binance Cash, daily.
- **EMA-Cross-Index** : Long SPY quand EMA20 > EMA50, flat sinon. Daily.
- **EMA-Cross-Stocks** : Equal-weight portfolio de 5 tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA). Chaque stock est long individuellement quand son EMA20 > EMA50.

### Momentum & Rotation (Intermediaire)

- **SectorMomentum** : Dual Momentum d'Antonacci entre SPY/TLT/GLD. Lookback 12 mois.
- **MomentumStrategy** : Rotation mensuelle parmi 11 ETFs sectoriels, top-3 par momentum.
- **FamaFrench** : Rotation trimestrielle entre 5 facteurs Fama-French (VLUE/MTUM/SIZE/QUAL/USMV).
- **DualMomentum** : Momentum absolu + relatif entre equities et bonds.
- **FuturesTrend** : Donchian breakout sur ETFs (trend following classique).

### Portfolio Construction (Intermediaire/Avance)

- **AllWeather** : Portfolio Bridgewater "All Weather" simplifie (SPY/TLT/IEF/GLD). Rebalancement avec drift 3%.
- **RiskParity** : Allocation inversement proportionnelle a la volatilite.
- **AdaptiveAssetAllocation (AAA)** : Momentum + minimum-variance sur un univers multi-asset.
- **RegimeSwitching** : Detection de regimes de marche (bull/bear/crisis) et rotation d'actifs.

### Mean Reversion & Pairs (Intermediaire)

- **MeanReversion** : Signaux RSI multi-asset, achat en survente, vente en surachat.
- **PairsTrading** : Arbitrage statistique sur paires d'actions cointegrees.
- **ETF-Pairs** : Cointegration-based pairs trading sur ETFs.

### Options & Volatilite (Avance)

- **OptionsIncome** : Covered calls sur SPY avec filtre VIX (bande 15-35). Resolution MINUTE.
- **VIX-TermStructure** : Trading de la structure a terme du VIX (contango/backwardation).

### Crypto avancee (Avance)

- **Crypto-MultiCanal** : 3 canaux ZigZag imbriques (macro/meso/micro) sur BTCUSDT. Signaux de rebond sur support et breakout de resistance. Trail SL a breakeven. Binance Cash daily.

### Anomalies calendaires (Debutant)

- **TurnOfMonth** : Exploitation de l'anomalie "Turn of Month" (derniers/premiers jours du mois).

### Forex (Intermediaire)

- **ForexCarry** : Strategie momentum/carry sur devises G7.

## Structure d'un Projet

```
MonProjet/
+-- main.py              # Algorithme (deploye sur QC Cloud)
+-- channel_helpers.py   # Helpers (si applicable)
+-- research.ipynb       # Notebook standalone (yfinance, executable partout)
+-- README.md            # Documentation (optionnel)
```

Chaque `research.ipynb` est **autonome** : il telecharge les donnees via yfinance et ne necessite ni QuantConnect ni Docker.

## Lecons Apprises

Patterns transversaux decouverts pendant l'optimisation iterative :

### Risk Management
- **SL 6% minimum sur BTC daily** : 5% trop serre, la volatilite intraday declenche le stop
- **Trail breakeven a 3%** : protege les gains sans couper les gros moves
- **Stop-loss -8% a -12%** pour actions : reduit MaxDD sans tronquer les reversions
- **Profit target 50%** pour options (TastyTrade) + bande VIX 15-35

### Signal Quality
- **TLT risk-off detruit la valeur** sur 2015-2026 (hausse des taux 2022). Alternatives: XLP/IEF/GLD/cash
- **Risk-adjusted momentum** (return/vol) superieur au momentum brut
- **SMA50 >> SMA100 pour crypto** : SMA100 trop lent, filtre les bonnes entrees
- **1 parametre a la fois** : changer plusieurs params simultanement cause des regressions

### Portfolio Construction
- **Drift rebalancing 3%** > SMA overlay pour portfolios statiques
- **Monthly + regime-change rebalancing** > daily : reduit les trades de 80%
- **Vol window 60d > 20d** pour covariance min-var
- **Ne pas combiner risk-adj momentum + min-var** : double penalisation

### Technique QC
- **Binance Cash** : `set_account_currency("USDT")` + `set_cash(N)`
- **Options** : Resolution.MINUTE obligatoire (sinon chain vide)
- **1 backtest a la fois** sur un node QC
- **`read_file` AVANT `update_file_contents`** pour le collaboration lock

## Utilisation

### Sur QuantConnect Cloud

1. Creer un nouveau projet Python
2. Copier le contenu de `main.py` (et `channel_helpers.py` si present)
3. Lancer le backtest

### En Local (research)

```bash
pip install yfinance pandas matplotlib
jupyter notebook projects/MomentumStrategy/research.ipynb
```

## Ressources

- [QuantConnect Community](https://www.quantconnect.com/forum)
- [Algorithm Lab](https://www.quantconnect.com/terminal)
- [Documentation](https://www.quantconnect.com/docs)
