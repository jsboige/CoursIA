# QuantConnect Algorithmic Trading Projects

Strategies de trading algorithmique backtestees sur QuantConnect Cloud, avec notebooks de recherche standalone (yfinance/pandas).

## Performance Summary

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Lang | Niveau |
|--------|-------------|--------|------|--------|---------|------|--------|
| [Multi-Layer-EMA](Multi-Layer-EMA/) | Multi-layer EMA + vol filter BTCUSDT | **1.891** | 120.9% | 54.4% | 2020-2026 | Py | Intermediaire |
| [EMA-Cross-Crypto](EMA-Cross-Crypto/) | EMA 20/50 + SMA200 + trailing stop BTCUSDT | **1.272** | 38.2% | 33.1% | 2020-2026 | Py | Debutant |
| [BTC-MACD-ADX](BTC-MACD-ADX/) | MACD + ADX filter BTC daily | **1.224** | 38.1% | 48.8% | 2009-2026 | C# | Intermediaire |
| [CSharp-BTC-EMA-Cross](CSharp-BTC-EMA-Cross/) | EMA crossover BTC (C#) | **1.094** | 36.2% | 40.7% | 2017-2026 | C# | Debutant |
| [Option-Wheel](Option-Wheel/) | Wheel strategy SPY (sell puts/calls) | **0.996** | 12.9% | 7.4% | 2019-2026 | Py | Avance |
| [EMA-Cross-Stocks](EMA-Cross-Stocks/) | EMA 20/50 multi-stock (AAPL/MSFT/GOOGL/AMZN/NVDA) | **0.872** | 25.7% | 35.7% | 2015-2026 | Py | Debutant |
| [SectorMomentum](SectorMomentum/) | Dual Momentum SPY/TLT/GLD (Antonacci) | **0.555** | 13.0% | 22.8% | 2015-2026 | Py | Intermediaire |
| [RegimeSwitching](RegimeSwitching/) | Regime detection + asset rotation | **0.553** | 11.7% | 33.0% | 2008-2026 | Py | Avance |
| [FamaFrench](FamaFrench/) | Factor ETF rotation (VLUE/MTUM/SIZE/QUAL/USMV) | **0.540** | 12.1% | 24.2% | 2015-2026 | Py | Intermediaire |
| [AllWeather](AllWeather/) | Portfolio multi-asset (SPY/IEF/GLD/XLP, no TLT) | **0.520** | 8.2% | 17.0% | 2015-2026 | Py | Debutant |
| [AdaptiveAssetAllocation](AdaptiveAssetAllocation/) | Momentum + min-variance multi-asset | **0.518** | 8.0% | 18.8% | 2008-2026 | Py | Avance |
| [Options-VGT](Options-VGT/) | Options income VGT (wheel NVDA/ORCL/CSCO/AMD/QCOM) | **0.507** | 14.2% | 16.2% | 2020-2026 | Py | Avance |
| [CSharp-CTG-Momentum](CSharp-CTG-Momentum/) | CTG momentum strategy (C#) | **0.507** | 17.7% | 36.1% | 2015-2026 | C# | Intermediaire |
| [Crypto-MultiCanal](Crypto-MultiCanal/) | ZigZag multi-channel (macro/meso/micro) BTCUSDT | **0.486** | 7.6% | 16.8% | 2020-2026 | Py | Avance |
| [MomentumStrategy](MomentumStrategy/) | Rotation momentum 11 ETFs + stop-loss | **0.472** | 11.1% | 25.8% | 2015-2026 | Py | Intermediaire |
| [EMA-Cross-Index](EMA-Cross-Index/) | EMA 20/60 + cooldown 3d SPY | **0.470** | 9.4% | 17.5% | 2015-2026 | Py | Debutant |
| [RiskParity](RiskParity/) | Risk parity multi-asset portfolio | **0.399** | 7.8% | 20.9% | 2015-2026 | Py | Intermediaire |
| [DualMomentum](DualMomentum/) | Absolute + relative momentum ETFs | **0.350** | 9.2% | 33.6% | 2015-2026 | Py | Intermediaire |
| [FuturesTrend](FuturesTrend/) | Donchian breakout ETFs (trend following) | **0.301** | 8.0% | 12.9% | 2018-2026 | Py | Intermediaire |
| [MeanReversion](MeanReversion/) | RSI multi-asset mean reversion | **0.294** | 7.5% | 16.5% | 2015-2026 | Py | Intermediaire |
| [BTC-ML](BTC-ML/) | Machine learning BTC prediction | **0.282** | 8.3% | 13.7% | 2023-2026 | Py | Avance |
| [OptionsIncome](OptionsIncome/) | Covered Call SPY + VIX filter | **0.234** | 6.8% | 19.3% | 2018-2026 | Py | Avance |
| [TurnOfMonth](TurnOfMonth/) | Anomalie calendaire (Turn of Month) | 0.128 | 4.8% | 23.7% | 2015-2026 | Py | Debutant |
| [Trend-Following](Trend-Following/) | Multi-oracle trend following (MACD/RSI/Bollinger) | 0.060 | -14.3% | 80.6% | 2019-2026 | Py | Avance |
| [VIX-TermStructure](VIX-TermStructure/) | Contango/backwardation VIX (SVXY) | 0.051 | 3.6% | 35.2% | 2010-2026 | Py | Avance |
| [ForexCarry](ForexCarry/) | FX momentum IR + skip-month G10 | -0.324 | 1.5% | 10.5% | 2013-2026 | Py | Intermediaire |
| [PairsTrading](PairsTrading/) | Statistical arbitrage equity pairs | -0.361 | 0.9% | 15.1% | 2010-2026 | Py | Intermediaire |
| [ETF-Pairs](ETF-Pairs/) | Cointegration-based ETF pairs | -0.706 | -4.7% | 35.0% | 2020-2026 | Py | Intermediaire |

*28 strategies au total (25 Python, 3 C#). Metriques issues des backtests QC Cloud.*

## Description des strategies

### EMA Crossover (Debutant)

Strategies basees sur le croisement de moyennes mobiles exponentielles :

- **EMA-Cross-Crypto** : Long BTCUSDT quand EMA20 > EMA50 ET BTC > SMA200 (filtre bull). Trailing stop 10%, position 80%. Binance Cash, daily.
- **EMA-Cross-Index** : Long SPY quand EMA20 > EMA60, flat sinon. Cooldown 3 jours apres sortie. Daily.
- **EMA-Cross-Stocks** : Equal-weight portfolio de 5 tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA). Chaque stock est long individuellement quand son EMA20 > EMA50.
- **Multi-Layer-EMA** : EMA multi-couches sur BTCUSDT avec filtre de volatilite (seuil 60%). Allocation 100%.
- **CSharp-BTC-EMA-Cross** : EMA crossover BTC en C# avec parametres (45, 120). Daily.

### Trend Following & Indicateurs Techniques (Intermediaire/Avance)

- **Trend-Following** : Multi-oracle scoring (MACD, RSI, Bollinger) + detection HH/HL/LL/LH + ATR trailing stop. Universe equity top 600. Multi-fichiers (alpha.py, oracles). Hourly resolution.
- **BTC-MACD-ADX** : MACD + ADX filter sur BTC daily en C#. Backtest long (2009-2026).
- **CSharp-CTG-Momentum** : Momentum strategy avec indicateurs custom en C#.

### Momentum & Rotation (Intermediaire)

- **SectorMomentum** : Dual Momentum d'Antonacci entre SPY/TLT/GLD. Lookback 12 mois.
- **MomentumStrategy** : Rotation mensuelle parmi 11 ETFs sectoriels, top-3 par momentum + stop-loss -10%.
- **FamaFrench** : Rotation trimestrielle entre 5 facteurs Fama-French (VLUE/MTUM/SIZE/QUAL/USMV).
- **DualMomentum** : Momentum absolu + relatif entre equities et bonds.
- **FuturesTrend** : Donchian breakout sur ETFs (trend following classique).

### Portfolio Construction (Intermediaire/Avance)

- **AllWeather** : Portfolio "All Weather" simplifie (SPY 30%/IEF 40%/GLD 20%/XLP 10%, TLT elimine). Drift rebalancing 3%.
- **RiskParity** : Allocation inversement proportionnelle a la volatilite.
- **AdaptiveAssetAllocation (AAA)** : Momentum + minimum-variance sur un univers multi-asset.
- **RegimeSwitching** : Detection de regimes de marche (bull/bear/crisis) et rotation d'actifs.

### Mean Reversion & Pairs (Intermediaire)

- **MeanReversion** : Signaux RSI multi-asset, achat en survente, vente en surachat.
- **PairsTrading** : Arbitrage statistique sur paires d'actions cointegrees.
- **ETF-Pairs** : Cointegration-based pairs trading sur ETFs.

### Options & Volatilite (Avance)

- **OptionsIncome** : Covered calls sur SPY avec filtre VIX (bande 15-35). Resolution MINUTE.
- **Option-Wheel** : Wheel strategy sur SPY (sell puts, si assigne sell calls). DTE 30, OTM 5%.
- **Options-VGT** : Covered calls sur VGT ETF (NVDA/ORCL/CSCO/AMD/QCOM). Resolution MINUTE.
- **VIX-TermStructure** : Trading de la structure a terme du VIX (contango/backwardation).

### Crypto avancee (Avance)

- **Crypto-MultiCanal** : 3 canaux ZigZag imbriques (macro/meso/micro) sur BTCUSDT. Signaux de rebond sur support et breakout de resistance. Trail SL a breakeven. Binance Cash daily.
- **BTC-ML** : Prediction BTC par machine learning (features techniques + filtre de volatilite 60%).

### Anomalies calendaires (Debutant)

- **TurnOfMonth** : Exploitation de l'anomalie "Turn of Month" (derniers/premiers jours du mois).

### Forex (Intermediaire)

- **ForexCarry** : Strategie momentum FX G10 risk-adjusted (IR + skip-month). Etendue 2013-2026.

## Structure d'un Projet

```
MonProjet/
+-- main.py / Main.cs    # Algorithme Python ou C# (deploye sur QC Cloud)
+-- alpha.py / helpers    # Modules auxiliaires (si applicable)
+-- research.ipynb        # Notebook standalone (yfinance, executable partout)
+-- README.md             # Documentation (optionnel)
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
