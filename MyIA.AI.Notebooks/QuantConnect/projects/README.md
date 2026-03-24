# QuantConnect Algorithmic Trading Projects

Bibliotheque pedagogique de 36 strategies de trading algorithmique backtestees sur QuantConnect Cloud.
Chaque strategie illustre un concept ou une famille de strategies ; les performances varient volontairement
pour montrer que toutes les idees academiques ne survivent pas au backtest realiste.

## Classification

Les strategies sont classees en 3 categories pedagogiques :

| Label | Signification | Action |
|-------|---------------|--------|
| **Robuste** | Sharpe > 0.5, stable sur longue periode, signal propre | Conserver, iterer si besoin |
| **Historique** | Prime connue mais regime-dependante ou affaiblie | Conserver comme contre-exemple, documenter les regimes favorables |
| **Exploratoire** | Implementation naive ou signal insuffisant | Conserver si pedagogique, sinon retravailler |

Voir [OPTIMIZATION_BACKLOG.md](OPTIMIZATION_BACKLOG.md) pour les plafonds structurels et hypotheses testees.

## Performance Summary

### Robuste (Sharpe > 0.5)

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Lang | Niveau | Research | Note |
|--------|-------------|--------|------|--------|---------|------|--------|----------|------|
| [BTC-MACD-ADX](BTC-MACD-ADX/) | MACD + ADX filter BTC daily | **1.647** | 38.1% | 48.8% | 2020-2026 | C# | Intermediaire | — | |
| [Framework_Composite_TrendWeather](Framework_Composite_TrendWeather/) | TrendStocksLite + AllWeather via Algorithm Framework (T75/AW25, Mom3m) | **1.155** | 27.4% | 27.7% | 2015-2026 | Py | Avance | QuantBook | |
| [EMA-Cross-Crypto](EMA-Cross-Crypto/) | EMA 20/50 + SMA200 + trailing stop BTCUSDT | **1.272** | 38.2% | 33.1% | 2017-2026 | Py | Debutant | yfinance | ⏳ Période étendue 2020→2017, backtest en attente |
| [CSharp-BTC-EMA-Cross](CSharp-BTC-EMA-Cross/) | EMA crossover BTC (C#) | **1.094** | 36.2% | 40.7% | 2017-2026 | C# | Debutant | — | |
| [Option-Wheel](Option-Wheel/) | Wheel strategy SPY (sell puts/calls) | **0.524** | 12.69% | 26.40% | 2015-2026 | Py | Avance | QuantBook | ✅ Validé 2015-2026 (Sharpe 0.524) |
| [EMA-Cross-Stocks](EMA-Cross-Stocks/) | EMA 20/50 multi-stock (AAPL/MSFT/GOOGL/AMZN/NVDA) | **0.872** | 25.7% | 35.7% | 2015-2026 | Py | Debutant | — | |
| [TrendStocksLite](TrendStocksLite/) | EMA20/50 + SMA200 trend 15 large-caps diversifies | **0.719** | 18.2% | 33.7% | 2015-2026 | Py | Intermediaire | — | |
| [AllWeather](AllWeather/) | Portfolio multi-asset (SPY/IEF/GLD/XLP, no TLT) | **0.667** | 9.3% | 16.4% | 2010-2026 | Py | Debutant | yfinance | |
| [SectorMomentum](SectorMomentum/) | Dual Momentum SPY/TLT/GLD (Antonacci) | **0.621** | 13.2% | 22.8% | 2010-2026 | Py | Intermediaire | yfinance | |
| [MomentumStrategy](MomentumStrategy/) | Rotation momentum 11 ETFs + stop-loss | **0.565** | 11.8% | 25.8% | 2010-2026 | Py | Intermediaire | yfinance | |
| [RegimeSwitching](RegimeSwitching/) | Regime detection + asset rotation | **0.553** | 11.7% | 33.0% | 2008-2026 | Py | Avance | — | |
| [FamaFrench](FamaFrench/) | Factor ETF rotation (VLUE/MTUM/SIZE/QUAL/USMV) | **0.540** | 12.1% | 24.2% | 2015-2026 | Py | Intermediaire | yfinance | |
| [AdaptiveAssetAllocation](AdaptiveAssetAllocation/) | Momentum + min-variance multi-asset | **0.518** | 8.0% | 18.8% | 2008-2026 | Py | Avance | — | |
| [Options-VGT](Options-VGT/) | Options income VGT (wheel NVDA/ORCL/CSCO/AMD/QCOM) | **0.507** | 14.2% | 16.2% | 2020-2026 | Py | Avance | — | |
| [CSharp-CTG-Momentum](CSharp-CTG-Momentum/) | CTG momentum strategy (C#) | **0.507** | 17.7% | 36.1% | 2015-2026 | C# | Intermediaire | — | |

### Historique / Regime-dependante (Sharpe 0-0.5, prime connue mais affaiblie)

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Lang | Niveau | Research | Note |
|--------|-------------|--------|------|--------|---------|------|--------|----------|------|
| [Multi-Layer-EMA](Multi-Layer-EMA/) | Multi-layer EMA + vol filter BTCUSDT | **0.928** | 120.9% | 54.4% | 2020-2026 | Py | Intermediaire | QuantBook | NON ROBUSTE: Sharpe chute a 0.38 hors bulle 2017, MaxDD 67.7% |
| [Crypto-MultiCanal](Crypto-MultiCanal/) | ZigZag multi-channel (macro/meso/micro) BTCUSDT | **0.486** | 7.6% | 16.8% | 2017-2026 | Py | Avance | QuantBook | Plafond apres 18 versions. ⏳ Période étendue 2020→2017, backtest en attente |
| [EMA-Cross-Index](EMA-Cross-Index/) | EMA 20/60 + cooldown 3d SPY | **0.470** | 9.4% | 17.5% | 2015-2026 | Py | Debutant | yfinance | 25 combos testees |
| [DualMomentumNoTLT](DualMomentumNoTLT/) | Momentum rotation SPY/QQQ/IEF/GLD/XLP (no TLT) | **0.469** | 11.0% | 23.6% | 2015-2026 | Py | Intermediaire | — | Variante sans TLT |
| [RiskParity](RiskParity/) | Risk parity multi-asset portfolio | **0.399** | 7.8% | 20.9% | 2015-2026 | Py | Intermediaire | — | Plafond (3 hyp. rejetees) |
| [DualMomentum](DualMomentum/) | Absolute + relative momentum ETFs | **0.350** | 9.2% | 33.6% | 2015-2026 | Py | Intermediaire | yfinance | MaxDD COVID structurel |
| [FuturesTrend](FuturesTrend/) | Donchian breakout ETFs (trend following) | **0.136** | 4.896% | 18.70% | 2015-2026 | Py | Intermediaire | yfinance | ✅ Validé 2015-2026 (Sharpe 0.136) |
| [MeanReversion](MeanReversion/) | RSI multi-asset mean reversion | **0.294** | 7.5% | 16.5% | 2015-2026 | Py | Intermediaire | yfinance | SMA filter rejete |
| [BTC-ML](BTC-ML/) | Machine learning BTC prediction | **0.282** | 8.3% | 13.7% | 2023-2026 | Py | Avance | QuantBook | Periode courte, potentiel features |
| [OptionsIncome](OptionsIncome/) | Covered Call SPY + VIX filter | **0.207** | 5.435% | 17.50% | 2015-2026 | Py | Avance | — | ✅ Validé 2015-2026 (Sharpe 0.207) |
| [Trend-Following](Trend-Following/) | Multi-oracle trend following (MACD/RSI/Bollinger) | **0.212** | 7.3% | 40.9% | 2015-2026 | Py | Avance | — | v2 apres revert leverage. ⏳ Période étendue 2019→2015, backtest en attente |
| [TurnOfMonth](TurnOfMonth/) | Anomalie calendaire (Turn of Month) | 0.128 | 4.8% | 23.7% | 2015-2026 | Py | Debutant | yfinance | Effet faible en bull 2015-2026 |
| [VIX-TermStructure](VIX-TermStructure/) | Contango/backwardation VIX (SVXY) | 0.051 | 3.6% | 35.2% | 2010-2026 | Py | Avance | yfinance | Post-VIXplosion, SVXY affaibli |

### Exploratoire / Implementation insuffisante (Sharpe < 0)

| Projet | Description | Sharpe | CAGR | Max DD | Periode | Lang | Niveau | Research | Probleme |
|--------|-------------|--------|------|--------|---------|------|--------|----------|----------|
| [TrendFilteredMeanReversion](TrendFilteredMeanReversion/) | RSI(2) pullback SPY en bull regime (SMA200) | -0.016 | 3.4% | 11.4% | 2015-2026 | Py | Debutant | — | Signal reel (73% win) mais trop rare (~9 trades/an) |
| [ForexCarry](ForexCarry/) | FX momentum IR + skip-month G10 | -0.324 | 1.5% | 10.5% | 2013-2026 | Py | Intermediaire | yfinance | CAGR < T-bills, carry prime evaporee |
| [PairsTrading](PairsTrading/) | Statistical arbitrage equity pairs | -0.361 | 0.9% | 15.1% | 2010-2026 | Py | Intermediaire | — | Paires non cointegrees 2010-2026 |
| [ETF-Pairs](ETF-Pairs/) | Cointegration-based ETF pairs | -0.706 | -4.7% | 35.0% | 2020-2026 | Py | Intermediaire | QuantBook | Cointregration instable |

*36 strategies au total (33 Python, 3 C#). Metriques issues des backtests QC Cloud (3 projets ML en phase de recherche).*
*Multi-Layer-EMA reclassee Historique apres analyse de robustesse (Sharpe gonfle par bulle BTC 2017).*
*Research: type de notebook de recherche (yfinance = donnees Yahoo, QuantBook = donnees QC natives, — = pas de notebook).*

## Description des strategies

### EMA Crossover (Debutant)

Strategies basees sur le croisement de moyennes mobiles exponentielles :

- **EMA-Cross-Crypto** : Long BTCUSDT quand EMA20 > EMA50 ET BTC > SMA200 (filtre bull). Trailing stop 10%, position 80%. Binance Cash, daily.
- **EMA-Cross-Index** : Long SPY quand EMA20 > EMA60, flat sinon. Cooldown 3 jours apres sortie. Daily.
- **EMA-Cross-Stocks** : Equal-weight portfolio de 5 tech stocks (AAPL, MSFT, GOOGL, AMZN, NVDA). Chaque stock est long individuellement quand son EMA20 > EMA50.
- **TrendStocksLite** : EMA20/50 + SMA200 filter sur 15 large-caps diversifies (5 secteurs). Equal-weight hebdomadaire. Extension de EMA-Cross-Stocks.
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
- **DualMomentumNoTLT** : Momentum rotation mensuelle sur SPY/QQQ/IEF/GLD/XLP (sans TLT). Top-2 par momentum 12M.
- **FuturesTrend** : Donchian breakout sur ETFs (trend following classique).

### Portfolio Construction (Intermediaire/Avance)

- **Framework_Composite_TrendWeather** : Composite strategy combinant TrendStocksLite (15 large-caps momentum-weighted) + AllWeather (SPY/IEF/GLD/XLP) via QC Algorithm Framework. T75/AW25 allocation, 3m momentum weighting, monthly rebalance. Itere de v1.0 (Sharpe 0.622) a v1.5 (Sharpe 1.155).
- **Framework_Composite_FamaFrenchAllWeather** : Composite strategy combinant FamaFrench (5 facteurs ETF avec momentum risk-adjusted) + AllWeather (SPY/IEF/GLD/XLP) via QC Algorithm Framework. Baseline FF50/AW50, allocation sweep prevu (FF40/AW60, FF50/AW50, FF60/AW40). **PENDING QC deployment et backtest.**
- **AllWeather** : Portfolio "All Weather" simplifie (SPY 30%/IEF 30%/GLD 30%/XLP 10%, TLT elimine). Drift rebalancing 3%.
- **RiskParity** : Allocation inversement proportionnelle a la volatilite.
- **AdaptiveAssetAllocation (AAA)** : Momentum + minimum-variance sur un univers multi-asset.
- **RegimeSwitching** : Detection de regimes de marche (bull/bear/crisis) et rotation d'actifs.

### Mean Reversion & Pairs (Intermediaire)

- **MeanReversion** : Signaux RSI multi-asset, achat en survente, vente en surachat.
- **TrendFilteredMeanReversion** : RSI(2) pullback sur SPY conditionne par regime bull (SMA200). Time stop 5 jours.
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
- **Crypto-LSTM-Prediction** : Deep Learning DLinear (AAAI 2023) pour prediction BTCUSDT. PyTorch avec SeriesDecomposition (trend/seasonal). **Research Phase**.

### Machine Learning / Deep Learning (Research Phase)

Projets pedagogiques bases sur HandsOnAITrading book, en phase de recherche :

- **Sector-ML-Classification** : Random Forest pour classification de rotation sectorielle (11 sector ETFs). Features techniques (RSI, MACD, SMA, EMA, ATR, Bollinger). Target: BUY/HOLD/AVOID. **Research Phase**.
- **Portfolio-Optimization-ML** : MPT (Markowitz) avec covariance Ledoit-Wolf + returns predits par ML. Universe: 15 large-caps US (5 secteurs). Risk Parity weighting. **Research Phase**.

### Anomalies calendaires (Debutant)

- **TurnOfMonth** : Exploitation de l'anomalie "Turn of Month" (derniers/premiers jours du mois).

### Forex (Intermediaire)

- **ForexCarry** : Strategie momentum FX G10 risk-adjusted (IR + skip-month). Etendue 2013-2026.

## Structure d'un Projet

```
MonProjet/
+-- main.py / Main.cs    # Algorithme Python ou C# (deploye sur QC Cloud)
+-- alpha.py / helpers    # Modules auxiliaires (si applicable)
+-- research.ipynb        # Notebook de recherche exploratoire
+-- quantbook.ipynb       # Notebook QuantBook (donnees QC natives, optionnel)
+-- README.md             # Documentation (optionnel)
```

### Types de notebooks de recherche

| Type | Source de donnees | Avantage | Inconvenient |
|------|-------------------|----------|--------------|
| **yfinance** (standalone) | Yahoo Finance | Executable partout, pas besoin de QC | Divergences possibles avec QC (REITs, bond ETFs, dividendes) |
| **QuantBook** (QC native) | QuantConnect | Donnees identiques au backtest, memes indicateurs | Necessite l'environnement QC (Docker lean ou cloud) |

**Recommandation QC** : Passer plus de temps dans la recherche exploratoire (QuantBook) que dans les backtests d'algo.
Les notebooks yfinance restent utiles pedagogiquement (accessibles aux etudiants sans compte QC)
mais les conclusions doivent etre validees avec les donnees QC avant implementation.

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
