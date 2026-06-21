# Quantitative Trading with QuantConnect - Partner Course Template

Workspace for partner school quant trading courses.
Sponsored by Jared Broad (CEO QuantConnect) via the "Trading Firm" tier.

---

## Student Registration

### Registration Process

To participate and benefit from QuantConnect sponsoring (Trading Firm tier):

1. **Create a free account** on [quantconnect.com](https://www.quantconnect.com) with your **school email**
2. **Send your username** to the instructor
3. **Wait to be added** to the Trading Firm organization
4. **Start the exercises** : notebooks QC-Py-01 to QC-Py-04, then course exercises

### Cloud-First Workflow

All development happens on **QuantConnect Cloud** (QC Lab), not locally.

- **Benefits** : No local installation, access to QC historical data, instant compilation
- **Projects** : Create your projects directly in QuantConnect Lab

---

## Student Templates

Templates in `templates/` are starting points for your projects. Each level corresponds to increasing difficulty.

### Starter (Beginner)

**File** : `templates/starter/main.py`

**Strategy** : EMA crossover on BTCUSDT (Golden Cross / Death Cross)

**Prerequisites** :
- Completed notebooks QC-Py-01 to QC-Py-04
- Understand the basics : Initialize, OnData, indicators

**Concepts covered** :
- `AddCrypto` : Add a crypto asset with market and resolution
- `self.EMA(...)` : Create an Exponential Moving Average indicator
- `SetWarmUp` : Pre-warm indicators before trading
- `SetHoldings` : Allocate a percentage of the portfolio
- `Liquidate` : Sell the entire position
- `OnOrderEvent` : Receive execution notifications

**Suggested modifications** :
- Change EMA periods : (5, 20), (20, 50) or (50, 200)
- Add an RSI filter : don't buy if RSI > 70
- Implement a -5% stop-loss
- Test on other cryptos : ETHUSDT, SOLUSDT

**Full documentation** : [templates/starter/README.md](templates/starter/README.md)

---

### Intermediate

**File** : `templates/intermediate/main.py`

**Strategy** : Momentum ranking on S&P 500 stocks with Alpha Framework

**Prerequisites** :
- Completed QC-Py-13 (Alpha Models)
- Understand the QC Algorithm Framework

**Alpha Framework Modules** :
| Module | Role | Class |
|--------|------|-------|
| **AlphaModel** | Generate signals (Insights) | `MomentumAlphaModel` |
| **PortfolioConstructionModel** | Convert Insights to allocations | `EqualWeightingPortfolioConstructionModel` |
| **RiskManagementModel** | Adjust for risk | `TrailingStopRiskManagementModel(0.05)` |
| **ExecutionModel** | Send orders | `ImmediateExecutionModel` |

**Suggested modifications** :
- Change the momentum lookback : 60, 120 or 252 days
- Add an RSI filter to avoid overbought stocks
- Sector filtering : focus on specific sectors
- Change construction model : InsightWeighting, MeanVariance, RiskParity

**Full documentation** : [templates/intermediate/README.md](templates/intermediate/README.md)

---

### Advanced

**File** : `templates/advanced/main.py`

**Strategy** : Machine Learning (RandomForest) on BTCUSDT

**Prerequisites** :
- Completed QC-Py-18 (ML Features Engineering) and QC-Py-19 (ML Classification)
- Familiar with sklearn : RandomForestClassifier, feature engineering

**ML Pipeline** :
```
Data (BTCUSDT Daily)
    -> Feature Engineering (SMA, RSI, EMA ratios, returns)
    -> RandomForest Training (100 trees, max_depth=5)
    -> Daily Prediction (1 = long, 0 = cash)
    -> Automatic Monthly Re-training
```

**Suggested modifications** :
- Add features : ADX, ATR, Bollinger Bands, volume
- Try other models : XGBoost, SVC
- Add short positions (requires Margin account)
- Walk-forward optimization : train on N months, test on next month
- Risk management : stop-loss, take-profit, position sizing

**Full documentation** : [templates/advanced/README.md](templates/advanced/README.md)

---

## Instructor Examples

The `examples/` directory contains validated projects with positive backtests.

### Python - Crypto

| Project | Cloud ID | Description |
|---------|----------|-------------|
| **Multi-Layer-EMA** | 20216947 | EMA crossover multi-crypto (BTC/ETH/LTC) + RSI filter |

### Python - Equities/ETFs

| Project | Cloud ID | Description |
|---------|----------|-------------|
| **Sector-Momentum** | 20216980 | Dual momentum SPY/TLT/GLD + Risk Parity PCM |
| **Trend-Following** | 20216930 | Multi-oracle (MACD/RSI/Bollinger) + ATR trailing stop |

### Python - Options

| Project | Cloud ID | Description |
|---------|----------|-------------|
| **Options-VGT** | 21113806 | OTM PUT selling on 5 tech stocks (NVDA, ORCL, CSCO, AMD, QCOM) |
| **Option-Wheel-Strategy** | 20216898 | Wheel strategy SPY : PUT selling -> assignment -> covered CALL |

### Python - ML

| Project | Cloud ID | Description |
|---------|----------|-------------|
| **ML-RandomForest** | 29686996 | RandomForest on large-cap stocks, 6 features, monthly re-training |
| **Framework-Composite** | 29687005 | Alpha Framework : EMAMomentum + SectorMomentum alphas, MaxDD 15% |

### C#

| Project | Cloud ID | Description |
|---------|----------|-------------|
| **CSharp-BTC-MACD-ADX** | 19898232 | BTC MACD+ADX daily on Binance Cash |
| **CSharp-BTC-EMA-Cross** | 19050970 | Classic BTC EMA crossover (18/23) |
| **CSharp-CTG-Momentum** | 19225388 | "Stocks on the Move" (Clenow) - Momentum ranking |

---

## Research Notebooks (QuantBook)

Five Researcher projects with operational QuantBook notebooks for exploring QC Cloud data :

| Project | Cloud ID | QuantBook | Research Content |
|---------|----------|-----------|------------------|
| **Multi-Layer-EMA-Researcher** | 28433748 | research.ipynb | Grid search EMA/RSI/stop-loss on BTC/ETH/LTC |
| **BTC-ML-Researcher** | 28433750 | research.ipynb | Feature importance, walk-forward, confidence grid |
| **MomentumStrategy-Researcher** | 28657837 | quantbook.ipynb | H1-H4 : top-N, lookback, vol window, regime filter |
| **AllWeather-Researcher** | 28657833 | quantbook.ipynb | Grid search allocations All-Weather (SPY/IEF/GLD/XLP) |
| **Sector-Momentum-Researcher** | 28433643 | quantbook.ipynb + research.ipynb | Dual Momentum SPY/TLT/GLD, full redesign |

These notebooks illustrate the QuantBook -> QCAlgorithm workflow : idea -> research -> backtest.

---

## ML Research 2026 - Validated Models (Pipeline V2)

The ML research pipeline (`ML-Training-Pipeline/`) follows a 7-stage curriculum
based on *Hands-On AI Trading* (Broad/QuantConnect, 2025). Models below passed
the **S1 (vol-forecasting)** gate with significant Diebold-Mariano test
(p < 0.05, >= 4 seeds, walk-forward 5-fold).

### S1 KEEPERS - Multi-coin crypto volatility forecasting (BEATS)

| Model | Task | Verdict | DM p-value | Architecture |
|-------|------|---------|-----------|--------------|
| **M12 HAR-RV-J** | 5-day vol forecast | BEATS RW + GARCH | **0.0015** | Heterogeneous Autoregressive + Jump component (Corsi 2009) |
| **M15 LSTM h=32** | Short-scale vol forecast | BEATS RW | **0.0107** | LSTM hidden=32, 53/84 combos BEAT cross-coin (BTC/XRP/DOT/ADA) |

Complementarity observed : M12 captures ETH/SOL better, M15 captures DOT better.

### S3 - HMM Regime daily (delivered, feeds S5 sizing)

Hidden Markov Model 2-regime (calm vs stress) on daily returns SPY+VIX+BTC.
Discrete output used as switch in vol-target strategies (reduce exposure in stress regime).

### S4 v2 - Inverse-Vol Ridge + HMM Regime (BEATS EqW)

Inverse-vol weighted allocation with Ridge regression on features
(momentum + M12 vol forecast) and HMM switch. Delta Sharpe **+0.325 vs EqW**
(Equal Weight baseline) on QC Cloud backtest.

### L4 Decision Transformer - Action-based trading (BEATS)

First model to beat buy-and-hold across 24/26 symbols. Action-based (buy/hold/sell classification)
massively outperforms forecast-based approaches (PatchTST). Median AUC 0.5582, 104 combos validated.

### QC Cloud strategies powered by these models

| QC Cloud Project | Cloud ID | Source Model | Description |
|-----------------|----------|-------------|-------------|
| **HAR-RV-Kelly** | 31456164 | M12 HAR-RV-J | Vol forecast -> Kelly 1/4 sizing on SPY/EFA/EEM/TLT/GLD/DBC |
| **Vol-GARCH-Target** | 31456084 | GARCH(1,1) baseline | Vol-targeting 15% annualized (reference for M12) |
| **Vol-Ensemble-Conservative** | 31456204 | Ensemble M12+M15 | Inverse-vol weighting + leverage cap |

These projects are available in `../projects/`.

---

## Pedagogical Concepts Covered

Examples and templates cover **4 asset classes** and **8+ trading concepts** :

| Level | Concepts | Strategies |
|-------|----------|------------|
| **1 - Foundations** | EMA Crossover, MACD+ADX, Basic Options | Multi-Layer-EMA, CSharp-BTC-EMA-Cross, Options-VGT |
| **2 - Intermediate** | Alpha Framework, Multi-indicators, Wheel Strategy | Sector-Momentum, Option-Wheel-Strategy, Trend-Following |
| **3 - Advanced** | Momentum ranking, Risk Parity, ML | CSharp-CTG-Momentum, Sector-Momentum, ML-RandomForest |

---

## Backtest Results

### Instructor Examples - 8 validated projects

| # | Project | Sharpe | CAGR | Max DD |
|---|---------|--------|------|--------|
| 1 | **Sector-Momentum** | 2.530 | 66.1% | 5.6% |
| 2 | **Trend-Following** | 2.157 | 136.0% | 20.5% |
| 3 | **Multi-Layer-EMA** | 1.891 | 120.9% | 54.4% |
| 4 | **CSharp-BTC-MACD-ADX** | 1.224 | 38.1% | 48.8% |
| 5 | **CSharp-BTC-EMA-Cross** | 1.094 | 36.2% | 40.7% |
| 6 | **Options-VGT** | 0.892 | 25.3% | 15.6% |
| 7 | **Option-Wheel-Strategy** | 0.524 | 12.7% | 26.4% |
| 8 | **CSharp-CTG-Momentum** | 0.507 | 17.7% | 36.1% |

---

## Recommended Learning Path

### For beginners

1. **Foundation notebooks** : QC-Py-01 to QC-Py-04 (~4.5h)
2. **Starter Template** : Understand and modify `templates/starter/main.py`
3. **First personal project** : Adapt the template with your ideas
4. **Iteration** : Backtest, analyze results, improve

### For intermediate

1. **Alpha Framework notebooks** : QC-Py-13 to QC-Py-15 (~4h)
2. **Intermediate Template** : Study `templates/intermediate/main.py`
3. **Example projects** : Analyze `Sector-Momentum`, `Trend-Following`
4. **Personal project** : Create your own strategy with Alpha Framework

### For advanced

1. **ML notebooks** : QC-Py-18 to QC-Py-21 (~4h)
2. **Advanced Template** : Study `templates/advanced/main.py`
3. **ML projects** : Analyze `BTC-MachineLearning`, `Sector-ML-Classification`
4. **Advanced research** : Features engineering, hyperparameter tuning, walk-forward

---

## Companion Notebooks

28 progressive Python notebooks in `../Python/` (QC-Py-01 to QC-Py-28) :

1. **Setup** : Account, IDE, first algorithm
2. **Foundations** : API, Resolution, Consolidators, QuantBook
3. **Indicators** : MACD, RSI, Bollinger, EMA
4. **Strategies** : Mean Reversion, Momentum, Pairs Trading, Options
5. **Framework** : Alpha, Portfolio Construction, Risk, Execution
6. **ML/AI** : Features, models, ObjectStore, RL, NLP
7. **Production** : Paper trading, live, monitoring

---

## Documentation

- **[GETTING-STARTED.md](../GETTING-STARTED.md)** : Detailed getting started guide
- **[projects/README.md](../projects/README.md)** : Strategy catalog

---

## Conclusion / Prochaines étapes

### Ce que vous avez appris

Ce cours partenaire est une **plateforme de démarrage structurée** vers le trading algorithmique professionnel sur QuantConnect, pensée pour des étudiants partant de zéro jusqu'à un projet personnel ML. Il s'appuie sur deux piliers :

- **Le workflow Cloud-First** : tout le développement se fait sur QuantConnect Cloud (QC Lab), sans installation locale — accès direct aux données historiques QC, compilation instantanée, et sponsoring *Trading Firm* offert par Jared Broad / QuantConnect. On apprend que la plateforme gère l'infrastructure pour que l'étudiant se concentre sur la *stratégie*, pas sur le plumbing.
- **Les templates progressifs** : trois points de départ (`starter` → `intermediate` → `advanced`) calibrés par difficulté croissante. Le `starter` (EMA crossover sur BTCUSDT) enseigne le `QCAlgorithm` lifecycle ; l'`intermediate` introduit l'Algorithm Framework modulaire ; l'`advanced` ajoute le machine learning. On apprend qu'**un bon template est un échafaudage** : il code les bonnes pratiques (Initialize, Risk Management, execution) pour que l'étudiant itère sur l'alpha, pas sur la plomberie.
- **Les exemples de projets** (`Sector-Momentum`, `Trend-Following`, `BTC-MachineLearning`, `Sector-ML-Classification`) montrent des stratégies *achevées* à étudier puis adapter. On apprend que **lire du code qui marche** est aussi formateur que d'en écrire.

Le fil rouge : la **progression pédagogique** — les 28 notebooks compagnons (`../Python/`, QC-Py-01 à 28) fournissent la théorie, et ce cours fournit la *pratique guidée* via templates et exemples. Les deux sont conçus pour avancer ensemble.

### Prochaines étapes

1. **Créer votre compte** sur [quantconnect.com](https://www.quantconnect.com) avec votre email d'école, puis envoyer votre username à l'instructeur pour rejoindre l'organisation *Trading Firm*.
2. **Faire les fondations** : notebooks QC-Py-01 à 04 avant tout (compte, lifecycle, data, QuantBook).
3. **Démarrer avec le template `starter`** : copier `templates/starter/main.py` dans un projet QC Lab, le backtester, puis le modifier (changer la paire, la période EMA).
4. **Monter de niveau** : passer à `intermediate` (Algorithm Framework) puis `advanced` (ML) à mesure que vous maîtrisez le niveau précédent.
5. **Étudier puis adapter un exemple** : analyser `Sector-Momentum` ou `Trend-Following`, comprendre chaque module, puis créer votre propre variante comme projet personnel.
6. **Consulter le catalogue** : `../projects/README.md` recense les 50+ stratégies backtestées de la série complète pour inspiration et comparaison.

> **Rappel honnête** : un template qui backteste bien n'est pas une stratégie déployable. Le sponsoring vous donne l'infrastructure, pas l'edge. La même discipline que dans toute la série QuantConnect s'applique : walk-forward, out-of-sample, et Sharpe *net* après frais avant de croire à un résultat.

---

## Resources

- [QuantConnect Documentation](https://www.quantconnect.com/docs)
- [Hands-On AI Trading Book](https://www.hands-on-ai-trading.com)
- [Book GitHub](https://github.com/QuantConnect/HandsOnAITradingBook)
