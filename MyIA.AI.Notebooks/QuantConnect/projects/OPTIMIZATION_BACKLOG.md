# QuantConnect Strategy Optimization Backlog

Fichier commite dans le workspace. Source de verite pour tous les agents (Claude Code, Roo, etc.) sur toutes les machines.
Objectif : eviter de retester des hypotheses deja explorees et capturer les plafonds structurels.

**Derniere MAJ** : 2026-03-28 (Temporal-CNN-Prediction v2: real MLPClassifier 8-ETF 18-features, Sharpe 0.169->0.536, alpha -0.018->+0.003)

---

## Regles universelles confirmees

Ces patterns sont valides pour TOUTES les strategies. Ne pas les contredire.

| # | Regle | Source | Strategies validees |
|---|-------|--------|---------------------|
| 1 | **Risk-adjusted momentum** (return/vol) > raw momentum | Barroso 2015 | MomentumStrategy, FamaFrench, ForexCarry |
| 2 | **Skip-month** (exclure dernier mois) pour momentum | Jegadeesh 1990 | MomentumStrategy, FamaFrench, ForexCarry |
| 3 | **TLT risk-off detruit la valeur 2015-2026** -> XLP/IEF/GLD | Rate hike 2022 | AllWeather, FuturesTrend, SectorMomentum |
| 4 | **Stop-loss -8% a -12%** pour equities/ETFs | Empirique | MeanReversion, FamaFrench, MomentumStrategy |
| 5 | **Poids egaux > poids proportionnels** pour rotation ETFs | MomentumStrategy iter5 | MomentumStrategy, FamaFrench |
| 6 | **Trailing breakeven 3% > 4%** pour BTC daily | Crypto-MultiCanal | Crypto-MultiCanal |
| 7 | **SL 6% minimum sur BTC daily** (5% trop serre) | Crypto-MultiCanal | Crypto-MultiCanal |
| 8 | **Drift rebalancing 3%** > SMA overlay pour portfolios statiques | AllWeather | AllWeather |
| 9 | **Monthly + regime-change rebal > daily** | MomentumStrategy | MomentumStrategy, FamaFrench |
| 10 | **1 parametre a la fois** : changer plusieurs = regression | Crypto-MultiCanal v16 | Toutes |
| 11 | **Vol window 60d > 20d** pour covariance min-var | AAA | AAA, RiskParity |
| 12 | **Raw momentum + min-var** : ne pas combiner risk-adj + min-var | AAA | AAA |
| 13 | **SPY Parking = INTERDIT** (beta loading deguise) | Fondamental | Toutes |
| 14 | **Profit target 50%** pour options (TastyTrade) + VIX band 15-35 | OptionsIncome | OptionsIncome, Options-VGT |
| 15 | **Fix structural bugs >> academic improvements** | iter5 | Trend-Following, Toutes |
| 16 | **Backtests courts = overfitting** (toujours tester sur max periode) | Trend-Following | Trend-Following, OptionsIncome |
| 17 | **yfinance auto_adjust misleading pour REITs/bonds** | FuturesTrend, RiskParity | FuturesTrend, RiskParity, DualMomentum |
| 18 | **2-level trailing stop contre-productif sur BTC daily** | Crypto-MultiCanal v18 | Crypto-MultiCanal |
| 19 | **Diversifier instruments > relacher seuils** pour augmenter frequence | TrendFilteredMeanReversion | TrendFilteredMeanReversion |
| 20 | **MaximumDrawdownPercentPortfolio = INTERDIT** sur multi-stock (liquidation simultanée catastrophique) | Trend-Following v3 | Trend-Following, Toutes |
| 21 | **ATR stop serre + gates restrictives = whipsaw** (plus de stop-outs, DD pire) | Trend-Following v3b | Trend-Following |

---

## Plafonds structurels par strategie

### Strategies a plafond confirme (NE PLUS ITERER)

| Strategie | Sharpe | CAGR | MaxDD | Iterations | Raison du plafond |
|-----------|--------|------|-------|------------|-------------------|
| **AllWeather** | 0.667 | 9.3% | 16.4% | 5 iter | Poids optimaux trouves (SPY30/IEF30/GLD30/XLP10). Aucun angle restant. Extended 2010-2026: Sharpe 0.667 (ROBUST, inclut 2010-2014 recovery post-GFC). |
| **VIX-TermStructure** | 0.051 | 3.6% | 35.2% | 11 variantes | Post-VIXplosion 2018, SVXY -0.5x = premium halve. MaxDD structural (tail events). |
| **TurnOfMonth** | 0.128 | 4.8% | 23.7% | 6 variantes | ToM effect minimal en bull 2015-2026. Signal period-dependent. |
| **ForexCarry** | -0.324 | 1.5% | 12.3% | 8+ variantes | G10 FX momentum ~0.8% CAGR < T-bills ~2.5%. Structurellement negatif post-2008. |
| **OptionsIncome** | 0.234 | 6.8% | 19.3% | v8.0 final | Covered calls = alpha structurellement negatif. Premium ~6%/yr vs crashes -20/-34%. |
| **MomentumStrategy** | 0.565 | 11.8% | 25.8% | iter5 H10 rej | v4.0 final. Vol-adj, skip-month, top-4, SMA200+SMA20, SL-10%. Extended 2010-2026: Sharpe 0.565 (ROBUST, MaxDD stable). |
| **FuturesTrend** | 0.301 | 8.0% | 12.9% | 14 configs | Donchian 20/10 sur 6 ETFs. Grid search exhaustif. |
| **Crypto-MultiCanal** | 0.486 | 7.6% | 16.8% | 18 versions | 3 canaux ZigZag. Trail breakeven. Alpha=0.012, beta=0.053. |
| **SectorMomentum** | 0.621 | 13.2% | 22.8% | iter3 stable | Composite lookback + TLT+GLD defensif + daily SMA200 exit. Extended 2010-2026: Sharpe 0.621 (ROBUST, CAGR stable). |
| **DualMomentum** | 0.350 | 9.2% | 33.6% | iter2 SHY rej | MaxDD=COVID structural. Signal mensuel ne reagit pas assez vite. |
| **RiskParity** | 0.399 | 7.8% | 20.9% | H5-H7 all rej | IEF degrade, vol targeting anti-pattern en bull, VIX filter = trop peu de temps. |
| **Trend-Following** | 0.212 | 7.3% | 40.9% | v2+v3+v3b | 6 gates + MaxDD Per Security 10%. ATR 1.5, SMA200, portfolio stop tous rejetes. MaxDD structural. |
| **EMA-Cross-Index** | 0.470 | 9.4% | 17.5% | 25 combos | EMA 20/60 + cooldown 3j optimal. Volume filter, triple EMA, trailing tous rejetes. |

### Nouvelles strategies (2026-03-09, inspirees ChatGPT)

| Strategie | Sharpe | CAGR | MaxDD | Alpha | Beta | Verdict |
|-----------|--------|------|-------|-------|------|---------|
| **TrendStocksLite** | **0.719** | 18.2% | 33.7% | 0.049 | 0.822 | EXCELLENT. EMA20/50+SMA200 sur 15 large-caps diversifies. Meilleur Sharpe equity. |
| **DualMomentumNoTLT** | **0.469** | 11.0% | 23.6% | 0.012 | 0.612 | BON. Mieux que DualMomentum original (0.350). Sans TLT = MaxDD reduit (33.6%->23.6%). |
| **TrendFilteredMeanReversion** | -0.016 | 3.4% | 11.4% | -0.009 | 0.108 | FAIBLE. Signal reel (73% win rate) mais RSI(2)<10 trop rare. PLAFOND CONFIRME (H4 multi-instrument REJETE: Sharpe -0.129, 550 trades). |

**Lecon**: Strategies simples (EMA/SMA + equal weight) > strategies sophistiquees (multi-oracle, factor rotation). Confirme la meta-lecon.

### Strategies potentiellement ameliorables

| Strategie | Sharpe | Notes |
|-----------|--------|-------|
| **TrendFilteredMeanReversion** | -0.016 | **PLAFOND CONFIRME**. v1.0 final. RSI<20, RSI(3)<15, multi-instrument (SPY+QQQ+IWM) tous rejetes. Plafond structurel: trop peu de signaux RSI(2)<10 en bull 2015-2026. |
| **PairsTrading** | -0.361 | Paires structurellement non-cointegrees 2010-2026. OLS hedge ratio teste, echoue. Changer les paires? |
| **ETF-Pairs** | -0.706 | Meme probleme que PairsTrading. Cointregration instable. |
| **BTC-ML** | 0.282 | ML prediction. Potentiel features engineering. Object Store pour pre-training. |
| **Trend-Following** | 0.212 | **PLAFOND CONFIRME**. v3 (ATR1.5+SMA200+portfolio stop)=0.011, v3b (ATR1.5 seul)=0.151. MaxDD 40.9% structural. |
| **LSTM-Forecasting** | 0.525 | **v2.1 IMPROVED**. Real MLPClassifier (64,32), 7-ETF universe, threshold=0.52, min_pos=2. Potentiel: biweekly vs weekly, threshold tuning, feature selection. |
| **Chronos-Foundation-Forecasting** | 0.253 | **v2 IMPROVED** (2026-03-28). Replaced fake Chronos (hardcoded weights) with real GBM+Ridge ensemble. SMA200 regime filter + threshold=0.002. Beta 0.643->0.252, Alpha -0.023->+0.002, MaxDD 31.4%->22.4%. Signal-driven (beta=0.252). |
| **RL-DQN-Trading** | 0.533 | **v2.0.1 IMPROVED** (2026-03-28). Fake linear DQN -> real MLPRegressor(64,32). 5-ETF universe, risk-adj reward. Beta=0.452, Alpha=+0.019, CAGR 10.9%, MaxDD 25.8%. Pistes: SMA200 regime, 4th allocation (cash-heavy). |

### Strategies saines (Sharpe > 0.5, pas de degradation)

| Strategie | Sharpe | Notes |
|-----------|--------|-------|
| **Multi-Layer-EMA** | 1.891 | EMA multi-couches BTCUSDT + vol filter. Stable. |
| **EMA-Cross-Crypto** | 1.272 | EMA 20/50 + SMA200 + trailing 10%. Stable. |
| **BTC-MACD-ADX** | 1.224 | MACD+ADX BTC C#. Stable. |
| **CSharp-BTC-EMA-Cross** | 1.094 | EMA crossover BTC C#. Stable. |
| **Option-Wheel** | 0.996 | Wheel SPY. Stable. |
| **EMA-Cross-Stocks** | 0.872 | 5 tech stocks. Stable. |
| **Gaussian-Direction-Classifier** | 0.761 | v2.0 (2015-2026). GaussianNB manuelle. SMA200 regime filter. Beta 0.540. MaxDD 25.6%. Treynor 0.283 (meilleur que v1.0). |
| **FamaFrench** | 0.540 | Factor rotation. Stable apres iter3. |

---

## Hypotheses testees et rejetees (par strategie)

### AllWeather
- [x] SMA200 overlay : Sharpe 0.858 standalone mais 0.264 sur QC. Friction sans gain.
- [x] SMA25% reduction : Sharpe 0.325 < no-SMA 0.365.
- [x] TIP (TIPS inflation) : marginal, pas de gain significatif.
- [x] Vol targeting : cash pendant low-vol = anti-pattern en bull. Pas de levier.
- [x] IEF 40%->30% + GLD 20%->30% : ACCEPTED (v5.0, Sharpe 0.602).
- [x] Extension 2015->2010 (issue #37) : Sharpe 0.667, CAGR 9.3%, MaxDD 16.4%. ROBUST. GLD/IEF beneficient de 2010-2012 (safe haven demand post-GFC). Pas de regime catastrophique.

### VIX-TermStructure
- [x] Double SMA (vix < sma5 < sma20) : trop restrictif, miss entries.
- [x] VIX < 18 threshold : trop peu d'entrees.
- [x] Dynamic sizing by contango depth : augmente MaxDD sans gain Sharpe.
- [x] Tighter 8% stop + smaller position : net negatif.
- [x] SHY 70% + stop 7% (v5.0) : trop dilue (13.5% effective).
- [x] Position 25% (v5.1) : MaxDD 21.5% mais Sharpe -0.125 (cash drag).

### TurnOfMonth
- [x] Momentum filter 21d : anti-correle avec ToM alpha. Pire.
- [x] Window 4/4 vs 4/3 : pas d'amelioration pratique.
- [x] Stop-loss 4% : Sharpe 0.096, MaxDD -2.5% seulement. Pas worth it.
- [x] IWM addition : dilue l'alpha de QQQ.
- [x] SPY seul (sans QQQ) : Sharpe -0.026.

### Chronos-Foundation-Forecasting (2026-03-28)
- [x] Fake Chronos v1-v5 (hardcoded attention weights + random noise) : Sharpe 0.114, Beta 0.341, 4/7 versions had 0 trades. Not a real model.
- [x] Real GBM+Ridge ensemble, SPY only : Sharpe 0.234, Beta 0.643, Alpha -0.023. High beta = bull market bias.
- [x] SMA200 regime filter + threshold=0.002, 8-ETF universe (v2) : Sharpe 0.253, Beta 0.252, Alpha +0.002, MaxDD 22.4%. ACCEPTED.
  - SMA200 bear regime -> only GLD/IEF/TLT max 2 positions. Dramatically reduces Beta and MaxDD.
  - threshold=0.002 filters noise predictions and reduces false positives.
  - Key insight: regime filter transforms a beta-loading strategy into a signal-driven one.

### ForexCarry
- [x] Vol filter "skip rebalance" : change Sharpe < 0.1.
- [x] Vol filter "liquidate on spike" : whipsaw exits, pire.
- [x] SMA200, trailing stops, entry stops, strict momentum gates : tous pires que v3.2.
- [x] USDCHF, NZDUSD substitutions : tous degrades.
- [x] USD trend filter + 6 paires + top-3 (v5) : Sharpe -0.324 -> -0.849.

### MomentumStrategy
- [x] Momentum-proportional weights (H10) : Sharpe 0.472->0.398. Concentration XLK risquee.
- [x] Extension 2015->2010 (issue #37) : Sharpe 0.565, CAGR 11.8%, MaxDD 25.8%. ROBUST. XLRE/XLC absents 2010-2015 = 9 ETFs actifs au lieu de 11, pas de degradation. Strategie tient sur 16 ans.

### OptionsIncome
- [x] Stock stop-loss -15% (v8.0) : Sharpe 0.234->0.090. Whipsaw 2022 slow bear.
- [x] Extension 2023-2024 -> 2018-2026 : Sharpe 0.791->0.234 (structurel).

### FuturesTrend
- [x] ATR position sizing : Sharpe 0.209 (degrades breakout entries).
- [x] SMA100 filter : trop restrictif sur 6 ETFs.
- [x] SMA30 : IS 0.864 mais OOS -0.010 = overfitting severe.
- [x] 4x25% / 5x20% : tous < 3x33%.
- [x] Exit=15j : MaxDD monte.
- [x] Sans VNQ : yfinance +11% mais QC -10% (yfinance auto_adjust bias).

### Crypto-MultiCanal
- [x] 2-level progressive trailing (+3% lock at +6% gain, v18) : Sharpe 0.486->0.232. BTC daily vol trop haute.

### MeanReversion
- [x] RSI(7) au lieu de RSI(14) : plus de bruit, pas plus d'edge.
- [x] Dynamic position sizing (oversold-weighted) : plus complexe, pas plus robuste.
- [x] SMA100 filter (iter5 ChatGPT) : Sharpe 0.294->-0.042. Filtre trop d'entrees.

### PairsTrading
- [x] OLS hedge ratio + 5 paires + test cointegration (v2 iter5) : Sharpe -0.361->-0.420.

### DualMomentum
- [x] SHY comme refuge (vs BND) : Sharpe 0.324 < 0.350. MaxDD identique (COVID structural).

### RiskParity
- [x] IEF remplace TLT (H5) : Sharpe 0.330 < 0.399. TLT superieur grace au bull bond 2015-2020.
- [x] Vol Targeting 10% (H6) : cash low-vol = anti-pattern.
- [x] VIX filter >25 (H7) : <15% du temps en stress. Cash drag.

### Trend-Following (PLAFOND CONFIRME - v2 = Sharpe 0.212)
- [x] v3 SPY SMA200 filter + MaxDD 7%/15% : Sharpe 0.212->0.011. Filtre + risk mgmt trop serre coupe trop de positions. REVERT a v2.
- [x] v3b ATR 1.5 seul (sans SMA200, sans portfolio stop) : Sharpe 0.151, MaxDD 54.1%. ATR serre + 6 gates d'entree = plus de whipsaw.
- **PLAFOND** : MaxDD 40.9% est structural (concentration momentum pendant pics). ATR, SMA200, portfolio stop tous rejetes.

### TrendFilteredMeanReversion (NOUVELLE 2026-03-09)
- [x] RSI(2)<10, SMA200 bull filter, time stop 5j, v1.0 : Sharpe -0.016. Signal reel (73% win, beta 0.108) mais ~9 trades/an trop rare.
- [x] RSI(2)<20 (v2.0) : Sharpe -0.002, 31 trades/an, 71% win, MaxDD 16.2%. Frequence triple mais qualite diluee et DD double.
- [x] RSI(3)<15 (v3.0) : Sharpe -0.050, 12 trades/an, 72% win, MaxDD 10.3%. Pas d'amelioration significative.
- **CAUSE RACINE** : Cash drag structurel (~85% du temps en cash, 0% return vs risk-free 2-5%).
- [ ] H4 Multi-instrument (SPY+QQQ+IWM) : multiplier les opportunites 3x sans diluer le signal. Non teste.

### EMA-Cross-Index
- [x] Triple EMA (8/21/55) : Sharpe -10%. Entree trop restrictive.
- [x] Volume filter : Sharpe -5% a -19%. SPY trop liquide, volume non-directionnel pour ETFs.
- [x] Trailing stop 3% : +11.8% IS mais 68 trades vs 19 (micro-trading).
- [x] Trailing stop 5-8% : degrade. SPY vol ~1%/jour = triggers trop vite.
- [x] QQQ addition : corr 0.92-0.95 avec SPY. Pas de vraie diversification.
- [x] Cooldown > 5j : miss re-entries legitimes.

### RL-DQN-Trading (iter1 - 2026-03-28)

**Cloud ID** : 29443478 | Projet: RL-DQN-Trading

**Probleme v1.0 (fake DQN)**: Linear Q-function (matrix dot product state x n_actions).
SPY seul. 5 features. Sharpe 0.136, Beta 0.276, Alpha -0.009. Signaux aleatoires sans vrai apprentissage.

**v2.0.1 baseline** (2015-2026): Sharpe **0.533**, Beta 0.452, Alpha +0.019, CAGR 10.9%, MaxDD 25.8%
- Net profit 211.8%, 1944 trades, 65% win rate, fees $2,467

**Ce qui a marche:**
- [x] MLPRegressor(64,32) + StandardScaler Pipeline comme Q-network (state-action -> Q-value)
- [x] 5-ETF universe (SPY, QQQ, IWM, TLT, GLD) avec 3 allocations portfolio (AGGRESSIVE/MODERATE/DEFENSIVE)
- [x] 11 features: ROC (1/5/20j), RSI, BB position, vol regime (std20/std60), trend (price/SMA50),
      TLT-SPY spread (flight-to-safety), GLD momentum, QQQ-SPY spread (tech), action memory
- [x] Risk-adjusted reward: r - 0.5*r^2 (penalise asymetriquement les grosses pertes)
- [x] Transaction cost penalty (2bp) pour decourager le churning
- [x] Replay buffer 5000, batch 128, training weekly, target update monthly
- [x] Epsilon decay 0.5 -> 0.05 sur ~2 ans (0.9978 par step)
- [x] Period 2015-2026, weekly rebalance (Monday), training (Friday)

**Bug critique corrige (v2.0 -> v2.0.1)**: _target_network.predict() avant premier fit() -> NotFittedError.
FIX: _target_initialized = False separement de _network_initialized.
Utiliser Q-network comme fallback jusqu'a la premiere mise a jour mensuelle du target network.
Insidieux: build reussit, echec uniquement a l'execution apres quelques semaines.

**Pistes restantes (non testees):**
- [ ] SMA200 regime filter (SPY < SMA200 -> DEFENSIVE only) pour reduire Beta 0.452
- [ ] 4 allocations au lieu de 3 (ajouter CASH_HEAVY: 5% SPY + 40% TLT + 40% GLD + 15% IEF)
- [ ] Reward base sur le vrai portfolio return du jour precedent (pas approximation equity_weight*SPY_return)
- [ ] Lookback 30j pour std60 feature (contexte plus long)

### Temporal-CNN-Prediction (iter1 - 2026-03-28)

**Cloud ID** : 29443034 | Projet: Temporal-CNN-Prediction

**Probleme v1.0 (fake CNN)**: Hardcoded kernel weights (momentum/balanced/recent-weighted).
Weighted average of returns dressed up as convolution. SPY only. 2018-2024.
Resultat: Sharpe 0.169, beta=0.507, alpha=-0.018. Pas un vrai CNN.

**v1.0 baseline** (2018-2024): Sharpe 0.169, Alpha -0.018, Beta 0.507, CAGR 5.1%, MaxDD 20.6%

**v2.0** (real MLPClassifier 128/64/32, 8-ETF, 18 features, 2015-2026):
- Sharpe 0.536, Alpha +0.003, Beta 0.997, CAGR 13.8%, MaxDD 33.9%
- Net profit 315%, Total return $415K from $100K over 11 years
- 1584 trades, fees $3,205, Win rate 65%, Profit-Loss ratio 1.18

**Ce qui a marche:**
- [x] Remplacer fake convolution par sklearn MLPClassifier(128,64,32) avec StandardScaler pipeline
- [x] Universe 1->8 ETFs: SPY, QQQ, IWM, XLK, XLF, XLV, DIA, EFA
- [x] 18 features temporelles multi-echelle (5d/10d/20d): mean, vol, lags, cumulative, autocorr, vol-ratio
- [x] 3-class target: UP(>0.5%), DOWN(<-0.5%), NEUTRAL sur 10-day horizon
- [x] Warmup per-symbol `self.history[TradeBar](sym, timedelta(...))` (pattern oblige)
- [x] min_positions=2 pour eviter cash drag
- [x] Biweekly rebalance (10 jours) pour reduire friction vs daily
- [x] Periode 2018->2015 pour plus de training data

**Probleme observe: Beta=0.997 tres eleve.**
La strategie est presque pleinement investie (8 ETFs, min 2 toujours), ce qui
explique le beta proche de 1. L'alpha est modeste (+0.003). Le Sharpe 0.536 vient
principalement du bull market 2015-2026, pas du signal ML pur.

**Pistes restantes:**
- [ ] Ajouter SMA200 regime filter (SPY < SMA200 -> reduire to 2 positions defensives)
- [ ] Threshold plus eleve (0.45 ou 0.50) pour etre plus selectif -> beta plus bas
- [ ] Features: MACD signal, BB z-score pour signaux de retournement
- [ ] Lookback 30j au lieu de 20j (plus de contexte CNN)
- [ ] Retrain sur 2 ans (504j) au lieu de 1 an (252j)

**Lecon cle**: MLPClassifier(128,64,32) fonctionne sur QC Cloud.
La force du signal est limitee par la nature des features (returns/vol patterns
ne capturent pas toujours les reversals). Beta=1 indique que le min_positions=2
empeche les periodes defensives. Pour un vrai edge ML, il faut gerer le beta.

### LSTM-Forecasting (iter1 - 2026-03-28)

**Cloud ID** : 29443476 | Projet: LSTM-Forecasting

**Probleme v1.0 (fake LSTM)**: Fixed weights (0.7 forget, 0.3 input) + 0.5 momentum blend.
Resultat: beta=0.886 (essentiellement buy-and-hold SPY), alpha=-0.008. PAS un vrai LSTM.

**v1.0 baseline** (2018-2024): Sharpe 0.366, Beta 0.886, CAGR 9.75%, MaxDD 37.2%, Alpha -0.008

**v2.0** (real MLPClassifier, threshold=0.55, min_pos=0, 2015-2026): Sharpe 0.278, Beta 0.292, CAGR 6.1%, MaxDD 15.1%
- Beta chute dramatiquement (0.886->0.292) = vrai signal ML
- Mais Sharpe baisse car trop de periodes en cash (0 positions si aucun ETF > 0.55)
- 1422 trades, fees $1,955

**v2.1** (threshold=0.52, min_pos=2, 2015-2026): Sharpe 0.525, Beta 0.544, CAGR 11.3%, MaxDD 32.5%, Alpha +0.016
- min_positions=2 eliminele cash drag structurel
- Alpha devient POSITIF (+0.016): vrai edge ML confirme
- Total return 224.9% sur 11 ans (vs 74.7% fake LSTM sur 6 ans)
- 2094 trades, fees $3,961 (absorbables sur $227K profit)

**Ce qui a marche:**
- [x] Remplacer fake LSTM par sklearn MLPClassifier (64,32) avec StandardScaler pipeline
- [x] 7-ETF universe (SPY, QQQ, IWM, EFA, TLT, GLD, IEF) au lieu de SPY seul
- [x] 20 features temporelles: lag returns, rolling vol, RSI-like, momentum, autocorr, mean returns
- [x] Warmup per-symbol avec `self.history[TradeBar](sym, timedelta, Resolution.DAILY)` (vs multi-symbol qui donne TradeBars objects)
- [x] min_positions=2 pour eviter cash drag (toujours investis dans au moins 2 ETFs)
- [x] threshold=0.52 au lieu de 0.55 (plus de trades, meilleure couverture)

**Pistes restantes:**
- [ ] Biweekly au lieu de weekly (reduire trades de ~2094 a ~1000, baisser fees)
- [ ] Features: MACD, BB z-score pour signaux de retournement
- [ ] Lookback 90j au lieu de 60j (plus de contexte historique)
- [ ] Poids proportionnels a la confiance (scores[sym] - 0.5) au lieu d'equal-weight
- [ ] Augmenter train_window a 504j (2 ans) pour plus de data

**Lecon cle**: sklearn is available on QC Cloud. MLPClassifier(64,32) fonctionne. La cle est:
1. Warmup per-symbol (pas multi-symbol history)
2. min_positions pour eviter cash drag
3. Threshold pas trop eleve (0.52 > 0.55 pour ce type de signal)

### Gaussian-Direction-Classifier (iter1 - 2026-03-28)

**v1.0 baseline** (cloud ID 29398513): Sharpe 0.864, Beta 1.133, CAGR 29.1%, MaxDD 36.8%, Alpha 0.112
**v2.0** (universe8 + SMA200 + threshold 0.60 + prob-weighted): Sharpe 0.761, Beta 0.540, CAGR 23.1%, MaxDD 25.6%, Alpha 0.111

**Ce qui a ete change en v2.0:**
- [x] Universe 5->8 (AAPL, MSFT, GOOGL, AMZN, NVDA + META, TSLA, NFLX): diversification candidate pool
- [x] SMA200 regime filter: SPY < SMA200 = go to cash. Beta 1.133 -> 0.540. MaxDD -11pp.
- [x] Confidence threshold 0.55->0.60: signaux plus propres
- [x] Feature [5,10,21] -> [2,5,10,21]: added 2-day short-term reversal
- [x] Probability-weighted positions: poids proportionnels a (p - 0.5)

**Verdict v2.0**: Sharpe baisse (0.864->0.761) car CAGR reduit par periodes cash en bear market.
MAIS: Treynor 0.177->0.283 (meilleur), MaxDD -11pp, Beta halved. Trade-off valide pedagogiquement.
Le signal propre (Alpha~0.111) est preserve identiquement. La reduction vient du regime filter, pas d'une degradation du signal.

**Pistes restantes:**
- [ ] Holdingperiod: 1-day label est tres bruity (53% accuracy theorique max). Essayer 5-day label?
- [ ] Feature engineering: RSI, BB z-score au lieu de raw returns?
- [ ] Reduce universe to SPY sectors (XLK, XLF, XLE, etc.) au lieu de single stocks?
- [ ] Retrain interval: 10j au lieu de 21j pour s'adapter plus vite aux regimes?

---

## Divergences yfinance vs QC Cloud

| Contexte | Biais yfinance | Impact |
|----------|----------------|--------|
| **REITs (VNQ)** | auto_adjust integre dividendes retroactivement | Inverser les conclusions (VNQ semble drag, alors que QC = positif) |
| **Bond ETFs (TLT, IEF, BND)** | Adj Close inclut coupons ~2-3%/an | IEF semble meilleur en simulation qu'en QC |
| **Simulations mensuelles** | Lisse les crashes intramonth | MaxDD sous-estime (COVID -34% en 3 semaines) |
| **EMA strategies** | ~2x Sharpe overestimate (dividendes + no fees) | Relatif transfere, absolu non |

**Regle** : yfinance pour signaux de prix purs (trend, momentum). Pour universe selection/comparative incluant dividendes -> tester directement sur QC.

---

## Lecons techniques QC

| Probleme | Solution |
|----------|----------|
| `read_file` obligatoire avant `update_file_contents` | Collaboration lock |
| Options chain vide | Resolution.MINUTE obligatoire |
| "In Progress..." dans read_backtest | Bug MCP Pydantic. Attendre 30s, reessayer |
| `algo.rsi(symbol, 14, Resolution.Hour)` dans OnSecuritiesChanged | Utiliser `RelativeStrengthIndex(14)` + `register_indicator` |
| Multiple inheritance Python/CLR | `class X(QCAlgorithm, Mixin)` interdit. Composer a la place |
| Binance CASH setup | `set_account_currency("USDT")` + `set_cash(N)` |
| SL/TP qty sur Binance | `portfolio[sym].quantity` (fees preleves en BTC) |
| Universe Selection 500 stocks | Trop lent. Utiliser ETFs fixes |
| Short selling en bull market | Mean reversion long-short catastrophique. Long-only + SMA200 |
| `self.rsi(sym, 2, Resolution.DAILY)` : 3e arg = MovingAverageType | Utiliser `self.rsi(sym, 2)` sans 3e argument |

---

## Meta-lecons sur le processus d'optimisation

1. **~50% des suggestions de recherche degradent sur QC Cloud** (iter4: 6/12, iter5: 3/4 ChatGPT).
2. **Les fixes structurels (leverage, risk mgmt) marchent. Les raffinements academiques rarement.**
3. **La plupart des strategies atteignent un plafond apres 3-5 iterations serieuses.**
4. **Ne pas iterer indefiniment** : si 2+ hypotheses consecutives echouent, declarer ceiling.
5. **Toujours backtester sur la periode la plus longue possible** avant de conclure.
6. **Les suggestions ChatGPT/LLM doivent etre validees empiriquement** : 3/4 ont degrade.

---

## QuantBook Research Notebooks (issue #39, #42)

12 quantbook.ipynb notebooks created for QC Research environment (replacing yfinance research.ipynb).
All uploaded to QC Cloud, all compile successfully. Issue #39 COMPLETE (12/12).

| Strategie | Cloud ID | Cells | Hypotheses | Priority |
|-----------|----------|-------|------------|----------|
| FamaFrench | 28657910 | 23 | Factor models, lookback, stop-loss, universe | HIGH |
| AllWeather | 28657833 | 21 | Weights, rebal frequency, bond alternatives | HIGH |
| MeanReversion | 28657904 | 19 | RSI period, lookback, stop-loss, sector filter | HIGH |
| SectorMomentum | 28433643 | 18 | Lookback combo, top-N, regime filter, defensive | HIGH |
| MomentumStrategy | 28657837 | 21 | Top-N, lookback, vol window, regime filter | MEDIUM |
| DualMomentum | 28692516 | 23 | Lookback, abs threshold, refuge, universe | MEDIUM |
| RiskParity | 28692653 | 20 | Vol window, drift trigger, asset universe | MEDIUM |
| FuturesTrend | 28657834 | 21 | Donchian periods, SMA filter, max positions, universe | MEDIUM |
| PairsTrading | 28693651 | 20 | Cointegration, stability, z-score, pairs portfolio | PEDAGOGICAL |
| TurnOfMonth | 28657905 | 14 | Window size, universe, leverage, regime filter, stability | MEDIUM |
| VIX-TermStructure | 28657907 | 16 | Position size, VIX threshold, contango depth, trailing stop, SHY cash | MEDIUM |
| ForexCarry | 28657908 | 16 | Pure vs risk-adj, skip-month, lookback, top-N, universe expansion | LOW |

**Note**: These notebooks use `QuantBook()` + `qb.history()` for native QC data (no yfinance).
Cloud versions are compact (no matplotlib). Local versions in `projects/<strategy>/quantbook.ipynb` include visualizations.
