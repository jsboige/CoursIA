# QuantConnect Strategy Optimization Backlog

Fichier commite dans le workspace. Source de verite pour tous les agents (Claude Code, Roo, etc.) sur toutes les machines.
Objectif : eviter de retester des hypotheses deja explorees et capturer les plafonds structurels.

**Derniere MAJ** : 2026-03-09 (iteration 6 + 3 nouvelles strategies)

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

---

## Plafonds structurels par strategie

### Strategies a plafond confirme (NE PLUS ITERER)

| Strategie | Sharpe | CAGR | MaxDD | Iterations | Raison du plafond |
|-----------|--------|------|-------|------------|-------------------|
| **AllWeather** | 0.602 | 9.5% | 16.4% | 5 iter | Poids optimaux trouves (SPY30/IEF30/GLD30/XLP10). Aucun angle restant. |
| **VIX-TermStructure** | 0.051 | 3.6% | 35.2% | 11 variantes | Post-VIXplosion 2018, SVXY -0.5x = premium halve. MaxDD structural (tail events). |
| **TurnOfMonth** | 0.128 | 4.8% | 23.7% | 6 variantes | ToM effect minimal en bull 2015-2026. Signal period-dependent. |
| **ForexCarry** | -0.324 | 1.5% | 12.3% | 8+ variantes | G10 FX momentum ~0.8% CAGR < T-bills ~2.5%. Structurellement negatif post-2008. |
| **OptionsIncome** | 0.234 | 6.8% | 19.3% | v8.0 final | Covered calls = alpha structurellement negatif. Premium ~6%/yr vs crashes -20/-34%. |
| **MomentumStrategy** | 0.472 | 11.1% | 25.8% | iter5 H10 rej | v4.0 final. Vol-adj, skip-month, top-4, SMA200+SMA20, SL-10%. |
| **FuturesTrend** | 0.301 | 8.0% | 12.9% | 14 configs | Donchian 20/10 sur 6 ETFs. Grid search exhaustif. |
| **Crypto-MultiCanal** | 0.486 | 7.6% | 16.8% | 18 versions | 3 canaux ZigZag. Trail breakeven. Alpha=0.012, beta=0.053. |
| **SectorMomentum** | 0.555 | 13.0% | 22.8% | iter3 stable | Composite lookback + TLT+GLD defensif + daily SMA200 exit. |
| **DualMomentum** | 0.350 | 9.2% | 33.6% | iter2 SHY rej | MaxDD=COVID structural. Signal mensuel ne reagit pas assez vite. |
| **RiskParity** | 0.399 | 7.8% | 20.9% | H5-H7 all rej | IEF degrade, vol targeting anti-pattern en bull, VIX filter = trop peu de temps. |
| **EMA-Cross-Index** | 0.470 | 9.4% | 17.5% | 25 combos | EMA 20/60 + cooldown 3j optimal. Volume filter, triple EMA, trailing tous rejetes. |

### Nouvelles strategies (2026-03-09, inspirees ChatGPT)

| Strategie | Sharpe | CAGR | MaxDD | Alpha | Beta | Verdict |
|-----------|--------|------|-------|-------|------|---------|
| **TrendStocksLite** | **0.719** | 18.2% | 33.7% | 0.049 | 0.822 | EXCELLENT. EMA20/50+SMA200 sur 15 large-caps diversifies. Meilleur Sharpe equity. |
| **DualMomentumNoTLT** | **0.469** | 11.0% | 23.6% | 0.012 | 0.612 | BON. Mieux que DualMomentum original (0.350). Sans TLT = MaxDD reduit (33.6%->23.6%). |
| **TrendFilteredMeanReversion** | -0.016 | 3.4% | 11.4% | -0.009 | 0.108 | FAIBLE. Signal reel (73% win rate) mais RSI(2)<10 trop rare (~9 trades/an). Potentiel avec RSI<20. |

**Lecon**: Strategies simples (EMA/SMA + equal weight) > strategies sophistiquees (multi-oracle, factor rotation). Confirme la meta-lecon.

### Strategies potentiellement ameliorables

| Strategie | Sharpe | Notes |
|-----------|--------|-------|
| **TrendFilteredMeanReversion** | -0.016 | RSI<20 et RSI(3)<15 testes et rejetes. Cause : cash drag 85%. Tester multi-instrument (SPY+QQQ+IWM). |
| **PairsTrading** | -0.361 | Paires structurellement non-cointegrees 2010-2026. OLS hedge ratio teste, echoue. Changer les paires? |
| **ETF-Pairs** | -0.706 | Meme probleme que PairsTrading. Cointregration instable. |
| **BTC-ML** | 0.282 | ML prediction. Potentiel features engineering. Object Store pour pre-training. |
| **Trend-Following** | 0.212 | v3 degrade (0.011). v2 reste meilleure. Simplifier le design? |

### Strategies saines (Sharpe > 0.5, pas de degradation)

| Strategie | Sharpe | Notes |
|-----------|--------|-------|
| **Multi-Layer-EMA** | 1.891 | EMA multi-couches BTCUSDT + vol filter. Stable. |
| **EMA-Cross-Crypto** | 1.272 | EMA 20/50 + SMA200 + trailing 10%. Stable. |
| **BTC-MACD-ADX** | 1.224 | MACD+ADX BTC C#. Stable. |
| **CSharp-BTC-EMA-Cross** | 1.094 | EMA crossover BTC C#. Stable. |
| **Option-Wheel** | 0.996 | Wheel SPY. Stable. |
| **EMA-Cross-Stocks** | 0.872 | 5 tech stocks. Stable. |
| **FamaFrench** | 0.540 | Factor rotation. Stable apres iter3. |

---

## Hypotheses testees et rejetees (par strategie)

### AllWeather
- [x] SMA200 overlay : Sharpe 0.858 standalone mais 0.264 sur QC. Friction sans gain.
- [x] SMA25% reduction : Sharpe 0.325 < no-SMA 0.365.
- [x] TIP (TIPS inflation) : marginal, pas de gain significatif.
- [x] Vol targeting : cash pendant low-vol = anti-pattern en bull. Pas de levier.
- [x] IEF 40%->30% + GLD 20%->30% : ACCEPTED (v5.0, Sharpe 0.602).

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

### ForexCarry
- [x] Vol filter "skip rebalance" : change Sharpe < 0.1.
- [x] Vol filter "liquidate on spike" : whipsaw exits, pire.
- [x] SMA200, trailing stops, entry stops, strict momentum gates : tous pires que v3.2.
- [x] USDCHF, NZDUSD substitutions : tous degrades.
- [x] USD trend filter + 6 paires + top-3 (v5) : Sharpe -0.324 -> -0.849.

### MomentumStrategy
- [x] Momentum-proportional weights (H10) : Sharpe 0.472->0.398. Concentration XLK risquee.

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

### Trend-Following
- [x] v3 SPY SMA200 filter + MaxDD 7%/15% : Sharpe 0.212->0.011. Filtre + risk mgmt trop serre coupe trop de positions. REVERT a v2.

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
