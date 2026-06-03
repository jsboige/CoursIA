# Portfolio Hybride IBKR (50%) + Binance (50%)

Stratégie composite multi-broker associant un sleeve actions/ETFs (IBKR compte cash) et un sleeve crypto spot (Binance), rebalancement mensuel, en piochant dans les meilleures stratégies du dépôt CoursIA.

## Objectifs

- Diversification cross-asset (equities + crypto, corrélation historique ~0.15-0.30)
- Sharpe net cible 1.0-1.3 (CAGR ~14%, MaxDD ~22%)
- Pipeline reproductible : research → backtest agrégé → walk-forward → paper trading 30j → live nodes
- Aucune information personnelle dans le dépôt (clés API, montants → `.env` local seul)

## Composition cible

### Sleeve IBKR (50%) — 5 stratégies équipondérées

| Sous-strat | Univers | Sharpe backtest | Pondération sleeve |
|------------|---------|-----------------|---------------------|
| Framework_Composite_TrendWeather | SPY, IEF, GLD + signal régime | 1.155 | 30% |
| Framework_Composite_EMATrend | SPY + secteurs | 0.867 | 25% |
| SectorMomentum | 10 ETFs sectoriels (XLK, XLF, XLE, etc.) | 0.621 | 20% |
| AllWeather v5 | SPY / IEF / GLD / XLP | 0.667 | 15% |
| EMA-Cross-Alpha | SPY + ETFs sélectionnés | 0.996 | 10% |

### Sleeve Binance (50%) — 3 stratégies

| Sous-strat | Univers | Sharpe backtest | Pondération sleeve |
|------------|---------|-----------------|---------------------|
| EMA-Cross-Crypto | BTC/ETH | 1.272 | 50% |
| Crypto-MultiCanal | BTC/ETH + alts | (à benchmarker) | 30% |
| HAR-RV-J vol-target BTC (M12) | BTC, Kelly capé 0.5 | M12 BEATS (p=7.9e-7) | 20% |

## Roadmap 5 phases

### Phase 1 — Research notebook agrégé (S1)
- `quantbook.ipynb` : MultiAlphaModel agrégeant les 8 sous-stratégies
- Vérification compositions par sleeve, calcul Sharpe blend théorique
- Test corrélations historiques inter-strategies (matrice 8×8)

### Phase 2 — Backtest unified 2018-2025 (S1-S2)
- Backtest QC Cloud sur 8 ans (multi-régimes : 2018 vol, 2020 COVID, 2022 bear, 2023-25 reprise)
- Métriques : Sharpe net (après costs), CAGR, MaxDD, Calmar, Sortino, Beta SPY/BTC
- Comparaison à benchmarks : SPY B&H, 60/40 SPY/TLT, BTC B&H

### Phase 3 — Walk-forward + multi-seed (S2-S3)
- Walk-forward annual : train 5 ans → OOS 1 an, roll forward
- Multi-seed >= 4 sur sous-strats ML (HAR-RV-J vol-target en particulier)
- Edge >= 2σ cross-seed requis pour validation discipline (cf `feedback_multi_seed_required.md`)
- Sweep allocation IBKR/Binance : 60/40, 50/50, 40/60, régime-adaptatif

### Phase 4 — Paper trading 30j (S3-S4)
- Connexion paper IBKR + Binance testnet
- Logging quotidien : fills réels vs backtest, slippage, market impact
- Comparison live drift vs expected returns/vol

### Phase 5 — Live nodes QC (S4+)
- Déploiement sur 2 nœuds QC Cloud (1 par broker)
- Capital initial modéré (montants via `.env` local)
- Monitoring : Sharpe rolling 30j, MaxDD circuit-breaker -10%, alerte vol spike

## Configuration

Voir [`.env.template`](./.env.template) pour la liste des variables nécessaires. Ne JAMAIS committer un `.env` rempli — il est dans `.gitignore`.

## Discipline de validation (héritée du pipeline ML/Trading)

1. Walk-forward 5-fold expanding (pas single split)
2. Multi-seed >= 4 parmi {0, 1, 7, 42, 99} pour les composantes ML
3. Edge >= 2σ cross-seed obligatoire
4. OOS strict : training jusqu'à 2022, test 2023-2025 minimum
5. Transaction costs : 5bps IBKR equities, 10bps Binance spot, +5bps slippage market impact
6. Anti-survivorship : univers ETF stable (pas d'introduction posterieure aux events)
7. Verdict honnête : BEATS / NO BEATS / INCONCLUSIVE (pas de "promising")

## Caveats

- Backtests in-sample du catalogue (Sharpes 0.6-1.3) : discount 20-30% en live attendu
- EMA-Cross-Crypto Sharpe 1.272 inclut bull 2020-2021 — hors bull, estimation 0.5-0.7
- Régime crypto post-ETF spot BTC (jan 2024) modifie microstructure
- MaxDD tail possible -35-40% (crash crypto -60% + equities -25% concomitants)

## État

- **Phase 1** : initiation, skeleton créé 13/05/2026 (epic en cours)
- Issue tracker : (à lier dès création)

## Liens

- [Catalog complet QC](../../README.md)
- [BOOK_MAPPING](../../BOOK_MAPPING.md) — correspondance Hands-On AI Trading
- [M12 HAR-RV-J docs](../../ML-Training-Pipeline/docs/M_NEXT_VOL_PROPOSAL.md)
- [Discipline ML/Trading](../../../../.claude/memory/feedback_ml_trading_pitfalls.md)
