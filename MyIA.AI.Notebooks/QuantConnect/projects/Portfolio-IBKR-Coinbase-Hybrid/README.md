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

> **Note (2026-06-28)** : le sleeve crypto ci-dessus est décrit dans sa version Binance
> d'origine (avant migration MiCA). L'état courant du code est **Coinbase** — voir la
> section [Migration MiCA](#migration-mica-sleeve-crypto-binance--coinbase-2026-06-28)
> ci-dessous.

## Migration MiCA : sleeve crypto Binance → Coinbase (2026-06-28)

**Contexte réglementaire.** Les services Binance France cessent le **2026-07-01** (pas de
licence CASP MiCA). Coinbase détient la licence CASP MiCA France et est nativement supporté
par QuantConnect (`Market.COINBASE`, données depuis janvier 2015, 860+ paires). Le sleeve
crypto du portefeuille hybride est migré Binance → Coinbase. Le sleeve IBKR (equities) est
inchangé. See #1027.

### Changements de code

| Aspect | Avant (Binance) | Après (Coinbase) |
|--------|-----------------|------------------|
| Marché crypto | `Market.BINANCE` | `Market.COINBASE` |
| Tickers | `BTCUSDT`, `ETHUSDT`, … (USDT-quoted) | `BTCUSD`, `ETHUSD`, … (USD-quoted) |
| Fee crypto | `PercentFeeModel(0.001)` hardcodé (10bps) | `CoinbaseFeeModel()` natif (maker 0.6% / taker 0.8%) |
| Devise compte | `USDT` | `USDT` (inchangé — voir finding ci-dessous) |
| Paramètre | — | `crypto_fee_bps` (override flat bps pour isoler l'effet fee) |

Le `CoinbaseFeeModel()` natif applique le barème réaliste Coinbase Advanced-1 (maker 0.6% /
taker 0.8%). Comme `set_holdings()` émet des ordres **market**, le taux **taker 0.8% (80bps)**
s'applique par défaut — bien plus cher que les 10bps Binance. Le paramètre `crypto_fee_bps`
permet de surcharger avec un `PercentFeeModel` flat pour isoler l'effet fee pur (ex. `10`
reproduit le barème Binance sur les données Coinbase).

### Finding technique : `USD` casse le backtest (0 trades)

Avec `Market.COINBASE` + `add_crypto("BTCUSD")` + `set_account_currency("USD")`, le backtest
produit **0 trade** (le warmup ne se termine jamais — la comptabilité de cash-settlement
entre en collision quand la devise du compte égale la devise de cotation BTCUSD = USD, et
`is_warming_up` reste `True` → `rebalance()` retourne immédiatement). `set_account_currency("USDT")`
restaure les trades (QC convertit automatiquement la cotation USD → compte USDT, exactement
comme la version Binance canonique convertit l'USD equity → USDT). Vérifié firsthand : la
version Binance canonique sur le même projet QC donne Sharpe 0.908 (le projet fonctionne),
donc le coupable est bien la combinaison `USD` + `Market.COINBASE`, pas une défaillance du
projet. `CoinbaseBrokerageModel` n'impose aucune devise de compte (lu dans la source Lean) —
c'est une subtilité de couche de settlement, pas une contrainte du modèle de brokerage.

### Analyse fee-switch (fenêtre 2018-2025, sleeve 50/50)

| Config | Source données | Fee crypto | Sharpe | CAGR | MaxDD | PSR | Backtest |
|--------|-----------------|-----------|--------|------|-------|-----|----------|
| Référence Binance (avant) | Binance | 10bps | **0.908** | 29.1% | 38.5% | 42.7% | `db1cabdb` |
| Coinbase, fee Binance | Coinbase | 10bps | **0.399** | 10.9% | 39.8% | 8.1% | `a2e9df89` |
| Coinbase, fee intermédiaire | Coinbase | 60bps | 0.373 | 10.4% | 40.3% | 7.0% | `e5f96562` |
| Coinbase, fee natif (défaut) | Coinbase | ~80bps taker | 0.362 | 10.1% | 40.5% | 6.6% | `7bef8b7f` |

`totalOrders=0` dans le wrapper MCP est un artefact d'extraction connu (le CAGR 10% implique
des trades réels) — les statistiques QC sont fiables.

**Décomposition des effets** (isolation par fee constant d'un côté, data constante de l'autre) :

- **Effet data-source** (Binance@10 → Coinbase@10, fee constant à 10bps) : Sharpe **0.908 → 0.399 = −0.51 (−56%)**. **Effet dominant.** Le différentiel de prix historique BTC/alts entre Binance et Coinbase sur 2018-2025 (liquidité, spreads, disponibilité des alts dans le basket MultiCanal) dégrade le Sharpe bien plus que le fee.
- **Effet fee** (Coinbase@10 → Coinbase natif ~80bps taker, data Coinbase constante) : Sharpe **0.399 → 0.362 = −0.04 (−9%)**. **Modéré.** Le turnover du sleeve crypto est faible (3 stratégies mensuelles, dont 2 — EMA-Cross-Crypto et HAR-RV-VolTarget — passent souvent en cash), ce qui limite l'impact du fee malgré un barème 8× plus élevé.

**Verdict honnête.** La migration MiCA coûte ~0.55 de Sharpe (0.908 → 0.362, −60%), mais **~93% de
cette dégradation vient du changement de source de données**, pas de l'augmentation du fee
Coinbase (souvent pointé du doigt, mais qui ne coûte que ~0.04). Le Sharpe 0.362 reste viable
mais sous le target 1.0-1.3 du README — la migration MiCA est une contrainte réglementaire
(continuité du service après le 2026-07-01), pas un gain de performance. Le sleeve crypto
reste dominé par le BTC (seul BTC/ETH ont des données continues pleine fenêtre sur QC) ;
la valeur ajoutée du basket MultiCanal et du HAR-RV-VolTarget est à ré-évaluer sous données
Coinbase en Phase 3.

### Analyse fee-switch — sleeve crypto isolé (`ibkr_alloc=0`)

La décomposition ci-dessus porte sur le portefeuille **composite 50/50**. Pour isoler
le coût MiCA du **sleeve crypto seul** — la question pertinente pour le double
portefeuille, où le sleeve crypto est détenu séparément du sleeve equity IBKR — on
relance le même backtest avec `ibkr_alloc=0` (sleeve IBKR désactivé, 100% crypto) sur
trois régimes de fee. Le point d'ancrage pré-MiCA est la référence Binance
sleeve-isolé (`Phase4-BinanceSleeve-Standalone-100pct`, code Binance pré-migration,
2026-06-14). Fenêtre 2018-2025, même `main.py` (le paramètre `ibkr_alloc` évite toute
duplication de code).

| Config | Source données | Fee crypto | Sharpe | CAGR | MaxDD | PSR | Backtest |
|--------|-----------------|-----------|--------|------|-------|-----|----------|
| Référence Binance sleeve-isolé | Binance | 10bps | **0.990** | 47.0% | 57.0% | 36.9% | `46aaf08e` |
| Coinbase sleeve-isolé, fee-free | Coinbase | 0bps | 0.348 | 11.9% | 58.1% | 3.3% | `6f27c434` |
| Coinbase sleeve-isolé, fee Binance | Coinbase | 10bps | 0.342 | 11.7% | 58.2% | 3.1% | `3247554e` |
| Coinbase sleeve-isolé, fee natif | Coinbase | ~80bps taker | **0.298** | 10.1% | 59.3% | 2.3% | `9f7ebbbe` |

`totalOrders=0` reste l'artefact d'extraction connu du wrapper MCP (le CAGR 10-12%
implique des trades réels).

**Décomposition sleeve-isolé** (isolation par fee constant d'un côté, data constante de l'autre) :

- **Effet data-source** (Binance@10 → Coinbase@10, fee constant à 10bps) : Sharpe
  **0.990 → 0.342 = −0.648 (−65%)**. **Effet dominant**, et même *plus marqué* que sur
  le composite 50/50 (−0.51) : sans le sleeve equity (data-source-invariant — mêmes
  ETFs IBKR sur les deux sources) pour diluer l'effet, la dégradation prix crypto
  Binance→Coinbase apparaît à plein. Le différentiel de prix historique BTC/alts
  (liquidité, spreads Binance vs Coinbase, disponibilité des alts dans le basket
  MultiCanal) est le coupable unique.
- **Effet fee** (Coinbase@10 → Coinbase natif ~80bps taker, data Coinbase constante) :
  Sharpe **0.342 → 0.298 = −0.044 (−13%)**. **Modéré**, quasi identique au composite
  50/50 (−0.04) — l'effet fee est une propriété du turnover crypto (3 stratégies
  mensuelles, dont 2 — EMA-Cross-Crypto et HAR-RV-VolTarget — passent souvent en
  cash), pas du mix de portefeuille.
- **Plafond fee-free** (Coinbase@0 → Coinbase natif) : Sharpe 0.348 → 0.298 = −0.050
  au total pour le fee. **Même à fee nul, le sleeve Coinbase plafonne à 0.348** (vs
  0.990 Binance) — confirmation que la data-source est le goulet, pas le fee.

**Convergence composite vs sleeve-isolé.** Les deux vues convergent vers le même
verdict structurel : **~94% de la dégradation MiCA vient du changement de source de
données** (sleeve-isolé : −0.648 = 93.6% du −0.692 total ; composite 50/50 : −0.51 =
93% du −0.55 total). Le fee Coinbase (souvent pointé du doigt) ne coûte que ~6%, et
aucun niveau de fee ne ramène le sleeve crypto Coinbase au niveau Binance. Le MaxDD
(~57-59%) est quasi invariant au régime de fee — c'est le ratio return/vol qui
dégrade, pas le risque de queue.

**Implication double-portefeuille.** Pour le sleeve crypto détenu seul, la migration
MiCA coûte ~0.69 de Sharpe (0.99 → 0.30, −70%). C'est une contrainte réglementaire
(continuité du service après le 2026-07-01), pas un choix de performance. Le levier
d'amélioration n'est PAS le fee (rabais taker→maker = ~+0.02) mais la **sélection de
stratégies crypto sous données Coinbase** (ré-évaluer le basket MultiCanal et le
HAR-RV-VolTarget, dont la valeur a été calibrée sur données Binance — cf Roadmap
Phase 3).

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
- **Contrainte architecturale (leçon Phase 2)** : `set_brokerage_model(IBKR)` REJETTE
  le type Crypto ("Unsupported security type") → un backtest unifié 2-broker n'est pas
  transposable tel quel en live unified. Deux approches pour Phase 4 :
  1. **Binance-first** (recommandé, un seul nœud) : paper trader le sleeve crypto seul
     sur Binance testnet (sleeve IBKR en backtest parallèle, agrégation manuelle) ;
  2. **2 algorithms séparés** (Phase 5) : un algorithm IBKR (equities) + un algorithm
     Binance (crypto), chacun sur son nœud QC Cloud, agrégation des P&L hors-pipeline.
- **Gate** : credentials IBKR paper prêts côté user (mdp reset 12/06, cf #1199) ;
  reste MAJ `.env` + test login IB Gateway avant exécution.

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

- **Phase 1** : livrée — `research.ipynb` (sleeve crypto seul, PR #1179) puis `quantbook.ipynb`
  (portefeuille complet 8 sous-stratégies : sleeve IBKR + matrice de corrélation mensuelle 8×8
  + blend net de coûts, exécuté via lean research container avec données QC réelles)
- **Phase 2** : livrée (v1) — backtest unifié 2018-2025 (`main.py`, rebalance composite direct
  des 8 sous-stratégies). Backtest QC Cloud `Phase2-DirectComposite-v7` : **Sharpe 0.916,
  CAGR 29.2%, MaxDD -38.7%** (PSR 43.6%). Verdict : **NO BEATS** — Sharpe sous le target 1.0-1.3
  et MaxDD au-delà du target -22% (mais dans la fourchette -35-40% anticipée, cf Caveats).
  CAGR élevé tiré par le sleeve crypto 50%. Coûts explicites 5bps equity/10bps crypto + 5bps
  slippage. Phase 3 = walk-forward annual + multi-seed HAR-RV-J + sweep allocation.
- **Phase 3 (OOS)** : livrée — `main.py` paramétré (`ibkr_alloc`, `start`/`end`) pour sweep
  sans duplication de code. **OOS strict 2023-2025** (params catalog frozen, jamais tunés sur
  la fenêtre) : Sharpe **1.321**, CAGR 42.8%, MaxDD -16.4%, PSR 78%. Sweep allocation OOS :
  60/40 → Sharpe 1.283 / MaxDD -15.2% ; 50/50 → 1.321 / -16.4% ; 40/60 → 1.347 / -18.8%.
  **Verdict : INCONCLUSIVE (regime-dependent).** L'OOS BEATS le target, mais la fenêtre
  2023-2025 est un bull crypto+equity sans crash ; le stress-inclusive IS (incluant l'hiver
  crypto 2022) reste à Sharpe 0.916. L'allocation ne change que ~5% le Sharpe OOS — le levier
  dominant est le régime, pas le mix. Multi-seed HAR-RV-J (passer du proxy au vrai modèle
  seedé M12) reste à faire pour durcir le verdict.
- Issue tracker : [#1027](https://github.com/jsboige/CoursIA/issues/1027)

## Liens

- [Catalog complet QC](../../README.md)
- [BOOK_MAPPING](../../BOOK_MAPPING.md) — correspondance Hands-On AI Trading
- [M12 HAR-RV-J docs](../../ML-Training-Pipeline/docs/M_NEXT_VOL_PROPOSAL.md)
- [Discipline ML/Trading](../../../../.claude/rules/pr-review-discipline.md) — Critères multi-seed et validation ML
