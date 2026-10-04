# Portfolio Hybride IBKR (50%) + Coinbase (50%)

Stratégie composite multi-broker associant un sleeve actions/ETFs (IBKR compte cash) et un sleeve crypto spot (Coinbase — migration MiCA depuis Binance, 2026-06-28), rebalancement mensuel, en piochant dans les meilleures stratégies du dépôt CoursIA.

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

### Sleeve crypto Coinbase (50%) — 3 stratégies

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
| Devise compte | `USDT` | `USD` depuis 2026-10 (paramètre `account_currency` ; `USDT` reproduit les mesures antérieures — voir [Correctif devise du compte](#correctif-devise-du-compte-2026-10)) |
| Univers crypto | 6 paires | `BTCUSD`, `ETHUSD` depuis 2026-10 (paramètre `crypto_universe` ; `basket6` = l'ancien panier de 6 paires) |
| Paramètre | — | `crypto_fee_bps` (override flat bps pour isoler l'effet fee) |

Le `CoinbaseFeeModel()` natif applique le barème réaliste Coinbase Advanced-1 (maker 0.6% /
taker 0.8%). Comme `set_holdings()` émet des ordres **market**, le taux **taker 0.8% (80bps)**
s'applique par défaut — bien plus cher que les 10bps Binance. Le paramètre `crypto_fee_bps`
permet de surcharger avec un `PercentFeeModel` flat pour isoler l'effet fee pur (ex. `10`
reproduit le barème Binance sur les données Coinbase).

### Correctif devise du compte (2026-10)

Cette section affirmait jusqu'ici que « `USD` casse le backtest (0 trade) et `USDT` restaure
les trades ». Le constat mélangeait deux causes distinctes. Elles ont été séparées sur un
projet QC de diagnostic : mêmes règles crypto que `main.py`, mêmes données Coinbase, fenêtre
2018-01-01 → 2025-06-01, sans frais pour isoler l'effet de la devise.

| Test | Compte | Univers | Ordres | Sharpe | CAGR | MaxDD | Backtest |
|------|--------|---------|--------|--------|------|-------|----------|
| BTC détenu | USD | BTC | 1 | 0.694 | 31.7% | 79.9% | `7995aecc` |
| BTC détenu | USDT | BTC | **0** | 0 | 0% | 0% | `6bf2e9ab` |
| BTC détenu, départ 2022-01-01 | USDT | BTC | 1 | 0.564 | 25.7% | 65.4% | `033d2c7b` |
| Volet crypto | USD | BTC/ETH | 174 | **0.734** | 32.8% | 64.3% | `1beb47ae` |
| Volet crypto | USDT | BTC/ETH | 95 | **0.298** | 10.0% | 55.7% | `cab3432d` |
| Volet crypto | USD | panier 6 paires | **0** | — | — | — | `ac5e57c2` |

**1. Le compte en USDT déforme la mesure.** À code, données et frais identiques, le volet
crypto passe de Sharpe 0.734 (compte USD) à 0.298 (compte USDT), avec 95 ordres au lieu de
174. Un BTC simplement détenu depuis 2018 ne passe aucun ordre en compte USDT, alors que le
même test démarré en 2022 en passe un. Explication la plus probable, cohérente avec ces trois
mesures : un compte USDT ne valorise un actif coté en USD qu'à travers une paire de conversion
USDT/USD, absente des données QC avant 2021-2022. Dans cette hypothèse, les ordres crypto
antérieurs échouent et le volet reste en cash.

**2. Le blocage en compte USD vient du panier de 6 paires, pas de la devise.** En USD, le
volet BTC/ETH tourne normalement. Le panier de 6 paires (BTC, ETH, SOL, ADA, LTC, XRP) ne passe
aucun ordre et rend une valeur de portefeuille aberrante, que le calendrier soit celui de SPY
ou celui de BTC. Seuls BTC et ETH ont des données continues sur toute la fenêtre.

**Conséquences pour `main.py`.** La devise du compte passe à `USD` (paramètre
`account_currency`) et l'univers crypto à BTC/ETH (paramètre `crypto_universe`). Avec
`account_currency=USDT` et `crypto_universe=basket6`, `main.py` retrouve l'ancienne mesure
(Sharpe 0.368 contre 0.362 publié, CAGR 10.1 %, MaxDD 40.5 %, backtest `49b5e90a`).

**Conséquences pour les analyses ci-dessous.** Les deux tableaux « fee-switch » ont été
mesurés en compte USDT avec le panier de 6 paires. La référence Binance, elle, cotait en USDT
sur un compte USDT, sans conversion. L'écart Binance → Coinbase attribué à la « source de
données » mesurait donc surtout l'artefact de conversion. Les chiffres sont conservés comme
trace historique ; leur interprétation est corrigée en tête de chaque tableau. Une comparaison
propre Binance/Coinbase, sur un compte de même devise que la cotation, reste à faire.

### Mesure corrigée (compte USD, BTC/ETH, frais Coinbase natifs)

Fenêtre 2018-01-01 → 2025-06-01, `main.py` avec ses paramètres par défaut.

| Config | Ordres | Sharpe | CAGR | MaxDD | PSR | Backtest |
|--------|--------|--------|------|-------|-----|----------|
| Portefeuille 50/50 (défaut) | 619 | **0.648** | 21.0% | 40.2% | 9.4% | `ebe12706` |
| Volet crypto seul (`ibkr_alloc=0`) | 174 | **0.681** | 29.8% | 64.7% | 9.2% | `7deee9e0` |
| Référence : BTC détenu (sans frais) | 1 | 0.694 | 31.7% | 79.9% | 8.3% | `7995aecc` |
| Ancien paramétrage (USDT, panier 6 paires) | 612 | 0.368 | 10.1% | 40.5% | 1.6% | `49b5e90a` |

**Verdict : NO BEATS.** Le volet crypto ne bat pas le BTC détenu en Sharpe (0.681 contre
0.694). En revanche, il réduit le drawdown maximal d'une quinzaine de points (64.7 % contre
79.9 %), et son Calmar est meilleur (0.46 contre 0.40) — sur cette fenêtre seulement : hors
échantillon, le BTC détenu a le plus faible drawdown (voir la sensibilité à `ibkr_alloc`
plus bas). Aucun PSR ne dépasse 10 % : aucune
de ces différences n'est statistiquement significative. Le portefeuille 50/50 reste sous la
cible de Sharpe 1.0-1.3 de ce README.

**Walk-forward et hors échantillon (compte USD, portefeuille 50/50, frais natifs).** Mêmes
fenêtres glissantes de 3 ans et même fenêtre hors échantillon que la Phase 3, même code. La
dernière colonne rappelle la mesure de la Phase 3, faite en compte USDT avec le panier de 6
paires.

| Fenêtre | Ordres | Sharpe | CAGR | MaxDD | PSR | Backtest | Sharpe Phase 3 (USDT) |
|---------|--------|--------|------|-------|-----|----------|-----------------------|
| 2019-2021 | 243 | **1.705** | 63.3% | 32.6% | 78.1% | `d6ec3484` | 0.834 |
| 2020-2022 | 258 | **0.771** | 24.4% | 38.7% | 27.4% | `6f07bf2b` | −0.193 |
| 2021-2023 | 263 | **0.628** | 19.2% | 38.7% | 18.9% | `4caa60a4` | 0.346 |
| 2022-2024 | 253 | **0.319** | 11.9% | 33.1% | 7.0% | `fa20d544` | 0.391 |
| Hors échantillon 2023-01 → 2025-06 | 201 | **1.038** | 33.2% | 19.2% | 42.6% | `affc6d09` | 1.321 |

Sur les quatre fenêtres, le Sharpe moyen passe de 0.344 (USDT) à 0.856 (USD), avec un
écart-type de 0.597 : l'écart moyen vaut 1.4 écart-type, sous le seuil de 2 retenu par ce
README. Une seule fenêtre dépasse 50 % de PSR, et la moyenne est tirée par la fenêtre
2019-2021, qui couvre le marché haussier de 2020-2021.

Les fenêtres qui démarrent en 2022 ou plus tard ne dépendent plus de la devise du compte. Sur
la fenêtre hors échantillon, un compte USDT avec BTC/ETH donne 1.041 (`8f089107`), contre
1.038 en USD : la paire de conversion existe alors. L'écart avec le 1.321 de la Phase 3 se
décompose ainsi :

- le panier de 6 paires, en compte USDT sur données Coinbase, donne 1.161 (`c028af1e`) :
  l'univers explique environ 0.12 point ;
- le 1.321 n'est pas reproduit par le code actuel. Son backtest est antérieur aux premiers
  backtests Coinbase du projet QC d'origine : il date de la version Binance du code, donc des
  données Binance et du barème de frais de cette version (10 bps crypto d'après l'état de la
  Phase 2 ci-dessous).

**Verdict Phase 3 en compte USD : NO BEATS, dépendant du régime.** Le correctif de devise
relève nettement le walk-forward, mais l'avantage reste sous 2 écarts-types et dépend
fortement de la fenêtre.

**Sensibilité à `ibkr_alloc` (compte USD, frais natifs).** Même code ; seul varie le poids du
volet IBKR (`ibkr_alloc=1` : volet IBKR seul ; `ibkr_alloc=0` : volet crypto seul). La
dernière ligne de chaque tableau est la référence BTC détenu, sans frais.

Fenêtre 2018-01-01 → 2025-06-01 :

| `ibkr_alloc` | Ordres | Sharpe | CAGR | MaxDD | PSR | Backtest |
|--------------|--------|--------|------|-------|-----|----------|
| 1.0 (IBKR seul) | 432 | 0.288 | 7.5% | 19.3% | 0.9% | `bfd0101f` |
| 0.6 | 618 | 0.637 | 18.6% | 34.5% | 9.1% | `3a8ed80e` |
| 0.5 (défaut) | 619 | 0.648 | 21.0% | 40.2% | 9.4% | `ebe12706` |
| 0.4 | 610 | 0.656 | 23.1% | 45.9% | 9.4% | `1035fd89` |
| 0.0 (crypto seul) | 174 | 0.681 | 29.8% | 64.7% | 9.2% | `7deee9e0` |
| BTC détenu | 1 | 0.694 | 31.7% | 79.9% | 8.3% | `7995aecc` |

Hors échantillon 2023-01-01 → 2025-06-01 :

| `ibkr_alloc` | Ordres | Sharpe | CAGR | MaxDD | PSR | Backtest |
|--------------|--------|--------|------|-------|-----|----------|
| 1.0 (IBKR seul) | 143 | 0.495 | 13.5% | 11.8% | 15.1% | `aaa80999` |
| 0.6 | 206 | 1.022 | 29.4% | 17.4% | 42.4% | `5f9586bd` |
| 0.5 (défaut) | 201 | 1.038 | 33.2% | 19.2% | 42.6% | `affc6d09` |
| 0.4 | 193 | 1.046 | 36.9% | 20.9% | 42.4% | `e9fe390e` |
| 0.0 (crypto seul) | 57 | 1.076 | 51.0% | 33.0% | 41.0% | `2e952776` |
| BTC détenu | 1 | **1.924** | 113.2% | 28.1% | 76.0% | `92dcbc1b` |

Trois constats :

- **Le mélange déplace le couple rendement/drawdown, pas le Sharpe.** Dès que la crypto est
  présente, le Sharpe varie de moins de 0.06 entre 60/40 et 0/100, sur les deux fenêtres ;
  CAGR et MaxDD montent ensemble avec la part crypto. C'est le régime de marché, pas le
  mélange, qui fait le Sharpe — conclusion déjà tirée en Phase 3.
- **Le volet IBKR seul est faible** : Sharpe 0.288 sur 2018-2025 (PSR 0.9 %), 0.495 hors
  échantillon. Le Sharpe du portefeuille vient de la crypto ; le volet IBKR sert surtout à
  amortir le drawdown.
- **Hors échantillon, le BTC détenu bat le volet crypto sur tous les critères, drawdown
  compris** (MaxDD 28.1 % contre 33.0 %). La réduction de drawdown constatée sur 2018-2025
  vient des krachs de 2018 et 2022, que la fenêtre récente ne contient pas : elle ne suffit
  pas, à elle seule, à justifier le volet face à une simple détention de BTC.

### Analyse fee-switch (fenêtre 2018-2025, sleeve 50/50)

> **Mesure historique, compte USDT, panier de 6 paires (2026-06).** Les lignes Coinbase de
> ce tableau portent l'artefact de conversion décrit dans
> [Correctif devise du compte](#correctif-devise-du-compte-2026-10). L'« effet data-source »
> déduit ci-dessous n'est pas établi : la mesure corrigée est dans
> [Mesure corrigée](#mesure-corrigée-compte-usd-btceth-frais-coinbase-natifs).

| Config | Source données | Fee crypto | Sharpe | CAGR | MaxDD | PSR | Backtest |
|--------|-----------------|-----------|--------|------|-------|-----|----------|
| Référence Binance (avant) | Binance | 10bps | **0.908** | 29.1% | 38.5% | 42.7% | `db1cabdb` |
| Coinbase, fee Binance | Coinbase | 10bps | **0.399** | 10.9% | 39.8% | 8.1% | `a2e9df89` |
| Coinbase, fee intermédiaire | Coinbase | 60bps | 0.373 | 10.4% | 40.3% | 7.0% | `e5f96562` |
| Coinbase, fee natif (défaut) | Coinbase | ~80bps taker | 0.362 | 10.1% | 40.5% | 6.6% | `7bef8b7f` |

`totalOrders=0` dans le wrapper MCP est un artefact d'extraction connu (le CAGR 10% implique
des trades réels) — les statistiques QC sont fiables.

**Lecture corrigée (2026-10).** La lecture initiale attribuait ~93 % de l'écart à la source
de données. Elle est retirée.

- **Effet source de données (Binance@10 → Coinbase@10) : non établi.** La ligne Binance
  négocie des paires cotées en USDT sur un compte USDT. Les lignes Coinbase négocient des
  paires cotées en USD sur ce même compte USDT, donc à travers la conversion absente avant
  2021-2022. L'écart 0.908 → 0.399 mélange le changement de données et cet artefact.
- **Effet frais : la conclusion tient.** Re-mesuré en compte USD sur le volet crypto seul
  (BTC/ETH), le Sharpe passe de 0.734 sans frais (`1beb47ae`, projet de diagnostic) à 0.681
  avec le barème Coinbase natif (`7deee9e0`), soit environ −0.05. Le volet rebalance une fois
  par mois et ses deux sous-stratégies BTC passent souvent en cash : le barème taker de 0.8 %
  pèse peu.

### Analyse fee-switch — sleeve crypto isolé (`ibkr_alloc=0`)

> **Mesure historique, compte USDT, panier de 6 paires (2026-06).** Même réserve que pour le
> tableau précédent : les lignes Coinbase portent l'artefact de conversion. Le volet crypto
> seul, re-mesuré en compte USD, fait Sharpe 0.681 avec les frais natifs, et non 0.298.

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

**Lecture corrigée (2026-10).** La lecture initiale concluait que ~94 % de la dégradation
venait de la source de données, et qu'à frais nuls le volet Coinbase plafonnait à 0.348.
Ces deux conclusions sont retirées : le plafond observé était celui du compte USDT. En compte
USD, à frais nuls, le même volet sur BTC/ETH atteint 0.734.

Ce qui reste établi pour le double portefeuille :

- **Les frais pèsent peu.** Environ −0.05 de Sharpe entre zéro frais et le barème taker natif,
  dans les deux devises de compte.
- **Le levier est le choix des stratégies et de l'univers.** Le volet crypto n'apporte pas de
  meilleur Sharpe que le BTC détenu, mais un drawdown plus faible. C'est sur ce critère qu'il
  se juge (voir [Mesure corrigée](#mesure-corrigée-compte-usd-btceth-frais-coinbase-natifs)).

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
- Sweep allocation IBKR/Coinbase : 60/40, 50/50, 40/60, régime-adaptatif

### Phase 4 — Paper trading 30j (S3-S4)
- **Harness livré** (`paper_harness/`, PR #3942) : sleeves `ibkr_sleeve.py` +
  `coinbase_sleeve.py` (migration Binance → Coinbase, `binance_sleeve.py` conservé en
  legacy pré-MiCA) + `smoke_test_*.py` par sleeve + `risk.py` (circuit breakers).
- Connexion paper IBKR + **Coinbase sandbox** (remplace Binance testnet post-MiCA).
- Logging quotidien : fills réels vs backtest, slippage, market impact
- Comparison live drift vs expected returns/vol
- **Contrainte architecturale (leçon Phase 2)** : `set_brokerage_model(IBKR)` REJETTE
  le type Crypto ("Unsupported security type") → un backtest unifié 2-broker n'est pas
  transposable tel quel en live unified. Deux approches pour Phase 4 :
  1. **Crypto-first** (un seul nœud) : paper trader le sleeve crypto seul sur Coinbase
     sandbox (sleeve IBKR en backtest parallèle, agrégation manuelle) ;
  2. **2 algorithms séparés** (Phase 5) : un algorithm IBKR (equities) + un algorithm
     Coinbase (crypto), chacun sur son nœud QC Cloud, agrégation des P&L hors-pipeline.
- **Gate mainteneur** : les accès aux plateformes (sandbox Coinbase, compte paper IBKR, cf
  #1199) relèvent du mainteneur. Exécution Phase 4 = RECOVERABLE-USER-HAND.

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
5. Transaction costs : 5bps IBKR equities, ~80bps taker Coinbase Advanced (native `CoinbaseFeeModel()`, ou override via `crypto_fee_bps`), +5bps slippage market impact
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
  dominant est le régime, pas le mix.

  Multi-seed HAR-RV-J (passer du proxy au vrai modèle
  seedé M12) reste à faire pour durcir le verdict.

  > Les chiffres des Phases 2 et 3 ci-dessus datent de la version Binance du volet crypto
  > (avant la migration du 2026-06-28). Le code actuel, en compte USD sur données Coinbase, est
  > re-mesuré dans [Mesure corrigée](#mesure-corrigée-compte-usd-btceth-frais-coinbase-natifs) :
  > Sharpe 0.648 sur 2018-2025, 1.038 hors échantillon, verdict NO BEATS dépendant du régime.
- **Phase 4 (paper harness)** : livrée (`paper_harness/`, PR #3942) — sleeves IBKR +
  Coinbase (+ legacy Binance), smoke tests par sleeve, circuit breakers (`risk.py`).
  Exécution paper 30j **RECOVERABLE-USER-HAND** : accès aux plateformes à la main du
  mainteneur (#1199).
- Issue tracker : [#18789](https://github.com/jsboige/CoursIA/issues/18789) (correctif devise du
  compte), à la suite de [#1027](https://github.com/jsboige/CoursIA/issues/1027)

## Liens

- [Catalog complet QC](../../README.md)
- [BOOK_MAPPING](../../BOOK_MAPPING.md) — correspondance Hands-On AI Trading
- [M12 HAR-RV-J docs](../../ML-Training-Pipeline/docs/M_NEXT_VOL_PROPOSAL.md)
- [Discipline ML/Trading](../../../../.claude/rules/pr-review-discipline.md) — Critères multi-seed et validation ML
