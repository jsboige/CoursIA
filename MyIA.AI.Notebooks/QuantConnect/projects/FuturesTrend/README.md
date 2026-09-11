# FuturesTrend (Multi-Asset Trend Following v3.1)

Stratégie de **suivi de tendance multi-actifs** sur 6 ETF diversifiés (SPY, GLD, EFA, VNQ, DBC, XLE), basée sur un breakout Donchian filtré par tendance. Malgré son nom historique, l'algorithme courant (`main.py`, classe `FuturesTrendFollowing`) trade des **ETF actions/matières premières** — non des contrats futures.

## Résumé

| Paramètre | Valeur |
|-----------|--------|
| **Instrument** | 6 ETF (SPY, GLD, EFA, VNQ, DBC, XLE) |
| **Univers** | Actions US, or, intl, immobilier, matières, énergie |
| **Signal** | Breakout Donchian (20j) + filtre tendance SMA50 |
| **Entry** | Clôture > Max(High, 20 jours) ET prix > SMA50 |
| **Exit** | Clôture < Min(Low, 10 jours) |
| **Position Sizing** | 33 % de poids fixe par position |
| **Max positions** | 3 (concentrées sur les meilleures dynamiques) |
| **Benchmark** | SPY |

## Métriques de backtest (2015-2024)

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | 0.07 |
| CAGR | 4.170% |
| Max Drawdown | 15.500% |
| Net Profit | 60.618% |
| Total Orders | 463 |
| Probabilistic Sharpe Ratio | 0.007% |

> **Provenance** : backtest QC Cloud `b869c19d1320401e3c3a84ae7037abc4` (2026-08-05),
> projet 28657834, IBKR margin, 2913 jours tradeables (2015-2024), $100k initial.
> Re-exécuter via QC Cloud ou `lean backtest` pour recalculer.
>
> **Lecture honnête** : un Sharpe de 0,07 avec PSR 0,007 % est un **edge statistiquement
> nul** — la stratégie ne bat pas de façon fiable le buy-and-hold de SPY. La docstring du
> `main.py` épingle v3.1 = Sharpe 0,301 / CAGR 8,0 %, mesurés sur une fenêtre plus étroite
> (antérieure à l'extension 2015-2024) ; sur la période complète, l'edge de trend-following
> s'érode (0,301 → 0,07). C'est un contre-exemple pédagogique : une logique de suivi de
> tendance séduisante en sample ne conserve pas son edge hors-échantillon. Les valeurs
> `~0.5-0.8` auparavant inscrites en prose ici étaient **surévaluées** (de ~5-10x).

## Fichiers

- `main.py` - Stratégie `FuturesTrendFollowing` v3.1 (breakout Donchian + filtre SMA50)
- `research.ipynb` - Analyse des tendances, optimisation des paramètres
- `quantbook.ipynb` - Notebook de recherche QuantConnect

## Logique

### Entry
- **Long** : sur les ETF en **tendance haussière** (prix > SMA50) dont la clôture casse le **Max(High, 20 jours)** (breakout Donchian).
- Les candidats sont triés par momentum (prix / entry_high) ; seuls les **3 meilleurs** entrent (concentration sur les tendances les plus fortes).

### Exit
- **Long exit** : clôture < **Min(Low, 10 jours)** (canal Donchian de sortie).

### Position Sizing
- **Poids fixe de 33 %** par position (`set_holdings(symbol, 0.33)`), jusqu'à **3 positions** simultanées (99 % max investis). Pas de sizing par risque/ATR (testé en v4.0, régressif — coupait les gagnants trop tôt).

## Configuration

```python
self.entry_period = 20      # Canal Donchian d'entrée (high breakout)
self.exit_period = 10       # Canal Donchian de sortie (low breakdown)
self.trend_sma_period = 50  # Filtre de tendance long-terme
self.weight = 0.33          # Poids fixe par position
self.max_positions = 3      # Concentration maximale
```

## Risques

- **Whipsaws** : faux signaux en marchés range-bound (le breakout Donchian génère de nombreuses petites pertes en consolidation).
- **Low Win Rate** : beaucoup de petites pertes, peu de grosses tendances gagnantes (profil asymétrique du trend-following).
- **Drawdown** : 15,5 % observés sur 2015-2024 (le filtre SMA50 les atténue sans les éliminer).
- **Regime dependency** : l'edge s'érode hors des régimes de tendance forte (cf. écart 0,301 → 0,07 entre fenêtre étroite et période complète).

## Améliorations possibles

- Filtre de volatilité (ATR) pour réduire les whipsaws.
- Trailing stop (testé en v4.0 = régressif, à reprendre différemment).
- Pyramiding (ajouter sur confirmation de tendance).
- Dynamisation de l'univers (rotation sectorielle).

## Variante Carver #13 (portage substantiel — issue #15549)

Le fichier `main_carver13.py` (classe `CarverThirteen`) est un **portage local** de la
stratégie n° 13 de Robert Carver (*Advanced Futures Trading Strategies*, Harriman House
2023, ISBN 9780857199683), telle que recréée dans l'article QuantConnect
*Futures Trend Following and Carry in Different Risk Regimes* (#15989, Derek Melchin,
2026-01-02). Cette variante coexiste avec `main.py` v3.1 sans le modifier — v3.1
reste la **baseline ETF** à laquelle Carver #13 sera comparé.

| Composant | v3.1 (ETF, baseline) | Carver #13 (c.1109) |
|-----------|----------------------|---------------------|
| Univers | 6 ETF (SPY/GLD/EFA/VNQ/DBC/XLE) | 19 futures continus (ES/NQ/YM/ZN/ZB/ZF/6E/6B/6J/CL/NG/RB/GC/SI/HG/ZC/ZW/ZS/SB) |
| Signal entrée | Donchian 20j + filtre SMA50 | 6 horizons EWMAC (Carver pairs 8/32, 16/64, 32/128, 64/256, 16/48, 32/96) avec scalaire per-horizon `sqrt(slow/32)` (c.1063 increment) |
| Carry factor | absent | **désactivé** (voir note ci-dessous ; c.1107 + c.1109) |
| Multiplicateur régime | absent | vol-régime borné [0.5, 2] |
| FDM (Forecast Diversification Multiplier) | absent | **requalifié honnêtement** en *breadth multiplier* clip [1, 2] (c.1109 REPAIR-3, voir note) |
| Cap forecasts | n/a | +/-20 par forecast |
| Position sizing | fixe 33% par position (max 3) | vol-scaled, sign-normalisé, retarget du **delta** (pas d'aller-retour fabriqué, c.1109) |
| Fenêtre de backtest | 2015-2024 | 2016-2026 (acceptance #15549) |

### Note Tell c.1069 strict — Carry désactivé sur cette implémentation (c.1107)

Le carry proxy front-only initialement livré (c.1106) réduisait à la pente
`EWMA(8,32)` sur la même série de closes — formule bit-identique au signal
`EWMAC(8,32)` déjà inclus dans la moyenne des 6 horizons EWMAC. Le blend 60/40
trend+carry était donc un forecast 100% trend avec un coefficient 0.4 sur un
signal dupliqué. Pour éviter de livrer une stratégie qui se présente à tort
comme un blend trend+carry, l'implémentation c.1107 fait **trend-only** :
`_carry_forecast(front, deferred)` reste défini comme stub utilisable mais
n'est plus appelé depuis `_rebalance` ; le forecast est `trend_component` pur
(moyenne des 6 EWMAC, capée à +/-20).

Le carry **proprement dit** (rapport front/deferred via l'API `Future` chain)
est documenté comme follow-up de l'acceptance #15549 : il demande la
disponibilité de la chain API (présent en QC Cloud, pas en local sans
credentials). La méthode `_carry_forecast(front_close, deferred_close)`
reste l'interface prévue — l'appelant futur (lane QC équipée) n'a qu'à passer
les deux closes réelles.

### Note Tell c.1069 strict — FDM requalifié en breadth multiplier (c.1109 REPAIR-3)

Le préflight adjoint po-2025 (`msg-20260911T043805-i7tl0g`) a détecté que
la formule `_fdm()` livrée c.1107 (`sum(|f|)/sqrt(sum(f^2))` clip `[1, 2]`)
est un **breadth bonus**, pas une pénalité de concentration comme Carver
chap. 9 l'aurait prescrit : le ratio monte (≥1) quand les signaux
s'alignent, et monte aussi quand ils sont indépendants — c'est l'inverse
de l'intention Carver. Sans estimateur de corrélation exogène, la formule
instantanée ne peut pas pénaliser la concentration.

**REPAIR-3 c.1109** (Tell c.1069 strict honnêteté référentielle) :
- Renommage `_fdm` → `_breadth_multiplier` (honnêteté du nom)
- Docstring Carver-true : bonus quand le book est unidirectionnel, pas pénalité
- Clip inchangé `[1, 2]` (soft cap de gross leverage, conservateur)
- Module docstring et class docstring mis à jour en conséquence
- Le Carver FDM au sens propre reste une dette de fond (#15549 acceptance
  follow-up : estimateur de corrélation rolling)

### Note Tell c.1069 strict — Retarget delta direct, pas d'aller-retour fabriqué (c.1109 REPAIR-3)

Le préflight adjoint a aussi détecté que `_rebalance` liquidait toutes
les positions investies avant `set_holdings`, ce qui **fabrique** un
aller-retour (1 liquidate + 1 set_holdings = double commission) même
quand la cible est proche de la position actuelle.

**REPAIR-3 c.1109** :
- Liquidation uniquement sur **changement de signe** (long → short ou
  inverse) ou **cible ~ 0**.
- `set_holdings(sym, target_weight)` est idempotent côté broker
  (ajustement à la cible absolue, pas de commission synthétique sur la
  jambe existante quand le signe est conservé).
- Les coûts backtestés deviennent comparables à un rebalancement réel.

### Statut courant (c.1109, lane `myia-po-2027:CoursIA-2`)

- Le code **compile statiquement** (`ast.parse` PASS, 8 fonctions / 1 classe / 386
  lignes, EOL LF, 0 secret literal).
- **Aucun backtest exécuté** : le verdict SOTA est `RECOVERABLE-MACHINE` (credentials
  QC absents sur po-2027 — vérifié firsthand `env | grep -iE "QC_|QUANTCONNECT"` =
  0 hit). La jambe QC Cloud (compile/backtests) sera déléguée à une lane CoursIA-2
  équipée, sur cette branche, **sans transmission de secret** (Tell secrets-hygiene
  règle 1 : jamais de clair sur dashboard/PR/commit, `os.getenv("KEY","<literal>")`
  interdit).
- **Verdict futur** : `BEATS` / `NO BEATS` / `INCONCLUSIVE` selon Sharpe/CAGR/MaxDD/
  PSR/exposition/coûts/ordres sur fenêtre >= 2016-2026, **sans présumer** du
  Sharpe 0,944 vs 0,749 rapporté par l'article #15989 sur 2020-2023 (fenêtre
  favorable non-représentative).
- **REPAIR c.1107** : deux défauts détectés par le préflight adjoint po-2025
  (`msg-20260911T040615-4c08xy`) avant lancement des runs QC Cloud — (a) carry
  proxy identique à EWMAC(8,32), (b) FDM clip à l'inverse de la docstring.
- **c.1063 increment** : scalaire per-horizon `sqrt(slow/32)`, warmup 2x cohérent,
  history bulk 1 call. Détails dans le commit `e41a4eb8d632`.
- **REPAIR-3 c.1109** : FDM requalifié en breadth multiplier (Tell c.1069 strict
  honnêteté référentielle) + retarget delta direct (pas d'aller-retour fabriqué).
  Préflight adjoint po-2025 `msg-20260911T043805-i7tl0g` ; jambe QC po-2026
  suspendue jusqu'au nouveau head exact.

## Références

- Curtis Faith (2007), *Way of the Turtle* — règles de trend-following Donchian.
- Moskowitz, Ooi & Pedersen (2012), *Time Series Momentum* — trend-following multi-actifs.
- Carver, Robert (2023), *Advanced Futures Trading Strategies: 30 Fully Tested
  Strategies for Multiple Trading Styles and Time Frames*, Harriman House,
  ISBN 9780857199683 — source primaire de la stratégie n° 13 (EWMAC + carry +
  vol-régime + FDM).
- QuantConnect research article #15989 (Derek Melchin, 2026-01-02) — recréation
  pédagogique de la stratégie n° 13 sur QC Cloud.
- Analyse détaillée : `research.ipynb`.
