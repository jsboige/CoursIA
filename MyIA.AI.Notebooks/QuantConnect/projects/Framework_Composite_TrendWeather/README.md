# Framework_Composite_TrendWeather

**Classe d'actifs :** Actions US (ETF + actions)
**Cloud project ID :** Aucun (local uniquement)

> 🇬🇧 **English version** : voir [`README.en.md`](README.en.md) (golden set préservé).
> 🇫🇷 **Version FR golden set** : [`README.fr.md`](README.fr.md) (préserve l'original FR avant bascule c.1284).

## Description

Composite framework combinant TrendStocks (75 %) avec AllWeather (25 %) via l'Algorithm Framework de QuantConnect. La composante tendance utilise SMA200+EMA20/EMA50 sur 15 large-caps (AAPL/MSFT/GOOGL/AMZN/NVDA/JPM/V/MA/UNH/JNJ/XOM/CVX/HD/PG/KO), AllWeather apporte la diversification statique (SPY 30 % / IEF 30 % / GLD 30 % / XLP 10 %).

## Mesures vérifiées (multi-source)

> **Note honnête (#1621, drainage #9434)** : le dossier Framework_Composite_TrendWeather souffrait d'une **misattribution méthodologique « sweep comment »** : le README présentait « Sharpe 1.155, CAGR 27.4 %, MaxDD 27.7 % » comme « Métriques de backtest » alors que ces chiffres sont tirés du **bloc commentaire de `main.py:8-13`** (`Allocation sweep results (2015-2026)` v1.3/v1.4b/v1.4c/v1.4d/v1.4e — un sweep d'allocation **sans backtest tracé**) **et NON d'une exécution persistante** dans le dépôt : **pas de `lean-workspace/`, pas de `create_backtest` artifact**, pas de JSON output cloud. La stratégie a été ajoutée dans le commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) qui déclarait « Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155) » — la valeur 1.155 est donc plausiblement issue d'un backtest cloud **one-shot** au moment du commit initial, **non préservé** dans le dépôt. Le `quantbook.ipynb` (recherche locale Docker + yfinance) utilise un **défaut 50/50 différent** et **avertit explicitement** (cf. `iter4_research.py:176` : « Simulation Sharpe is typically 2-3x cloud Sharpe »). Les tableaux ci-dessous citent chaque source avec sa traçabilité explicite + un **drapeau SUSPECT overfit « sweep-comment »**.

| Source | Sharpe | CAGR | MaxDD | Allocation | Période | Méthodologie |
|--------|--------|------|-------|-----------|---------|--------------|
| **`main.py:8-13` sweep comment** (claim original commit `fa122ae7e`) | **1.155** | **27.4 %** | **27.7 %** | T75 / AW25 (v1.4d selected) | **2015-2026** | Allocation sweep interne (5 tranches T60→T80), **pas de backtest tracé dans le dépôt** |
| `iter4_research.py` yfinance local | n/a (script) | n/a | n/a | grid 5×5×3 | 2014-2026 | yfinance local, **AVERTIT** « Simulation Sharpe typically 2-3× cloud Sharpe » |
| `quantbook.ipynb` cell 12 (research default 50/50) | **0.680** | **10.88 %** | **-23.53 %** | T50 / AW50 (default research) | 2015-2026 | Lean CLI Docker research, **défaut 50/50 ≠ main.py T75/AW25** |
| `quantbook.ipynb` cell 8 (allocation sweep) | 0.382 → 0.738 | 7.22 % → 14.02 % | -33.72 % → -17.29 % | grid T0/T10/.../T100 (PAS de T75) | 2015-2026 | Lean CLI Docker, **T75 absente du grid (jumps T70→T80)** |
| `quantbook.ipynb` cell 9 (stop-loss sweep) | **0.684 → 2.124** ⚠️ | 10.93 % → 21.29 % | -23.53 % → -4.86 % | T50/AW50 + stop-loss | 2015-2026 | Lean CLI Docker, **Stop 5 % Sharpe 2.124 = SUSPECT overfit structurel** |
| `quantbook.ipynb` cell 11 (rebalance freq sweep) | 0.626 → 1.070 | 9.92 % → 16.13 % | -23.53 % → -23.94 % | T50/AW50 weekly/bi-weekly/monthly | 2015-2026 | Lean CLI Docker, **monthly > weekly par 35-40 % Sharpe** |
| `quantbook.ipynb` cell 12 (T×freq grid) | 0.544 → 1.161 | 8.90 % → 17.83 % | -27.88 % → -22.00 % | T30→T60 × W/2W/M | 2015-2026 | Lean CLI Docker, **T60/Monthly Sharpe 1.161 ≈ main.py T75** |
| **Production cloud backtest (one-shot, fa122ae7e)** | **1.155** | **27.4 %** | **27.7 %** | T75 / AW25 (v1.4d) | 2015-2026 | **NON PERSISTÉ dans le dépôt** — claim original du commit initial |

**Lecture honnête — SUSPECT « SWEEP-COMMENT MISATTRIBUTION » (c.1284-L1 ★★)** : un Sharpe de **1.155** revendiqué sur 11 ans (2015-2026) avec **allocation T75/AW25**, cité depuis un **bloc commentaire dans `main.py:8-13`** (`Allocation sweep results`) **sans backtest cloud traçable dans le dépôt**, est exposé à **3 sources méthodologiques de surestimation** distinctes des library clones (c.1281-L2/82-L2/83-L2) :

1. **Sweep-comment overfitting structurel** : le `main.py:8-13` docstring cite 5 tranches (T60/T65/T70/**T75**/T80) qui varient **monotonement** (Sharpe 1.130→1.141→1.149→**1.155**→1.163, CAGR 23.8 %→25.0 %→26.2 %→**27.4 %**→28.7 %, MaxDD 24.5 %→25.6 %→26.6 %→**27.7 %**→28.7 %) — **+0.033 Sharpe entre T70 et T75 sur 11 ans = 0.003/an, dans le bruit statistique**. Le choix « T75/AW25 selected » est un **milieu de grid monotone** (pas un optimum discriminant), avec un commentaire « best risk/return balance before beta exceeds 0.80 and MaxDD approaches 29 % » qui n'est étayé par aucune mesure de beta dans le dépôt. La grille est **régulière** (T60→T65→T70→T75→T80, step 5), **pas discriminante**.

2. **`quantbook.ipynb` 50/50 ≠ `main.py` T75/AW25** : la recherche locale du dépôt utilise un **défaut 50/50** (cf. `quantbook.ipynb:11-12` : « TrendStocks (50 %) + AllWeather (50 %) ») **différent du T75/AW25 production**. La grille d'allocation `quantbook.ipynb` cell 8 montre **T70/T30 = Sharpe 0.728** et **T80/T20 = Sharpe 0.737** — donc **interpolation vers T75 ≈ Sharpe 0.732**, **pas 1.155**. L'écart **1.155 - 0.732 = +0.42** ne s'explique pas par le seul changement d'allocation ; il vient probablement de **différences méthodologiques substantielles** (frais Interactive Brokers dans `main.py:45` `INTERACTIVE_BROKERS_BROKERAGE` vs simulation 0 frais dans `quantbook.ipynb:155-160`, périmètre univers TrendStocks `main.py:36-50` 15 noms vs 15 noms identiques OK, **MAIS** momentum-weighted `main.py:36-37` `TrendStocksAlpha` vs equal-weight dans `quantbook.ipynb:131-148`, **ET** période warmup + rééquilibrage mensuel 31j dans `main.py:54` vs weekly default dans `quantbook.ipynb` cell 11 sweep). Sans **rétro-engineering complet**, l'écart reste non-attribué.

3. **`iter4_research.py` AVERTIT 2-3× overstate** : le script de recherche locale affiche explicitement (ligne 176) « Simulation Sharpe is typically 2-3× cloud Sharpe ». Donc la **simulated Sharpe 0.732 (cell 8, T70)** pourrait masquer une **cloud Sharpe ≈ 0.24-0.37**, **pas 1.155**. Inversement, le **cloud Sharpe 1.155** pourrait correspondre à une **simulation ≈ 2.3-3.5** (jamais observée dans le grid du quantbook, où max = 2.124 sur Stop 5 % — mais ce 2.124 est lui-même SUSPECT). **L'écart entre 1.155 (production) et 0.732 (local sim 50/50) reste non-résolu**.

**Cumul des 3 effets** : le Sharpe 1.155 / CAGR 27.4 % / MaxDD 27.7 % cité en README pourrait masquer un Sharpe réel **0.6-0.9** sur la même stratégie avec (a) IBKR fees réels + dividendes + slippage quantifiés, (b) window OOS fixée a priori (pas sweep a posteriori), (c) périmètre TrendStocks élargi ou restreint documenté. C'est **PAS** un signal de déploiement live sans **rétro-engineering méthodologique complet** ou **backtest QC Cloud frais** avec output JSON préservé.

Cf. **c.1281-L3 / c.1282-L3 / c.1283-L3 ★★** (library clones) : le pattern « misattribution » s'applique ici avec un **3ᵉ archétype** : library clones (claim OOS 1Y sans repro locale, c.1281/82/83) + **sweep-comment (c.1284) = bloc commentaire `main.py:N` cité comme « backtest metrics » sans backtest traçable**. La mécanique constante reste : **provenance explicite + SUSPECT pedagogy warning obligatoire**.

**Vérification de la provenance** : le commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) déclare « Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155) » dans son message — **le 1.155 est donc un claim d'auteur de commit, non une mesure reproductible** depuis le dépôt. **Pas de tag QC Cloud Project ID**, **pas de `lean-workspace/`, pas de backtest JSON préservé**. Pour reproduire, il faudrait **re-créer un projet QC Cloud, copier `main.py + alpha_models.py + portfolio_construction.py`, et exécuter `lean backtest` ou `create_compile` + `create_backtest`** — opération **hors scope** cette PR (PR markdown-only).

**Reproductibilité** : la sweep-comment claim est **non reproductible** depuis le dépôt actuel (pas d'artifacts). Les recherches locales **sont reproductibles** : `python iter4_research.py` (yfinance local, 2-3× overstate) ou `jupyter nbconvert --execute quantbook.ipynb` (Lean CLI Docker, défaut 50/50). Le tableau ci-dessus cite **les deux sources** pour transparence.

## Comment exécuter

**Lean CLI (recherche locale, défaut 50/50) :** `lean research "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather" --notebook quantbook.ipynb`
**Lean CLI (backtest, défaut 50/50) :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather"`
**Lean CLI (backtest production T75/AW25) :** identique, `main.py` fixe `alpha_allocations={"TrendStocks": 0.75, "AllWeather": 0.25}` ligne 53. **Mais attendre une variation ~±30-50 % sur Sharpe** vs le 1.155 docstring à cause de (a) `INTERACTIVE_BROKERS_BROKERAGE` ligne 45 vs 0 frais dans recherche, (b) périmètre univers TrendStocks `main.py:36-50` (15 noms) vs 15 noms identiques OK, (c) momentum-weighted TrendStocks vs equal-weight, (d) mensuel 31j vs weekly par défaut.
**QC Cloud :** non déployé. Copier `main.py + alpha_models.py + portfolio_construction.py` dans un nouveau projet QC Cloud pour exécuter et préserver les outputs dans `lean-workspace/<project>/backtests/<timestamp>/`. **Recommandation anti-SUSPECT** : **re-exécuter** le backtest cloud avec le T75/AW25 exact, **préserver le JSON output** dans le worktree, et **comparer** au 1.155 docstring — l'écart attendu (cf. `iter4_research.py:176` 2-3× overstate) devrait ramener le Sharpe à ~0.4-0.6 dans le pire cas (surestimation locale) ou confirmer le 1.155 (backtest one-shot originel correct).

**Note variations Docker Lean** : `quantbook.ipynb` cell 12 montre que la même stratégie exécutée en **monthly vs weekly** donne Sharpe **1.064** vs **0.674** (cell 11) — c'est l'effet « less-frequent-rebalance » qui réduit le turnover et préserve les trends. Le `main.py` ligne 54 utilise `rebalance=timedelta(days=31)` (monthly) — donc **dans la même veine que les 1.064**, **pas 0.674**.

## Fichiers

- `main.py` — Stratégie composite v1.5 production (T75/AW25, monthly rebalance, IBKR fees). **Contient le sweep comment `Allocation sweep results (2015-2026)` lignes 8-13, source du 1.155/27.4 %/27.7 %** ⚠️
- `alpha_models.py` — TrendStocksAlpha (momentum-weighted) + AllWeatherAlpha (static)
- `portfolio_construction.py` — MultiStrategyPCM (allocation dict + rebalance interval)
- `iter4_research.py` — Recherche yfinance locale (avertit 2-3× overstate cloud Sharpe, ligne 176)
- `quantbook.ipynb` — Recherche Lean CLI Docker : 50/50 default + sweeps (allocation, stop-loss, rebalance freq, T×freq) avec outputs préservés

## Références

- Commit `fa122ae7e` (2026-03-09, jsboige + Claude Opus) — ajout initial de la stratégie, message déclare « Iterated from v1.0 (Sharpe 0.622) to v1.5 (Sharpe 1.155) » — **source originelle du 1.155**, **pas d'artifacts préservés**.
- `main.py:8-13` docstring — `Allocation sweep results (2015-2026)` block, **source du claim sweep-comment c.1284-L1**.
- `iter4_research.py:176` — avertissement explicite « Simulation Sharpe typically 2-3× cloud Sharpe ».
- `quantbook.ipynb` cells 5/8/9/11/12 — sweeps allocation/stop-loss/rebalance/T×freq avec outputs préservés.
- c.1281-L3 / c.1282-L3 / c.1283-L3 ★★ — pattern méta misattribution 6 sœurs (5 library clones + 1 sweep-comment c.1284)
- #1621 (drainage epic — prose réelle mesurée vs stale dans le repo)
- #9434 (drainage umbrella — multi-PR cleanup des README stale)
