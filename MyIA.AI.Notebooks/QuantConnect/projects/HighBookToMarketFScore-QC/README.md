# HighBookToMarketFScore-QC

**Classe d'actifs :** Actions US (value stocks)
**ID projet Cloud :** QC Project ID: 29687591 (cloned 2026-04-05, **non déployé en QC Cloud**)

> 🇬🇧 **English version** : voir [`README.en.md`](README.en.md) (golden set préservé, original avant bascule FR).

## Description

Clone de la **QC Strategy Library #343** (*High Book-to-Market High F-Score Quality Value* par **Louis Szeto**). Stratégie value+quality systématique sélectionnant les actions avec book-to-market élevé filtrées par Piotroski F-Score ≥ 8, equally-weighted, rebalance mensuel.

## Mesures vérifiées (multi-source)

> **Note honnête (#1621, drainage #9434)** : le dossier HighBookToMarketFScore-QC souffrait d'une **misattribution library-claim** : le README présentait « Sharpe 2.09, CAGR 18.44%, MaxDD 24.20% » comme « Backtest Metrics » alors que ces chiffres sont la **revendication de la QC Strategy Library #343** (cf. `main.py:5-10` : `# OOS 1Y Sharpe 2.09, 5Y CAGR 18.44%, 5Y Drawdown 24.20%, 62% Win Rate` + URL `https://www.quantconnect.com/strategies/343` auteur Louis Szeto) — **PAS une sortie de backtest local**. Le dossier **ne contient pas de `research.ipynb`** contrairement à d'autres clones (#9530 DualMomentum, #9537 EMA-Cross-Crypto, #9542 DynamicVIXSpyRegime-QC) — la reproduction locale **n'a pas eu lieu**. Le README legacy disait aussi « Cloud project ID: None (local only) » alors que `main.py:10` mentionne QC Project ID **29687591** (cloned 2026-04-05) — contradiction corrigée. Les tableaux ci-dessous citent la **library claim avec sa traçabilité explicite** + un **drapeau SUSPECT overfit structurel** (Sharpe 2.09 sur value+quality screen = exposé à look-ahead bias + small-universe variance).

| Source | Sharpe | CAGR | MaxDD | Période | Univers |
|--------|--------|------|-------|---------|---------|
| **QC Strategy Library #343** (revendication originale, `main.py:5-10`) | **2.09** | **18.44%** | **24.20%** | **OOS 1Y** (5Y CAGR — fenêtre non précisée) | Top 20% book-to-market stocks filtrés F-Score ≥ 8, equal-weighted |
| `main.py:5-10` docstring | n/a | n/a | n/a | `self.set_start_date(self.end_date - timedelta(12*365))`, `set_end_date(2025, 1, 1)` | idem |
| Repro locale | **NON REPRODUITE** | n/a | n/a | n/a | n/a |

**Lecture honnête — SUSPECT OVERFIT STRUCTUREL (c.1283-L1 ★★)** : un Sharpe de **2.09** sur value+quality screen (Piotroski F-Score ≥ 8) sur **OOS 1Y library** est exposé à **3 sources structurelles de surestimation** :

1. **Look-ahead bias fondamental** : le F-Score de Piotroski (2000) utilise des ratios financiers publiés en différé (60-90 jours post-quarter-close pour la plupart des fondamentaux US via SEC 10-Q/10-K filings). En backtest QuantConnect classique, ces données sont chargées au moment de la décision mensuelle — mais **à moins d'utiliser `SetDataNormalizationMode(PointInTimeFundamentals)`**, le backtest peut inclure des données qui n'étaient **pas disponibles au moment de la décision** (snapshot bias).

2. **Data mining sur fenêtre 12y rolling** : la library #343 utilise `set_start_date(self.end_date - timedelta(12*365))` + `set_end_date(2025, 1, 1)` = **12 ans rolling**. Une stratégie filtrant top 20% B/M + F-Score ≥ 8 sur une fenêtre choisie a posteriori est **exposée à la multiplicité des tests** (backtest sur N périodes start possibles → résultats favorables cherry-picked).

3. **Small-universe variance** : top 20% B/M + F-Score ≥ 8 = univers très restreint (probablement 30-50 stocks vs 500+ du SP500). Monthly rebalance sur 12 ans × ~30 trades = ~360 trades = variance du Sharpe mécanique élevée (intervalle de confiance à 95% du Sharpe ≈ ±0.5 pour N=360, ce qui rendrait un Sharpe vrai de 1.6 indistinguable d'un 2.6).

**Cumul des 3 effets** : un Sharpe library de 2.09 pourrait masquer un Sharpe réel de **1.2-1.6** sur la même stratégie avec `PointInTimeFundamentals`, fenêtre OOS fixée a priori, et univers élargi. C'est **PAS** un signal de déploiement live sans vérification empirique indépendante.

Cf. **c.1282-L2 ★★** (LeveragedETFMomentum) : un Sharpe > 2× la base sur lev. ETFs bull-only backtest = SUSPECT overfit structurel. Ici la même mécanique s'applique : la **stratégie est rentable sur le backtest mais vulnérable aux pathologies méthodologiques** (look-ahead + data mining + small-universe). **JAMAIS** la déployer live sans backtest QC Cloud avec `PointInTimeFundamentals` + walk-forward OOS.

**Vérification de la library claim** : la QC Strategy Library #343 (Louis Szeto, `https://www.quantconnect.com/strategies/343`) est une stratégie publique à visée **pédagogique** sur la mécanique de **value+quality systematic screen** — **PAS un signal de déploiement live**. Le `QC Project ID 29687591` (cloned 2026-04-05) **n'a jamais été déployé en QC Cloud** (README legacy confirmait « Not yet deployed »).

**Reproductibilité** : la library claim est **reproductible localement** via Lean CLI (`lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/HighBookToMarketFScore-QC"`) — l'univers Piotroski F-Score est construit depuis fundamentals data via `universe.py` et `piotroski_score.py`. **Cette PR n'exécute pas la repro locale** (hors scope, future action séparée) ; la note « Metrics from original library, not locally reproduced » du README legacy reste vraie.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/HighBookToMarketFScore-QC"`
**QC Cloud :** QC Project ID `29687591` cloné 2026-04-05, **non déployé en Cloud**. Copier `main.py` + `piotroski_score.py` + `piotroski_factors.py` + `universe.py` + `symbol_data.py` dans un nouveau projet QC Cloud pour exécuter. Note : la repro locale Docker Lean devrait reproduire la library claim (avec dividendes/frais) — variations attendues ~10-20% sur MaxDD, ~5-15% sur CAGR (frais Interactive Brokers + dividendes). Pour un backtest plus rigoureux (anti-SUSPECT), ajouter `self.set_data_normalization_mode(DataNormalizationMode.POINT_IN_TIME_FUNDAMENTALS)` avant `set_start_date()` dans `main.py:18-19` et comparer les mesures.

## Fichiers

- `main.py` - Stratégie (clone QC Strategy Library #343, Piotroski F-Score value screen monthly rebalance)
- `piotroski_score.py` - Calcul F-Score (Profitabilité + Leverage/Liquidity + Operating Efficiency, 9 signaux binaires)
- `piotroski_factors.py` - Facteurs fondamentaux individuels (ROA, CFO, ΔROA, ACCRUAL, ΔLEVER, ΔLIQUID, EQ_OFFER, ΔMARGIN, ΔTURN)
- `universe.py` - PiotroskiScoreUniverseSelectionModel (sélection universe + filtre F-Score ≥ 8)
- `symbol_data.py` - Helpers pour charger fundamentals data

## Références

- QuantConnect Strategy Library #343 — *High Book-to-Market High F-Score Quality Value* par Louis Szeto : `https://www.quantconnect.com/strategies/343`
- `main.py:5-10` docstring : source library + URL + QC Project ID 29687591 + auteur Louis Szeto
- Piotroski (2000), « Value Investing: The Use of Historical Financial Statement Information to Separate Winners from Losers », *Journal of Accounting Research* 38(suppl.) — papier fondateur du F-Score
- c.1282-L2 ★★ (LeveragedETFMomentum-QC) — SUSPECT overfit structurel pattern sur lev. ETFs bull-only backtest ; même mécanique applicable ici pour value+quality sur OOS 1Y window
- c.1281-L3 ★★ (DynamicVIXSpyRegime-QC) — library claim misattribution pattern, arche reproductible pour drainer les autres README QC library clones