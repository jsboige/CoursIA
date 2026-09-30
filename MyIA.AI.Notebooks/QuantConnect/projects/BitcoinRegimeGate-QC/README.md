# BitcoinRegimeGate-QC — porte de régime BTC pour QQQ/SHY

Distillation de l'article QC Research **« Bitcoin Regime Signal for Growth Equities »** (Derek Melchin, publié août 2026) — [source](https://www.quantconnect.com/research/21195/bitcoin-regime-signal-for-growth-equities/). Porté dans le dépôt pour l'issue #18576 (re-évaluation de la lecture #12748 : les raisons « non publié » et « pas de sources primaires » du verdict IGNORE d'août sont tombées sur la version publiée).

## Idée

Lire le régime de risque sur le **BTC, un marché 24/7** (« no halts, circuit breakers, or closing bell » — l'auteur), pour allouer entre **QQQ** (risque on) et **SHY** (risque off) — la face **crypto → equity** du spillover documenté par Iyer 2022 (IMF GFSN 2022/001) : le BTC explique 14-18 % de la variation de volatilité equity, ~17 % pour le S&P 500.

**Règle** (fidèle à l'article) :

> QQQ si (BTC > SMA50 BTC) **ET** (ROC20 BTC > 0), sinon SHY.
> Réévaluation hebdomadaire : premier jour de trading à 8 h ET, avant l'open US.

C'est le même geste que `DynamicVIXSpyRegime-QC` (gate de régime → equity/obligataire), avec une **source différente** (BTC Bitfinex 24/7 au lieu du VIX) et un sous-jacent growth (QQQ). La cohorte BTC tranche 11 du dépôt avait mesuré **0 edge crypto → crypto** ; ce distillat teste la face crypto → equity, non couverte.

## Sources primaires (article publié)

- Faber 2007 (SSRN 962461) — timing tactique par moyenne mobile.
- Liu & Tsyvinski 2021 (RFS 34(6)) — risques crypto systématiques.
- Iyer 2022 (IMF GFSN 2022/001) — spillovers BTC → vol equity.

## Claims de l'article confrontés — mesures du dépôt (QC Cloud, 2026-09-30)

| Claim auteur (2014-2026) | Valeur |
|---|---|
| Sharpe stratégie | 0.838 (vs QQQ 0.682, SPY 0.564) |
| Grille 30-70 j × 10-30 j | 25/25 > SPY, 23/25 > QQQ, médiane 0.812 |

**Mesuré (projet QC 37168922, même compile pour les 4 runs, benchmark QQQ buy-and-hold apparié) :**

| Run | Période | Sharpe | CAGR | MaxDD | PSR |
|---|---|---|---|---|---|
| **Gate IS** | 2016-01 → 2021-12 | **1.133** | 18.51 % | **14.40 %** | 56.4 % |
| QQQ-hold IS (benchmark) | 2016-01 → 2021-12 | 0.961 | 24.74 % | 28.20 % | 36.0 % |
| **Gate OOS** | 2022-01 → 2026-06 | **0.640** | 14.87 % | **15.20 %** | 14.3 % |
| QQQ-hold OOS (benchmark) | 2022-01 → 2026-06 | 0.426 | 15.25 % | 34.70 % | 5.9 % |

**Lecture** : le gate domine le buy-and-hold QQQ en risque-adjusté sur les **deux** fenêtres (Sharpe OOS +50 %, MaxDD OOS divisé par 2.3 — 15.2 % contre 34.7 %, en couvrant le bear 2022) pour un CAGR égal. Réserves honnêtes : PSR OOS 14.3 % (l'edge vs cash n'est pas statistiquement établi sur la seule fenêtre OOS), et la cohorte BTC tranche 11 du dépôt avait mesuré 0 edge **crypto → crypto** — l'edge ici vit sur la face **crypto → equity**. Statut : `Alive — risk-adjusted` (entrée `docs/qc/qc-strategies-status.md`).

## Structure

- `main.py` — algorithme LEAN (~60 lignes, sans ML : le gate de l'article est un pur filtre de régime).
- Pas de notebook de recherche : contrairement à `DynamicVIXSpyRegime-QC` (overlay RandomForest), il n'y a rien à entraîner — le distillat est le filtre lui-même.
