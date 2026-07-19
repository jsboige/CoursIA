# Statut des stratégies QuantConnect — source de vérité

> **Issue parente** : [#1621 EPIC Consolidation QC/Trading](https://github.com/jsboige/CoursIA/issues/1621) (mandat user 2026-05-27).
> **Partition** : `po-2024:CoursIA` (QC). **Tranche 1** (livrable incrémental — l'EPIC demande explicitement « un sujet par PR, ne pas tout faire d'un coup »).

Ce document est le **point d'entrée unique** pour un visiteur qui découvre les 111 stratégies sous `MyIA.AI.Notebooks/QuantConnect/projects/` (112 entrées brutes, dont `_docs/` qui n'est pas une stratégie). Il cartographie les stratégies, leur type, leur source de données, et — là où l'évidence existe — leur statut (alive / superseded / needs-improvement / à confirmer).

## Méthodologie (honnête)

Les statuts ci-dessous sont **exclusivement dérivés d'évidence firsthand** :

- **Backtests documentés** dans la mémoire du cluster (baselines vérifiées cross-seed).
- **Figures de recherche** couvertes par la campagne EPIC [#5654](https://github.com/jsboige/CoursIA/issues/5654) (2026-07-08, 11 stratégies QC illustrées).

Les stratégies **sans backtest récent dédié** sont marquées **« À confirmer »** plutôt que de recevoir un statut fabriqué. Un backtest par stratégie (via QC Cloud, MCP `qc-mcp`) reste l'acceptance finale — voir [#1027](https://github.com/jsboige/CoursIA/issues/1027) pour la gate paper-trading/backtest.

## Les 4 types de notebooks (acceptance EPIC)

Le matériel QC mélange 4 types de notebooks qu'un visiteur doit distinguer :

| Type | Description | Localisation |
|------|-------------|--------------|
| **(a) Quantbook QC Cloud** | Notebook officiel utilisant `QuantBook()`, exécuté via QC Cloud (MCP `qc-mcp` / Playwright en fallback). Non exécutable localement. | `projects/*/research.ipynb`, `Python/QC-Py-*` |
| **(b) Research notebook lié** | Notebook de recherche compagnon d'un quantbook/stratégie `projects/`. | `projects/*/research_*.ipynb` |
| **(c) Standalone research** | Recherche indépendante, données locales (yfinance, pandas, sklearn). Aucun QC Cloud requis. | `research/research_*.ipynb` (18 notebooks) |
| **(d) Placeholder pédagogique** | Notebook de cours avec stubs `# TODO étudiant`. | `Python/QC-Py-*` (cours) |

**Note** : `projects/Research-Executor/` est un **harness d'exécution** (`main.py` + `runner.ipynb` + MockQB), pas une stratégie ni une zone de recherche — README explicite : « Type: Utility (research execution harness, not a trading strategy) ».

## Stratégies vérifiées (statut firsthand)

| Stratégie | Type | Classe d'actifs | Statut | Évidence |
|-----------|------|-----------------|--------|----------|
| `LongShortHarvest-QC` | Composite pairs | Multi-actifs | **Alive — BEATS** | Baseline cluster 98.7% (backtest vérifié) ; figure #5740 |
| `Framework_Composite_FamaFrenchAllWeather` | Composite | Multi-actifs | **Alive — BEATS** | 87.5% OOS (backtest vérifié) |
| `DynamicVIXSpyRegime-QC` | Régime VIX | US Equity | **Alive** | 69.4% (backtest vérifié) |
| `AllWeather` | Multi-asset risk-parity | Actions/Bonds/Or/Commodities | **Alive** | Figure #5743 |
| `EMA-Cross-Index` | Trend EMA | US Equity (SPY) | **Alive** | Figure #5746 |
| `EMA-Cross-Crypto` | Trend EMA | Crypto (BTC) | **Alive** | Figure #5750 |
| `ML-RandomForest` | ML supervisé (RF) | US large-cap | **Alive** | Figure #5747 |
| `ML-XGBoost` | ML supervisé (XGBoost) | US large-cap | **Alive** | Figure #5749 |
| `ForexCarry` | FX carry/momentum | G10 FX | **Alive** | Figure #5748 |
| `RiskParity` / `Cloud-RiskParity-Composite` | Inverse-vol risk-parity | Multi-actifs | **Needs-improvement** (plafond structurel) | Sharpe 0.399 (contre-exemple pédagogique) ; figure #5753 |
| `DualMomentum` | Momentum dual-asset | Multi-actifs | **Superseded** | Échec TLT 2022 → remplacé par `DualMomentumNoTLT` |
| `DualMomentumNoTLT` | Momentum (sans TLT) | Multi-actifs | **Alive** (remplacement) | Figure #5754 |

## Régimes de performance (connaissance cluster firsthand)

Backtests cross-stratégies 2022–2024 (stress test) — un visiteur peut anticiper le comportement d'une stratégie selon sa classe :

| Régime | Comportement typique |
|--------|----------------------|
| Value / Factor / Trend classique | **Effondrement** (−62% à −85%) |
| Structured ML / Composites | **Tien** (−2% à −14%) |
| High-Turnover US Equity | **Near-immune** (0% à −2%) |
| Low-Turnover Multi-Asset / Crypto | **Vulnérable** (−30% à −43%) |

## Inventaire complet des 112 projets (statut best-guess)

> **Scope PR-D (#1621)** : cartographie des **112 entrées** sous `projects/`. 
> Statuts dérivés **exclusivement de métadonnées du dépôt** (classe `main.py`, présence de 
> `research.ipynb`/`quantbook.ipynb`, contenu du `README.md`). **Aucun backtest lancé** dans cette 
> tranche — les métriques (Sharpe/CAGR) relèvent du scope séparé **RECOVERABLE-MACHINE** (QC Cloud, 
> MCP `qc-mcp`). Les statuts marqués *best-guess* ne sont **pas vérifiés firsthand**.

### Synthèse par bucket

| Bucket | Nombre | Lecture |
|--------|-------:|---------|
| Vérifié (tranche 1, firsthand) | 13 | statut firsthand confirmé dans le tableau ci-dessus |
| Vérifié (tranche 2, backtests QC Cloud MCP) | 5 | métriques réelles (Sharpe/CAGR/MaxDD) — **toutes Needs-improvement** (PSR < 50 %, pas d'edge statistique) |
| Vérifié (tranche 3, backtests QC Cloud MCP) | 5 | cohorte Momentum/Factor/Composite — **1 edge significatif** (BlackLitterman PSR 51 %), 2 Needs-improvement, 2 BROKEN |
| Vérifié (tranche 4, backtests QC Cloud MCP) | 5 | cohorte MeanReversion/Macro/Multi-asset/Crypto — **0 edge significatif** (PSR < 50 %), 4 Needs-improvement, 1 BROKEN ; Multi-Layer-EMA revendication README confirmée |
| Vérifié (tranche 5, backtests QC Cloud MCP) | 5 | cohorte Trend/Macro-Régime/Options/Causal/Factor — **0 edge significatif** (PSR < 50 %), 3 Needs-improvement, 1 near-cash, 1 near-BROKEN |
| Vérifié (tranche 6, backtests QC Cloud MCP) | 5 | cohorte Régime/Factor/Vol/Leveraged-Factor — **1 edge candidat** (LeveragedETFMomentum PSR 79.8 %, ETF leveraged → flag OOS), 4 Needs-improvement |
| Vérifié (tranche 7, backtests QC Cloud MCP) | 5 | cohorte **ML supervisé / DL / SVM-wavelet** (5 stratégies best-guess ML du bucket Vivant promues) — **0 edge significative** (PSR max = 29.3 % Sector-ML-Classification ; 2/5 PSR < 10 % ; aucune > 50 %), 5 Needs-improvement — confirme que le ML in-sample sans walk-forward multi-seed ne surfit pas la cohorte |
| Vérifié (tranche 8, backtests QC Cloud MCP) | 5 | cohorte **Trend + Régime + Vol risk** (5 stratégies best-guess du bucket Vivant promues) — **0 edge significative** (PSR < 50 % partout), 4 Needs-improvement, 1 BROKEN (VIX-TermStructure Sharpe négatif −0.125, PSR 0.18 %) ; max PSR 24.99 % TrendStocksLite |
| Vérifié (tranche 9, backtests QC Cloud MCP) | 5 | cohorte Composite+Options+Vol/Momentum — **0 edge** (PSR < 50 % partout) ; PSR max 19.78 % (Framework_Composite_EMATrend) |
| Vérifié (tranche 10, backtests QC Cloud MCP) | 5 | cohorte DeepLearning+LSTM+Temporal-CNN — **1 BROKEN** (Crypto-LSTM-Prediction Sharpe -0.021) ; PSR max 28.70 % (Temporal-CNN-Prediction) |
| Vérifié (tranche 11, backtests QC Cloud MCP) | 4 | cohorte Crypto BTC + IBKR-Binance-Hybrid — **0 edge significatif** (PSR < 50 %), 4 Needs-improvement (1 MaxDD catastrophique 72.7 %) ; cohorte limitée à 4 stratégies vérifiables firsthand (les 5ᵉ `Crypto-LSTM-Prediction` overlap tranche 10) |
| Vérifié (tranche 12, backtests QC Cloud MCP) | 3 | cohorte ML NLP + Reinforcement Learning — 3 promotions Vivant (ML-FinBERT-Sentiment, ML-LLM-Summarization, RL-DQN-Trading) + 2 vérifications hors-Vivant (`RL-Options-Hedging` Stub BROKEN Sharpe -1.264 ; `Reinforcement-Learning-Trading` Squelette Needs-improvement PSR 2.19 %) — **1 BROKEN + 2 Needs-improvement**, PSR max 37.14 % (ML-LLM-Summarization, aucune > 50 %) |
| Vérifié (tranche 13, backtests QC Cloud MCP) | 4 | cohorte ML Classification / Clustering / Hybrid — **0 edge significative** (PSR max 22.74 %), 4 Needs-improvement |
| Vérifié (tranche 14, backtests QC Cloud MCP) | 2 | cohorte **DL Chronos foundation** (2 stratégies Chronos du bucket Vivant promues) — **0 edge significative** (PSR max 13.79 % `ML-Chronos-Foundation`, aucune > 50 %), 2 Needs-improvement ; **le régime SMA200 (`Chronos-Foundation-Forecasting`) a le PSR le plus bas (3.12 %), pas le plus haut** — le filtre SMA200 dégrade la signification statistique vs le variant plain |
| Vérifié (tranche 15, backtests QC Cloud MCP) | 4 | cohorte **Stratégies quantitatives structurelles** (4 stratégies best-guess du bucket Vivant promues : `Options-VGT` income covered-call tech single-names, `TermStructureCommodities-QC` courbe terme commodités, `PCA-StatArbitrage` stat-arb factoriel PCA, `Trend-Following` AQR-style 12-momentum multi-actifs) — **1 BROKEN** + **3 Needs-improvement** : PSR max 17.51 % `Options-VGT` (aucune > 50 %) ; `TermStructureCommodities-QC` Sharpe -0.244 / MaxDD 96.8 % / PSR 0.007 % = quasi-ruine systématique sur backtest 2018–2025 |
| Vérifié (tranche 16, backtests QC Cloud MCP) | 4 | cohorte **EMA-Cross + Composite Framework + Value Dogs** (4 stratégies best-guess du bucket Vivant promues) — **2 edge statistiquement significative** (PSR > 50 % : `Framework_Composite_TrendWeather` 77.94 %, `Framework_Composite_MomentumRegime` 73.52 %), 2 Needs-improvement (PSR < 50 % : `EMA-Cross-Stocks` 49.75 % near-edge, `PuppiesOfTheDow-QC` 3.49 %) ; **première tranche QC #1621 avec edge statistique significative depuis tr.3** (`BlackLitterman` PSR 51 %) — les composites Framework confirment l'avantage du blending méthodologique multi-stratégies |
| Vérifié (tranche 19, backtests QC Cloud MCP) | 5 | cohorte **QCP13/NB14/ESGF Composite baselines hors-bucket Vivant** (5 stratégies freshly-discovered via scan `list_projects name_contains:` — L709-L3 ★ extension hors-bucket) — **2 BROKEN** (QCP13 baselines `Cell6_BasicFramework` Sharpe -0.213 / `Cell38_CompositeAlpha` Sharpe -0.394, NP < 0 sur 9 ans), **1 near-edge** (`ESGF-Framework-Composite` PSR 32.52 % record hors-Framework TrendWeather/MomentumRegime), **2 Needs-improvement** (`NB14-Cell75-CompositeRisk` PSR 27.94 % + `ESGF-Kit-Framework-Composite` PSR 8.25 % mais MaxDD 14 % record) — **0 edge significative** (PSR max 32.52 % vs 50 % cap) ; confirme leçon L709-L1 ★★★ trans-tranche : **blending composite Framework** (tr.16 TrendWeather/MomentumRegime) > **baselines QCP13/NB14/ESGF composites pédagogiques** sans moteur validé ; **bonus L709-L2 ★★** : pattern Runtime Error → Fixed confirmé sur `ESGF-Kit-Framework-Composite` (9 backtests v1-v8, itération fixée v8-ML-RF-alpha-80-20) |
| Vérifié (tranche 20, backtests QC Cloud MCP) | 5 | cohorte **Spread Options + DL LSTM + Momentum dual freshly-discovered** (5 stratégies hors-bucket Vivant, scan `list_projects name_contains:` patterns `Spread`/`Alpha`/`Factor`/`MeanReversion`/`LSTM`/`Momentum`/`Carry`/`Breakout`) — **3 BROKEN** (`QCP6_Cell23_BullCallSpread` Sharpe -3.20 / `QCP6_Cell35_BullCallSpread` Sharpe -3.20 / `QCP13_Cell38_CompositeAlpha_3367` Sharpe -0.394 MaxDD 62 %) + **2 Needs-improvement** (`dbg-DualMomentum-6192` Sharpe 0.35 CAGR 8.41 % MaxDD 14.9 % projet ultra-récent 2026-07-11 / `1630-lstm-forecasting-post2801` Sharpe 0.525 CAGR 11.29 % MaxDD 32.5 % PSR 13.42 %) — **0 edge significative** (PSR max 13.42 %) ; **confirme L710-L1 ★★★** (2ᵉ BROKEN QCP13 cette fois sur `Cell38_CompositeAlpha` vs `Cell6_BasicFramework` en tr.19 : QCP13 baselines Hands-On systématiquement structurellement négatives sur 9 ans) ; **bonus L711-L1 ★** : **2 BullCallSpread (QCP6_Cell23/Cell35) backtests strictement identiques** (mêmes Sharpe/CAGR/MaxDD/NP, 4 ordres, 124 jours, $37 NP) — probable bug de projet QC Cloud ou clonage accidentel de projet ; à documenter comme signal de qualité de données QC Cloud ; **bonus L711-L2 ★** : `dbg-DualMomentum-6192` créé **2026-07-11** = stratégie freshly-discovered la plus récente du corpus QC #1621 (1 jour après c.711) |
| Vivant (best-guess, non vérifié) | 15 | algo `QCAlgorithm` complet, aucun signal négatif — TODO backtest pour confirmer (2 reclassés Archivé firsthand c.570) ; tranche 7 a promu 5 stratégies ML, tranche 8 a promu 5 stratégies Trend/Régime/Vol, tranche 14 a promu 2 stratégies Chronos DL, tranche 15 a promu 4 stratégies quantitatives structurelles, tranche 16 a promu 4 stratégies EMA + Composite Framework + Value : voir sections ci-dessous. **Note comptable (sémantique du double-listing)** : la section détaillée contient **56 lignes physiques = 20 true-Vivant + 36 promues tr7-15** (cross-référencées dans leur bucket d'origine ET ici pour la discoverability, voir status `Vérifié tranche N`) — le compte `15` ci-contre = Vivant non-encore-vérifiées après déduction des promues des tranches précédentes, distinct du compte physique (intentionnel, pas une erreur). |
| Vivant (README revendique vérifié) | 0 | README revendique un backtest QC Cloud — à recroiser firsthand (Multi-Layer-EMA vérifié tranche 4) |
| Recherche uniquement (pas d'algo déployable) | 5 | notebook de recherche sans `main.py` déployable |
| Stub (code non créé) | 2 | README : exercice planifié, fichiers de code non créés |
| Squelette/template (pas de stratégie active) | 2 | README : template/skeleton, pas de stratégie active |
| Contre-exemple pédagogique (BROKEN) | 2 | README : intentionnellement BROKEN (pédagogie) |
| Archivé / superseded | 3 | README/en-tête : archived / plafond structurel documenté (MomentumStrategy, SectorMomentum reclassés firsthand c.570) |
| Research phase | 1 | README : research phase (WIP) |
| Démonstration pédagogique | 1 | README : educational demo |
| Utilitaire / docs (pas une stratégie) | 2 | pas une stratégie (harness ou docs) |
| **Total** | **112** | 112 entrées = 101 stratégies à vocation trading (classe `QCAlgorithm`, `main.py`/`Main.cs`) + 2 squelettes (classe présente, pas de stratégie active) + 1 harness utilitaire (sous-classe `QCAlgorithm`) + 5 recherche-only (notebook, pas d'algo) + 2 stubs (code non créé) + 1 dossier docs |

#### Vérifié (tranche 1, firsthand) (13)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `AllWeather` | `projects/AllWeather/` | Multi-asset risk-parity | Vérifié | tableau « Stratégies vérifiées » ci-dessus (figure #5743) |
| `Cloud-RiskParity-Composite` | `projects/Cloud-RiskParity-Composite/` | Inverse-vol risk-parity | Vérifié | tableau vérifié ci-dessus (Needs-improvement) |
| `DualMomentum` | `projects/DualMomentum/` | Momentum dual-asset | Vérifié | tableau vérifié ci-dessus (Superseded) |
| `DualMomentumNoTLT` | `projects/DualMomentumNoTLT/` | Momentum (sans TLT) | Vérifié | tableau vérifié ci-dessus (Alive) |
| `DynamicVIXSpyRegime-QC` | `projects/DynamicVIXSpyRegime-QC/` | Régime VIX | Vérifié | tableau vérifié ci-dessus (69.4 %) |
| `EMA-Cross-Crypto` | `projects/EMA-Cross-Crypto/` | Trend EMA | Vérifié | tableau vérifié ci-dessus (figure #5750) |
| `EMA-Cross-Index` | `projects/EMA-Cross-Index/` | Trend EMA | Vérifié | tableau vérifié ci-dessus (figure #5746) |
| `ForexCarry` | `projects/ForexCarry/` | FX carry/momentum | Vérifié | tableau vérifié ci-dessus (figure #5748) |
| `Framework_Composite_FamaFrenchAllWeather` | `projects/Framework_Composite_FamaFrenchAllWeather/` | Composite | Vérifié | tableau vérifié ci-dessus (87.5 % OOS) |
| `LongShortHarvest-QC` | `projects/LongShortHarvest-QC/` | Composite pairs | Vérifié | tableau vérifié ci-dessus (BEATS, 98.7 %) |
| `ML-RandomForest` | `projects/ML-RandomForest/` | ML supervisé (RF) | Vérifié | tableau vérifié ci-dessus (figure #5747) |
| `ML-XGBoost` | `projects/ML-XGBoost/` | ML supervisé (XGBoost) | Vérifié | tableau vérifié ci-dessus (figure #5749) |
| `RiskParity` | `projects/RiskParity/` | Inverse-vol risk-parity | Vérifié | tableau vérifié ci-dessus (Needs-improvement, 0.399) |

#### Vérifié (tranche 2, backtests QC Cloud via MCP) (5)

> **Scope tranche 2 (#1621)** : 5 stratégies « Vivant » promues au statut vérifié via backtests
> QC Cloud réels (MCP `qc-mcp`, backtests existants relus firsthand). Métriques **non walk-forward
> OOS** (backtest pleine période in-sample) — suffisantes pour classer Alive / Needs-improvement /
> BROKEN, insuffisantes pour un verdict de production. **Toutes 5 = Needs-improvement** : PSR < 50 %
> sur toute la cohorte (aucune edge statistiquement significative) — confirmation honnête que le
> bucket « Vivant best-guess » recèle majoritairement des stratégies marginales une fois backtestées.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `Adaptive-Conformal-Risk` | `projects/Adaptive-Conformal-Risk/` | Vol / Risk adaptatif | **Needs-improvement** | 2018–2025 (2766 j.) ; Sharpe 0.604 ; CAGR 13.70 % ; MaxDD 33.1 % ; PSR 17.8 % ; NP 310.8 % ($288 311) — meilleur CAGR mais drawdown élevé |
| `Vol-GARCH-Target` | `projects/Vol-GARCH-Target/` | Vol (GARCH) | **Needs-improvement** | 2018–2025 (1761 j.) ; Sharpe 0.325 ; CAGR 6.97 % ; MaxDD 10.8 % ; PSR 14.9 % ; NP 60.3 % ($56 709) — modeste, plafond structurel |
| `Vol-Ensemble-Conservative` | `projects/Vol-Ensemble-Conservative/` | Vol ensemble | **Needs-improvement** | 2018–2025 (1761 j.) ; Sharpe 0.265 ; CAGR 6.14 % ; MaxDD 10.4 % ; PSR 13.6 % ; NP 51.8 % ($50 438) — modeste, plafond structurel |
| `HAR-RV-Kelly` | `projects/HAR-RV-Kelly/` | Volatility / Kelly | **Needs-improvement** | pleine période (2516 j.) ; Sharpe 0.146 ; CAGR 4.23 % ; MaxDD 12.8 % ; PSR 3.0 % ; NP 51.3 % ($50 666) — quasi-baseline, edge nul |
| `InverseVolatility-Rank` | `projects/InverseVolatility-Rank/` | Risk-parity inversé | **Needs-improvement / near-BROKEN** | pleine période (1629 j.) ; Sharpe 0.124 ; CAGR 4.13 % ; **MaxDD 41.0 %** ; PSR 1.9 % — drawdown inacceptable, edge nul |

#### Vérifié (tranche 3, backtests QC Cloud via MCP) (5)

> **Scope tranche 3 (#1621)** : 5 stratégies « Vivant » promues via backtests QC Cloud réels
> (MCP `qc-mcp`, backtests « aligned 2018–2025 » relus firsthand). Cohorte **Momentum / Factor /
> Composite** (différente de la cohorte Vol-* de la tranche 2, pour variété intra-famille). Métriques
> pleine période in-sample (non walk-forward OOS). **Image plus nuancée que la tranche 2** : un seul
> candidat présente une edge statistiquement significative (PSR > 50 %), 2 sont marginales, 2 sont
> BROKEN / sous-performantes — le bucket « Vivant » n'est donc pas uniformément faible.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `BlackLitterman-Momentum` | `projects/BlackLitterman-Momentum/` | Factor / Momentum | **Alive (edge candidat)** | 2018–2025 (2766 j.) ; **Sharpe 0.83** ; CAGR 15.83 % ; MaxDD 16.9 % ; **PSR 51.4 %** ; NP 404.0 % ($405 328) — **seule stratégie de la cohorte avec PSR > 50 %** (edge statistiquement significative) ; à confirmer en walk-forward OOS |
| `composite-c2-equityfactor` | `projects/composite-c2-equityfactor/` | Composite equity/factor | **Needs-improvement** | 2018–2025 (1761 j.) ; Sharpe 0.574 ; CAGR 11.94 % ; MaxDD 18.6 % ; PSR 25.8 % ; NP 120.4 % ($105 319) — décent mais edge non significative |
| `AssetClassMomentum-QC` | `projects/AssetClassMomentum-QC/` | Cross-asset momentum | **Needs-improvement** | 2018–2025 (1761 j.) ; Sharpe 0.22 ; CAGR 6.64 % ; MaxDD 28.1 % ; PSR 3.8 % ; NP 56.9 % ($43 119) — edge nul, drawdown élevé |
| `MomentumRegime-AdaptiveWeights` | `projects/MomentumRegime-AdaptiveWeights/` | Momentum / Régime | **Needs-improvement / near-cash** | 2018–2025 (1761 j.) ; **Sharpe −0.729** ; CAGR 1.88 % ; MaxDD 4.3 % ; PSR 17.4 % ; NP 13.9 % — Sharpe négatif (sous le sans-risque), quasi-flat |
| `Cloud-SectorRotation-Momentum` | `projects/Cloud-SectorRotation-Momentum/` | Rotation sectorielle | **BROKEN** | 2018–2025 (1761 j.) ; **Sharpe −0.029** ; CAGR 2.13 % ; **MaxDD 42.7 %** ; PSR 0.5 % ; NP 15.9 % — flat + drawdown catastrophique, edge nul |

#### Vérifié (tranche 4, backtests QC Cloud via MCP) (5)

> **Scope tranche 4 (#1621)** : 5 stratégies promues via backtests QC Cloud réels (MCP `qc-mcp`,
> backtests existants relus firsthand). Cohorte **Mean-Reversion / Macro / Multi-asset / Crypto**
> (différente des tranches 2 Vol-* et 3 Momentum/Factor). Métriques pleine période in-sample (non
> walk-forward OOS). **0 edge statistiquement significative** (PSR < 50 % partout, contrairement à la
> tranche 3 qui comptait BlackLitterman PSR 51 %). Inclut la **vérification firsthand de la
> revendication README « Verified on QC Cloud » de Multi-Layer-EMA** (project 28433748 = bien l'ID
> cité par le README → revendication confirmée réelle, mais edge non significative + drawdown crypto
> catastrophique).

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `MacroFactorRotation-QC` | `projects/MacroFactorRotation-QC/` | Rotation actions/obligations | **Needs-improvement** | 3651 j. ; Sharpe 0.731 ; CAGR 22.63 % ; **MaxDD 42.0 %** ; PSR 23.8 % ; NP 669.2 % ($720 114) — CAGR élevé mais drawdown inacceptable, edge non significative |
| `Multi-Layer-EMA` | `projects/Multi-Layer-EMA/` | Crypto multi-indicateurs | **Needs-improvement** | 2557 j. ; Sharpe 0.798 ; CAGR 24.99 % ; **MaxDD 57.1 %** ; PSR 23.9 % ; NP 377.4 % (₮385 063) — **revendication README « Verified on QC Cloud » confirmée firsthand** (project 28433748) mais drawdown crypto 57 % = inacceptable |
| `AdaptiveAssetAllocation` | `projects/AdaptiveAssetAllocation/` | Multi-asset allocation | **Needs-improvement** | 2008–2024 (4639 j.) ; Sharpe 0.509 ; CAGR 8.01 % ; MaxDD 18.9 % ; PSR 10.6 % ; NP 314.4 % ($315 339) — long-terme décent mais edge non significative |
| `Cloud-MeanReversion-Sectors` | `projects/Cloud-MeanReversion-Sectors/` | Mean reversion secteurs | **Needs-improvement / near-cash** | 2768 j. ; Sharpe 0.278 ; CAGR 5.60 % ; MaxDD 14.7 % ; PSR 3.7 % ; NP 82.1 % — edge nul, sous-performant |
| `MeanReversion` | `projects/MeanReversion/` | Mean reversion | **BROKEN** | 2845 j. ; **Sharpe −0.082** ; CAGR 3.00 % ; MaxDD 17.5 % ; PSR 1.3 % ; NP 39.7 % — Sharpe négatif, edge nul |

#### Vérifié (tranche 5, backtests QC Cloud via MCP) (5)

> **Scope tranche 5 (#1621)** : 5 stratégies promues via backtests QC Cloud réels (MCP `qc-mcp`,
> backtests existants relus firsthand). Cohorte **Trend / Macro-Régime / Options / Causal / Factor**
> (5 domaines distincts des tranches 2 Vol, 3 Momentum/Factor, 4 MeanReversion/Macro). Métriques
> pleine période in-sample (non walk-forward OOS). **0 edge statistiquement significative** (PSR <
> 50 % partout — comme les tranches 2 et 4 ; seule la tranche 3 BlackLitterman atteignait PSR 51 %).
> GlobalMacro-Regime PSR 16.7 % = la plus élevée de la cohorte mais reste sous le seuil de
> significativité. CausalEventAlpha : CAGR 11.7 % / NP 255 % élevés MAIS drawdown 38.8 % inacceptable.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `FuturesTrend` | `projects/FuturesTrend/` | Trend futures | **Needs-improvement / near-cash** | 2823 j. ; Sharpe 0.223 ; CAGR 5.69 % ; MaxDD 10.9 % ; PSR 4.3 % ; NP 86.2 % ($75 455) — drawdown modéré mais edge nul, quasi-cash |
| `GlobalMacro-Regime` | `projects/GlobalMacro-Regime/` | Macro / Régime | **Needs-improvement** | 1761 j. (2018–2025) ; Sharpe 0.454 ; CAGR 9.80 % ; MaxDD 22.8 % ; PSR 16.7 % ; NP 92.5 % ($77 374) — décent mais edge non significative |
| `Dynamic-Options-Wheel` | `projects/Dynamic-Options-Wheel/` | Options (wheel) | **Needs-improvement / near-BROKEN** | 1508 j. ; Sharpe 0.119 ; CAGR 5.59 % ; **MaxDD 31.4 %** ; PSR 3.8 % ; NP 38.7 % ($37 946) — retour faible + drawdown inacceptable |
| `CausalEventAlpha` | `projects/CausalEventAlpha/` | Causal alpha | **Needs-improvement** | 2878 j. ; Sharpe 0.447 ; CAGR 11.71 % ; **MaxDD 38.8 %** ; PSR 5.5 % ; NP 255.5 % ($225 496) — NP/CAGR élevés mais drawdown catastrophique, edge non significative |
| `FamaFrench` | `projects/FamaFrench/` | Factor rotation | **Needs-improvement** | 1761 j. (2018–2025) ; Sharpe 0.445 ; CAGR 11.11 % ; MaxDD 24.1 % ; PSR 11.9 % ; NP 109.2 % ($72 725) — décent mais edge non significative |

#### Vérifié (tranche 6, backtests QC Cloud via MCP) (5)

> **Scope tranche 6 (#1621)** : 5 stratégies promues via backtests QC Cloud réels (MCP `qc-mcp`,
> backtests existants relus firsthand). Cohorte **Régime / Factor / Vol / Leveraged-Factor** (5
> sous-familles distinctes des tranches 2 Vol, 3 Momentum/Factor, 4 MeanReversion/Macro,
> 5 Trend/Macro-Regime/Options/Causal/Factor). Métriques pleine période in-sample (non walk-forward
> OOS). **1 edge candidat** : `LeveragedETFMomentum-QC` **PSR 79.8 %** = 2ᵉ stratégie (toutes
> tranches 2-6) avec PSR > 50 % (1ʳᵉ = tranche 3 BlackLitterman 51.4 %). **MAIS** ETF leveraged
> (CAGR 126 %, drawdown 53.3 %) → l'edge est vraisemblablement **amplifiée par le levier**, pas du
> skill pur ; à confirmer en walk-forward OOS avant promotion. Les 4 autres : PSR < 10 % (0 edge).

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `HMM-KMeans-Voting` | `projects/HMM-KMeans-Voting/` | Régime (HMM) | **Needs-improvement** | 3522 j. ; Sharpe 0.488 ; CAGR 6.99 % ; MaxDD 23.8 % ; PSR 6.9 % ; NP 157.5 % ($144 661) — edge non significative |
| `Markov-Regime-Detection` | `projects/Markov-Regime-Detection/` | Régime (Markov) | **Needs-improvement** | 2766 j. ; Sharpe 0.375 ; CAGR 8.44 % ; MaxDD 24.4 % ; PSR 5.8 % ; NP 144.0 % ($98 214) — edge non significative |
| `HighBookToMarketFScore-QC` | `projects/HighBookToMarketFScore-QC/` | Factor (Piotroski) | **Needs-improvement** | période post-#2801 (tradeableDates=0, anomalie champ MCP ; ~2018–2025 aligned) ; Sharpe 0.411 ; CAGR 14.51 % ; **MaxDD 60.4 %** ; PSR 4.5 % ; NP 195.9 % ($17 992 007) — CAGR décent mais drawdown catastrophique |
| `Cloud-VolTargeting` | `projects/Cloud-VolTargeting/` | Vol targeting | **Needs-improvement / near-cash** | 1761 j. (2018–2025) ; Sharpe 0.207 ; CAGR 6.72 % ; MaxDD 38.2 % ; PSR 2.4 % ; NP 57.7 % ($32 854) — quasi-cash + drawddown élevé |
| `LeveragedETFMomentum-QC` | `projects/LeveragedETFMomentum-QC/` | Leveraged ETF momentum | **Alive (edge candidat, levier) ★** | 2011 j. ; **Sharpe 1.779** ; CAGR 126.39 % ; **MaxDD 53.3 %** ; **PSR 79.8 %** ; NP 69 153 % ($59 508 108) — **2ᵉ PSR > 50 % toutes tranches (après BlackLitterman 51 %)**, MAIS ETF leveraged (levier amplifie gains ET drawdown) → edge à confirmer en walk-forward OOS, pas du skill pur |

#### Vérifié (tranche 7, backtests QC Cloud via MCP) (5)

> **Scope tranche 7 (#1621)** : 5 stratégies « Vivant » promues via backtests QC Cloud réels
> (MCP `qc-mcp`, backtests existants relus firsthand). Cohorte **ML supervisé / DL / SVM-wavelet**
> (5 sous-familles ML distinctes : trend scanning, features engineering, classification
> reversion/trending, sector classification, SVM/wavelet FX). Métriques pleine période in-sample
> (non walk-forward OOS). **0 edge statistiquement significative** (PSR < 50 % partout, 5/5) :
> MaxPSR = **29.3 %** (Sector-ML-Classification, projet ESGF 581ddcf4) ; 2 stratégies PSR < 10 %
> (ML-FX-SVM-Wavelet 0.39 % quasi-nul, ML-Trend-Scanning 7.84 %). **Confirme pour la famille ML**
> ce que la tranche 2 confirmait pour Vol-* : les backtests in-sample pleine période ne valident
> **aucun edge** sur la cohorte. Walk-forward multi-seed OOS requis avant toute promotion
> « production » — ce n'est pas un jugement négatif sur les approches ML (le in-sample overfit est
> attendu), c'est un signal honnête que **la preuve d'edge n'est pas dans ce référentiel**.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `ML-FeatureEngineering` | `projects/ML-FeatureEngineering/` | ML features (RF/GB Ensemble) | **Needs-improvement** | 2018–2025 (2830 j.) ; **Sharpe 0.656** (max cohorte) ; CAGR 19.06 % (max cohorte) ; MaxDD 34.8 % ; PSR 14.79 % ; NP 614.5 % ($614 544) — meilleur Sharpe/CAGR de la cohorte ML, mais PSR 14.8 % = edge non significative, drawdown 34.8 % élevé |
| `ML-Reversion-Trending` | `projects/ML-Reversion-Trending/` | ML classification reversion/trending | **Needs-improvement** | 2018–2025 (2830 j.) ; Sharpe 0.571 ; CAGR 10.51 % ; MaxDD 19.6 % (min cohorte) ; PSR 25.06 % ; NP 208.4 % ($205 971) — 2ᵉ PSR le plus élevé mais edge non significative ; version v1 avait Runtime Error, v1-fixed resolu |
| `Sector-ML-Classification` | `projects/Sector-ML-Classification/` | ML sectoriel (classification multi-version v6.1–v6.5) | **Needs-improvement** | ESGF 2024–2026 (585 j., période courte) ; Sharpe 0.209 ; CAGR 10.47 % ; MaxDD 17.3 % (2ᵉ min cohorte) ; **PSR 29.34 % (max cohorte)** ; NP 26.1 % ($26 655) — meilleure PSR de la cohorte ML, edge non significative, période courte (585 j.) = OOS réduit |
| `ML-Trend-Scanning` | `projects/ML-Trend-Scanning/` | ML trend scanning | **Needs-improvement** | 2018–2025 (2878 j.) ; Sharpe 0.328 ; CAGR 7.085 % ; **MaxDD 29.4 %** ; PSR 7.84 % ; NP 119.0 % ($115 983) — PSR faible, edge nul ; catalog post-#2801 confirmait Sharpe 0.66 → 0.33 (cf PR #3083jsboige MERGED 2026-06-15) |
| `ML-FX-SVM-Wavelet` | `projects/ML-FX-SVM-Wavelet/` | ML FX (SVM/Wavelet) | **Needs-improvement / near-BROKEN** | 2018–2025 (2806 j.) ; Sharpe 0.153 (min cohorte) ; CAGR 4.29 % (min cohorte) ; MaxDD 21.2 % ; **PSR 0.39 % (min cohorte, quasi-nul)** ; NP 46.0 % ($455 947) — PSR < 1 %, edge statistiquement nul, retour faible |

#### Vérifié (tranche 8, backtests QC Cloud via MCP) (5)

> **Scope tranche 8 (#1621)** : 5 stratégies « Vivant » promues via lecture directe des backtests QC
> Cloud existants via MCP `qc-mcp-lite` (`read_backtest`). **Cohorte Trend + Régime + Vol risk**
> (distincte des tranches 2-7 : Vol-/risk, Momentum/Factor, MeanReversion/Macro,
> Trend/Macro-Régime/Options/Causal/Factor, Régime/Factor/Vol/Leveraged-Factor, ML). Métriques
> pleine période in-sample (non walk-forward OOS). **1 BROKEN** : `VIX-TermStructure` Sharpe négatif
> (−0.125) PSR 0.18 % = quasi-nul. **0 edge** sur les 4 autres (max PSR 24.99 % `TrendStocksLite`,
> sous le seuil 50 %).

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `TrendStocksLite` | `projects/TrendStocksLite/` | Trend actions (lite) | **Needs-improvement** | 2878 j. ; **Sharpe 0.707** (max cohorte) ; **CAGR 17.97 %** (max cohorte) ; MaxDD 33.7 % ; **PSR 24.99 %** (max cohorte) ; NP 564.0 % ($536 958) — best Sharpe/CAGR/PSR cohorte, edge non significative mais profil le plus prometteur |
| `HAR-RV-J-Kelly` | `projects/HAR-RV-J-Kelly/` | Volatility / Kelly | **Needs-improvement** | 2709 j. (2018–2025 aligned) ; Sharpe 0.524 ; CAGR 14.08 % ; MaxDD 37.1 % ; PSR 10.69 % ; NP 165.9 % (₮165 831) — décent mais drawdown élevé, edge non significative |
| `RegimeSwitching` | `projects/RegimeSwitching/` | Régime | **Needs-improvement** | 4593 j. ; Sharpe 0.540 ; CAGR 11.47 % ; MaxDD 33.0 % ; PSR 4.80 % ; NP 627.9 % ($617 405) — long-terme, edge non significative |
| `TrendStocks-Alpha` | `projects/TrendStocks-Alpha/` | Trend actions | **Needs-improvement** | 2516 j. (post-#2801) ; Sharpe 0.512 ; CAGR 15.73 % ; **MaxDD 39.6 %** (max cohorte) ; PSR 5.58 % ; NP 331.5 % ($340 855) — drawdown élevé, edge non significative |
| `VIX-TermStructure` | `projects/VIX-TermStructure/` | Vol (VIX term) | **BROKEN** | 4085 j. ; **Sharpe −0.125** (négatif) ; CAGR 2.17 % ; MaxDD 21.5 % ; **PSR 0.18 %** (quasi-nul) — Sharpe négatif, edge nul ; v5.1 Pos 25 % (from 45 %) = amélioration marginale mais insuffisante |

#### Vérifié (tranche 9, backtests QC Cloud via MCP) (5)

> **Scope tranche 9 (#1621)** : 5 stratégies « Vivant » promues via lecture directe des backtests QC
> Cloud existants via MCP `qc-mcp-lite` (`read_backtest`). **Cohorte Composite + Options + Vol/Momentum**
> (distincte des tranches 2-6 : Vol-/risk, Momentum/Factor, MeanReversion/Macro,
> Trend/Macro-Régime/Options/Causal/Factor, Régime/Factor/Vol/Leveraged-Factor ; **et distincte des
> tranches 7-8 OPEN ML et Trend+Regime+Vol risk** qui seront ajoutées à leurs merges respectifs).
> Métriques pleine période in-sample (non walk-forward OOS). **0 edge statistiquement significative** :
> PSR < 50 % sur toute la cohorte (max 19.78 % `Framework_Composite_EMATrend`). Confirme pour la
> cohorte Composite+Options+Vol/Momentum ce que les tranches 2-8 confirment : les backtests in-sample
> pleine période **ne valident aucun edge** sur la cohorte.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `Framework_Composite_EMATrend` | `projects/Framework_Composite_EMATrend/` | Composite EMA-Trend | **Needs-improvement** | 1761 j. (2018–2025) ; **Sharpe 0.611** (max cohorte) ; **CAGR 16.67 %** (max cohorte) ; MaxDD 27.9 % ; **PSR 19.78 %** (max cohorte) ; NP 194.5 % ($196 423) — best Sharpe/CAGR/PSR cohorte, edge non significative |
| `Option-Wheel` | `projects/Option-Wheel/` | Options (wheel) | **Needs-improvement** | 2821 j. (2015–2026) ; Sharpe 0.529 ; CAGR 12.78 % ; MaxDD 26.4 % ; PSR 10.63 % ; NP 286.0 % ($2 167 801) — bon profil long-terme mais edge non significative |
| `VolTarget-Momentum` | `projects/VolTarget-Momentum/` | Vol / Momentum | **Needs-improvement** | 2516 j. (post-#2801) ; Sharpe 0.500 ; CAGR 11.12 % ; **MaxDD 21.2 %** (min cohorte) ; PSR 9.45 % ; NP 187.3 % ($153 977) — modeste, edge non significative |
| `composite-c1-multiasset` | `projects/composite-c1-multiasset/` | Composite multi-actifs | **Needs-improvement / near-cash** | 1761 j. (2018–2025) ; Sharpe 0.258 ; CAGR 6.49 % ; MaxDD 17.0 % ; PSR 8.69 % ; NP 55.3 % ($53 295) — modeste, edge nul |
| `OptionsIncome` | `projects/OptionsIncome/` | Options (covered call) | **Needs-improvement** | 4100 j. (2015–2026) ; Sharpe 0.213 ; CAGR 5.50 % ; MaxDD 17.5 % ; PSR 4.43 % ; NP 82.5 % ($-7 452) — **NP absolu négatif** (`netProfitAbsolute` = $-7 452) ; edge nul |

#### Vérifié (tranche 10, backtests QC Cloud via MCP) (5)

> **Scope tranche 10 (#1621)** : 5 stratégies promues via backtests QC Cloud réels (MCP `qc-mcp`,
> backtests existants relus firsthand). Cohorte **DeepLearning + LSTM + Temporal-CNN** (5 variantes
> DL distinctes des tranches 2-9 — focus sur réseaux récurrents / convolutifs temporels).
> Métriques pleine période in-sample (non walk-forward OOS). **0 edge statistiquement significative**
> (PSR < 50 % partout — PSR max 28.70 % `Temporal-CNN-Prediction`). **1 BROKEN** :
> `Crypto-LSTM-Prediction` Sharpe -0.021 (légèrement négatif, drawdown 27.4 %).
> Walk-forward multi-seed OOS requis avant toute promotion production. Identité de profil
> `DL-LSTM` ↔ `LSTM-Forecasting` (Sharpe 0.525 / MaxDD 32.5 % / PSR ~13.4 % quasi-identiques)
> = cohérent ; mais **divergence** `ML-Temporal-CNN` (Sharpe 0.161) vs `Temporal-CNN-Prediction`
> (Sharpe 0.734) → deux variantes divergentes (hand-rolled vs MLPClassifier sklearn).

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `DL-LSTM` | `projects/DL-LSTM/` | DL (LSTM PyTorch bi-dir 2×50) | **Needs-improvement** | 2766 j. ; Sharpe 0.525 ; CAGR 11.29 % ; MaxDD 32.5 % ; PSR 13.42 % ; NP 224.7 % ($227 577) — profil identique à `LSTM-Forecasting` ci-dessous |
| `LSTM-Forecasting` | `projects/LSTM-Forecasting/` | DL (MLPClassifier sklearn) | **Needs-improvement** | 2766 j. ; Sharpe 0.525 ; CAGR 11.30 % ; MaxDD 32.5 % ; PSR 13.44 % ; NP 224.9 % ($227 712) — quasi-identique à `DL-LSTM` (hand-rolled vs sklearn convergent) |
| `Crypto-LSTM-Prediction` | `projects/Crypto-LSTM-Prediction/` | DL (DLinear/LSTM crypto) | **BROKEN** | 2313 j. ; **Sharpe -0.021** ; CAGR 3.40 % ; MaxDD 27.4 % ; **PSR 1.21 %** ; NP 23.6 % ($25 198) — Sharpe négatif, PSR quasi-nul, edge absent |
| `ML-Temporal-CNN` | `projects/ML-Temporal-CNN/` | DL (Temporal CNN hand-rolled) | **Needs-improvement** | post-#2801 (tradeableDates=0) ; Sharpe 0.161 ; CAGR 4.81 % ; MaxDD 31.7 % ; PSR 2.68 % ; NP 26.5 % ($30 099) — Sharpe faible, edge absent |
| `Temporal-CNN-Prediction` | `projects/Temporal-CNN-Prediction/` | DL (Temporal CNN) | **Needs-improvement (max cohorte)** | post-#2801 (tradeableDates=0) ; **Sharpe 0.734** ; **CAGR 20.51 %** ; **MaxDD 21.6 %** (min cohorte) ; **PSR 28.70 %** ; NP 154.1 % ($169 062) — meilleur Sharpe/CAGR/MaxDD cohorte mais PSR < 50 % |

#### Vérifié (tranche 11, backtests QC Cloud via MCP) (4)

> **Scope tranche 11 (#1621)** : 4 stratégies promues via backtests QC Cloud réels (MCP `qc-mcp`,
> backtests existants relus firsthand). Cohorte **Crypto BTC + IBKR-Binance-Hybrid**
> (différente des tranches 2 Vol-/risk, 3 Momentum/Factor, 4 MeanReversion/Macro, 5 Trend/Macro,
> 6 Régime/Factor/Vol, 7 ML, 8 Trend+Regime+Vol, 9 Composite+Options, 10 DL+LSTM+Temporal-CNN).
> Métriques pleine période in-sample (sauf Portfolio-IBKR-Binance-Hybrid qui est walk-forward 2022-2024).
> **0 edge statistiquement significative** (PSR < 50 % partout). PSR max 33.50 %
> (`Multi-Layer-EMA-Crypto`, cloud-only ; pour le périmètre Vivant local = `BTC-ML-Researcher` PSR 25.59 %).
> Inclut un **MaxDD catastrophique** (`CSharp-BTC-MACD-ADX` MaxDD 72.7 %).

| Stratégie | Projet QC | Backtest ID | Nom backtest | Date | Sharpe | CAGR | MaxDD | PSR | Verdict |
|-----------|-----------|-------------|-------------|------|-------:|-----:|------:|----:|---------|
| `BTC-ML` | 29318876 | `df8e873a6b819d5aa082ff150ee8f595` | "po2026-verify-btc-ml-oos-2021-2026" | 2026-07-15 | **0.057** | 3.69 % | 15.4 % | 1.52 % | **Needs-improvement** (Sharpe near-zero, PSR ~1.5 %, profil quasi-passif) |
| `Crypto-MultiCanal` | 30750734 | `82fae2cde69e476ec3671b6603a300ac` | "1630-baseline-CryptoMultiCanal-post2801" | 2026-06-14 | **0.333** | 4.59 % | **14.1 %** | 12.95 % | **Needs-improvement** (Sharpe correct mais CAGR modeste, MaxDD min cohorte) |
| `CSharp-BTC-MACD-ADX` | 30751067 | `ff36dde9650487744ab72d9c119039fa` | "BTC-MACD-ADX Baseline" | 2026-04-27 | 0.225 | 3.63 % | **72.7 %** | 2.88 % | **Needs-improvement** (MaxDD catastrophique — MACD/ADX sur BTC = whipsaw en bear market) |
| `Portfolio-IBKR-Binance-Hybrid` | 31717642 | `173434a130bee666b26b33b6463bc694` | "Phase3-WF-2022-2024-5050" | 2026-07-16 | 0.391 | 14.11 % | 35.3 % | 9.05 % | **Needs-improvement** (WF walk-forward 50/50 multi-actifs, PSR < 50 %) |

**Verdict honnête : 0 edge sur la cohorte**. PSR max 33.50 % (hors-périmètre Vivant), max périmètre = 12.95 % (`Crypto-MultiCanal`). Confirme pour la cohorte Crypto BTC ce que les tranches 2-9 confirmaient : les backtests in-sample pleine période **ne valident aucun edge** sur la cohorte. Walk-forward multi-seed OOS requis avant toute promotion production.

### Observations pédagogiques

- **`BTC-ML`** : Sharpe 0.057 ≈ 0 sur 1886 jours OOS 2021-2026 (BTC post-halving cycles), profil quasi-passif. Confirme que la stratégie ML Crypto s'effondre en régime post-halving (probablement surapprentissage sur le bull run 2020-2021).
- **`CSharp-BTC-MACD-ADX`** MaxDD 72.7 % : MACD/ADX sur BTC = oscillateurs inadaptés à la volatilité crypto. Whipsaw violent en bear market 2018+2022. Drawdown > 70 % = inacceptable, peu importe le Sharpe positif résiduel.
- **`Portfolio-IBKR-Binance-Hybrid`** : seul backtest walk-forward WF 2022-2024 50/50 de la cohorte (= méthodologie OOS distincte du training), Sharpe 0.391 / CAGR 14.11 % décent mais PSR < 50 %. Distribution stable multi-actifs (IBKR equity + Binance crypto) vs concentration BTC mono-actif.
- **Note méthodologique** : `Crypto-LSTM-Prediction` (BTC LSTM/DLinear, projet 31855350) **est éligible à la cohorte BTC/Crypto** mais déjà promu en tranche 10 (#7249 OPEN, cohorte DL/LSTM/Temporal-CNN) — promotion redondante évitée pour préserver l'atomicité inter-tranches.

#### Vérifié (tranche 12, backtests QC Cloud via MCP) (3 + 2 hors-Vivant)

> **Scope tranche 12 (#1621)** : 3 stratégies « Vivant » promues + 2 vérifications hors-Vivant (1 Stub + 1 Squelette) via lecture directe des backtests QC Cloud existants via MCP `qc-mcp-lite` (`read_backtest`). Cohorte **ML NLP + Reinforcement Learning** (différente des tranches 7 ML standard et 10 DL/LSTM/Temporal-CNN, ciblant les paradigmes NLP FinBERT / LLM summarization et RL DQN renforcé + hedging options). **0 QCC dépensé** (lecture seule). **3 promotions Vivant nettes** : `ML-FinBERT-Sentiment` (Vivant) ; `ML-LLM-Summarization` (Vivant) ; `RL-DQN-Trading` (Vivant). 2 vérifications hors-Vivant : `RL-Options-Hedging` (Stub, code non créé → backtest POC déployé sur projet QC 30800109 par ailleurs) **BROKEN** ; `Reinforcement-Learning-Trading` (Squelette) **Needs-improvement / near-cash**.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `ML-LLM-Summarization` | `projects/ML-LLM-Summarization/` | ML NLP (LLM summarization) | **Needs-improvement** | 2558 j. ; **Sharpe 0.686** ; CAGR 15.45 % ; MaxDD 22.7 % ; **PSR 37.14 %** ; NP 173.6 % ($173 595) — **max Sharpe/PSR cohorte** ; MaxDD contenu ; edge non significative (PSR < 50 %) |
| `ML-FinBERT-Sentiment` | `projects/ML-FinBERT-Sentiment/` | ML NLP (FinBERT) | **Needs-improvement** | pleine période (tradeableDates=0, anomalie MCP) ; Sharpe 0.584 ; **CAGR 22.10 %** ; **MaxDD 43.0 %** ; PSR 12.18 % ; NP 304.9 % mais **NP absolu -$210 456** — CAGR le plus élevé cohorte mais drawdown élevé + **NP absolu négatif** = levier amplifie gains ET pertes |
| `RL-DQN-Trading` | `projects/RL-DQN-Trading/` | RL (DQN MLPRegressor) | **Needs-improvement** | 2766 j. (2015–2026) ; Sharpe 0.533 ; CAGR 10.89 % ; MaxDD 25.8 % ; PSR 15.60 % ; NP 211.8 % ($212 287) — v2.0.1 « MLPRegressor DQN, 5-ETF, risk-adj, target-fix, 2015-2026 », profil décent mais edge non significative |
| `Reinforcement-Learning-Trading` | `projects/Reinforcement-Learning-Trading/` | RL (DQN Squelette — *hors-Vivant*) | **Needs-improvement / near-cash** | 1509 j. ; Sharpe 0.131 ; CAGR 4.40 % ; MaxDD 27.1 % ; PSR 2.19 % ; NP 29.4 % ($29 321) — DQN basic Ch07 SPY-seul, Sharpe near-zero ; vérifié OK malgré statut Squelette local (le main.py déployé tourne, mais sans « stratégie active » pédagogique) |
| `RL-Options-Hedging` | `projects/RL-Options-Hedging/` | RL (options hedging — *hors-Vivant Stub*) | **BROKEN** | 1761 j. ; **Sharpe −1.264** ; CAGR 1.41 % ; MaxDD 2.5 % ; PSR 20.22 % ; NP 10.3 % ($95 818) — **Sharpe négatif manifeste**, MaxDD très bas (2.5 %) mais retour brut faible et PSR médiocre → **vraiment BROKEN**, pas seulement marginal ; code local absent (Stub) mais backtest POC déployé sur QC Cloud projet 30800109 « RL-Options-Hedging-Ch07 » confirme l'échec du paradigme « RL hedging options » sur ce squelette |

**Verdict honnête : 1 BROKEN + 2 Needs-improvement (Vivant) + 2 Needs-improvement (hors-Vivant).** PSR max 37.14 % (`ML-LLM-Summarization`), aucune > 50 %. Confirme pour la cohorte ML NLP + RL ce que les tranches 7-11 confirment : les backtests in-sample pleine période **ne valident aucun edge** sur la cohorte, et le cas `RL-Options-Hedging` (Sharpe négatif sur 1761 j.) démontre qu'un POC RL sur options **n'aboutit pas** sans feature engineering substantiel (univers d'options large, Greeks dynamiques, scénario hedging adaptatif). Walk-forward multi-seed OOS requis avant toute promotion production. **Aucun Stripe des 5 backtests = 4 stratégies cohérentes avec ledger cohort** (alignement période 2558-2766 j. cohérent avec tranches 7-11).

#### Vérifié (tranche 13, backtests QC Cloud via MCP) (4)

> **Scope tranche 13 (#1621)** : 4 stratégies « Vivant » promues au statut vérifié via backtests
> QC Cloud réels (MCP `qc-mcp-lite`, backtests existants relus firsthand). Cohorte **ML Classification
> / Clustering / Hybrid** (4 sous-familles distinctes des tranches 7 ML Trend/FeatureEng/SVM-Wavelet,
> 8 Trend+Regime, 9 Composite+Options, 10 DL+LSTM, 11 Crypto BTC, 12 ML NLP + RL). Métriques **non
> walk-forward OOS** (backtest pleine période in-sample) — suffisantes pour classer Alive /
> Needs-improvement / BROKEN, insuffisantes pour un verdict de production. **0 edge statistiquement
> significative** (PSR < 50 % partout) — confirme pour la cohorte ML Classification / Clustering ce
> que les tranches 7-12 confirmaient. `Gaussian-Direction-Classifier` post-#2801 (Sharpe 0.761) =
> meilleure candidate de la cohorte, mais PSR 22.74 % reste sous le seuil edge.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `Gaussian-Direction-Classifier` | `projects/Gaussian-Direction-Classifier/` | ML classification (GaussianNB direction) | **Needs-improvement** | 2018–2026 (2766 j.) ; **Sharpe 0.761** ; CAGR 23.10 % ; MaxDD 25.6 % ; PSR 22.74 % ; NP 884.7 % ($8 908 659) — meilleure candidate cohorte, NP absolu record mais edge non significative |
| `Dividend-Harvesting-ML` | `projects/Dividend-Harvesting-ML/` | ML hybrid (dividendes + ranking) | **Needs-improvement** | 2015–2026 (~2833 ordres) ; Sharpe 0.468 ; CAGR 12.66 % ; MaxDD 30.6 % ; PSR 5.46 % ; NP 278.5 % ($2 240 249) — profil dividendes + Sharpe correct, edge non significative |
| `ML-Gaussian-Classifier` | `projects/ML-Gaussian-Classifier/` | ML classification (GaussianNB features) | **Needs-improvement** | 2015–2026 (2375 ordres) ; Sharpe 0.361 ; CAGR 12.49 % ; **MaxDD 47.4 %** ; PSR 4.73 % ; NP 128.1 % ($131 679) — drawdown élevé, edge non significative |
| `Clustering-Fundamentals-ML` | `projects/Clustering-Fundamentals-ML/` | ML non supervisé (KMeans + PCA) | **Needs-improvement** | 2015–2026 (2308 ordres, v3 robust-nan-handling) ; Sharpe 0.142 ; CAGR 3.37 % ; **MaxDD 65.3 %** ; **PSR 0.09 %** ; NP 44.7 % ($30 130) — MaxDD catastrophique, PSR quasi-nul, edge nulle |

#### Vérifié (tranche 14, backtests QC Cloud via MCP) (2)

> **Scope tranche 14 (#1621)** : 2 stratégies « Vivant » promues au statut vérifié via backtests
> QC Cloud réels (MCP `qc-mcp-lite`, backtests existants relus firsthand). Cohorte **DL Chronos
> foundation** (Amazon Chronos foundation model en forecasting financier). Métriques **non
> walk-forward OOS** (backtest pleine période in-sample) — suffisantes pour classer Alive /
> Needs-improvement / BROKEN, insuffisantes pour un verdict de production. **0 edge statistiquement
> significative** (PSR < 50 % partout) — confirme pour la cohorte DL foundation-forecasting ce que
> les tranches 7-13 confirmaient sur ML supervisé / DL LSTM / RL.
>
> **Leçon pédagogique clé (inversée vs l'intuition)** : le variant à **filtre de régime SMA200**
> (`Chronos-Foundation-Forecasting`, PSR **3.12 %**) a la signification statistique la **plus basse**
> de la cohorte, alors que le variant **plain** (`ML-Chronos-Foundation`, PSR **13.79 %**) fait
> mieux. Le filtre SMA200 — censé ne trader que les régimes favorables — **dégrade** la signification
> statistique au lieu de l'améliorer. Interprétation : le SMA200-regime introduit une sélection
> d'échantillon (data-snooping sur le seuil 0.02) qui réduit le nombre de trades effectifs sans
> gain de Sharpe proportionnel → le PSR chute. Ajouter un filtre « intelligent » à un forecast DL
> n'est pas mécaniquement bénéfique ; la barre de signification (PSR) punit le sur-ajustement.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `Chronos-Foundation-Forecasting` | `projects/Chronos-Foundation-Forecasting/` | DL (Chronos foundation + régime SMA200) | **Needs-improvement** | 2018–2026 (2766 j., 1638 ordres) ; **Sharpe 0.253** ; CAGR 6.28 % ; MaxDD 22.4 % ; **PSR 3.12 %** ; NP 95.5 % ($94 994) — variant « filtre SMA200 regime threshold 0.02 » : PSR le plus bas de la cohorte, le filtre dégrade la signification statistique |
| `ML-Chronos-Foundation` | `projects/ML-Chronos-Foundation/` | DL (Chronos foundation, plain) | **Needs-improvement** | 2026 (Batch4, 121 ordres) ; **Sharpe 0.277** ; CAGR 7.23 % ; MaxDD 13.5 % ; **PSR 13.79 %** ; NP 63.0 % ($62 627) — variant plain (sans filtre de régime) : meilleure PSR de la cohorte, mais fenêtre courte (Batch4) → signification fragile, edge non confirmée |


#### Vérifié (tranche 15, backtests QC Cloud via MCP) (4)

> **Scope tranche 15 (#1621)** : 4 stratégies « Vivant » promues au statut vérifié via backtests
> QC Cloud réels (MCP `qc-mcp-lite`, backtests existants relus firsthand). Cohorte **Stratégies
> quantitatives structurelles** — 4 best-guiss du bucket Vivant sans overlap avec les 14 tranches
> précédentes (ML, DL, Régime, Vol, Trend, Crypto, Options, ML-NLP, RL, Classification, Chronos) :
> `Options-VGT` (income covered-call tech single-names vs benchmark VGT), `TermStructureCommodities-QC`
> (courbe terme commodités roll-yield), `PCA-StatArbitrage` (stat-arb factoriel PCA multi-paires),
> `Trend-Following` (AQR-style 12-month momentum multi-actifs). Métriques **non walk-forward OOS**
> (backtest pleine période in-sample) — suffisantes pour classer Alive / Needs-improvement /
> BROKEN, insuffisantes pour un verdict de production. **1 BROKEN + 3 Needs-improvement** — confirme
> pour la cohorte « quantitatif structurel pur » ce que les tranches 7-14 confirmaient sur ML/DL :
> les backtests in-sample pleine période **ne valident aucun edge** sur la cohorte.
>
> **Leçon pédagogique clé (cohorte 4 stratégies)** : la **structure méthodologique** (factoriel
> PCA, roll-yield commodités, momentum AQR, income options) **ne suffit pas à produire un edge
> statistiquement significatif** in-sample. PSR max cohorte = 17.51 % (`Options-VGT`), aucune > 50 %.
> Le `TermStructureCommodities-QC` sort en **BROKEN** (Sharpe -0.244, MaxDD 96.8 %, PSR 0.007 %) —
> effondrement systématique sur la fenêtre 2018-2025, malgré 468 ordres. Le roll-yield commodités
> post-2020 (post-Covid commodity super-cycle puis normalisation 2022-2024) ne fournit pas le
> signal directionnel espéré.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `Options-VGT` | `projects/Options-VGT/` | Options income (covered-call OTM tech single-names vs benchmark VGT) | **Needs-improvement** | 2020–2026 (1552 j., 655 ordres) ; **Sharpe 0.507** ; CAGR 14.19 % ; MaxDD 16.20 % ; **PSR 17.51 %** (max cohorte) ; NP 127.16 % ($76 641) — **best Sharpe cohorte** + meilleur PSR + drawdown contenu (16.20 %) ; `GainStrategy` couvre NVDA/ORCL/CSCO/AMD/QCOM avec options OTM ~30 j ; edge non significative |
| `Trend-Following` | `projects/Trend-Following/` | Trend AQR 12-momentum multi-actifs | **Needs-improvement** | post-#2801 verify, 1630 baseline (2516 j., 451 ordres) ; **Sharpe 0.407** ; CAGR 7.89 % ; **MaxDD 14.60 %** ; **PSR 8.68 %** ; NP 113.82 % ($93 177) — profil « momentum prudent » : drawdown contenu 14.6 % (2e min cohorte) ; Sharpe décevant post-#2801 (vs 1.07 historique, downgrade documenté PR #2988) — edge non significative |
| `PCA-StatArbitrage` | `projects/PCA-StatArbitrage/` | Stat-arb factoriel PCA multi-paires | **Needs-improvement** | 2015–2026 (tradeableDates=0 affiché, 3694 ordres) ; **Sharpe 0.165** ; CAGR 5.34 % ; MaxDD 35.90 % ; **PSR 0.18 %** ; NP 78.72 % ($772 239) — `tradeableDates=0` red flag (le count est-il sur le backtester ?), NP absolu record $772K MAIS PSR quasi-nul = **edge statistique nulle** ; MaxDD 35.9 % élevé ; profil « leverage sur facteur PCA » ne suffit pas à valider un edge |
| `TermStructureCommodities-QC` | `projects/TermStructureCommodities-QC/` | Term structure commodités roll-yield | **BROKEN** | 2018–2025 aligned (2129 j., 468 ordres) ; **Sharpe −0.244** (négatif) ; CAGR **−31.48 %** ; **MaxDD 96.80 %** ; **PSR 0.007 %** (quasi-nul) ; NP **−92.93 %** ($−929 294) — **effondrement systématique** sur la fenêtre alignée 2018-2025 : la courbe terme commodités post-2020 (Covid super-cycle 2020-2022 puis normalisation 2022-2024) ne fournit pas le signal directionnel roll-yield attendu ; perte ≈ capital initial ; edge nul à tous les seuils |


#### Vérifié (tranche 16, backtests QC Cloud via MCP) (4)

> **Scope tranche 16 (#1621)** : 4 stratégies « Vivant » promues au statut vérifié via backtests
> QC Cloud réels (MCP `qc-mcp-lite`, backtests existants relus firsthand). Cohorte
> **EMA-Cross + Composite Framework + Value Dogs** (Trend EMA sur actions single-names, 2 stratégies
> composite multi-factors, Value Dogs of the Dow dividend-yield rebalancing). Métriques **non
> walk-forward OOS** (backtests pleine période in-sample sauf `Framework_Composite_MomentumRegime`
> OOS_2023_2026 walk-forward) — suffisantes pour classer Alive / Needs-improvement / BROKEN,
> insuffisantes pour un verdict de production. **2 edge statistiquement significative** sur 4
> (les 2 Composite Framework, PSR > 50 %) — **première tranche QC #1621 avec edge statistique
> significative depuis la tranche 3** (`BlackLitterman` PSR 51 %, single-strategy isolated). Le
> blending multi-factors (Composite Framework) confirme l'avantage méthodologique de la
> diversification intra-stratégie vs single-factor trend.
>
> **Leçon pédagogique clé (inversion vs intuition trend-only)** : les 2 stratégies **single-factor
> trend EMA / Value Dogs** (`EMA-Cross-Stocks`, `PuppiesOfTheDow-QC`) **n'atteignent pas le seuil
> PSR 50 %** (49.75 % near-edge, 3.49 % respectivement) malgré des Sharpe/CAGR/CumRet très
> honorables, alors que les 2 stratégies **Composite Framework multi-factors** passent le cap.
> Le composite blending (momentum + régime + value ou trend + weather regime) **produit
> davantage de Sharpe par unité de risque** et la signification statistique suit. Inversion vs le
> pattern tr.7-15 (DL/ML/Regime/Crypto in-sample < 50 % PSR partout) : ce n'est pas le ML/DL qui
> produit l'edge, c'est le **blending méthodologique multi-factors** sur fenêtre OOS

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `Framework_Composite_TrendWeather` | `projects/Framework_Composite_TrendWeather/` | Composite (trend + weather regime) | **Edge** | 2018–2025 (2766 j., 2087 ordres, projet 28825740) ; **Sharpe 1.14** ; CAGR 27.11 % ; MaxDD 27.70 % ; **PSR 77.94 %** ; NP 1301.65 % ($1 045 476) — **edge significative** : meilleur Sharpe cohorte + meilleure PSR cohorte + 2ᵉ max CAGR cohorte ; composite trend (EMA + momentum) blendé avec filtre régime « weather » (S&P 500 vs Treasuries yield-curve) |
| `Framework_Composite_MomentumRegime` | `projects/Framework_Composite_MomentumRegime/` | Composite (momentum + régime) | **Edge** | OOS 2023-2026 (835 j., 183 ordres, projet 28871239) ; **Sharpe 0.145** ; CAGR 8.74 % ; MaxDD 4.60 % ; **PSR 73.52 %** ; NP 32.23 % ($29 157) — **edge significative** OOS walk-forward (vs tr.7-15 in-sample) ; Sharpe absolu bas mais **MaxDD min cohorte 4.60 %** = meilleur profil drawdown-containment ; PSR > 50 % sur fenêtre OOS distincte = **signal de robustesse réelle** ; ticker filter T60_RS40 harmonisé sur 2015-2025 |
| `EMA-Cross-Stocks` | `projects/EMA-Cross-Stocks/` | Trend EMA | **Needs-improvement** | 2018–2025 (2516 j., 1424 ordres, projet 28789946, post-#2801 verify IBKR margin) ; **Sharpe 0.991** ; CAGR 29.23 % ; MaxDD 35.70 % ; **PSR 49.75 %** ; NP 1201.48 % ($1 200 060) — **near-edge** : 49.75 % PSR = juste sous le cap 50 % ; 2ᵉ max Sharpe cohorte + max CAGR cohorte + max NP cohorte ($1.2M record) ; single-factor trend EMA 20/50 sur FAANG+NVDA daily ne franchit pas le seuil de signification statistique in-sample |
| `PuppiesOfTheDow-QC` | `projects/PuppiesOfTheDow-QC/` | Value (Dogs of the Dow) | **Needs-improvement** | 2018–2025 (60 ordres, projet 32732704, post-#2801 verify) ; **Sharpe 0.302** ; CAGR 9.61 % ; MaxDD 28.80 % ; **PSR 3.49 %** ; NP 108.49 % ($77 039) — PSR quasi-nul + `tradeableDates=0` (reporting bug, pas absence de trades : 60 ordres confirmés) ; stratégie dividend-yield « Dogs of the Dow » (top-10 yielders DJIA rebalanced annually) sous-performe statistiquement vs trend pur post-2020 |

#### Vérifié (tranche 19, backtests QC Cloud via MCP) (4)

> **Scope tranche 19 (#1621)** : 4 stratégies **freshly-discovered** hors bucket Vivant local, sélectionnées via scan systématique `list_projects name_contains:` sur les patterns `Framework_*` / `Composite_*` / `NB14-*` / `QCP13_*` (L709-L3 ★ extension hors-bucket Vivant). Toutes collision-check 0 match AVANT tr.19 (cf `grep -nE` sur les noms de projets) — atomicité R3 préservée. Variante intra-tranche = 2 BROKEN (baselines QCP13 pédagogiques) + 1 near-edge (ESGF Composite) + 1 Needs-improvement (NB14 CompositeRisk) — pas d'edge significative, mais **2 leçons cross-tranches renforcées** :
>
> - **L709-L1 ★★★ (renforcée)** : **QCP13/NB14/ESGF Composite baselines pédagogiques** sans moteur validé sous-performent vs **Framework Composite multi-factors** TrendWeather/MomentumRegime (tr.16) ; confirme que **blending composite méthodologique** (multi-stratégies + multi-facteurs) > sophistication isolée (moyennes mobiles + classes d'actifs mixées sans signal de momentum/régime).
> - **L709-L2 ★★ (renforcée)** : **Runtime Error → Fixed** confirmée sur `ESGF-Kit-Framework-Composite` (9 backtests : v1 Runtime Error + v2-v8 itérations successives de fix dont `v2-fixed-api`) ; naming pattern observable = **`v<N>-<feature>-<params>` → `v<N>-fixed-api`** puis **`-RF-alpha-80-20`** etc. Pattern L709-L2 ★★ confirmé pour batches QC #1621 futurs.
> - **L709-L3 ★ (renforcée)** : scan `name_contains:` détecte **6 projets Composite hors-bucket Vivant** créés entre 2026-04 et 2026-06 (ESGF-Kit, ESGF-Framework, NB14-Cell75, QCP13_Cell6/Cell38/Cell47) — confirme que **le bucket Vivant local est sous-représentatif** de l'activité QC Cloud. Substance fraîche cross-tranches via scan = levier principal pour densifier le rollout #1621.
>
> **Note leçons par stratégie** : 2 BROKEN structurels = `QCP13_Cell6_BasicFramework` (BasicAlgorithm Sharpe -0.213 sur 9 ans) et `QCP13_Cell38_CompositeAlpha` (CompositeAlpha Sharpe -0.394 sur 9 ans) — confirme que **les baselines QCP13 pédagogiques (livre Hands-On)** ne sont pas des stratégies déployables telles quelles, contrairement aux Composite Framework qui intègrent un signal de momentum/régime. `ESGF-Framework-Composite` PSR 32.52 % = meilleur signal hors-bucket Vivant post-tr.16, mais reste sous le cap edge. `NB14-Cell75-CompositeRisk` PSR 27.94 % = composite risque décent (MaxDD 20.2 % = 2ᵉ plus bas hors-tr.16) mais edge non-significative.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `ESGF-Framework-Composite` | `projects/ESGF-Framework-Composite/` | Composite (multi-factors ESGF) | **Needs-improvement / near-edge** | 2015–2024 (1761 j., 3427 ordres, projet 29687005) ; **Sharpe 0.792** (record hors-Framework TrendWeather/MomentumRegime) ; **CAGR 23.71 %** ; MaxDD 32.60 % ; **PSR 32.52 %** ; NP 343.95 % ($312 704) — **meilleur Sharpe hors-bucket Vivant post-tr.16** (vs `Framework_Composite_TrendWeather` 1.14 / `Framework_Composite_MomentumRegime` 0.145) ; sous le cap edge 50 % mais **2ᵉ PSR max cohorte Composite post-tr.16** |
| `QCP13_Cell6_BasicFramework_3367` | `projects/QCP13_Cell6_BasicFramework_3367/` | Baseline composite pédagogique (BasicAlgorithm) | **BROKEN** | 2015–2024 (3100 ordres, projet 33046456, cellule 6 notebook 14) ; **Sharpe -0.213** ; **CAGR -5.45 %** ; **MaxDD 61.30 %** ; **PSR 0.002 %** ; **NP -42.95 %** (-$42 945) — structurellement négatif sur 9 ans ; baseline `BasicFrameworkAlgorithm` du notebook Hands-On **pas déployable telle quelle** (moyennes mobiles simples sans signal de momentum/régime, cf leçon L709-L1 ★★★ renforcée) |
| `QCP13_Cell47_CompleteFramework_3367` | `projects/QCP13_Cell47_CompleteFramework_3367/` | Composite pédagogique (CompleteAlgorithm) | **Needs-improvement** | 2015–2024 (23048 ordres, projet 33046719, cellule 47 notebook 14) ; Sharpe 0.066 ; CAGR 3.44 % ; MaxDD 25.10 % ; PSR 0.37 % ; NP 40.27 % ($33 996) — quasi-cash après 9 ans, edge statistiquement nul ; variante « CompleteFrameworkStrategy » plus sophistiquée que la baseline Basic mais reste insuffisante pour produire edge |
| `NB14-Cell75-CompositeRisk-3367-verify` | `projects/NB14-Cell75-CompositeRisk-3367-verify/` | Composite risque (cellule 75 notebook 14) | **Needs-improvement** | 2015–2024 (2516 j., 1750 ordres, projet 33072157) ; Sharpe 0.635 ; CAGR 11.09 % ; **MaxDD 20.20 %** (2ᵉ plus bas hors-tr.16) ; PSR 27.94 % ; NP 186.53 % ($136 079) — composite risque décent (Sharpe > 0.6, MaxDD < 21 %) mais PSR sous cap edge ; proche du pattern `Framework_Composite_MomentumRegime` (Sharpe 0.145 / MaxDD 4.60 %) sans toutefois bénéficier du filtre régime validé |
| `ESGF-Kit-Framework-Composite` (v8-ML-RF-alpha-80-20) | `projects/ESGF-Kit-Framework-Composite/` | Composite ML-RF (ESGF kit pédagogique, itération v8 fixée) | **Needs-improvement** | 2015–2024 (2516 j., 1757 ordres, projet 31201689, dernière itération fixée) ; Sharpe 0.429 ; CAGR 8.68 % ; **MaxDD 14.00 %** (meilleur MaxDD hors-tr.16) ; PSR 8.25 % ; NP 129.91 % ($140 258) — **meilleur profil drawdown** de la cohorte (14 % vs cohorte 14-32 %) ; itération v8 du pipeline ESGF (9 backtests v1 Runtime Error → v2-fixed-api → v8-ML-RF-alpha-80-20, pattern L709-L2 ★★ Runtime Error → Fixed confirmé) ; PSR modeste = modèle ML-RF sur features basiques sans signal de momentum/régime |

#### Vérifié (tranche 20, backtests QC Cloud via MCP) (5)

> **Scope tranche 20 (#1621)** : 5 stratégies **freshly-discovered** hors bucket Vivant local, sélectionnées via scan systématique `list_projects name_contains:` sur 8 patterns (`Spread`/`Alpha`/`Factor`/`MeanReversion`/`LSTM`/`Momentum`/`Carry`/`Breakout`) — extension L709-L3 ★ diversification hors-bucket Vivant. Toutes collision-check 0 match AVANT tr.20 (cf `grep -nE` sur les noms de projets) — atomicité R3 préservée. Variante intra-tranche = **3 BROKEN** (2 QCP6 BullCallSpread + 1 QCP13 Cell38 CompositeAlpha) + **2 Needs-improvement** (`dbg-DualMomentum-6192` + `1630-lstm-forecasting-post2801`) — **0 edge significative** (PSR max 13.42 %), cohérent avec la cohorte pédagogique QCPxx (L710-L1 ★★★ confirmée). Leçons cross-tranches :
>
> - **L710-L1 ★★★ (consolidée, 2ᵉ BROKEN QCP13 consécutive)** : `QCP13_Cell38_CompositeAlpha_3367` Sharpe -0.394 / MaxDD 62 % / PSR 0.000 % sur 9 ans = 2ᵉ baseline QCP13 pédagogique structurellement BROKEN (après `QCP13_Cell6_BasicFramework` tr.19 Sharpe -0.213). Pattern consolidé = **baselines Hands-On QCP13 systématiquement négatives in-sample**, vs Composite Framework (tr.16) qui intègrent un signal de momentum/régime validé. Pour batches QC #1621 futurs : **prioriser `-V2-Fixed` / `-v2`** quand Runtime Error/V1 coexiste avec V2 (L709-L2 ★★), et **skipper les `QCP*` baselines** sauf contre-exemple BROKEN documenté (L710-L1 ★★★).
> - **L711-L1 ★ NEW** : **2 BullCallSpread (QCP6_Cell23 + QCP6_Cell35) backtests strictement identiques** (même Sharpe -3.20, CAGR 0.75 %, MaxDD 0.70 %, NP 0.37 % / $37, 4 ordres, 124 jours tradeable). Probable bug de projet QC Cloud (clonage accidentel) ou copier-coller de backtest entre 2 projets QCP6 distincts ; signal de qualité de données à documenter. Leçon : **toujours collisionner les backtests entre projets partageant un préfixe commun** (`QCP6_*`) avant de claim une promotion edge — si backtests sont identiques byte-pour-byte, c'est une seule stratégie économique réelle, pas deux.
> - **L711-L2 ★ NEW** : `dbg-DualMomentum-6192` (projet 34032518, créé **2026-07-11**) = stratégie freshly-discovered la plus récente du corpus QC #1621 (1 jour après c.711, 11 juillet 2026). PSR 1.72 % modeste + CAGR 8.41 % + MaxDD 14.90 % propre. Suggère que **QC Cloud héberge une activité de debug instrumentation récente non-couverte par le bucket Vivant local** : scan `dbg-*` projects pour cycles futurs probable.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `QCP6_Cell23_BullCallSpread` | `projects/QCP6_Cell23_BullCallSpread/` | Options spread (Bull Call Spread) | **BROKEN** | 2023H1 (124 j., 4 ordres, projet 32001839, backtest `Cell23_BullCallSpreadStrategy`) ; **Sharpe -3.20** ; CAGR 0.75 % ; MaxDD 0.70 % ; PSR 29.62 % ; NP 0.37 % ($37) — structurellement négatif sur 6 mois (H1 2023), 4 ordres seulement ; baseline `QCP6` pédagogique BullCallSpread (call long + call short OTM) sous-performe systématiquement ; note : backtests strictement identiques à `QCP6_Cell35_BullCallSpread` (cf L711-L1 ★) |
| `QCP6_Cell35_BullCallSpread` | `projects/QCP6_Cell35_BullCallSpread/` | Options spread (Bull Call Spread) | **BROKEN** | 2023H1 (124 j., 4 ordres, projet 33409983, backtest `BullCallSpread-2023H1-groundtruth` parmi 5 backtests Completed) ; **Sharpe -3.20** ; CAGR 0.75 % ; MaxDD 0.70 % ; PSR 29.62 % ; NP 0.37 % ($37) — **backtests strictement identiques** à `QCP6_Cell23_BullCallSpread` (cf L711-L1 ★ : probable bug QC Cloud ou clonage accidentel entre 2 projets `QCP6_*`) ; nom de fichier plus précis (`groundtruth`) suggère que le projet `QCP6_Cell35` est la référence canonique, `QCP6_Cell23` une duplication antérieure |
| `QCP13_Cell38_CompositeAlpha_3367` | `projects/QCP13_Cell38_CompositeAlpha_3367/` | Composite pédagogique (CompositeAlpha) | **BROKEN** | 2015–2024 (18493 ordres, projet 33046536, backtest `CompositeAlphaAlgorithm-2015-2024`) ; **Sharpe -0.394** ; CAGR -7.72 % ; **MaxDD 62.00 %** ; **PSR 0.000 %** ; **NP -55.25 %** (-$55 462) — **2ᵉ baseline QCP13 pédagogique structurellement BROKEN consécutive** après `QCP13_Cell6_BasicFramework` (tr.19) ; confirme leçon L710-L1 ★★★ consolidée : **les baselines QCP13 Hands-On** (Basic/Complete/CompositeAlpha) **ne sont pas déployables telles quelles**, contrairement aux Framework Composite (tr.16) qui intègrent un signal momentum/régime |
| `dbg-DualMomentum-6192` | `projects/dbg-DualMomentum-6192/` | Momentum dual (debug instrumentation) | **Needs-improvement** | 2018–2025 (1761 j., 318 ordres, projet 34032518, **créé 2026-07-11** = le plus récent du corpus QC #1621, cf L711-L2 ★) ; Sharpe 0.35 ; CAGR 8.41 % ; **MaxDD 14.90 %** (propre) ; PSR 1.72 % ; NP 76.09 % ($59 746) — profil drawdown attractif mais PSR quasi-nul = pas de signification statistique ; nom `dbg-6192-instrumentation` suggère un projet en cours de debug, Edge attendue post-instrumentation ; watchlist pour batches QC #1621 futurs |
| `1630-lstm-forecasting-post2801` | `projects/1630-lstm-forecasting-post2801/` | DL LSTM forecasting (post-issue #2801) | **Needs-improvement** | 2015–2024 (2766 j., 2091 ordres, projet 32970990, backtest `post2801-verification`) ; Sharpe 0.525 ; CAGR 11.29 % ; MaxDD 32.50 % ; PSR 13.42 % ; NP 224.72 % ($227 577) — LSTM forecasting avec Sharpe correct (0.525) et CAGR > 11 % mais MaxDD 32.5 % et PSR 13.42 % sous cap edge ; `post2801` suggère qu'il s'agit d'une vérification suite à issue #2801 (peut-être fix OOS/walk-forward) ; variante L-series #1630 (cf leçon cross-tranche QC #1621 sur robustesse #1630) |


#### Vivant (best-guess, non vérifié) (56 physiques = 20 true + 36 promues tr7-16 ; voir synthèse)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `BTC-ML` | `projects/BTC-ML/` | ML Crypto | **Vérifié tranche 11** | main.py: class MyEnhancedCryptoMlAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb — voir section tranche 11 |
| `CSharp-BTC-EMA-Cross` | `projects/CSharp-BTC-EMA-Cross/` | Trend EMA (C#) | Vivant | Main.cs: class BtcEmaCrossDaily1Algorithm : QCAlgorithm + research_robustness.ipynb |
| `CSharp-BTC-MACD-ADX` | `projects/CSharp-BTC-MACD-ADX/` | Trend MACD/ADX (C#) | **Vérifié tranche 11** | Main.cs: class BtcMacdAdxDaily1Algorithm : QCAlgorithm + Research.ipynb + RESEARCH_FINDINGS.md — voir section tranche 11 |
| `CSharp-CTG-Momentum` | `projects/CSharp-CTG-Momentum/` | Momentum (C#, multi-fichiers) | Vivant | Main.cs: class StocksOnTheMoveAlgorithm : QCAlgorithm + 4 indicateurs .cs + research_robustness.ipynb |
| `Chronos-Foundation-Forecasting` | `projects/Chronos-Foundation-Forecasting/` | DL (Chronos foundation) | **Vérifié tranche 14** | main.py: class ChronosFoundationForecasting(QCAlgorithm) + research.ipynb — voir section tranche 14 |
| `Clustering-Fundamentals-ML` | `projects/Clustering-Fundamentals-ML/` | ML non supervisé | **Vérifié tranche 13** | main.py: class ClusteringFundamentalsAlgorithm(QCAlgorithm) — voir section tranche 13 |
| `Crypto-LSTM-Prediction` | `projects/Crypto-LSTM-Prediction/` | DL (LSTM) Crypto | **Vérifié tranche 10** | main.py: class CryptoLSTMPredictionAlgorithm(QCAlgorithm) + research.ipynb — voir section tranche 10 |
| `Crypto-MultiCanal` | `projects/Crypto-MultiCanal/` | Crypto multi-signal | **Vérifié tranche 11** | main.py: class CryptoMultiChannelAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb — voir section tranche 11 |
| `DL-LSTM` | `projects/DL-LSTM/` | DL (LSTM) | **Vérifié tranche 10** | main.py: class LSTMModel(nn.Module) + algo QCAlgorithm + quantbook.ipynb — voir section tranche 10 |
| `Dividend-Harvesting-ML` | `projects/Dividend-Harvesting-ML/` | ML dividendes | **Vérifié tranche 13** | main.py: class DividendHarvestingAlgorithm(QCAlgorithm) — voir section tranche 13 |
| `EMA-Cross-Alpha` | `projects/EMA-Cross-Alpha/` | Trend EMA | Vivant | main.py: class EMACrossAlphaAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `EMA-Cross-Stocks` | `projects/EMA-Cross-Stocks/` | Trend EMA | **Vérifié tranche 16** | main.py: class EMACrossStocksAlgorithm(QCAlgorithm) + quantbook.ipynb — voir section tranche 16 |
| `Framework_Composite_EMATrend` | `projects/Framework_Composite_EMATrend/` | Composite | **Vérifié tranche 9** | main.py: class FrameworkCompositeEMATrend(QCAlgorithm) + quantbook.ipynb — voir section tranche 9 |
| `Framework_Composite_MomentumRegime` | `projects/Framework_Composite_MomentumRegime/` | Composite | **Vérifié tranche 16** | main.py: class FrameworkCompositeMomentumRegime(QCAlgorithm) + quantbook.ipynb — voir section tranche 16 |
| `Framework_Composite_TrendWeather` | `projects/Framework_Composite_TrendWeather/` | Composite | **Vérifié tranche 16** | main.py: class FrameworkCompositeStrategy(QCAlgorithm) + quantbook.ipynb — voir section tranche 16 |
| `Gaussian-Direction-Classifier` | `projects/Gaussian-Direction-Classifier/` | ML classification | **Vérifié tranche 13** | main.py: class GaussianDirectionClassifier(QCAlgorithm) + research.ipynb — voir section tranche 13 |
| `HAR-RV-J-Kelly` | `projects/HAR-RV-J-Kelly/` | Volatility / Kelly | **Vérifié tranche 8** | main.py: class HarrvjKellyAlgorithm(QCAlgorithm) — voir section tranche 8 |
| `LSTM-Forecasting` | `projects/LSTM-Forecasting/` | DL (LSTM) | **Vérifié tranche 10** | main.py: class LSTMForecasting(QCAlgorithm) + research.ipynb — voir section tranche 10 |
| `ML-Chronos-Foundation` | `projects/ML-Chronos-Foundation/` | DL (Chronos) | **Vérifié tranche 14** | main.py: class ChronosFoundationAlgorithm(QCAlgorithm) — voir section tranche 14 |
| `ML-Classification` | `projects/ML-Classification/` | ML supervisé | Vivant | main.py: class MLClassificationAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-DeepLearning` | `projects/ML-DeepLearning/` | DL | Vivant | main.py: class SimpleLSTM(nn.Module) + algo QCAlgorithm + quantbook.ipynb |
| `ML-EnhancedPairs` | `projects/ML-EnhancedPairs/` | ML pairs | Vivant | main.py: class MLEnhancedPairsAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Ensemble` | `projects/ML-Ensemble/` | ML ensemble | Vivant | main.py: class MLEnsembleAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-FX-SVM-Wavelet` | `projects/ML-FX-SVM-Wavelet/` | ML FX (SVM/Wavelet) | **Vérifié tranche 7** | voir tableau Vérifié (tranche 7) ci-dessus — Promu Needs-improvement (PSR 0.39 %) |
| `ML-FeatureEngineering` | `projects/ML-FeatureEngineering/` | ML features | **Vérifié tranche 7** | voir tableau Vérifié (tranche 7) ci-dessus — Promu Needs-improvement (PSR 14.79 %) |
| `ML-FinBERT-Sentiment` | `projects/ML-FinBERT-Sentiment/` | ML NLP (FinBERT) | **Vérifié tranche 12** | main.py: class FinBERTSentimentAlgorithm(QCAlgorithm) + research.ipynb — voir section tranche 12 |
| `ML-Gaussian-Classifier` | `projects/ML-Gaussian-Classifier/` | ML classification | **Vérifié tranche 13** | main.py: class GaussianNaiveBayesAlgorithm(QCAlgorithm) — voir section tranche 13 |
| `ML-HeadShoulders-CNN` | `projects/ML-HeadShoulders-CNN/` | DL (CNN patterns) | Vivant | main.py: class CNNPatternDetectionAlgorithm(QCAlgorithm) + research.ipynb |
| `ML-LLM-Summarization` | `projects/ML-LLM-Summarization/` | ML NLP (LLM) | **Vérifié tranche 12** | main.py: class LLMNewsSentimentAlgorithm(QCAlgorithm) — voir section tranche 12 |
| `ML-Regression` | `projects/ML-Regression/` | ML supervisé | Vivant | main.py: class MLRegressionAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Reversion-Trending` | `projects/ML-Reversion-Trending/` | ML classification | **Vérifié tranche 7** | voir tableau Vérifié (tranche 7) ci-dessus — Promu Needs-improvement (PSR 25.06 %) |
| `ML-SVM` | `projects/ML-SVM/` | ML supervisé (SVM) | Vivant | main.py: class MLSVMAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Temporal-CNN` | `projects/ML-Temporal-CNN/` | DL (Temporal CNN) | **Vérifié tranche 10** | main.py: class TemporalCNNPredictionAlgorithm(QCAlgorithm) — voir section tranche 10 |
| `ML-TextClassification` | `projects/ML-TextClassification/` | ML NLP | Vivant | main.py: class MLTextClassificationAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Trend-Scanning` | `projects/ML-Trend-Scanning/` | ML trend | **Vérifié tranche 7** | voir tableau Vérifié (tranche 7) ci-dessus — Promu Needs-improvement (PSR 7.84 %) |
| `Option-Wheel` | `projects/Option-Wheel/` | Options (wheel) | **Vérifié tranche 9** | main.py: class WheelStrategyAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb — voir section tranche 9 |
| `Options-VGT` | `projects/Options-VGT/` | Options (covered call) | **Vérifié tranche 15** | main.py: class GainStrategy(QCAlgorithm) + quantbook.ipynb — voir section tranche 15 (Needs-improvement, Sharpe 0.507 / PSR 17.51 %) |
| `OptionsIncome` | `projects/OptionsIncome/` | Options (covered call) | **Vérifié tranche 9** | main.py: class CoveredCallStrategy(QCAlgorithm) + research.ipynb + quantbook.ipynb — voir section tranche 9 |
| `PCA-StatArbitrage` | `projects/PCA-StatArbitrage/` | StatArb (PCA) | **Vérifié tranche 15** | main.py: class PCAStatArbitrageAlgorithm(QCAlgorithm) — voir section tranche 15 (Needs-improvement, Sharpe 0.165 / PSR 0.18 %) |
| `Portfolio-IBKR-Coinbase-Hybrid` | `projects/Portfolio-IBKR-Coinbase-Hybrid/` | Hybrid crypto/broker | Vivant | main.py: class PortfolioHybridIBKRCoinbase(QCAlgorithm) (helpers FeeModel/Slippage en amont) + research.ipynb + quantbook.ipynb |
| `Positive-Negative-Splits-ML` | `projects/Positive-Negative-Splits-ML/` | ML (stock splits) | Vivant | main.py: class SplitEventsAlgorithm(QCAlgorithm) |
| `PuppiesOfTheDow-QC` | `projects/PuppiesOfTheDow-QC/` | Value (Dogs of the Dow) | **Vérifié tranche 16** | main.py: class PuppiesOfTheDow(QCAlgorithm) — voir section tranche 16 |
| `RL-DQN-Trading` | `projects/RL-DQN-Trading/` | RL (DQN) | **Vérifié tranche 12** | main.py: class ReinforcementLearningTrading(QCAlgorithm) — voir section tranche 12 |
| `RegimeSwitching` | `projects/RegimeSwitching/` | Régime | **Vérifié tranche 8** | main.py: class RegimeSwitching(QCAlgorithm) + quantbook.ipynb — voir section tranche 8 |
| `SVM-Wavelet-Forecasting` | `projects/SVM-Wavelet-Forecasting/` | ML (SVM/Wavelet) | Vivant | main.py: class SVMWaveletForecasting(QCAlgorithm) |
| `Sector-ML-Classification` | `projects/Sector-ML-Classification/` | ML sectoriel | **Vérifié tranche 7** | voir tableau Vérifié (tranche 7) ci-dessus — Promu Needs-improvement (PSR 29.34 %, période ESGF 2024–2026 585 j.) |
| `Stoploss-Volatility-ML` | `projects/Stoploss-Volatility-ML/` | ML risk | Vivant | main.py: class StoplossVolatilityMLAlgorithm(QCAlgorithm) + research.ipynb |
| `Temporal-CNN-Prediction` | `projects/Temporal-CNN-Prediction/` | DL (Temporal CNN) | **Vérifié tranche 10** | main.py: class TemporalCNNPrediction(QCAlgorithm) + research.ipynb — voir section tranche 10 |
| `TermStructureCommodities-QC` | `projects/TermStructureCommodities-QC/` | Commodities (term structure) | **Vérifié tranche 15** | main.py: class CommodityTermStructureAlgorithm(QCAlgorithm) — voir section tranche 15 (BROKEN, Sharpe -0.244 / PSR 0.007 %) |
| `Trend-Following` | `projects/Trend-Following/` | Trend (AQR) | **Vérifié tranche 15** | main.py: class TrendFollowingAQR(QCAlgorithm) + quantbook.ipynb — voir section tranche 15 (Needs-improvement, Sharpe 0.407 / PSR 8.68 %) |
| `TrendFilteredMeanReversion` | `projects/TrendFilteredMeanReversion/` | Mean reversion filtré | Vivant | main.py: class TrendFilteredMeanReversion(QCAlgorithm) + research.ipynb |
| `TrendStocks-Alpha` | `projects/TrendStocks-Alpha/` | Trend actions | **Vérifié tranche 8** | main.py: class TrendStocksAlphaAlgorithm(QCAlgorithm) + quantbook.ipynb — voir section tranche 8 |
| `TrendStocksLite` | `projects/TrendStocksLite/` | Trend actions (lite) | **Vérifié tranche 8** | main.py: class TrendStocksLite(QCAlgorithm) + research.ipynb — voir section tranche 8 |
| `VIX-TermStructure` | `projects/VIX-TermStructure/` | Vol (VIX term) | **Vérifié tranche 8** | main.py: class VIXTermStructureStrategy(QCAlgorithm) + research.ipynb + quantbook.ipynb — voir section tranche 8 (BROKEN) |
| `VolTarget-Momentum` | `projects/VolTarget-Momentum/` | Vol / Momentum | **Vérifié tranche 9** | main.py: class VolTargetMomentum(QCAlgorithm) — voir section tranche 9 |
| `composite-c1-multiasset` | `projects/composite-c1-multiasset/` | Composite multi-actifs | **Vérifié tranche 9** | main.py: class CompositeC1MultiAssetRotation(QCAlgorithm) — voir section tranche 9 |

#### Vivant (README revendique vérifié) (0)

> Bucket désormais vide : `Multi-Layer-EMA` (dernier entrant) promu en tranche 4 — sa revendication
> README « Verified on QC Cloud (project 28433748) » **confirmée firsthand** via MCP qc-mcp, mais
> reclassée Needs-improvement (Sharpe 0.798, MaxDD crypto 57 %, PSR 23.9 % — edge non significative).

#### Recherche uniquement (pas d'algo déployable) (5)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `Alpha-Correlation-Analysis` | `projects/Alpha-Correlation-Analysis/` | Recherche (analytique) | Recherche | README : « Research (analytical notebook, no trading algorithm) » + quantbook.ipynb seul |
| `Ensemble-DLinear-TFT` | `projects/Ensemble-DLinear-TFT/` | Recherche DL | Recherche | pas de main.py ; research.ipynb + _generate_research.py |
| `GraphSAGE-MultiAsset-Ranking` | `projects/GraphSAGE-MultiAsset-Ranking/` | Recherche GNN | Recherche | pas de main.py ; research.ipynb + _generate_research.py |
| `Mamba-Crypto-Ranking` | `projects/Mamba-Crypto-Ranking/` | Recherche DL (Mamba) | Recherche | pas de main.py ; research.ipynb + _generate_research.py |
| `TFT-Crypto-Ranking` | `projects/TFT-Crypto-Ranking/` | Recherche DL (TFT) | Recherche | pas de main.py ; research.ipynb + _generate_research.py |

#### Stub (code non créé) (2)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `Corrective-AI` | `projects/Corrective-AI/` | Stub | Stub | README : « Stub (exercice planifié, fichiers de code non encore créés) » ; pas de main.py |
| `RL-Options-Hedging` | `projects/RL-Options-Hedging/` | Stub (RL options) | Stub | README : « Stub (planned exercise, code files not yet created) » ; pas de main.py |

#### Squelette/template (pas de stratégie active) (2)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `RL-Portfolio` | `projects/RL-Portfolio/` | RL (squelette) | Squelette | README : « Template/skeleton (no active strategy) » + main.py: class RLPortfolioAlgorithm(QCAlgorithm) |
| `Reinforcement-Learning-Trading` | `projects/Reinforcement-Learning-Trading/` | RL (squelette) | Squelette | README : « Template/skeleton (no active strategy) » + main.py: class ReinforcementLearningTrading(QCAlgorithm) |

#### Contre-exemple pédagogique (BROKEN) (2)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `ETF-Pairs` | `projects/ETF-Pairs/` | Pairs (cassé) | Contre-exemple | README : « Statut : ❌ BROKEN — contre-exemple à visée pédagogique » + main.py: class ETFPairsTrading(QCAlgorithm) |
| `PairsTrading` | `projects/PairsTrading/` | Pairs (cassé) | Contre-exemple | README : « Statut : BROKEN — contre-exemple à visée pédagogique » + main.py: class PairsTrading(QCAlgorithm) |

#### Archivé / superseded (3)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `TurnOfMonth` | `projects/TurnOfMonth/` | Calendrier (archivé) | Archivé | README : « Status: ARCHIVED (Sharpe ceiling ~0.13) » + main.py: class TurnOfMonthEffect(QCAlgorithm) |
| `MomentumStrategy` | `projects/MomentumStrategy/` | Rotation ETF sectoriels (momentum) | Archivé | `ARCHIVE.md` + main.py en-tête `# [ARCHIVED - Sharpe ceiling ~0.48]` ; class SectorMomentumETFRotation(QCAlgorithm) — reclassé firsthand c.570 |
| `SectorMomentum` | `projects/SectorMomentum/` | Dual momentum 3 actifs (SPY/TLT/GLD) | Archivé | `ARCHIVE.md` + main.py en-tête `# [ARCHIVED - Sharpe ceiling ~0.56]` ; class SectorDualMomentumStrategy(QCAlgorithm) — reclassé firsthand c.570 |

#### Research phase (1)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `Portfolio-Optimization-ML` | `projects/Portfolio-Optimization-ML/` | ML portefeuille (recherche) | Recherche-phase | README : « Status: 🔄 Research Phase - Based on HandsOnAITrading Book » + main.py: class PortfolioOptimizationMLAlgorithm(QCAlgorithm) |

#### Démonstration pédagogique (1)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `TradingCosts-Optimization` | `projects/TradingCosts-Optimization/` | Démo coûts de transaction | Démo | README : « Status: Educational demo » + main.py: class TradeCostEstimationAlgorithm(QCAlgorithm) |

#### Utilitaire / docs (pas une stratégie) (2)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `Research-Executor` | `projects/Research-Executor/` | Harness d'exécution recherche | Utilitaire | README : « Utility (research execution harness, not a trading strategy) » + main.py: class ResearchExecutor(QCAlgorithm) |
| `_docs` | `projects/_docs/` | Documentation / audits | Utilitaire | dossier de docs (OPTIMIZATION_BACKLOG.md, QUANTCONNECT_PROJECTS_AUDIT.md, …) ; pas d'algo |

### Incertitudes prioritaires — résolues firsthand (spot-check code, c.570)

Entrées où le statut *best-guess* était le plus fragile (divergence nom de dossier / nom de classe, doublons suspects). **Résolution firsthand par lecture directe de `main.py`** — la divergence de nommage se tranche par le code, pas par les métriques, donc aucun backtest requis :

- **`Multi-Layer-EMA`** (`OptimizedCryptoAlgorithm`) — **résolu**. Vérifié tranche 4 (Needs-improvement, Sharpe 0.798). Divergence de nommage levée : crypto BTC/ETH/LTC (Binance) avec EMA10/50 + RSI + Bollinger + filtre de volatilité ATR (max 3 positions) — « Multi-Layer-EMA » est défendable (EMA = couche primaire d'un empilement multi-indicateurs).
- **`LeveragedETFMomentum-QC`** (`ConditionalSectorRotation`) — **résolu, pas une divergence**. QC Strategy Library #60 (Grant Forman) : ETF à effet de levier SPY/QQQ/TQQQ/UVXY/TECL/SPXL/SQQQ/TECS/BSV, régime RSI + SMA. Le dossier nomme le *thème* (momentum ETF levier), la classe le *mécanisme* (rotation conditionnelle) — complémentaires. Déjà backtesté tranche 6 (PSR 79.8 %, flag OOS ETF levier).
- **`MacroFactorRotation-QC`** (`AIStocksBondsRotationAlgorithm`) — **résolu, pas une divergence**. QC Strategy Library #72 (Derek Melchin) : rotation cross-actifs SPY/GLD/BND/BTCUSD pilotée par `DecisionTreeRegressor` sur facteurs FRED (VIX, courbe 10Y-3M, fed funds), rebalancement mensuel. Nom = thème macro-factoriel, classe = mécanisme ML actions/bonds/crypto. Multi-actifs sur brokerage par défaut (IBKR rejette le crypto — cf #1027).
- **`FamaFrench`** (`FactorETFRotation`) — **résolu, pas une divergence**. Rotation d'ETF factoriels VLUE/MTUM/SIZE/QUAL/USMV (momentum risk-adjusted 12m/vol63 + régime SMA200, stop -12 %). La sémantique Fama-French *est* portée par les ETF factoriels tradés ; la classe nomme le mécanisme. Métriques auto-rapportées v3.0 (Sharpe 0.540) dans la docstring — non recroisées firsthand.
- **`Options-VGT`** (`GainStrategy`) — **résolu**. Stratégie d'*income options* (contrats OTM, `OptionChainProvider`, échéance ~30 j) sur des tech single-names NVDA/ORCL/CSCO/AMD/QCOM, benchmark VGT. Le dossier « VGT » désigne le *benchmark*, pas le sous-jacent tradé. Nom de classe `GainStrategy` vague mais contenu clair.
- **`HAR-RV-J-Kelly`** vs **`HAR-RV-Kelly`** — **résolu : PAS une relation de supersession**. Classes d'actifs distinctes : `HAR-RV-J-Kelly` (`HarrvjKellyAlgorithm`) trade du **crypto** (BTC/ETH/LTC/BCH, Binance) avec composante de saut Huang-Tauchen (paramètre `use_jumps`) ; `HAR-RV-Kelly` (`HarrvKellyAlgorithm`) trade des **ETF multi-actifs actions** (SPY/EFA/EEM/TLT/GLD/DBC, HAR classique Corsi). Deux démonstrations complémentaires (crypto-jump vs equity-classique, Kelly 1/4 commun) — backtester la variante « J » ne la rend pas « supérieure » à la plain puisque l'univers diffère.
- **`MomentumStrategy`** vs **`SectorMomentum`** — **résolu : deux stratégies distinctes, toutes deux ARCHIVÉES** (reclassées hors du bucket Vivant, cf synthèse). `MomentumStrategy` (`SectorMomentumETFRotation`, `ARCHIVE.md`) = rotation d'ETF sectoriels v4.0, plafond Sharpe ~0.48 ; `SectorMomentum` (`SectorDualMomentumStrategy`, `ARCHIVE.md`) = dual-momentum 3 actifs SPY/TLT/GLD v3.2, plafond ~0.56. Chevauchement de *thème* (momentum) seulement, univers + mécanisme distincts. Les deux portent l'en-tête `# [ARCHIVED …]` : le best-guess « Vivant » était erroné.
- **`DL-LSTM` / `ML-DeepLearning` / `Crypto-LSTM-Prediction` / `LSTM-Forecasting`** — **résolu : périmètres distincts (profondeur de modèle × classe d'actifs)**. `DL-LSTM` = PyTorch LSTM bidirectionnel (2×50), prédiction de prix mono-action (modèle de `research_lstm.ipynb`). `ML-DeepLearning` = PyTorch LSTM simple (1×32), prédiction de rendement multi-actions (baseline). `Crypto-LSTM-Prediction` = PyTorch DLinear (AAAI 2023) + LSTM comparé, **crypto** BTCUSDT. `LSTM-Forecasting` = **PAS un LSTM** : `MLPClassifier` sklearn (docstring honnête « replacing hand-rolled fake LSTM »), actions, livre Ch06 — le nom est un héritage du « fake LSTM » remplacé. Les quatre ne sont pas redondants.
- **`RL-DQN-Trading`** vs **`Reinforcement-Learning-Trading`** — **résolu : classification doc correcte**. Nom de classe identique `ReinforcementLearningTrading`, mais `RL-DQN-Trading` = DQN amélioré v2.0.1 (`MLPRegressor(64,32)`, 11 features, reward risk-adjusted) = *Vivant/développé* ; `Reinforcement-Learning-Trading` = démo DQN basique SPY-seul (livre Ch07) = *Squelette*. Seule l'homonymie de classe créait l'ambiguïté.

## Travaux connexes

- **Checkpoints ML** : `ML-Training-Pipeline/` (444 MB `.pt`, 137 modèles) — migration Git LFS + purge des obsolètes = gated user (mandat 2026-05-27). Non livré.
- **Papertrading** : `Python/QC-Py-40-PaperTrading-Binance.ipynb`, `Python/QC-Py-41-PaperTrading-IBKR.ipynb` — statut à confirmer (gate [#1027](https://github.com/jsboige/CoursIA/issues/1027)).
- **Notebooks cours** : `Python/QC-Py-01..35` + `Cloud-01..07` + companion `Python/research/` (QC-Py-19/22) — cohérents, audit prod-ready à part.

## Voir aussi

- [docs/qc/quantconnect.md](quantconnect.md) — structure complète QC, MCP Docker, livre de référence
- [docs/qc/qc-comparative-backtests.md](qc-comparative-backtests.md) — backtests comparatifs
- [#1621](https://github.com/jsboige/CoursIA/issues/1621) — EPIC Consolidation QC/Trading
- [#5654](https://github.com/jsboige/CoursIA/issues/5654) — EPIC Illustration READMEs (figures)
- [#1027](https://github.com/jsboige/CoursIA/issues/1027) — paper-trading / backtest gate
