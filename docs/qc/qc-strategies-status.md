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
| Vérifié (tranche 14, backtests QC Cloud MCP) | 4 | cohorte DL Chronos Foundation / Régime Switching / ML Trend Scanning — **0 edge significative** (PSR max 13.79 %), 4 Needs-improvement |
| Vivant (best-guess, non vérifié) | 52 | algo `QCAlgorithm` complet, aucun signal négatif — TODO backtest pour confirmer (2 reclassés Archivé firsthand c.570) |
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

#### Vérifié (tranche 14, backtests QC Cloud via MCP) (4)

> **Périmètre tranche 14** : 4 stratégies best-guess du bucket « Vivant » promues via lecture directe
> des backtests QC Cloud existants via MCP `qc-mcp-lite` (`read_backtest`). **0 QCC dépensé**
> (lecture seule de backtests déjà réalisés). Cohorte **DL Foundation Model (Chronos) / Régime
> Switching / ML Trend Scanning** (4 sous-familles distinctes des tranches 7 ML Trend/FeatureEng/
> SVM-Wavelet, 8 Trend+Regime+Vol risk, 9 Composite+Options+Vol/Momentum, 10 DL/LSTM/Temporal-CNN,
> 11 Crypto BTC + IBKR-Binance-Hybrid, 12 ML NLP + RL, 13 ML Classification/Clustering/Hybrid).
> Métriques pleine période in-sample (non walk-forward OOS). **0 edge significative cohorte** :
> PSR max 13.79 % (`Chronos-Foundation-Forecasting` post-#2801 SMA200 regime threshold 0.02),
> toutes < 50 %. Confirme pour cette cohorte DL Foundation / Régime Switching / ML Trend Scanning
> ce que les tranches 7-13 confirmaient : les backtests in-sample pleine période **ne valident
> aucun edge** sur la cohorte. Walk-forward multi-seed OOS requis avant toute promotion production.

| Stratégie | Chemin | Type | Statut | Métriques backtest (période ; Sharpe ; CAGR ; MaxDD ; PSR ; Net Profit) |
|-----------|--------|------|--------|------------------------------------------------------------------------|
| `RegimeSwitching` | `projects/RegimeSwitching/` | Régime (Markov switching) | **Needs-improvement** | 4642 j. (long record cohorte, projet 1630-post2801 verify) ; Sharpe 0.581 (max cohorte) ; CAGR 12.29 % ; MaxDD 33.0 % ; PSR 7.04 % ; NP 750.7 % ($656 416) — record durée tradeable, Sharpe max cohorte, PSR sous 50 % |
| `ML-Trend-Scanning` | `projects/ML-Trend-Scanning/` | ML trend | **Needs-improvement** | 2878 j. (post-#2801 verify) ; Sharpe 0.328 ; CAGR 7.09 % ; MaxDD 29.4 % ; PSR 7.84 % ; NP 119.0 % ($115 983) — profile trend modéré, edge statistique non significative |
| `Chronos-Foundation-Forecasting` | `projects/Chronos-Foundation-Forecasting/` | DL (Chronos foundation) | **Needs-improvement** | période projet 29443479 batch 4 (tradeableDates=0 anomalie champ MCP, ~2018–2025 aligned) ; Sharpe 0.277 ; CAGR 7.23 % ; **MaxDD 13.5 % (min cohorte)** ; **PSR 13.79 % (max cohorte)** ; NP 63.0 % ($62 626) — meilleur MaxDD cohorte + meilleur PSR, edge statistique non confirmée |
| `ML-Chronos-Foundation` | `projects/ML-Chronos-Foundation/` | DL (Chronos) | **Needs-improvement** | 2766 j. (projet 29936072 Ex18-Chronos-Foundation batch 4) ; Sharpe 0.253 ; CAGR 6.28 % ; MaxDD 22.4 % ; PSR 3.12 % (min cohorte) ; NP 95.5 % ($94 994) — Sharpe min cohorte, PSR quasi-nul |

**Verdict honnête : 0 edge cohorte**. PSR max 13.79 % (`Chronos-Foundation-Forecasting`), aucune > 50 %.
Observations pédagogiques :

- **`RegimeSwitching` (Sharpe 0.581 / PSR 7.04 %)** : **meilleur Sharpe cohorte** mais PSR 7.04 % = edge statistique quasi-nulle. Pattern « Sharpe décent mais PSR ne suit pas » récurrent ML/DL post-2020. Record durée tradeable (4642 j.) = robustesse long-terme du post-#2801 verify (projet 1630-post2801).
- **`Chronos-Foundation-Forecasting` (Sharpe 0.277 / PSR 13.79 %)** : **PSR max cohorte** + **MaxDD min cohorte 13.5 %** = profil drawdown-containment le plus discipliné. MAIS PSR 13.79 % reste < 50 %, edge statistique non confirmée. Foundation model Chronos = SOTA 2024-2025 (Amazon) pour forecasting zero-shot, intégration QC Cloud prometteuse mais validation OOS requise.
- **`ML-Chronos-Foundation` (Sharpe 0.253 / PSR 3.12 %)** vs **`Chronos-Foundation-Forecasting` (0.277 / 13.79 %)** : **2 stratégies Chronos**, profil proche (Sharpe ~0.27, NP ~80-95 %), mais **`Chronos-Foundation-Forecasting` 4.4× meilleur PSR** = feature engineering spécifique (post-#2801 SMA200 regime threshold 0.02) fait la différence malgré Sharpe quasi-identique. Variante HandsOn Ex09 (sans SMA200 regime filter) sous-performe statistiquement.
- **`ML-Trend-Scanning` (Sharpe 0.328 / PSR 7.84 %)** : profile trend scanning (ML supervisé sur trends actions) = médian cohorte. PSR 7.84 % = edge non significative. post-#2801 verify confirme stabilité long-terme (2878 j. tradeable).

#### Vivant (best-guess, non vérifié) (52)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `BTC-ML` | `projects/BTC-ML/` | ML Crypto | Vivant | main.py: class MyEnhancedCryptoMlAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `CSharp-BTC-EMA-Cross` | `projects/CSharp-BTC-EMA-Cross/` | Trend EMA (C#) | Vivant | Main.cs: class BtcEmaCrossDaily1Algorithm : QCAlgorithm + research_robustness.ipynb |
| `CSharp-BTC-MACD-ADX` | `projects/CSharp-BTC-MACD-ADX/` | Trend MACD/ADX (C#) | Vivant | Main.cs: class BtcMacdAdxDaily1Algorithm : QCAlgorithm + Research.ipynb + RESEARCH_FINDINGS.md |
| `CSharp-CTG-Momentum` | `projects/CSharp-CTG-Momentum/` | Momentum (C#, multi-fichiers) | Vivant | Main.cs: class StocksOnTheMoveAlgorithm : QCAlgorithm + 4 indicateurs .cs + research_robustness.ipynb |
| `Chronos-Foundation-Forecasting` | `projects/Chronos-Foundation-Forecasting/` | DL (Chronos foundation) | **Vérifié tranche 14** | main.py: class ChronosFoundationForecasting(QCAlgorithm) + research.ipynb |
| `Clustering-Fundamentals-ML` | `projects/Clustering-Fundamentals-ML/` | ML non supervisé | Vivant | main.py: class ClusteringFundamentalsAlgorithm(QCAlgorithm) |
| `Crypto-LSTM-Prediction` | `projects/Crypto-LSTM-Prediction/` | DL (LSTM) Crypto | Vivant | main.py: class CryptoLSTMPredictionAlgorithm(QCAlgorithm) + research.ipynb |
| `Crypto-MultiCanal` | `projects/Crypto-MultiCanal/` | Crypto multi-signal | Vivant | main.py: class CryptoMultiChannelAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `DL-LSTM` | `projects/DL-LSTM/` | DL (LSTM) | Vivant | main.py: class LSTMModel(nn.Module) + algo QCAlgorithm + quantbook.ipynb |
| `Dividend-Harvesting-ML` | `projects/Dividend-Harvesting-ML/` | ML dividendes | Vivant | main.py: class DividendHarvestingAlgorithm(QCAlgorithm) |
| `EMA-Cross-Alpha` | `projects/EMA-Cross-Alpha/` | Trend EMA | Vivant | main.py: class EMACrossAlphaAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `EMA-Cross-Stocks` | `projects/EMA-Cross-Stocks/` | Trend EMA | Vivant | main.py: class EMACrossStocksAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `Framework_Composite_EMATrend` | `projects/Framework_Composite_EMATrend/` | Composite | Vivant | main.py: class FrameworkCompositeEMATrend(QCAlgorithm) + quantbook.ipynb |
| `Framework_Composite_MomentumRegime` | `projects/Framework_Composite_MomentumRegime/` | Composite | Vivant | main.py: class FrameworkCompositeMomentumRegime(QCAlgorithm) + quantbook.ipynb |
| `Framework_Composite_TrendWeather` | `projects/Framework_Composite_TrendWeather/` | Composite | Vivant | main.py: class FrameworkCompositeStrategy(QCAlgorithm) + quantbook.ipynb |
| `Gaussian-Direction-Classifier` | `projects/Gaussian-Direction-Classifier/` | ML classification | Vivant | main.py: class GaussianDirectionClassifier(QCAlgorithm) + research.ipynb |
| `HAR-RV-J-Kelly` | `projects/HAR-RV-J-Kelly/` | Volatility / Kelly | Vivant | main.py: class HarrvjKellyAlgorithm(QCAlgorithm) |
| `LSTM-Forecasting` | `projects/LSTM-Forecasting/` | DL (LSTM) | Vivant | main.py: class LSTMForecasting(QCAlgorithm) + research.ipynb |
| `ML-Chronos-Foundation` | `projects/ML-Chronos-Foundation/` | DL (Chronos) | **Vérifié tranche 14** | main.py: class ChronosFoundationAlgorithm(QCAlgorithm) |
| `ML-Classification` | `projects/ML-Classification/` | ML supervisé | Vivant | main.py: class MLClassificationAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-DeepLearning` | `projects/ML-DeepLearning/` | DL | Vivant | main.py: class SimpleLSTM(nn.Module) + algo QCAlgorithm + quantbook.ipynb |
| `ML-EnhancedPairs` | `projects/ML-EnhancedPairs/` | ML pairs | Vivant | main.py: class MLEnhancedPairsAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Ensemble` | `projects/ML-Ensemble/` | ML ensemble | Vivant | main.py: class MLEnsembleAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-FX-SVM-Wavelet` | `projects/ML-FX-SVM-Wavelet/` | ML FX (SVM/Wavelet) | Vivant | main.py: class SVMWaveletForecastingAlgorithm(QCAlgorithm) (helper SVMWavelet en amont) |
| `ML-FeatureEngineering` | `projects/ML-FeatureEngineering/` | ML features | Vivant | main.py: class MLFeatureEngineeringAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-FinBERT-Sentiment` | `projects/ML-FinBERT-Sentiment/` | ML NLP (FinBERT) | Vivant | main.py: class FinBERTSentimentAlgorithm(QCAlgorithm) + research.ipynb |
| `ML-Gaussian-Classifier` | `projects/ML-Gaussian-Classifier/` | ML classification | Vivant | main.py: class GaussianNaiveBayesAlgorithm(QCAlgorithm) |
| `ML-HeadShoulders-CNN` | `projects/ML-HeadShoulders-CNN/` | DL (CNN patterns) | Vivant | main.py: class CNNPatternDetectionAlgorithm(QCAlgorithm) + research.ipynb |
| `ML-LLM-Summarization` | `projects/ML-LLM-Summarization/` | ML NLP (LLM) | Vivant | main.py: class LLMNewsSentimentAlgorithm(QCAlgorithm) |
| `ML-Regression` | `projects/ML-Regression/` | ML supervisé | Vivant | main.py: class MLRegressionAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Reversion-Trending` | `projects/ML-Reversion-Trending/` | ML classification | Vivant | main.py: class MLReversionTrendingClassifier(QCAlgorithm) + research.ipynb |
| `ML-SVM` | `projects/ML-SVM/` | ML supervisé (SVM) | Vivant | main.py: class MLSVMAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Temporal-CNN` | `projects/ML-Temporal-CNN/` | DL (Temporal CNN) | Vivant | main.py: class TemporalCNNPredictionAlgorithm(QCAlgorithm) |
| `ML-TextClassification` | `projects/ML-TextClassification/` | ML NLP | Vivant | main.py: class MLTextClassificationAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `ML-Trend-Scanning` | `projects/ML-Trend-Scanning/` | ML trend | **Vérifié tranche 14** | main.py: class MLTrendScanning(QCAlgorithm) |
| `Option-Wheel` | `projects/Option-Wheel/` | Options (wheel) | Vivant | main.py: class WheelStrategyAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `Options-VGT` | `projects/Options-VGT/` | Options (covered call) | Vivant | main.py: class GainStrategy(QCAlgorithm) + quantbook.ipynb — nom classe vague (cf. incertitudes) |
| `OptionsIncome` | `projects/OptionsIncome/` | Options (covered call) | Vivant | main.py: class CoveredCallStrategy(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `PCA-StatArbitrage` | `projects/PCA-StatArbitrage/` | StatArb (PCA) | Vivant | main.py: class PCAStatArbitrageAlgorithm(QCAlgorithm) |
| `Portfolio-IBKR-Coinbase-Hybrid` | `projects/Portfolio-IBKR-Coinbase-Hybrid/` | Hybrid crypto/broker | Vivant | main.py: class PortfolioHybridIBKRCoinbase(QCAlgorithm) (helpers FeeModel/Slippage en amont) + research.ipynb + quantbook.ipynb |
| `Positive-Negative-Splits-ML` | `projects/Positive-Negative-Splits-ML/` | ML (stock splits) | Vivant | main.py: class SplitEventsAlgorithm(QCAlgorithm) |
| `PuppiesOfTheDow-QC` | `projects/PuppiesOfTheDow-QC/` | Value (Dogs of the Dow) | Vivant | main.py: class PuppiesOfTheDow(QCAlgorithm) |
| `RL-DQN-Trading` | `projects/RL-DQN-Trading/` | RL (DQN) | Vivant | main.py: class ReinforcementLearningTrading(QCAlgorithm) |
| `RegimeSwitching` | `projects/RegimeSwitching/` | Régime | **Vérifié tranche 14** | main.py: class RegimeSwitching(QCAlgorithm) + quantbook.ipynb |
| `SVM-Wavelet-Forecasting` | `projects/SVM-Wavelet-Forecasting/` | ML (SVM/Wavelet) | Vivant | main.py: class SVMWaveletForecasting(QCAlgorithm) |
| `Sector-ML-Classification` | `projects/Sector-ML-Classification/` | ML sectoriel | Vivant | main.py: class SectorMLClassificationAlgorithm(QCAlgorithm) + research.ipynb |
| `Stoploss-Volatility-ML` | `projects/Stoploss-Volatility-ML/` | ML risk | Vivant | main.py: class StoplossVolatilityMLAlgorithm(QCAlgorithm) + research.ipynb |
| `Temporal-CNN-Prediction` | `projects/Temporal-CNN-Prediction/` | DL (Temporal CNN) | Vivant | main.py: class TemporalCNNPrediction(QCAlgorithm) + research.ipynb |
| `TermStructureCommodities-QC` | `projects/TermStructureCommodities-QC/` | Commodities (term structure) | Vivant | main.py: class CommodityTermStructureAlgorithm(QCAlgorithm) |
| `Trend-Following` | `projects/Trend-Following/` | Trend (AQR) | Vivant | main.py: class TrendFollowingAQR(QCAlgorithm) + quantbook.ipynb |
| `TrendFilteredMeanReversion` | `projects/TrendFilteredMeanReversion/` | Mean reversion filtré | Vivant | main.py: class TrendFilteredMeanReversion(QCAlgorithm) + research.ipynb |
| `TrendStocks-Alpha` | `projects/TrendStocks-Alpha/` | Trend actions | Vivant | main.py: class TrendStocksAlphaAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `TrendStocksLite` | `projects/TrendStocksLite/` | Trend actions (lite) | Vivant | main.py: class TrendStocksLite(QCAlgorithm) + research.ipynb |
| `VIX-TermStructure` | `projects/VIX-TermStructure/` | Vol (VIX term) | Vivant | main.py: class VIXTermStructureStrategy(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `VolTarget-Momentum` | `projects/VolTarget-Momentum/` | Vol / Momentum | Vivant | main.py: class VolTargetMomentum(QCAlgorithm) |
| `composite-c1-multiasset` | `projects/composite-c1-multiasset/` | Composite multi-actifs | Vivant | main.py: class CompositeC1MultiAssetRotation(QCAlgorithm) |

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
