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
| Vivant (best-guess, non vérifié) | 82 | algo `QCAlgorithm` complet, aucun signal négatif — TODO backtest pour confirmer |
| Vivant (README revendique vérifié) | 1 | README revendique un backtest QC Cloud — à recroiser firsthand |
| Recherche uniquement (pas d'algo déployable) | 5 | notebook de recherche sans `main.py` déployable |
| Stub (code non créé) | 2 | README : exercice planifié, fichiers de code non créés |
| Squelette/template (pas de stratégie active) | 2 | README : template/skeleton, pas de stratégie active |
| Contre-exemple pédagogique (BROKEN) | 2 | README : intentionnellement BROKEN (pédagogie) |
| Archivé / superseded | 1 | README : archived / plafond structurel documenté |
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

#### Vivant (best-guess, non vérifié) (82)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `Adaptive-Conformal-Risk` | `projects/Adaptive-Conformal-Risk/` | Vol / Risk adaptatif | Vivant | main.py: class AdaptiveConformalRisk(QCAlgorithm) ; aucun notebook compagnon |
| `AdaptiveAssetAllocation` | `projects/AdaptiveAssetAllocation/` | Multi-asset allocation | Vivant | main.py: class AdaptiveAssetAllocation(QCAlgorithm) + quantbook.ipynb |
| `AssetClassMomentum-QC` | `projects/AssetClassMomentum-QC/` | Cross-asset momentum | Vivant | main.py: class AssetClassMomentumAlgorithm(QCAlgorithm) |
| `BTC-ML` | `projects/BTC-ML/` | ML Crypto | Vivant | main.py: class MyEnhancedCryptoMlAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `BlackLitterman-Momentum` | `projects/BlackLitterman-Momentum/` | Factor / Momentum | Vivant | main.py: class BlackLittermanMomentum(QCAlgorithm) |
| `CSharp-BTC-EMA-Cross` | `projects/CSharp-BTC-EMA-Cross/` | Trend EMA (C#) | Vivant | Main.cs: class BtcEmaCrossDaily1Algorithm : QCAlgorithm + research_robustness.ipynb |
| `CSharp-BTC-MACD-ADX` | `projects/CSharp-BTC-MACD-ADX/` | Trend MACD/ADX (C#) | Vivant | Main.cs: class BtcMacdAdxDaily1Algorithm : QCAlgorithm + Research.ipynb + RESEARCH_FINDINGS.md |
| `CSharp-CTG-Momentum` | `projects/CSharp-CTG-Momentum/` | Momentum (C#, multi-fichiers) | Vivant | Main.cs: class StocksOnTheMoveAlgorithm : QCAlgorithm + 4 indicateurs .cs + research_robustness.ipynb |
| `CausalEventAlpha` | `projects/CausalEventAlpha/` | Causal alpha | Vivant | main.py: class CausalEventAlphaAlgorithm(QCAlgorithm) ; aucun notebook compagnon |
| `Chronos-Foundation-Forecasting` | `projects/Chronos-Foundation-Forecasting/` | DL (Chronos foundation) | Vivant | main.py: class ChronosFoundationForecasting(QCAlgorithm) + research.ipynb |
| `Cloud-MeanReversion-Sectors` | `projects/Cloud-MeanReversion-Sectors/` | Mean reversion secteurs | Vivant | main.py: class CloudMeanReversionSectors(QCAlgorithm) |
| `Cloud-SectorRotation-Momentum` | `projects/Cloud-SectorRotation-Momentum/` | Rotation sectorielle | Vivant | main.py: class SectorRotationMomentum(QCAlgorithm) |
| `Cloud-VolTargeting` | `projects/Cloud-VolTargeting/` | Vol targeting | Vivant | main.py: class VolTargetingAlgorithm(QCAlgorithm) |
| `Clustering-Fundamentals-ML` | `projects/Clustering-Fundamentals-ML/` | ML non supervisé | Vivant | main.py: class ClusteringFundamentalsAlgorithm(QCAlgorithm) |
| `Crypto-LSTM-Prediction` | `projects/Crypto-LSTM-Prediction/` | DL (LSTM) Crypto | Vivant | main.py: class CryptoLSTMPredictionAlgorithm(QCAlgorithm) + research.ipynb |
| `Crypto-MultiCanal` | `projects/Crypto-MultiCanal/` | Crypto multi-signal | Vivant | main.py: class CryptoMultiChannelAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `DL-LSTM` | `projects/DL-LSTM/` | DL (LSTM) | Vivant | main.py: class LSTMModel(nn.Module) + algo QCAlgorithm + quantbook.ipynb |
| `Dividend-Harvesting-ML` | `projects/Dividend-Harvesting-ML/` | ML dividendes | Vivant | main.py: class DividendHarvestingAlgorithm(QCAlgorithm) |
| `Dynamic-Options-Wheel` | `projects/Dynamic-Options-Wheel/` | Options (wheel) | Vivant | main.py: class DynamicOptionsWheel(QCAlgorithm) |
| `EMA-Cross-Alpha` | `projects/EMA-Cross-Alpha/` | Trend EMA | Vivant | main.py: class EMACrossAlphaAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `EMA-Cross-Stocks` | `projects/EMA-Cross-Stocks/` | Trend EMA | Vivant | main.py: class EMACrossStocksAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `FamaFrench` | `projects/FamaFrench/` | Factor rotation | Vivant | main.py: class FactorETFRotation(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `Framework_Composite_EMATrend` | `projects/Framework_Composite_EMATrend/` | Composite | Vivant | main.py: class FrameworkCompositeEMATrend(QCAlgorithm) + quantbook.ipynb |
| `Framework_Composite_MomentumRegime` | `projects/Framework_Composite_MomentumRegime/` | Composite | Vivant | main.py: class FrameworkCompositeMomentumRegime(QCAlgorithm) + quantbook.ipynb |
| `Framework_Composite_TrendWeather` | `projects/Framework_Composite_TrendWeather/` | Composite | Vivant | main.py: class FrameworkCompositeStrategy(QCAlgorithm) + quantbook.ipynb |
| `FuturesTrend` | `projects/FuturesTrend/` | Trend futures | Vivant | main.py: class FuturesTrendFollowing(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `Gaussian-Direction-Classifier` | `projects/Gaussian-Direction-Classifier/` | ML classification | Vivant | main.py: class GaussianDirectionClassifier(QCAlgorithm) + research.ipynb |
| `GlobalMacro-Regime` | `projects/GlobalMacro-Regime/` | Macro / Régime | Vivant | main.py: class GlobalMacroRegime(QCAlgorithm) |
| `HAR-RV-J-Kelly` | `projects/HAR-RV-J-Kelly/` | Volatility / Kelly | Vivant | main.py: class HarrvjKellyAlgorithm(QCAlgorithm) |
| `HAR-RV-Kelly` | `projects/HAR-RV-Kelly/` | Volatility / Kelly | Vivant | main.py: class HarrvKellyAlgorithm(QCAlgorithm) + research.ipynb |
| `HMM-KMeans-Voting` | `projects/HMM-KMeans-Voting/` | Régime (HMM) | Vivant | main.py: class HMMKMeansVoting(QCAlgorithm) (helpers KMeans/GaussianHMM en amont) |
| `HighBookToMarketFScore-QC` | `projects/HighBookToMarketFScore-QC/` | Factor (Piotroski) | Vivant | main.py: class PiotroskiScoreAlgorithm(QCAlgorithm) |
| `InverseVolatility-Rank` | `projects/InverseVolatility-Rank/` | Risk-parity inversé | Vivant | main.py: class InverseVolatilityRankAlgorithm(QCAlgorithm) + research.ipynb |
| `LSTM-Forecasting` | `projects/LSTM-Forecasting/` | DL (LSTM) | Vivant | main.py: class LSTMForecasting(QCAlgorithm) + research.ipynb |
| `LeveragedETFMomentum-QC` | `projects/LeveragedETFMomentum-QC/` | Rotation sectorielle | Vivant | main.py: class ConditionalSectorRotation(QCAlgorithm) — nom classe ≠ nom dossier (cf. incertitudes) |
| `ML-Chronos-Foundation` | `projects/ML-Chronos-Foundation/` | DL (Chronos) | Vivant | main.py: class ChronosFoundationAlgorithm(QCAlgorithm) |
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
| `ML-Trend-Scanning` | `projects/ML-Trend-Scanning/` | ML trend | Vivant | main.py: class MLTrendScanning(QCAlgorithm) |
| `MacroFactorRotation-QC` | `projects/MacroFactorRotation-QC/` | Rotation actions/obligations | Vivant | main.py: class AIStocksBondsRotationAlgorithm(QCAlgorithm) — nom classe ≠ nom dossier (cf. incertitudes) |
| `Markov-Regime-Detection` | `projects/Markov-Regime-Detection/` | Régime (Markov) | Vivant | main.py: class MarkovRegimeDetection(QCAlgorithm) |
| `MeanReversion` | `projects/MeanReversion/` | Mean reversion | Vivant | main.py: class ShortTermMeanReversion(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `MomentumRegime-AdaptiveWeights` | `projects/MomentumRegime-AdaptiveWeights/` | Momentum / Régime | Vivant | main.py: class MomentumRegimeAdaptiveWeights(QCAlgorithm) |
| `MomentumStrategy` | `projects/MomentumStrategy/` | Sector momentum ETF | Vivant | main.py: class SectorMomentumETFRotation(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `Option-Wheel` | `projects/Option-Wheel/` | Options (wheel) | Vivant | main.py: class WheelStrategyAlgorithm(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `Options-VGT` | `projects/Options-VGT/` | Options (covered call) | Vivant | main.py: class GainStrategy(QCAlgorithm) + quantbook.ipynb — nom classe vague (cf. incertitudes) |
| `OptionsIncome` | `projects/OptionsIncome/` | Options (covered call) | Vivant | main.py: class CoveredCallStrategy(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `PCA-StatArbitrage` | `projects/PCA-StatArbitrage/` | StatArb (PCA) | Vivant | main.py: class PCAStatArbitrageAlgorithm(QCAlgorithm) |
| `Portfolio-IBKR-Coinbase-Hybrid` | `projects/Portfolio-IBKR-Coinbase-Hybrid/` | Hybrid crypto/broker | Vivant | main.py: class PortfolioHybridIBKRCoinbase(QCAlgorithm) (helpers FeeModel/Slippage en amont) + research.ipynb + quantbook.ipynb |
| `Positive-Negative-Splits-ML` | `projects/Positive-Negative-Splits-ML/` | ML (stock splits) | Vivant | main.py: class SplitEventsAlgorithm(QCAlgorithm) |
| `PuppiesOfTheDow-QC` | `projects/PuppiesOfTheDow-QC/` | Value (Dogs of the Dow) | Vivant | main.py: class PuppiesOfTheDow(QCAlgorithm) |
| `RL-DQN-Trading` | `projects/RL-DQN-Trading/` | RL (DQN) | Vivant | main.py: class ReinforcementLearningTrading(QCAlgorithm) |
| `RegimeSwitching` | `projects/RegimeSwitching/` | Régime | Vivant | main.py: class RegimeSwitching(QCAlgorithm) + quantbook.ipynb |
| `SVM-Wavelet-Forecasting` | `projects/SVM-Wavelet-Forecasting/` | ML (SVM/Wavelet) | Vivant | main.py: class SVMWaveletForecasting(QCAlgorithm) |
| `Sector-ML-Classification` | `projects/Sector-ML-Classification/` | ML sectoriel | Vivant | main.py: class SectorMLClassificationAlgorithm(QCAlgorithm) + research.ipynb |
| `SectorMomentum` | `projects/SectorMomentum/` | Sector dual momentum | Vivant | main.py: class SectorDualMomentumStrategy(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `Stoploss-Volatility-ML` | `projects/Stoploss-Volatility-ML/` | ML risk | Vivant | main.py: class StoplossVolatilityMLAlgorithm(QCAlgorithm) + research.ipynb |
| `Temporal-CNN-Prediction` | `projects/Temporal-CNN-Prediction/` | DL (Temporal CNN) | Vivant | main.py: class TemporalCNNPrediction(QCAlgorithm) + research.ipynb |
| `TermStructureCommodities-QC` | `projects/TermStructureCommodities-QC/` | Commodities (term structure) | Vivant | main.py: class CommodityTermStructureAlgorithm(QCAlgorithm) |
| `Trend-Following` | `projects/Trend-Following/` | Trend (AQR) | Vivant | main.py: class TrendFollowingAQR(QCAlgorithm) + quantbook.ipynb |
| `TrendFilteredMeanReversion` | `projects/TrendFilteredMeanReversion/` | Mean reversion filtré | Vivant | main.py: class TrendFilteredMeanReversion(QCAlgorithm) + research.ipynb |
| `TrendStocks-Alpha` | `projects/TrendStocks-Alpha/` | Trend actions | Vivant | main.py: class TrendStocksAlphaAlgorithm(QCAlgorithm) + quantbook.ipynb |
| `TrendStocksLite` | `projects/TrendStocksLite/` | Trend actions (lite) | Vivant | main.py: class TrendStocksLite(QCAlgorithm) + research.ipynb |
| `VIX-TermStructure` | `projects/VIX-TermStructure/` | Vol (VIX term) | Vivant | main.py: class VIXTermStructureStrategy(QCAlgorithm) + research.ipynb + quantbook.ipynb |
| `Vol-Ensemble-Conservative` | `projects/Vol-Ensemble-Conservative/` | Vol ensemble | Vivant | main.py: class VolEnsembleConservativeAlgorithm(QCAlgorithm) + research.ipynb |
| `Vol-GARCH-Target` | `projects/Vol-GARCH-Target/` | Vol (GARCH) | Vivant | main.py: class GarchVolTargetAlgorithm(QCAlgorithm) + research.ipynb |
| `VolTarget-Momentum` | `projects/VolTarget-Momentum/` | Vol / Momentum | Vivant | main.py: class VolTargetMomentum(QCAlgorithm) |
| `composite-c1-multiasset` | `projects/composite-c1-multiasset/` | Composite multi-actifs | Vivant | main.py: class CompositeC1MultiAssetRotation(QCAlgorithm) |
| `composite-c2-equityfactor` | `projects/composite-c2-equityfactor/` | Composite equity/factor | Vivant | main.py: class CompositeC2EquityFactor(QCAlgorithm) |

#### Vivant (README revendique vérifié) (1)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `Multi-Layer-EMA` | `projects/Multi-Layer-EMA/` | Crypto multi-indicateurs | Vivant (revendiqué) | main.py: class OptimizedCryptoAlgorithm(QCAlgorithm) + research.ipynb + README revendique « Verified on QC Cloud (project 28433748) » |

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

#### Archivé / superseded (1)

| Stratégie | Chemin | Type | Statut (best-guess) | Signal source (fichier/ligne ou nom) |
|-----------|--------|------|---------------------|--------------------------------------|
| `TurnOfMonth` | `projects/TurnOfMonth/` | Calendrier (archivé) | Archivé | README : « Status: ARCHIVED (Sharpe ceiling ~0.13) » + main.py: class TurnOfMonthEffect(QCAlgorithm) |

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

### Incertitudes prioritaires (à spot-checker)

Entrées où le statut *best-guess* est le plus fragile — divergence nom de dossier / nom de 
classe, revendication de vérification non recoupée, ou doublons suspects. Cibles privilégiées 
pour un backtest dédié (scope RECOVERABLE-MACHINE) :

- **`Multi-Layer-EMA`** — README revendique « Verified on QC Cloud (project 28433748) » mais la classe est `OptimizedCryptoAlgorithm` (le README lui-même prévient « NOT a simple multi-layer EMA »). Vérification à recroiser firsthand.
- **`LeveragedETFMomentum-QC`** — classe `ConditionalSectorRotation` : divergence totale avec le nom de dossier « Leveraged ETF Momentum ». Contenu réel à confirmer.
- **`MacroFactorRotation-QC`** — classe `AIStocksBondsRotationAlgorithm` : divergence avec le nom de dossier.
- **`FamaFrench`** — classe `FactorETFRotation` : la sémantique Fama-French n'est pas évidente depuis le nom de classe.
- **`Options-VGT`** — classe `GainStrategy` (nom vague), aucun notebook de recherche compagnon.
- **`HAR-RV-J-Kelly`** vs **`HAR-RV-Kelly`** — deux dossiers quasi-identiques (variante « J » = jump) ; l'un supersède probablement l'autre (à clarifier).
- **`MomentumStrategy`** (classe `SectorMomentumETFRotation`) vs **`SectorMomentum`** (classe `SectorDualMomentumStrategy`) — chevauchement sector-momentum suspect (doublon partiel ?).
- **`DL-LSTM` / `LSTM-Forecasting` / `Crypto-LSTM-Prediction` / `ML-DeepLearning`** — quatre dossiers LSTM ; périmètres respectifs à clarifier pour éviter la redondance.
- **`RL-DQN-Trading`** (classe `ReinforcementLearningTrading`) vs **`Reinforcement-Learning-Trading`** (squelette, même nom de classe) — l'un est squelette, mais le nom identique crée une ambiguïté.

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
