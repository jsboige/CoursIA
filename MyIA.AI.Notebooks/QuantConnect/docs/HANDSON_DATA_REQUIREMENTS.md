# HandsOn AI Trading - Data Requirements

**Source**: [QuantConnect/HandsOnAITradingBook](https://github.com/QuantConnect/HandsOnAITradingBook)

Ce document documente les prérequis de données pour les exemples du livre qui ne peuvent pas être backtestés directement dans QuantConnect Cloud sans données externes.

---

## Exemples nécessitant des données externes

### Ex16 - LLM Summarization of Tiingo News

**Concept**: Utiliser un LLM pour résumer les news financières et extraire du sentiment.

**Prérequis**:
- **API Tiingo News**: Nécessite une clé API Tiingo Premium
- **LLM**: OpenAI GPT-4 ou Anthropic Claude (nécessite API key)
- **Données**: News textuelles de Tiingo (pas disponible dans QC standard)

**Pourquoi pas de backtest direct**: Les news Tiingo ne sont pas disponibles dans QuantConnect Cloud. L'exemple nécessite un téléchargement externe de données.

**Alternative QC**: Utiliser `Fundamental` ou `News` events dans QC avec des sources alternatives.

---

### Ex17 - Head Shoulders Pattern Matching with CNN

**Concept**: CNN pour détecter des patterns chartistes (Tête-Épaules) dans les prix.

**Prérequis**:
- **Images de patterns**: Dataset d'images de patterns chartistes annotés
- **Modèle CNN pré-entraîné**: Nécessite un modèle externe ou entraînement sur dataset externe
- **Données**: Séries temporelles converties en images

**Pourquoi pas de backtest direct**: L'exemple utilise des données d'images externes pour l'entraînement du CNN.

**Alternative QC**: Implémenter une détection de Tête-Épaules algorithmique avec des indicateurs techniques standard.

---

### Ex19 - FinBERT Model

**Concept**: Utiliser FinBERT (BERT fine-tuned pour la finance) pour analyser du texte financier.

**Prérequis**:
- **Modèle FinBERT**: Hugging Face `ProsusAI/finbert`
- **Infrastructure**: GPU pour inference (modèle BERT ~400MB)
- **Données**: Textes financières (news, rapports)

**Pourquoi pas de backtest direct**: FinBERT nécessite une infrastructure GPU externe et des données textuelles non disponibles dans QC.

**Alternative QC**: Utiliser un modèle de sentiment plus simple basé sur des indicateurs techniques.

---

## Exemples backtestables sans données externes

### Ex01-04 (Section 05 - Model Choice)
- Linear/Polynomial/Lasso/Ridge Regression
- Decision Tree Regression
- Support Vector Machines
- Random Forest
- Logistic Regression

**Ces exemples utilisent uniquement des prix OHLCV standards** disponibles dans QuantConnect.

### Ex02 (AllWeather-like)
- Portfolio multi-asset avec allocation statique
- Utilise SPY/IEF/GLD/XLP (disponibles dans QC)

### Autres exemples ML (Section 06)
- Trend Scanning (indicateurs techniques)
- Regime Detection (SMA, volatility)
- Classification (features prix)
- HMM (prix, returns)
- Stoploss dynamique (volatilité)
- Pairs Trading (cointégration)
- Clustering (fundamental data disponible dans QC)
- PCA Stat-Arb (prix, returns)

---

## Recommandations ESGF

Pour le cours ESGF 2026:

1. **Focus sur les exemples backtestables**: Sections 05 + exemples ML "purs" de la section 06
2. **Documents les prérequis**: Pour Ex16/17/19, expliquer aux étudiants pourquoi ils ne peuvent pas être backtestés directement
3. **Alternatives QC**: Proposer des implémentations QC équivalentes pour les concepts

---

**Version**: 1.0
**Date**: 2026-03-31
**Issue**: #143 (HandsOnAITrading examples)
