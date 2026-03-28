---
theme: ../theme-ia101
title: "Exercices TP - Trading Algorithmique avec QuantConnect"
info: IA 101 - S4 Trading Algorithmique - Travaux Pratiques
paginate: true
drawings:
  persist: false
transition: slide-left
mdc: true
layout: cover
---

# Exercices TP

TRADING ALGORITHMIQUE AVEC QUANTCONNECT

**IA 101 -- S4**

9 exercices progressifs du setup aux modeles de foundation

---
layout: section
---

# Instructions Generales

---
layout: default
---

# Organisation des TP

- **9 exercices** en progression du debutant a l'avance
- Chaque exercice utilise **QuantConnect Cloud** (lean-cli ou interface web)
- **Fichiers sources** : projets dans `QuantConnect/projects/`
- **Notebooks de cours** : `QuantConnect/Python/QC-Py-*.ipynb`

### Niveaux de difficulte

| Niveau | Exercices | Prerequis |
|--------|-----------|-----------|
| Debutant | Ex01, Ex02 | Python, aucun QC |
| Intermediaire | Ex03, Ex04, Ex05 | Ex01-02, stats de base |
| Avance | Ex06, Ex07, Ex08, Ex09 | Ex03-05, ML/DL |

### Metriques de reference

Pour chaque strategie, mesurez : **Sharpe Ratio**, **CAGR**, **Max Drawdown**, **Win Rate**

---
layout: default
---

# Ressources Disponibles

### Environnement

- **QuantConnect Cloud** : https://www.quantconnect.com/cloud
- **Documentation** : https://www.quantconnect.com/docs/v2
- **Dataset** : 100+ sources de donnees gratuites (US Equity, Crypto, Forex, Futures)

### Livre de reference

- **Hands-On AI Trading with Python, QuantConnect, and AWS** (Jared Broad, 2025)
- Mapping complet : `QuantConnect/docs/HANDSON_AI_TRADING_MAPPING.md`

### Notebooks d'accompagnement

- 28 notebooks `QC-Py-01` a `QC-Py-28` couvrant toute la plateforme
- Chaque exercice reference les notebooks pertinents

---
layout: section
---

# Ex01 - Setup et Premier Backtest

---
layout: default
---

# Ex01 - Objectif

> Configurer QuantConnect et executer votre premier backtest

### Ce que vous allez apprendre

- Creer un projet sur QC Cloud
- Comprendre la structure d'un algorithme (`Initialize`, `OnData`)
- Executer un backtest et lire les resultats

### Sources

- **Notebook** : `QC-Py-01-Setup.ipynb`
- **Notebook** : `QC-Py-02-Platform-Fundamentals.ipynb`

---
layout: default
---

# Ex01 - Consignes

1. **Creer un projet** `Ex01-Setup` sur QuantConnect Cloud (Python)

2. **Implementer un algorithme simple** qui :
   - Trade SPY (S&P 500 ETF)
   - Achte 100 actions le premier jour
   - Ne fait rien d'autre (buy and hold)

3. **Lancer un backtest** sur la periode 2020-2024 avec 100 000 USD

<v-click>

4. **Analyser les resultats** :
   - Quel est le rendement total ?
   - Quel est le ratio de Sharpe ?
   - Quel est le drawdown maximum ?

</v-click>

<v-click>

### Hints

- `self.AddEquity("SPY", Resolution.DAILY)` pour ajouter un actif
- `self.SetCash(100000)` pour le capital initial
- `self.MarketOrder(self.Symbol("SPY"), 100)` pour acheter

</v-click>

---
layout: default
---

# Ex01 - Resultats Attendus

| Metrique | Valeur attendue |
|----------|----------------|
| Net Profit | ~80-100% (2020-2024) |
| Sharpe Ratio | ~0.5-0.8 |
| Max Drawdown | ~25% |
| Trades | 1 |

### Pour aller plus loin

- Modifier pour trader QQQ (NASDAQ) au lieu de SPY
- Ajouter un schedule de rebalancement mensuel
- Comparer les metriques entre SPY et QQQ

---
layout: section
---

# Ex02 - Indicateurs Techniques et Crossover EMA

---
layout: default
---

# Ex02 - Objectif

> Implementer une strategie EMA Crossover avec indicateurs techniques

### Ce que vous allez apprendre

- Utiliser les indicateurs techniques de Lean (`self.EMA()`)
- Generer des signaux d'achat/vente sur croisement de moyennes
- Gerer les positions (ouvrir/fermer)

### Sources

- **Notebook** : `QC-Py-11-Technical-Indicators.ipynb`
- **Projet** : `EMA-Cross-Stocks/`

---
layout: default
---

# Ex02 - Consignes

1. **Creer un projet** `Ex02-EMA-Cross` sur QC Cloud

2. **Implementer la strategie EMA Crossover** :
   - EMA rapide : 12 periodes
   - EMA lente : 26 periodes
   - Signal d'achat quand la rapide croise au-dessus de la lente
   - Signal de vente quand la rapide croise au-dessous de la lente

<v-click>

3. **Backtester** sur 2020-2024 avec SPY, capital 100 000 USD

4. **Comparer** avec Ex01 (buy and hold)

</v-click>

<v-click>

### Hints

- `self.EMA(symbol, 12)` et `self.EMA(symbol, 26)` pour les indicateurs
- Utiliser `Indicator.Updated` ou `self.IndicatorIsReady`
- Piste : checker `self.fast.Current.Value > self.slow.Current.Value`
- Attention aux signaux precedents pour detecter le **croisement** (pas juste la position)

</v-click>

---
layout: default
---

# Ex02 - Resultats Attendus

| Metrique | Valeur attendue |
|----------|----------------|
| Sharpe Ratio | ~0.4-0.8 |
| Net Profit | ~40-80% |
| Max Drawdown | ~20-30% |
| Trades | ~20-50 |

### Pour aller plus loin

- Tester avec differentes periodes EMA (5/20, 20/50, 50/200)
- Ajouter un filtre de volume
- Implementer un stop-loss a 5%

---
layout: section
---

# Ex03 - Random Forest pour Direction Prediction

---
layout: default
---

# Ex03 - Objectif

> Predire la direction du marche avec un classificateur Random Forest

### Ce que vous allez apprendre

- Feature engineering pour le trading (rendements, volatilite, indicateurs)
- Entrainement d'un modele de classification supervisee
- Walk-forward training pour eviter le data leakage

### Sources

- **Notebook** : `QC-Py-19-ML-Supervised-Classification.ipynb`
- **Projet** : `ML-RandomForest/`

---
layout: default
---

# Ex03 - Consignes

1. **Explorer le projet** `ML-RandomForest/main.py`

2. **Identifier les features** utilisees par le modele :
   - Quels indicateurs techniques ?
   - Quelle fenetre temporelle ?
   - Comment les labels sont-ils construits ?

<v-click>

3. **Executer le backtest** sur QC Cloud (periode 2020-2025)

4. **Analyser les resultats** :
   - Le modele bat-il le buy-and-hold ?
   - Quelle est la precision de prediction ?
   - Y a-t-il des periodes de sous-performance ?

</v-click>

<v-click>

### Hints

- Le Random Forest utilise `sklearn.ensemble.RandomForestClassifier`
- Les features incluent : rendements, volatilite, RSI, ratio de volume
- Walk-forward : le modele est reentraine periodiquement
- Parametres cles : `n_estimators`, `max_depth`, `lookback`

</v-click>

---
layout: default
---

# Ex03 - Resultats Attendus

| Metrique | Valeur de reference |
|----------|---------------------|
| Sharpe Ratio | ~0.45 |
| CAGR | ~12% |
| Max Drawdown | ~20% |
| Win Rate | ~55% |

### Pour aller plus loin

- Comparer avec `ML-XGBoost/` (gradient boosting)
- Comparer avec `ML-SVM/` (support vector machine)
- Modifier les hyperparametres et observer l'impact

---
layout: section
---

# Ex04 - Detection de Regimes Markov

---
layout: default
---

# Ex04 - Objectif

> Detecter les regimes de marche avec un modele de Markov a changement de regime

### Ce que vous allez apprendre

- Modeles probabilistes pour les series temporelles financieres
- Detection de regimes (haute/basse volatilite)
- Allocation conditionnelle basee sur les probabilites

### Sources

- **Projet** : `Markov-Regime-Detection/`
- **Reference** : Hands-On AI Trading, Chapter 06, Example 04

---
layout: default
---

# Ex04 - Consignes

1. **Lire le code** de `Markov-Regime-Detection/main.py`

2. **Comprendre le modele** :
   - Qu'est-ce qu'un regime de marche ?
   - Comment le modele de Markov identifie-t-il 2 regimes ?
   - Comment les probabilites sont-elles utilisees pour l'allocation ?

<v-click>

3. **Executer le backtest** et analyser :
   - Quand le modele detecte-t-il un changement de regime ?
   - Comment l'allocation SPY/TLT change-t-elle ?
   - Quel est le role du GLD (10% constant) ?

</v-click>

<v-click>

### Hints

- `MarkovRegression` de `statsmodels` avec `k_regimes=2`
- `switching_variance=True` permet des variances differentes par regime
- Allocation : `poids_SPY = prob_low_vol * 0.80`
- Seuil de confirmation : prob > 0.55 pour rebalancer

</v-click>

---
layout: default
---

# Ex04 - Resultats Attendus

| Metrique | Valeur de reference |
|----------|---------------------|
| Sharpe Ratio | ~0.3-0.5 |
| Allocation SPY | 0-80% selon regime |
| Regime changes | ~2-4 par an |

### Concepts cles

- **Regime haussier** : faible volatilite, allocation SPY elevee
- **Regime baissier** : forte volatilite, allocation TLT elevee
- **Filtre de confirmation** : evite les faux signaux

---
layout: section
---

# Ex05 - Forecasting SVM + Wavelet

---
layout: default
---

# Ex05 - Objectif

> Prevoir les cours de change avec SVM et decomposition en ondelettes

### Ce que vous allez apprendre

- Transformation en ondelettes discrete (DWT) pour le denoising
- Decomposition multi-echelle d'une serie temporelle
- SVM de regression (SVR) applique a chaque composante

### Sources

- **Projet** : `SVM-Wavelet-Forecasting/`
- **Reference** : Hands-On AI Trading, Chapter 06, Example 05

---
layout: default
---

# Ex05 - Consignes

1. **Lire le code** de `SVM-Wavelet-Forecasting/main.py`

2. **Comprendre la decomposition en ondelettes** :
   - Niveau 3, Daubechies 4
   - Composantes : cA3 (tendance), cD3/cD2/cD1 (details)
   - Pourquoi decomposer avant de predire ?

<v-click>

3. **Executer le backtest** sur EUR/USD

4. **Questions** :
   - Quelle composante est la plus previsionnelle ?
   - Le denoising ameliore-t-il les predictions ?
   - Pourquoi le Forex plutot que les actions ?

</v-click>

<v-click>

### Hints

- `pywt.wavedec()` pour la decomposition
- Un SVR par composante (4 modeles)
- `pywt.waverec()` pour la reconstruction du signal
- Le bruit haute frequence (cD1) est souvent elimine

</v-click>

---
layout: section
---

# Ex06 - Temporal CNN pour Prediction

---
layout: default
---

# Ex06 - Objectif

> Predire la direction des prix avec un CNN temporel (1D Convolution)

### Ce que vous allez apprendre

- Architecture CNN 1D pour series temporelles
- Convolution sur des sequences de rendements
- Pooling global pour l'aggregation temporelle

### Sources

- **Projet** : `Temporal-CNN-Prediction/`
- **Notebook** : `QC-Py-22-Deep-Learning-LSTM.ipynb` (CNN section)
- **Reference** : Hands-On AI Trading, Chapter 06, Example 14

---
layout: default
---

# Ex06 - Consignes

1. **Lire l'architecture** dans `Temporal-CNN-Prediction/main.py` :
   - Input : sequence de N rendements quotidiens
   - Conv1D : detection de patterns locaux
   - Global pooling : aggregation
   - Dense : prediction de direction

<v-click>

2. **Executer le backtest** et analyser

3. **Comparer** avec le Random Forest (Ex03) :
   - Quelle methode est plus performante ?
   - Laquelle s'adapte mieux aux changements de regime ?

</v-click>

<v-click>

### Hints

- Les CNN captent des **patterns locaux** (courtes sequences)
- `lookback_days = 20` par defaut (modifiable)
- Le z-score rolling normalise les features
- Le reentrainment a lieu tous les 30 jours

</v-click>

---
layout: default
---

# Ex06 - Resultats Attendus

| Metrique | Valeur de reference |
|----------|---------------------|
| Sharpe Ratio | ~1.5 (ensemble) |
| CAGR | ~13% |
| Max Drawdown | ~34% |

### Concepts cles

- **Conv1D** : filtres qui glissent sur la serie temporelle
- **Feature map** : transformation des patterns detectes
- **Reentrainment periodique** : adaptation aux changements de marche

---
layout: section
---

# Ex07 - LSTM Forecasting

---
layout: default
---

# Ex07 - Objectif

> Predire les prix avec un reseau de neurones recurrent (LSTM)

### Ce que vous allez apprendre

- Architecture LSTM (Long Short-Term Memory)
- Portes d'oubli, d'entree et de sortie
- Capturer les dependances temporelles longues

### Sources

- **Projet** : `LSTM-Forecasting/`
- **Notebook** : `QC-Py-22-Deep-Learning-LSTM.ipynb`
- **Reference** : Hands-On AI Trading, Chapter 06, Example 07

---
layout: default
---

# Ex07 - Consignes

1. **Comprendre l'architecture LSTM** :
   - Comment les cellules LSTM memorisent-elles l'information ?
   - Quelle est la difference avec un RNN classique ?
   - Pourquoi `hidden_size = 32` ?

<v-click>

2. **Executer le backtest** et analyser

3. **Comparer** LSTM vs CNN (Ex06) :
   - Lequel capture mieux les tendances longues ?
   - Lequel s'entraine plus vite ?

</v-click>

<v-click>

### Hints

- LSTM = 3 portes : forget, input, output
- `lookback_days = 30` : sequence d'input plus longue que CNN
- Le LSTM est implemente manuellement (pas de lib externe)
- `prediction_threshold = 0.55` : seuil de confiance pour trader

</v-click>

---
layout: default
---

# Ex07 - Resultats Attendus

| Metrique | Valeur de reference |
|----------|---------------------|
| Sharpe Ratio | ~0.86 |
| CAGR | ~11% |
| Max Drawdown | ~16% |

### Architecture LSTM

```
Input (30 rendements) -> LSTM (32 hidden) -> Dense -> Sigmoid
                                      |
                                  Memory Cell
                                  Forget Gate
                                  Input Gate
                                  Output Gate
```

---
layout: section
---

# Ex08 - Reinforcement Learning Trading

---
layout: default
---

# Ex08 - Objectif

> Entrainer un agent de trading par apprentissage par renforcement (DQN)

### Ce que vous allez apprendre

- Formulation du trading comme probleme de RL
- Etat, action, recompense dans un contexte financier
- Deep Q-Network (DQN) avec experience replay

### Sources

- **Projet** : `Reinforcement-Learning-Trading/`
- **Notebook** : `QC-Py-25-Reinforcement-Learning.ipynb`
- **Reference** : Hands-On AI Trading, Chapter 07

---
layout: default
---

# Ex08 - Consignes

1. **Comprendre la formulation RL** :
   - **Etat** : rendements, volatilite, position actuelle
   - **Actions** : BUY, SELL, HOLD
   - **Recompense** : rendement du portefeuille

<v-click>

2. **Analyser le DQN** :
   - Comment fonctionne l'exploration (epsilon-greedy) ?
   - Qu'est-ce que l'experience replay ?
   - Pourquoi un target network ?

</v-click>

<v-click>

3. **Executer le backtest** et observer :
   - L'agent apprend-il au fil du temps ?
   - Quels comportements emergents ?

</v-click>

<v-click>

### Hints

- `epsilon` decroit de 0.3 a 0.05 (exploration -> exploitation)
- Experience replay : le modele re-apprend de situations passees
- Le Q-network est un simple MLP (pas de convolution)
- Attention au surapprentissage sur une seule periode

</v-click>

---
layout: default
---

# Ex08 - Resultats Attendus

| Metrique | Valeur de reference |
|----------|---------------------|
| Sharpe Ratio | ~0.64 |
| CAGR | ~8% |
| Max Drawdown | ~21% |

### Concepts cles

- **Exploration vs Exploitation** : equilibre entre essayer de nouvelles strategies et exploiter les connues
- **Experience Replay** : rompt la correlation temporelle des observations
- **Target Network** : stabilise l'apprentissage

---
layout: section
---

# Ex09 - Modeles de Foundation (Chronos)

---
layout: default
---

# Ex09 - Objectif

> Utiliser un modele de foundation pour la prevision de series temporelles

### Ce que vous allez apprendre

- Modeles de foundation pour series temporelles (zero-shot forecasting)
- Tokenisation de valeurs continues
- Architecture Transformer pour le forecasting

### Sources

- **Projet** : `Chronos-Foundation-Forecasting/`
- **Reference** : Hands-On AI Trading, Chapter 06, Example 18
- **Article** : "Chronos: Learning the Language of Time Series" (Amazon Science, 2024)

---
layout: default
---

# Ex09 - Consignes

1. **Comprendre le concept de modele de foundation** :
   - Preentraine sur un grand corpus de series temporelles
   - Zero-shot : pas de fine-tuning necessaire
   - Architecture T5 (Transformer)

<v-click>

2. **Analyser l'implementation simplifiee** :
   - Comment les valeurs continues sont-elles tokenisees ?
   - Comment le transformer predit-il les tokens futurs ?
   - Quelle est la difference avec LSTM (Ex07) ?

</v-click>

<v-click>

3. **Executer le backtest** et reflechir :
   - Le zero-shot forecasting est-il competitif ?
   - Quels sont les avantages par rapport a un modele entraine specifiquement ?

</v-click>

<v-click>

### Hints

- Chronos tokenize les valeurs en entiers via quantization
- Le forecasting devient un probleme de "language modeling"
- Implementation simplifiee dans le projet (pas le vrai package `chronos`)
- Pour la version complete : `from chronos import ChronosPipeline`

</v-click>

---
layout: default
---

# Ex09 - Resultats Attendus

| Metrique | Valeur de reference |
|----------|---------------------|
| Sharpe Ratio | ~0.77 |
| CAGR | ~15% |
| Max Drawdown | ~34% |

### Evolution des modeles

```
Ex03: Random Forest (ensemble, interpretable)
  -> Ex06: CNN 1D (patterns locaux)
    -> Ex07: LSTM (dependances longues)
      -> Ex09: Transformer/Chronos (attention globale, zero-shot)
```

---
layout: section
---

# Recapitulatif

---
layout: default
---

# Tableau des Exercices

| # | Titre | Difficulte | Concept cle | Projet |
|---|-------|-----------|-------------|--------|
| Ex01 | Setup et Premier Backtest | Debutant | QCAlgorithm, OnData | -- |
| Ex02 | EMA Crossover | Debutant | Indicateurs techniques | EMA-Cross-Stocks |
| Ex03 | Random Forest | Intermediaire | Classification ML | ML-RandomForest |
| Ex04 | Markov Regime | Intermediaire | Modeles probabilistes | Markov-Regime-Detection |
| Ex05 | SVM Wavelet | Intermediaire | Signal processing | SVM-Wavelet-Forecasting |
| Ex06 | Temporal CNN | Avance | CNN 1D | Temporal-CNN-Prediction |
| Ex07 | LSTM Forecasting | Avance | Reseaux recurrents | LSTM-Forecasting |
| Ex08 | RL Trading | Avance | Reinforcement Learning | Reinforcement-Learning-Trading |
| Ex09 | Chronos Foundation | Avance | Modeles de foundation | Chronos-Foundation-Forecasting |

---
layout: default
---

# Resultats Comparatifs (Backtests QC Cloud)

| Exercice | Sharpe | CAGR | Max DD | Win Rate |
|----------|--------|------|--------|----------|
| Ex06 CNN | 1.535 | 13.54% | 33.72% | ~55% |
| Ex07 LSTM | 0.863 | 10.98% | 16.48% | ~54% |
| Ex03 RF | 0.450 | 12.03% | 20.40% | 55% |
| Ex09 Chronos | 0.774 | 15.54% | 33.72% | ~54% |
| Ex08 RL | 0.639 | 8.06% | 20.81% | ~53% |

> **Note** : Les performances passees ne garantissent pas les resultats futurs.
> L'objectif est pedagogique, pas la recherche du meilleur Sharpe.

---
layout: default
---

# Conseils pour les TP

### Avant chaque exercice
1. Lisez le **notebook de cours** associe
2. Explorez le **code source** du projet sur GitHub
3. Notez les **parametres** et leur role

### Pendant l'exercice
4. Executez d'abord le backtest **tel quel**
5. Puis **modifiez un parametre** a la fois
6. **Documentez** vos observations

### Apres l'exercice
7. **Comparez** avec les resultats de reference
8. **Reflechissez** : pourquoi cette performance ?
9. **Experimentez** avec les suggestions "pour aller plus loin"

---
layout: default
---

# Points de vigilance

### Pieges courants

- **Overfitting** : un modele parfait en backtest peut etre mauvais en live
- **Data leakage** : ne jamais utiliser les donnees futures pour l'entrainement
- **Survivorship bias** : les donnees QC filtrent les entreprises disparues
- **Look-ahead bias** : verifier que chaque decision utilise uniquement les donnees passees

### Bonnes pratiques

- Toujours **diviser** la periode (train / validation / test)
- **Reentrainer** periodiquement les modeles
- **Diversifier** les strategies plutot qu'optimiser une seule
- **Questionner** les resultats anormalement bons

---
layout: cover
---

# Questions ?

IA 101 -- S4 Trading Algorithmique

**Exercices TP**

---

# Ressources

- **QuantConnect** : https://www.quantconnect.com
- **Documentation Lean** : https://www.quantconnect.com/docs/v2
- **Livre** : Hands-On AI Trading with Python, QuantConnect, and AWS
- **GitHub** : https://github.com/QuantConnect/HandsOnAITradingBook
- **Notebooks CoursIA** : `QuantConnect/Python/QC-Py-*.ipynb`

**Jean-Sylvain Boige** -- jsboige@myia.org
