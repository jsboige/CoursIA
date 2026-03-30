# Guide ECE Projet 2 - Sujets QuantConnect (H.1 a H.6)

> **A lire AVANT de commencer votre projet QuantConnect**
> Ce guide explique comment utiliser les ressources QC de ce depot pour votre Projet 2 ECE.

---

## Comprendre l'organisation des ressources

Ce depot contient **trois types de ressources QC** qu'il ne faut pas confondre :

| Type | Dossier | Usage | Executable dans QC Lab ? |
|------|---------|-------|--------------------------|
| **Notebooks pedagogiques** | `Python/QC-Py-XX-*.ipynb` | Cours theorique, explications, code a lire et comprendre | **NON** - ce sont des supports de cours |
| **Projets (strategies)** | `projects/*/main.py` | Strategies fonctionnelles prete a backtester | **OUI** - copier main.py dans votre projet QC |
| **Templates ESGF** | `ESGF-2026/templates/` | Points de depart pour votre projet | **OUI** - copier et adapter |

### Les notebooks QC-Py-XX ne sont PAS des QuantBooks

Les notebooks `QC-Py-01` a `QC-Py-27` sont des **supports de cours** conçus pour etre lus dans Jupyter local ou sur GitHub. Ils contiennent :
- Des explications theoriques
- Du code QCAlgorithm a **copier dans main.py** (pas a executer dans le notebook)
- Des visualisations matplotlib qui ne fonctionnent pas dans QC Lab

**Ne les uploadez pas tels quels dans QuantConnect Lab.** Lisez-les pour comprendre les concepts, puis utilisez les projets et templates comme base de code.

---

## Les deux modes de QuantConnect Lab

QuantConnect Lab a **deux modes distincts** qu'il faut maitriser :

### Mode Algorithm (main.py)

C'est le mode principal. Vous ecrivez une classe qui herite de `QCAlgorithm` :

```python
from AlgorithmImports import *

class MaStrategie(QCAlgorithm):
    def initialize(self):
        self.set_start_date(2020, 1, 1)
        self.set_end_date(2024, 12, 31)
        self.set_cash(100000)
        self.add_equity("SPY", Resolution.DAILY)

    def on_data(self, data):
        # Votre logique de trading ici
        if not self.portfolio.invested:
            self.set_holdings("SPY", 1.0)
```

- Cliquez **Backtest** pour executer
- Les resultats apparaissent dans le panneau de droite (equity curve, Sharpe, drawdown)
- C'est ce mode que vous utiliserez pour **90% de votre projet**

### Mode Research (QuantBook)

Pour l'exploration de donnees et l'entrainement de modeles ML :

```python
from QuantConnect.Research import QuantBook

qb = QuantBook()
symbol = qb.add_equity("SPY").symbol
history = qb.history(symbol, 360, Resolution.DAILY)

# Maintenant vous pouvez utiliser pandas, matplotlib, sklearn...
history['close'].plot()
```

- Creez un notebook dans votre projet QC (File > New Notebook)
- Le QuantBook donne acces aux memes donnees que l'algorithme
- Utile pour : visualiser des donnees, tester des features ML, entrainer des modeles
- **Limitation** : fichier < 128 KB, timeout 15 min par cellule

### Le pont entre Research et Algorithm : Object Store

Le pattern standard pour les projets ML :

1. **Dans research.ipynb** (QuantBook) : entrainer le modele, sauvegarder
   ```python
   qb = QuantBook()
   # ... entrainement du modele ...
   qb.object_store.save("my_model", model_bytes)
   ```

2. **Dans main.py** (Algorithm) : charger le modele, trader
   ```python
   def initialize(self):
       model_path = self.object_store.get_file_path("my_model")
       self.model = load_model(model_path)
   ```

Ce pattern est utilise dans le livre "Hands-On AI Trading" et dans nos exemples `ESGF-2026/examples/*-Researcher/`.

---

## Mapping des sujets ECE vers les ressources

### H.1 - Strategie Alpha ML sur QuantConnect

**Objectif** : Construire un Alpha Model qui utilise du ML (Random Forest, XGBoost) pour generer des signaux de trading.

**Notebooks a lire** (theorie) :
| Notebook | Contenu |
|----------|---------|
| QC-Py-13-Alpha-Models | Architecture Alpha Model, Insights, Framework |
| QC-Py-18-ML-Features-Engineering | Construction de features techniques |
| QC-Py-19-ML-Supervised-Classification | Random Forest, XGBoost pour prediction de direction |
| QC-Py-20-ML-Regression-Prediction | Regression pour prediction de rendements |
| QC-Py-21-Portfolio-Optimization-ML | Optimisation de portefeuille avec ML |

**Projets a utiliser comme base** :
| Projet | Description |
|--------|-------------|
| `projects/EMA-Cross-Alpha/` | Framework Alpha Model complet (main.py + alpha_models.py) |
| `projects/BTC-ML/` | ML sur Bitcoin |
| `ESGF-2026/examples/BTC-MachineLearning/` | Exemple etudiant ML |
| `ESGF-2026/examples/BTC-ML-Researcher/` | Research notebook ML |

**Librairies partagees** : `shared/ml_utils.py`, `shared/features.py`

**Workflow recommande** :
1. Copier `projects/EMA-Cross-Alpha/` comme point de depart
2. Lire QC-Py-18 et QC-Py-19 pour comprendre le feature engineering
3. Creer un research.ipynb dans votre projet QC pour tester vos features
4. Modifier alpha_models.py pour integrer votre modele ML
5. Backtester et iterer

---

### H.2 - Deep RL Trading avec QuantConnect

**Objectif** : Utiliser du Deep Learning (LSTM, Transformers) ou du Reinforcement Learning pour trader.

**Notebooks a lire** (theorie) :
| Notebook | Contenu |
|----------|---------|
| QC-Py-22-Deep-Learning-LSTM | LSTM pour series temporelles financieres |
| QC-Py-23-Attention-Transformers | Transformers pour prediction |
| QC-Py-24-Autoencoders-Anomaly | Detection d'anomalies avec autoencoders |
| QC-Py-25-Reinforcement-Learning | RL pour trading (DQN, PPO) |

**Projets a utiliser comme base** :
| Projet | Description |
|--------|-------------|
| `projects/BTC-ML/` | Base ML a etendre vers DL |
| `ESGF-2026/examples/BTC-MachineLearning/` | Exemple ML a adapter |

**Note importante** : L'entrainement DL/RL necessite du GPU. Deux approches :
1. Entrainer en local (votre GPU ou Google Colab), exporter le modele, charger via Object Store
2. Utiliser QC Research avec GPU (plan payant)

**Workflow recommande** :
1. Entrainer votre modele en local (Colab ou votre machine)
2. Exporter les poids du modele (pickle, ONNX, ou JSON)
3. Uploader dans QC Object Store
4. Creer un Alpha Model qui charge et utilise le modele

---

### H.3 - Composite AlphaModel Framework

**Objectif** : Combiner plusieurs signaux alpha (technique, fondamental, ML) dans une architecture modulaire.

**Notebooks a lire** (theorie) :
| Notebook | Contenu |
|----------|---------|
| QC-Py-13-Alpha-Models | Alpha Models et CompositeAlphaModel |
| QC-Py-14-Portfolio-Construction-Execution | Portfolio Construction et Execution Models |
| QC-Py-15-Parameter-Optimization | Optimisation des parametres |

**Projets a utiliser comme base** :
| Projet | Description |
|--------|-------------|
| `projects/Framework_Composite_EMATrend/` | Composite EMA + Trend |
| `projects/Framework_Composite_MomentumRegime/` | Composite Momentum + Regime |
| `projects/Framework_Composite_TrendWeather/` | Composite Trend + AllWeather |
| `projects/Framework_Composite_FamaFrenchAllWeather/` | Composite avance Fama-French |

**C'est le sujet le plus "QC-natif"** : tout le code est dans les projets Framework_Composite_*. Copiez un projet, comprenez l'architecture, puis ajoutez vos propres Alpha Models.

**Workflow recommande** :
1. Copier `projects/Framework_Composite_EMATrend/` dans votre projet QC
2. Lire QC-Py-13 pour comprendre Alpha Models et Insights
3. Creer 2-3 Alpha Models independants (technique, momentum, mean-reversion)
4. Les combiner avec CompositeAlphaModel
5. Optimiser les poids avec QC-Py-15

---

### H.4 - Regime Switching et Allocation Adaptative

**Objectif** : Detecter les regimes de marche (bull/bear/sideways) et adapter l'allocation dynamiquement.

**Notebooks a lire** (theorie) :
| Notebook | Contenu |
|----------|---------|
| QC-Py-09-Order-Types | Types d'ordres avances |
| QC-Py-10-Risk-Portfolio-Management | Gestion du risque, position sizing |
| QC-Py-11-Technical-Indicators | Indicateurs pour detection de regimes |
| QC-Py-12-Backtesting-Analysis | Analyse de performance par regime |

**Projets a utiliser comme base** :
| Projet | Description |
|--------|-------------|
| `projects/RegimeSwitching/` | Detection de regime + allocation adaptative |
| `projects/AllWeather/` | All-Weather portfolio (Dalio) |
| `projects/DualMomentum/` | Dual Momentum (Antonacci) |
| `projects/AdaptiveAssetAllocation/` | Allocation adaptative |

**Workflow recommande** :
1. Copier `projects/RegimeSwitching/` comme base
2. Lire QC-Py-11 pour les indicateurs de detection
3. Implementer votre detecteur de regime (HMM, volatilite, momentum)
4. Definir une allocation par regime (ex: 100% actions en bull, 100% bonds en bear)
5. Backtester sur une longue periode (2010-2024) pour couvrir plusieurs cycles

---

### H.5 - Options Strategies Automatisees (Wheel/Covered Call)

**Objectif** : Implementer des strategies d'options systematiques (Wheel, Covered Call, Iron Condor).

**Notebooks a lire** (theorie) :
| Notebook | Contenu |
|----------|---------|
| QC-Py-06-Options-Trading | Options chains, Greeks, strategies de base |
| QC-Py-08-Multi-Asset-Strategies | Strategies multi-actifs avec options |

**Projets a utiliser comme base** :
| Projet | Description |
|--------|-------------|
| `projects/Option-Wheel/` | Strategie Wheel complete |
| `projects/Options-VGT/` | Options sur VGT (tech ETF) |
| `projects/OptionsIncome/` | Strategies d'income avec options |
| `ESGF-2026/examples/Option-Wheel-Researcher/` | Research notebook options |
| `ESGF-2026/examples/Option-Wheel-Strategy/` | Strategie Wheel complete |

**Note** : Les options necessitent des donnees qui peuvent etre limitees en free tier. Verifiez la disponibilite des donnees options pour votre actif cible.

**Workflow recommande** :
1. Copier `projects/Option-Wheel/` ou `ESGF-2026/examples/Option-Wheel-Strategy/`
2. Lire QC-Py-06 pour comprendre les options dans QC
3. Adapter la strategie a votre actif (ex: SPY, QQQ, VGT)
4. Ajouter du risk management (position sizing, max loss)
5. Backtester et analyser les Greeks

---

### H.6 - Walk-Forward Analysis et Robustesse de Strategies

**Objectif** : Valider la robustesse d'une strategie avec walk-forward analysis, Monte Carlo, et tests out-of-sample.

**Notebooks a lire** (theorie) :
| Notebook | Contenu |
|----------|---------|
| QC-Py-15-Parameter-Optimization | Optimisation et overfitting |
| QC-Py-25-Reinforcement-Learning | Techniques avancees |
| QC-Py-26-LLM-Trading-Signals | Signaux alternatifs |
| QC-Py-27-Production-Deployment | Deploiement et monitoring |

**Projets a utiliser comme base** :
Choisissez N'IMPORTE QUELLE strategie des `projects/` et appliquez-lui une analyse de robustesse :

| Projet | Description |
|--------|-------------|
| `projects/MomentumStrategy/` | Momentum simple a valider |
| `projects/MeanReversion/` | Mean-reversion a tester |
| `projects/Trend-Following/` | Trend following a analyser |
| `ESGF-2026/examples/*-Researcher/` | Notebooks de recherche existants |

**Librairies partagees** : `shared/backtest_helpers.py`, `shared/features.py`, `shared/plotting.py`

**Workflow recommande** :
1. Choisir une strategie existante dans `projects/`
2. Creer un research.ipynb pour l'analyse walk-forward
3. Implementer : train/test split temporel, OOS/IS ratio, parameter stability
4. Tester sur differents regimes de marche (2008 crise, 2020 COVID, 2022 bear)
5. Documenter les resultats et les limites

---

## Demarrage rapide en 15 minutes

1. **Creer un compte QC** : [quantconnect.com/signup](https://www.quantconnect.com/signup) (gratuit)
2. **Creer un projet** : File > New Project > Python
3. **Copier un main.py** depuis `projects/` ou `ESGF-2026/templates/starter/`
4. **Cliquer Backtest** pour verifier que ca fonctionne
5. **Lire les notebooks QC-Py-XX** correspondant a votre sujet pour comprendre la theorie
6. **Modifier le code** pour implementer votre approche
7. **Iterer** : modifier > backtester > analyser > ameliorer

## Ressources cles

- **Documentation QC** : [quantconnect.com/docs](https://www.quantconnect.com/docs)
- **Livre de reference** : [Hands-On AI Trading](https://github.com/QuantConnect/HandsOnAITradingBook) (repo GitHub avec exemples)
- **Forum QC** : [quantconnect.com/forum](https://www.quantconnect.com/forum)
- **Shared libraries** : `shared/` (backtest_helpers, features, indicators, ml_utils, plotting)

## FAQ

**Q: Est-ce que je peux utiliser sklearn/pytorch dans QC Lab ?**
R: Oui, dans les **research notebooks** (QuantBook). Pour l'algorithme (main.py), vous devez charger un modele pre-entraine via Object Store ou utiliser les librairies supportees par QC.

**Q: Comment importer les modules shared/ dans QC Lab ?**
R: Creez une "Library" dans votre projet QC et copiez-y les fichiers Python de `shared/`. Ou copiez directement les fonctions dont vous avez besoin dans votre projet.

**Q: Le free tier est-il suffisant pour mon projet ?**
R: Oui pour la plupart des sujets (H.1, H.3, H.4, H.6). Pour les options (H.5), verifiez la disponibilite des donnees. Pour le DL (H.2), entrainez en local et deployez sur QC.

**Q: Puis-je utiliser les strategies existantes dans projects/ comme base ?**
R: Oui, c'est recommande. Partez d'une strategie qui marche et ameliorez-la. Citez la source dans votre rapport.
