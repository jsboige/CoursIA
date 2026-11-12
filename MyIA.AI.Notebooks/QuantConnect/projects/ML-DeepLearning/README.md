# ML-DeepLearning

**Asset class:** US Equities (SPY, QQQ, IWM — TLT s'ajoute dans le quantbook)
**Cloud project ID:** None (local only)

## Description

Prédiction de direction par deep learning avec un **vrai LSTM** (tensorflow/keras dans le quantbook, PyTorch dans main.py). Prédit la direction du lendemain (hausse/baisse/stable) sur les ETF de l'univers à partir de rendements open-close décalés. L'ancien libellé « Ridge as LSTM proxy » décrivait une itération antérieure du projet.

## Parcours de recherche : `quantbook.ipynb`

Le [carnet `quantbook.ipynb`](quantbook.ipynb) développe la partie expérimentale du projet dans QuantConnect Research. Il télécharge l'historique quotidien de SPY, QQQ, IWM et TLT, construit des variables à partir des rendements, du momentum, de la volatilité, du RSI et des variations de volume, puis forme des séquences de 20 jours. Le modèle Keras est un LSTM à deux couches récurrentes (64 puis 32 unités), avec dropout et une sortie de régression du rendement de SPY.

Le carnet sépare ensuite les séquences dans l'ordre temporel pour une validation train/test, mesure l'erreur quadratique moyenne et l'exactitude directionnelle, trace les prédictions, puis propose une validation walk-forward et une simulation de portefeuille avec réentraînement périodique. Il contient aussi une architecture GRU illustrative et des pistes d'extension. Ces étapes servent à explorer et à comparer des choix de modélisation ; les chiffres affichés sont ceux du carnet lorsqu'il est exécuté dans son environnement de recherche.

`main.py` est l'algorithme destiné à Lean : il implémente la stratégie en PyTorch. Le carnet, lui, est un support de recherche TensorFlow/Keras ; ses cellules ne constituent pas l'exécution de l'algorithme Lean et leur simulation de portefeuille ne remplace pas un backtest de production.

### Prérequis et limites du carnet

Le carnet attend un environnement QuantConnect Research fournissant `QuantBook` et l'accès aux historiques, ainsi que Python avec TensorFlow/Keras, scikit-learn, pandas, NumPy et matplotlib. Le chemin indiqué ci-dessous concerne Lean CLI ; l'identifiant de projet Cloud est absent et aucun déploiement QC Cloud n'est déclaré.

La validation présentée reste pédagogique : le découpage principal ajuste le `StandardScaler` avant le split train/test, ce qui fait entrer des statistiques de la période de test dans la normalisation. La simulation réutilise également un modèle entraîné sur SPY pour classer plusieurs ETF et ne modélise pas les coûts de transaction. Les résultats ne démontrent donc pas une performance exploitable en trading. Le carnet documente une fenêtre d'historique ancrée à `qb.Time` (initialisé à `StartDate`) ; ses contrôles d'intégrité signalent des historiques incomplets ou une fin de série plate, mais ne certifient ni la fraîcheur des données ni la validité hors échantillon.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-DeepLearning"`
**QC Cloud:** Not yet deployed. Copy files to a new QC Cloud project to run.

## Backtest Metrics

| Metric | Value |
|--------|-------|
| Model | LSTM (tensorflow/keras dans le quantbook, PyTorch dans main.py) |
| Universe | SPY, QQQ, IWM (+ TLT dans le quantbook) |
| Rebalance | Weekly |

## Files

- [`quantbook.ipynb`](quantbook.ipynb) - exploration et validation du modèle LSTM dans QuantConnect Research
- [`main.py`](main.py) - stratégie Lean (`MLDeepLearningAlgorithm`)
