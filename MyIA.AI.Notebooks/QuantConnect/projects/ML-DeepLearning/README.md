# ML-DeepLearning

**Asset class:** US Equities (SPY, QQQ, IWM — TLT s'ajoute dans le quantbook)
**Cloud project ID:** None (local only)

## Description

Prévision des rendements quotidiens par deep learning avec un **vrai LSTM** : TensorFlow/Keras dans le quantbook, PyTorch dans `main.py`. Le carnet entraîne un modèle sur les rendements historiques de SPY et mesure aussi son exactitude directionnelle ; l’algorithme Lean entraîne un modèle distinct pour chaque ETF et sélectionne les positions à partir des rendements prédits. Les deux parcours sont décrits séparément ci-dessous. L’ancien libellé « Ridge as LSTM proxy » décrivait une itération antérieure du projet.

## Parcours de recherche : `quantbook.ipynb`

Le [carnet `quantbook.ipynb`](quantbook.ipynb) développe la partie expérimentale du projet dans QuantConnect Research. Il télécharge l'historique quotidien de SPY, QQQ, IWM et TLT, construit des variables à partir des rendements, du momentum, de la volatilité, du RSI et des variations de volume, puis forme des séquences de 20 jours. Le modèle Keras est un LSTM à deux couches récurrentes (64 puis 32 unités), avec dropout et une sortie de régression du rendement de SPY.

Le carnet sépare ensuite les séquences dans l'ordre temporel pour une validation train/test, mesure l'erreur quadratique moyenne et l'exactitude directionnelle, trace les prédictions, puis propose une validation walk-forward et une simulation de portefeuille avec réentraînement périodique. Il contient aussi une architecture GRU illustrative et des pistes d'extension. Ces étapes servent à explorer et à comparer des choix de modélisation ; les chiffres affichés sont ceux du carnet lorsqu'il est exécuté dans son environnement de recherche.

`main.py` est l'algorithme destiné à Lean : il implémente la stratégie en PyTorch. Le carnet, lui, est un support de recherche TensorFlow/Keras ; ses cellules ne constituent pas l'exécution de l'algorithme Lean et leur simulation de portefeuille ne remplace pas un backtest de production.

### Prérequis et limites du carnet

Le carnet attend un environnement QuantConnect Research fournissant `QuantBook` et l'accès aux historiques, ainsi que Python avec TensorFlow/Keras, scikit-learn, pandas, NumPy et matplotlib. Le chemin indiqué ci-dessous concerne Lean CLI ; l'identifiant de projet Cloud est absent et aucun déploiement QC Cloud n'est déclaré.

La validation présentée reste pédagogique : le découpage principal ajuste le `StandardScaler` avant le split train/test, ce qui fait entrer des statistiques de la période de test dans la normalisation. La simulation réutilise également un modèle entraîné sur SPY pour classer plusieurs ETF et ne modélise pas les coûts de transaction. Les résultats ne démontrent donc pas une performance exploitable en trading. Le carnet documente une fenêtre d'historique ancrée à `qb.Time` (initialisé à `StartDate`) ; ses contrôles d'intégrité signalent des historiques incomplets ou une fin de série plate, mais ne certifient ni la fraîcheur des données ni la validité hors échantillon.

## Exécution

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-DeepLearning"`
**QC Cloud :** aucun déploiement déclaré ; copier les fichiers dans un nouveau projet QC Cloud pour lancer l’algorithme.

## Paramètres de l’algorithme Lean

| Paramètre | Valeur |
|--------|-------|
| Modèle | LSTM (TensorFlow/Keras dans le quantbook, PyTorch dans `main.py`) |
| Univers Lean | SPY, QQQ, IWM |
| Rééquilibrage | Chaque lundi |

## Fichiers

- [`quantbook.ipynb`](quantbook.ipynb) — exploration et validation du modèle LSTM dans QuantConnect Research
- [`main.py`](main.py) — stratégie Lean (`MLDeepLearningAlgorithm`)
