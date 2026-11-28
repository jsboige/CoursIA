# Python/research/ — notebooks de recherche *companions* du parcours QC-Py

[← parcours QC-Py](../README.md) | [→ hub de recherche standalone](../../research/README.md) | [→ projets](../../projects/)

Ce dossier porte les **notebooks de recherche appariés aux notebooks de cours** du parcours
[QC-Py](../README.md) — catégorie **(b) research companion** de la classification par modalité
d'exécution du [README Python](../README.md). Chaque companion approfondit, sur QuantBook, le
workflow démontré dans le notebook de cours correspondant : on y refait le geste de recherche —
charger l'historique, construire les features, entraîner, évaluer, persister le modèle — avant de
le porter dans un `main.py`.

## Comment lire ce README

- **Vous cherchez le companion d'un chapitre** : la colonne « Companion de » de la table ci-dessous
  donne le notebook de cours que chaque carnet prolonge.
- **Vous voulez voir la chaîne complète** : commencez par `research_classification.ipynb`, qui va du
  chargement QuantBook à la persistance du modèle dans l'ObjectStore.
- **Vous voulez le volet deep learning** : `research_lstm.ipynb` reprend la même chaîne avec PyTorch
  et une entrée séquentielle.
- **Vous hésitez entre les deux dossiers « research »** : la section [Ne pas confondre avec le
  hub](#ne-pas-confondre-avec-le-hub-quantconnectresearch) tranche entre les deux emplacements.
- Les nombres d'inventaire vivent dans le bloc `CATALOG-STATUS` et le catalogue généré ; ce README
  ne les recopie pas.

## Parcours principal

| Notebook | Ce qu'on y apprend | Companion de |
|---|---|---|
| [`research_classification.ipynb`](research_classification.ipynb) | Charger SPY et QQQ sur QuantBook, construire des features techniques (RSI, EMA, MACD) et une cible de direction, entraîner un `RandomForestClassifier` sous validation temporelle, lire le `classification_report`, puis persister le modèle dans l'ObjectStore pour `main.py` | [QC-Py-19-ML-Supervised-Classification](../QC-Py-19-ML-Supervised-Classification.ipynb) — support de recherche du projet [`projects/ML-Classification/`](../../projects/ML-Classification/README.md) |
| [`research_lstm.ipynb`](research_lstm.ipynb) | Normaliser des séries de prix, découper des séquences temporelles, définir et entraîner un LSTM PyTorch, suivre la perte, comparer prédictions et réalisé, sauvegarder le modèle dans l'ObjectStore pour l'integration dans `main.py` | [QC-Py-22-Deep-Learning-LSTM](../QC-Py-22-Deep-Learning-LSTM.ipynb) — support de recherche du projet [`projects/DL-LSTM/`](../../projects/DL-LSTM/README.md) |

**Exécution** : notebooks QuantBook — exécution via QuantConnect Cloud (voir
[GETTING-STARTED](../../GETTING-STARTED.md)), pas d'exécution locale fictive. Les fenêtres
d'historique y sont demandées en **nombre de barres** : les dates, les prix et les métriques
changent à chaque ré-exécution, seule la structure est stable — pour figer un résultat, passer des
bornes explicites à `qb.history(...)`.

## Ne pas confondre avec le hub `QuantConnect/research/`

Le dépôt porte **deux** emplacements « research » au sein de la série QC :

- **[`QuantConnect/research/`](../../research/README.md)** — le **hub de recherche autonome**
  (notebooks `research_*.ipynb`, données locales yfinance/sklearn, hors QC Cloud) ;
- **`QuantConnect/Python/research/`** (ce dossier) — les **2 companions pédagogiques** du
  parcours QC-Py ci-dessus, qui suivent leurs notebooks de cours.

Les deux ont des rôles distincts : recherche de stratégie standalone d'un côté, approfondissement
d'un chapitre de cours de l'autre. Voir le [README hub](../../README.md) pour la vue d'ensemble
de la série.

## Approfondissements

| Fil | Où continuer | Ce qu'on y apprend |
|---|---|---|
| Du carnet au projet | [`projects/ML-Classification/`](../../projects/ML-Classification/README.md), [`projects/DL-LSTM/`](../../projects/DL-LSTM/README.md) | comment un modèle persisté sur QuantBook devient un algorithme qui passe des ordres — ré-entraînement, période d'échauffement, décision |
| La même question hors QuantBook | [`QuantConnect/research/`](../../research/README.md) | la recherche sur données locales (yfinance, tick), avec coûts de transaction et verdicts mesurés — l'autre façon de faire de la recherche |
| La theorie des deux chapitres | [QC-Py-19](../QC-Py-19-ML-Supervised-Classification.ipynb), [QC-Py-22](../QC-Py-22-Deep-Learning-LSTM.ipynb) | le cours que ces carnets appliquent plutôt qu'ils ne le repetent |
| L'API de recherche elle-même | [GETTING-STARTED](../../GETTING-STARTED.md) | lancer l'environnement Research, et ce qui ne s'y execute pas |
