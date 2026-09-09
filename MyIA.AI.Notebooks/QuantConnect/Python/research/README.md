# Python/research/ — notebooks de recherche *companions* du parcours QC-Py

Ce dossier porte les **2 notebooks de recherche appariés aux notebooks de cours** du parcours
[QC-Py](../README.md) — catégorie **(b) research companion** de la classification par modalité
d'exécution du [README Python](../README.md). Chaque companion approfondit, sur QuantBook, le
workflow démontré dans le notebook de cours correspondant.

| Notebook | Companion de | Contenu |
|---|---|---|
| [`research_classification.ipynb`](research_classification.ipynb) | [QC-Py-19-ML-Supervised-Classification](../QC-Py-19-ML-Supervised-Classification.ipynb) | Classification ML supervisée sur QuantBook (45 min, niveau intermédiaire) ; sert de support de recherche au projet [`projects/ML-Classification/`](../../projects/ML-Classification/README.md) |
| [`research_lstm.ipynb`](research_lstm.ipynb) | [QC-Py-22-Deep-Learning-LSTM](../QC-Py-22-Deep-Learning-LSTM.ipynb) | Entraînement complet d'un modèle LSTM (PyTorch) pour la prédiction de prix ; support de recherche du projet [`projects/DL-LSTM/`](../../projects/DL-LSTM/README.md) |

**Exécution** : notebooks QuantBook — exécution via QuantConnect Cloud (voir
[GETTING-STARTED](../../GETTING-STARTED.md)), pas d'exécution locale fictive.

## Ne pas confondre avec le hub `QuantConnect/research/`

Le dépôt porte **deux** emplacements « research » au sein de la série QC :

- **[`QuantConnect/research/`](../../research/README.md)** — le **hub de recherche autonome**
  (17 notebooks `research_*.ipynb`, données locales yfinance/sklearn, hors QC Cloud) ;
- **`QuantConnect/Python/research/`** (ce dossier) — les **2 companions pédagogiques** du
  parcours QC-Py ci-dessus, qui suivent leurs notebooks de cours.

Les deux ont des rôles distincts : recherche de stratégie standalone d'un côté, approfondissement
d'un chapitre de cours de l'autre. Voir le [README hub](../../README.md) pour la vue d'ensemble
de la série.
