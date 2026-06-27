# ML-FinBERT-Sentiment (HandsOn Ex19)

**Classe d'actifs :** Actions US (top 10 tech)
**ID projet Cloud :** Aucun (local uniquement)

## Description

Analyse de sentiment FinBERT sur du texte financier. Nécessite TensorFlow et les poids du modèle, indisponibles sur QC Cloud.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-FinBERT-Sentiment"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest

| Métrique | Valeur |
|----------|--------|
| Modèle | FinBERT (HuggingFace) |
| Note | Nécessite une exécution Lean locale avec TensorFlow |

## Fichiers

- `main.py` — Stratégie (v1.0, sentiment FinBERT)
- `research.ipynb` — Évaluation du modèle de sentiment

## Références

- *Hands-On AI Trading*, Section 06, Exemple 19
