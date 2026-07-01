# GraphSAGE-MultiAsset-Ranking

**Type :** Recherche (notebook de recherche only, pas d'algorithme déployable)

**Classe d'actifs :** Actions (large-caps US)

**Cloud project ID :** N/A (recherche only, pas d'algorithme déployable)

## Description

Notebook de recherche appliquant le réseau de neurones sur graphe GraphSAGE (Hamilton, Ying et Leskovec 2017) à la prédiction de direction cross-asset sur 8 large-caps US (JPM, JNJ, XOM, PG, UNP, V, HD, BA). Construit un graphe basé sur les corrélations avec un seuil de 0.5 pour capturer les dépendances inter-actifs. Validation walk-forward 5-fold sur 4 seeds avec coûts de transaction 10bps. Verdict : INCONCLUSIVE (preuves statistiques insuffisantes pour confirmer ou rejeter l'approche).

## Comment exécuter

### Lean CLI
Non applicable (notebook de recherche only, pas de `main.py`).

### QC Cloud
Non applicable. Exécuter le notebook de recherche localement avec Python 3.10+ et PyTorch Geometric.

### Local
```bash
papermill research.ipynb output.ipynb
```

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| GraphSAGE ranking cross-asset | N/A (recherche) | Seuil de corrélation 0.5, walk-forward 5-fold x 4 seeds, T-cost 10bps |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `research.ipynb` | Notebook de recherche avec modèle GraphSAGE, construction du graphe de corrélation et validation walk-forward |
| `_generate_research.py` | Script qui génère le notebook de recherche |

## Références

- Hamilton, W., Ying, Z., Leskovec, J. (2017). *Inductive Representation Learning on Large Graphs*. NeurIPS.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
