# GraphSAGE-MultiAsset-Ranking

**Type :** Recherche (notebook de recherche only, pas d'algorithme déployable)

**Classe d'actifs :** Actions (large-caps US)

**Cloud project ID :** N/A (recherche only, pas d'algorithme déployable)

## Description

Notebook de recherche appliquant le réseau de neurones sur graphe GraphSAGE (Hamilton, Ying et Leskovec 2017) à la prédiction de direction cross-asset sur 8 large-caps US (JPM, JNJ, XOM, PG, UNP, V, HD, BA). Le graphe relie deux actions dont la corrélation des rendements dépasse 0.5 ; il est recalculé sur la fenêtre d'entraînement de chaque pli, et le passage de messages ne relie que des actions de la même date. Cinq plis temporels à fenêtre expansive, 4 graines ; la décision prise à la clôture d'un jour encaisse le rendement du lendemain, avec 10 points de base de frais sur le montant échangé ; le témoin est un portefeuille à poids égaux des mêmes actions, sur les mêmes dates. **Verdict committé : NO BEATS** — hors échantillon (2289 séances, fin 2015 à fin 2024), Sharpe −0.37 pour GraphSAGE et −0.05 pour un MLP sans graphe, contre 0.79 pour le témoin ; l'écart journalier est significativement négatif (t de Newey-West −8.29 pour GraphSAGE). Sans frais, le MLP égale à peu près le témoin (t = 0.54) : ce sont les frais d'une rotation quotidienne qui le font perdre. Le graphe dégrade le MLP (t = −2.99), et les probabilités des deux modèles sont moins bonnes que la simple climatologie (Diebold-Mariano, p < 0.01). Le carnet documente une **absence** d'edge, pas une validation.

## Comment exécuter

### Lean CLI
Non applicable (notebook de recherche only, pas de `main.py`).

### QC Cloud
Non applicable. Exécuter le notebook de recherche localement avec Python 3.10+ et PyTorch.

### Local
```bash
papermill research.ipynb output.ipynb
```

## Métriques de backtest

| Méthode | Rebalance | Paramètres clés |
|---------|-----------|-----------------|
| GraphSAGE ranking cross-asset | N/A (recherche) | Seuil de corrélation 0.5, 5 plis temporels x 4 graines, 10 pb sur le montant échangé |

## Fichiers

| Fichier | Description |
|---------|-------------|
| `research.ipynb` | Notebook de recherche avec modèle GraphSAGE, construction du graphe de corrélation et validation walk-forward |
| `_generate_research.py` | Script qui génère le notebook de recherche |

## Références

- Hamilton, W., Ying, Z., Leskovec, J. (2017). *Inductive Representation Learning on Large Graphs*. NeurIPS.
- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
