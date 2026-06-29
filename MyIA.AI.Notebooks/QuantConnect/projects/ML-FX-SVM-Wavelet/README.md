# ML-FX-SVM-Wavelet (HandsOn Ex05)

**Classe d'actifs :** Forex (4 paires : EURUSD, AUDUSD, USDJPY, USDCAD)
**ID projet Cloud :** Aucun (local uniquement)

## Description

SVR + décomposition en ondelettes sur les paires FX du G10. Utilise le débruitage par ondelettes (`pywt`) sur les séries de prix, puis un SVR pour prédire les rendements.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/ML-FX-SVM-Wavelet"`
**QC Cloud :** Pas encore déployé. Copier les fichiers dans un nouveau projet QC Cloud pour exécuter.

## Métriques du backtest

| Métrique | Valeur |
|----------|--------|
| Modèle | SVR + Ondelettes (pywt) |
| Univers | 4 paires FX du G10 |
| Rebalancement | Mensuel |

## Fichiers

- main.py - Stratégie (v1.0, SVR + ondelettes)
- research.ipynb - Analyse de la décomposition en ondelettes

## Références

- Hands-On AI Trading, Section 06, Exemple 05
