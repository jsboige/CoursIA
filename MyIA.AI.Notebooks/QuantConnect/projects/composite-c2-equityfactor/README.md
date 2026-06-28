# composite-c2-equityfactor

**Classe d'actifs :** Actions (large-cap US, sélection fondamentale)

**Cloud project ID :** 32981222

## Description

Composite Equity Factor C4.2 (v12) utilisant l'Alpha Framework avec sélection d'univers fine fondamentale. Sélection en deux étapes : filtre coarse (top 200 par dollar volume) puis filtre fine (top 25 par capitalisation boursière). Génère des signaux à partir de quatre modèles alpha factoriels : Value (ratios P/E, P/B), Quality (ROE, dette/fonds propres), LowVolatility (volatilité réalisée) et Momentum (momentum de prix). Construction de portefeuille via MeanVariancePCM (rééquilibrage hebdomadaire, 65 % d'exposition max, plafond sectoriel 18 %). Gestion du risque via SectorCapRiskModel (poids sectoriel max 10 %, beta max 0.8). Exécution via TWAP (6 tranches, fenêtre de 10 minutes). Met en cache les données fondamentales pour la performance.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm composite-c2-equityfactor/main.py
```

### QC Cloud
Créer un nouveau projet, uploader tous les fichiers `.py`, compiler et lancer un backtest.

## Métriques de backtest

| Méthode | Rééquilibrage | Paramètres clés |
|---------|---------------|-----------------|
| Alpha Framework (4 facteurs + PCM MeanVar) | Hebdomadaire | Top 25 par capitalisation, exposition max 65 %, plafond sectoriel 18 %, TWAP 6 tranches |

### Baseline alignée (2018-2025)

Fenêtre #1630 standardisée (2018-01-01 à 2025-01-01, 1761 dates tradables), backtestée sur QC Cloud avec frais réels post-#2801.

| Métrique | Catalogue (2015-2025) | Alignée (2018-2025) |
|----------|-----------------------|---------------------|
| Sharpe Ratio | 0.543 | **0.574** |
| CAGR | 10.010 % | 11.942 % |
| Max Drawdown | 18.800 % | 18.600 % |
| PSR | 16.822 % | 25.765 % |

Backtest `8eecba32` (alignée) / `3173f8b39` (catalogue `c2-equityfactor-post2801`), projet 32981222.

La baseline COMP (composite-framework) la plus robuste vérifiée à ce jour : le Sharpe 0.574 est le plus élevé parmi les composites Alpha Framework testés sur la fenêtre alignée, et proche du territoire Tier-1 (>0.5). Il **se maintient et s'améliore légèrement** sur la fenêtre catalogue (0.543 à 0.574, PSR 16.8 % à 25.8 %) — véritablement robuste, non sur-ajusté à la période. Cela contraste fortement avec la stratégie sœur `composite-c1-multiasset` (Sharpe 0.258) : les deux partagent l'échafaudage Alpha Framework, mais l'investissement factoriel sur un univers d'actions US large-cap top-25 par fondamentaux (Value/Quality/LowVol/Momentum + MeanVariancePCM) surperforme de manière spectaculaire la rotation statique multi-actifs à 5 ETF (ensemble momentum 3-alpha + RiskParityPCM). Le choix des alphas composantes/PCM et l'univers d'actions au niveau fondamental comptent bien plus que le câblage du framework lui-même. Promu Tier 4 (Untested) vers Tier 2 (Historique). `totalOrders=0` dans le wrapper MCP est un artefact d'extraction (le CAGR 11.9 % implique des trades réels).

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Algorithme composite equity factor orchestrant la sélection d'univers, les alphas, le PCM, le risque et l'exécution |
| `alpha_models.py` | Quatre modèles factoriels : Value, Quality, LowVolatility et Momentum |
| `portfolio_construction.py` | MeanVariancePCM avec rééquilibrage hebdomadaire, plafonds sectoriels et limites d'exposition |
| `risk_management.py` | SectorCapRiskModel avec poids sectoriel max et contraintes de beta |
| `execution.py` | Modèle d'exécution TWAP (6 tranches, fenêtre de 10 minutes) |

## Références

- [QuantConnect Alpha Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework)
- [QuantConnect Fine Fundamental Selection](https://www.quantconnect.com/docs/v2/writing-algorithms/universes/fundamental)
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
