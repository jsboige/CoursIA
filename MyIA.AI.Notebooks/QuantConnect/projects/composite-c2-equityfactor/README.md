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

### Ce que le composite calculait en fait (#21137, octobre 2026)

Les quatre alphas notent les mêmes titres au même instant, au premier passage de chaque mois. Avant d'appeler `determine_target_percent`, la classe de base Lean (`PortfolioConstructionModel.GetTargetInsights`) ne garde que l'insight actif le plus récent de chaque symbole : sur chaque titre, l'alpha qui émet en dernier efface les autres. C'est le mécanisme déjà mesuré par #19740 sur les `Framework_Composite_*`.

Trois backtests sur QC Cloud, même fenêtre (2018-01-01 à 2025-01-01, 1761 dates tradables), même code, deux paramètres de projet :

| Variante | `pcm_mode` | `alphas` | Sharpe | CAGR | Pire baisse | PSR | Ordres |
|----------|------------|----------|--------|------|-------------|-----|--------|
| A. Code d'avant #21137 | `symbol` | `all` | 0.584 | 13.183 % | 20.500 % | 7.631 % | 7568 |
| B. Témoin : momentum seul | `symbol` | `momentum` | 0.585 | 13.194 % | 20.500 % | 7.650 % | 7362 |
| C. Correction par poches (défaut) | `sleeve` | `all` | 0.441 | 9.126 % | 17.600 % | 3.284 % | 9003 |

Backtests `e8d5fd4f` (A), `122d1a54` (B), `67da341f` (C), projet 37945484.

**Lecture.** A et B sont presque identiques : le composite d'avant #21137 se réduisait au facteur momentum. Les compteurs écrits en fin de backtest (statistiques `PCM <alpha>`, insights actifs / insights reçus par le PCM) le confirment : seuls `MomFactor` (5729 / 23837) et `LowVol` (76 / 328, sur les titres que le momentum ne note pas) atteignent le PCM, `Value` et `Quality` jamais.

La correction par poches (C) garde le dernier insight de chaque couple (symbole, alpha), normalise les scores à l'intérieur de chaque poche, donne une part égale à chaque poche active et additionne par symbole. Elle fait ce que le composite annonce, et fait **moins bien** que le momentum seul sur cette fenêtre : Sharpe 0.441 contre 0.585, avec une volatilité plus basse (9.1 % contre 12.2 %) et une pire baisse plus faible. Verdict : **NO BEATS**. La correction est une correction de comptabilité, pas une amélioration de performance.

**Reste à mesurer.** `ValueAlpha` et `QualityAlpha` lisent `valuation_ratios.price_to_book`, `price_to_earnings`, `operation_ratios.return_on_equity` et `debt_to_equity` par `getattr(..., None)`. Les autres projets du dépôt utilisent `pb_ratio`, `pe_ratio` et `roe`. Si ces noms n'existent pas dans Lean, les deux alphas n'émettent jamais rien, et la variante C ne mélange que LowVol et momentum. Ce point n'est pas encore mesuré et relève d'un grain séparé.

### Paramètres de projet

| Paramètre | Valeurs | Effet |
|-----------|---------|-------|
| `pcm_mode` | `sleeve` (défaut), `symbol` | `symbol` reproduit le PCM d'avant #21137 |
| `alphas` | `all` (défaut), `momentum` | `momentum` ne branche que `MomentumFactorAlpha` (témoin) |

### Historique : baseline publiée avant #21137

Ces chiffres ont été obtenus avec le PCM d'avant #21137, donc avec le seul momentum en pratique. Rejoué en octobre 2026, le même code donne la ligne A ci-dessus : les données et le moteur QC ont évolué entre-temps.

| Métrique | Catalogue (2015-2025) | Alignée (2018-2025) |
|----------|-----------------------|---------------------|
| Sharpe Ratio | 0.543 | 0.574 |
| CAGR | 10.010 % | 11.942 % |
| Max Drawdown | 18.800 % | 18.600 % |
| PSR | 16.822 % | 25.765 % |

Backtest `8eecba32` (alignée) / `3173f8b39` (catalogue `c2-equityfactor-post2801`), projet 32981222. L'interprétation qui accompagnait ces chiffres (avantage de l'investissement factoriel à quatre facteurs sur la rotation multi-actifs de `composite-c1-multiasset`) ne tient plus : la performance mesurée était celle du momentum seul.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Algorithme composite equity factor orchestrant la sélection d'univers, les alphas, le PCM, le risque et l'exécution |
| `alpha_models.py` | Quatre modèles factoriels : Value, Quality, LowVolatility et Momentum |
| `portfolio_construction.py` | MeanVariancePCM avec rééquilibrage hebdomadaire, plafonds sectoriels et limites d'exposition ; mode par poches (`by_sleeve`) et compteurs par alpha (#21137) |
| `risk_management.py` | SectorCapRiskModel avec poids sectoriel max et contraintes de beta |
| `execution.py` | Modèle d'exécution TWAP (6 tranches, fenêtre de 10 minutes) |

## Références

- [QuantConnect Alpha Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework)
- [QuantConnect Fine Fundamental Selection](https://www.quantconnect.com/docs/v2/writing-algorithms/universes/fundamental)
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
