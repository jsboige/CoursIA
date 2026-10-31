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

La variante C ne mélangeait en fait que LowVol et le momentum : Value et Quality n'émettaient rien, pour deux raisons mesurées par #21141 (section suivante).

### Value et Quality branchés (#21141, octobre 2026)

Deux défauts empêchaient `ValueAlpha` et `QualityAlpha` d'émettre, et tous deux passaient sans erreur :

1. **Noms de champs.** La sélection fine lisait `valuation_ratios.price_to_book`, `price_to_earnings`, `operation_ratios.return_on_equity` et `debt_to_equity` par `getattr(..., None)` sous un `try/except`. Ces noms n'existent pas dans Lean : les quatre champs valaient `None` à chaque lecture (0 sur 50350). Les noms corrects sont `pb_ratio`, `pe_ratio` (des nombres), `roe` et `total_debt_equity_ratio` (des champs multi-périodes, lus par `.value`).
2. **Cache invisible.** Les deux alphas lisaient le cache fondamental par `getattr(algorithm, 'fundamental_cache', {})`. L'objet que le framework leur passe ne porte pas l'attribut Python posé par la sélection : le `{}` par défaut revenait à chacun des 84 appels mensuels, et l'alpha sortait sans score. Les deux alphas reçoivent désormais l'algorithme Python à leur construction (`owner=self`).

Les deux backtests finaux, même fenêtre et même projet que la section précédente :

| Variante | `pcm_mode` | `alphas` | Sharpe | CAGR | Pire baisse | PSR | Ordres |
|----------|------------|----------|--------|------|-------------|-----|--------|
| B''. Témoin : momentum seul | `symbol` | `momentum` | 0.585 | 13.194 % | 20.500 % | 7.650 % | 7362 |
| F. Quatre facteurs par poches (défaut) | `sleeve` | `all` | 0.301 | 7.106 % | 18.900 % | 1.195 % | 9685 |

Backtests `f678eaad` (B'') et `4482adb4` (F), projet 37945484. Statistiques écrites en fin de backtest : `Emitted Value` 504/2099 et `Emitted Quality` 496/2062 (insights UP / insights émis), `Cache Value` et `Cache Quality` 84/84 (appels où l'ancienne lecture du cache ne voyait rien / appels).

**Lecture.** B'' reproduit B à l'identique : le nouveau code de lecture ne touche pas au momentum seul. Avec ses quatre facteurs effectivement branchés, le composite fait moins bien que le momentum seul (Sharpe 0.301 contre 0.585) et moins bien que le mélange LowVol et momentum de la variante C (0.441). Sa volatilité est la plus basse des trois (8.7 % contre 12.2 % pour le momentum seul) et sa pire baisse reste sous celle du témoin, mais le rendement baisse davantage que le risque. Verdict : **NO BEATS**, selon une règle écrite avant les backtests. Une fenêtre unique, déjà vue : le verdict porte sur la conception du composite, pas sur une validation hors échantillon.

**Reproduction (#22788).** Le run « avant » de #21471, lancé le 2026-10-25 sur le même code (#21170), la même fenêtre et les paramètres par défaut, donne pour F un Sharpe de 0.290, un CAGR de 6.993 %, une pire baisse de 19.400 % et 9805 ordres (backtest `ab849b70`). La comparaison des ordres remplis des deux runs, titre par titre, situe l'écart dans les données : 42 des 44 titres sont remplis exactement au même prix, et les deux autres à un facteur constant près sur toute la fenêtre (PG : 1.00662 sur ses 205 remplissages ; ASML : 1.00134 sur un remplissage). Un facteur constant par titre est la trace d'une réécriture de l'historique ajusté entre les deux dates, comme en produit un dividende ajouté à la série ; les dates de détachement ne sont pas relevées ici. Le 2018-01-03, les 21 ordres des deux runs sont identiques ; le 2018-01-04, seul PG diffère (5 titres achetés contre 6, la quantité dépendant du prix), puis le portefeuille suit un autre chemin. Les chiffres du tableau sont donc ceux du 2026-10-17 : un nouveau run sur le même code donne des chiffres voisins, pas identiques. La dérive mesurée sur F (0.011 de Sharpe) est petite devant l'écart au témoin (0.284) et le verdict ne change pas ; le témoin B'' n'a pas été relancé.

Les statistiques `PCM <alpha>` comptent ce que la classe de base passe au PCM après sa déduplication par symbole. Le mode par poches reconstruit ses poches en amont, à partir de tous les insights actifs : ces compteurs ne mesurent donc pas ce qu'il consomme.

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
| `main.py` | Algorithme composite equity factor orchestrant la sélection d'univers, les alphas, le PCM, le risque et l'exécution ; cache fondamental et compteurs `Emitted`, `Field` et `Cache` (#21141) |
| `alpha_models.py` | Quatre modèles factoriels : Value, Quality, LowVolatility et Momentum ; Value et Quality lisent le cache par l'algorithme Python passé à leur construction (#21141) |
| `portfolio_construction.py` | MeanVariancePCM avec rééquilibrage hebdomadaire, plafonds sectoriels et limites d'exposition ; mode par poches (`by_sleeve`) et compteurs par alpha (#21137) |
| `risk_management.py` | SectorCapRiskModel avec poids sectoriel max et contraintes de beta |
| `execution.py` | Modèle d'exécution TWAP (6 tranches, fenêtre de 10 minutes) |

## Références

- [QuantConnect Alpha Framework](https://www.quantconnect.com/docs/v2/writing-algorithms/algorithm-framework)
- [QuantConnect Fine Fundamental Selection](https://www.quantconnect.com/docs/v2/writing-algorithms/universes/fundamental)
- [QuantConnect Documentation](https://www.quantconnect.com/docs/)
