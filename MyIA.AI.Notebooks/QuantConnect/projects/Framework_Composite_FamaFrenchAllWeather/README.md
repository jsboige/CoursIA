# Framework Composite - FamaFrench + AllWeather

## Description

Stratégie composite combinant deux approches complémentaires via le QuantConnect Algorithm Framework :

1. **FamaFrench (tranche 20 %)** : Rotation d'ETF factoriels (VLUE, MTUM, SIZE, QUAL, USMV)
   - Momentum ajusté du risque (rendement/volatilité sur 3/6/12 mois)
   - Skip-month (exclure le dernier mois pour éviter le retournement court terme)
   - Top-2 facteurs par momentum ajusté du risque
   - Rééquilibrage trimestriel

2. **AllWeather (tranche 80 %)** : Allocation statique multi-actifs (SPY 30 %, IEF 30 %, GLD 30 %, XLP 10 %)
   - Portefeuille « All Weather » inspiré de Ray Dalio (simplifié, sans TLT)
   - Rééquilibrage par dérive (seuil 3 %)
   - Rééquilibrage mensuel

## Principe de conception clé

**PAS de chevauchement entre univers** : ETF factoriels (facteurs actions) vs actifs traditionnels (actions/obligations/or). Cela crée une vraie diversification :
- FamaFrench : exposition aux facteurs actions (value, momentum, size, quality, low-vol)
- AllWeather : allocation macro (actions, obligations, or, défensif)

**Important** : FamaFrench utilise le momentum ajusté du risque UNIQUEMENT (pas de filtre SMA200). AllWeather gère la défense via son allocation statique.

## Fichiers

- `main.py` : Configuration de l'algorithme avec CompositeAlpha et MultiStrategyPCM
- `alpha_models.py` : Classes FamaFrenchAlpha et AllWeatherAlpha
- `portfolio_construction.py` : MultiStrategyPCM pour l'allocation de capital par stratégie
- `quantbook.ipynb` : Notebook de recherche avec analyse de backtest

## Performance

| Métrique | Valeur |
|----------|--------|
| Sharpe Ratio | **0.588** |
| CAGR | 9.9 % |
| Max Drawdown | 17.1 % |
| Période | 2010-2026 |

### Baseline alignée (2018-2025)

Fenêtre #1630 standardisée (2018-01-01 à 2025-01-01, 1761 dates tradables), backtestée sur QC Cloud avec frais réels post-#2801.

| Métrique | Headline README (sweep 2010-2026) | Catalogue (2015-2025) | **Alignée (2018-2025)** |
|----------|-----------------------------------|-----------------------|-------------------------|
| Sharpe | 0.588 | 0.472 | **0.338** |
| CAGR | 9.9 % | 7.226 % | 6.578 % |
| MaxDD | 17.1 % | 13.1 % | 13.1 % |
| PSR | — | 35.0 % | 22.9 % |

Backtest aligné `e9ac7c66` (1761 dates tradables, Completed) / backtest catalogue `70415edc` (`FF20_AW80_2015_2025_extended`, 2766 dates). `totalOrders=0` est un artefact d'extraction du wrapper MCP (le CAGR 6.6 % implique des trades réels) ; les statistiques calculées par QC sont fiables.

**Caveat de sur-ajustement de période** : les chiffres headline solides ne survivent PAS à l'alignement sur la fenêtre standardisée 2018-2025. Le Sharpe headline du README 0.588 (sweep 2010-2026) chute à **0.338** (-42 %), et le chiffre OOS 2023-2026 séparément (Sharpe 0.684, PSR 87.5 % — backtest `b08c8956`, seulement 835 dates tradables) s'effondre à 0.338 / PSR 22.9 % sur la fenêtre alignée complète : le PSR 87.5 % était un artefact de petit échantillon OOS, pas un avantage statistique robuste. Sur la fenêtre alignée, le sleeve AllWeather 80 % (largement statique SPY/IEF/GLD/XLP) tire le composite sous la rotation FamaFrench autonome (Sharpe 0.445, #72), bien qu'il achète un contrôle serré du drawdown (MaxDD 13.1 %, parmi les backbones les plus serrés). Promu Tier 4 (Untested) vers Tier 2 (Historique).

## Résultats du sweep d'allocation

| Allocation | Sharpe | CAGR | Max DD |
|------------|--------|------|--------|
| FF20/AW80 | **0.588** | 9.9 % | 17.1 % |
| FF40/AW60 | 0.564 | 10.5 % | 19.3 % |
| FF50/AW50 | 0.539 | 10.8 % | 21.7 % |
| FF60/AW40 | 0.512 | 11.2 % | 24.1 % |

**Gagnant** : FF20/AW80 (meilleurs rendements ajustés du risque)

## Stratégies composantes

| Stratégie | Sharpe | CAGR | Max DD |
|-----------|--------|------|--------|
| FamaFrench v3.0 | 0.540 | 12.1 % | 24.2 % |
| AllWeather | 0.667 | 9.3 % | 16.4 % |
| **Composite (FF20/AW80)** | **0.588** | **9.9 %** | **17.1 %** |

Le composite atteint de meilleurs rendements ajustés du risque que FamaFrench seul, avec un drawdown plus faible.

## Paramètres

| Paramètre | Défaut | Description |
|-----------|--------|-------------|
| `ff_allocation` | 0.20 | Tranche FamaFrench (0.20 = 20 %) |
| `aw_allocation` | 0.80 | Tranche AllWeather (0.80 = 80 %) |

## Période de backtest

2010-01-01 à 2026-03-10 (couvre les régimes haussier, baissier et latéral)

## Déploiement

- **Project ID** : 28882145
- **Organization** : Jean-Sylvain Boige (Researcher PAID)
- **Statut** : ✅ Déployé et backtesté

## Références

- **FamaFrench** : Rotation d'ETF factoriels avec momentum ajusté du risque
- **AllWeather** : Allocation statique multi-actifs (sans TLT)
- **SESSION5_PATTERNS.md** : Guide pédagogique AlphaModel Framework
