# DualMomentumNoTLT — Momentum dual sans TLT (variante Antonacci)

**Classe d'actifs :** Multi-actifs (SPY, QQQ, IEF, GLD, XLP)
**Cloud project ID :** 31244186 (variante Framework)
**Période backtestée :** 2015-01-01 → 2024-12-31

## Description

Stratégie de **rotation momentum dual multi-actifs** (Gary Antonacci, *Dual Momentum Investing*, 2014) **excluant les obligations long terme (TLT)**. Le momentum **absolu** (rendement 12 mois > 0) filtre les actifs en tendance négative ; le momentum **relatif** sélectionne les 2 meilleurs rendements 12 mois parmi les survivants, en pondération égale (50 % chacun). Si aucun actif ne passe le filtre absolu, le portefeuille bascule entièrement en cash.

**Pourquoi « No TLT » ?** TLT (obligations US long terme, ~20+ ans) a perdu ~40 % durant le cycle de hausses de taux 2020-2023. Cette variante remplace la duration longue par IEF (obligations intermédiaires 7-10 ans), GLD (or) et XLP (consumer staples) comme diversifiants. Le **trade-off pédagogique** : retirer TLT évite la perte de duration quand les taux montent, **mais** retire aussi un refuge *flight-to-quality* lors des crashes actions (TLT grimpe en mars 2020). Ce compromis est lisible dans le drawdown (cf. lecture honnête ci-dessous).

**Version anglaise préservée** : [README.en.md](README.en.md).

## Logique de la stratégie

| Composant | Paramètre | Rôle |
|-----------|-----------|------|
| Univers | SPY, QQQ, IEF, GLD, XLP | 5 actifs diversifiés |
| Lookback | 252 jours (12 mois) | Mesure du momentum |
| Filtre absolu | rendement 12M > 0 | Écarter le momentum négatif |
| Sélection | Top 2 par rendement 12M | Momentum relatif |
| Pondération | Égale | 50 % par position |
| Rebalancement | Mensuel | Calendaire |

## Backtest réel (QC Cloud, variante Framework, frais IBKR margin inclus)

| Métrique | Valeur |
|----------|--------|
| Sharpe ratio | **0.633** |
| CAGR | **16.91 %** |
| Drawdown max | **34.50 %** |
| Rendement total net | 377.4 % (+317 497 $ sur 100 k $) |
| PSR (Probabilistic Sharpe Ratio) | **5.98 %** |
| Ordres exécutés | 2238 |
| Jours tradés | 2516 |

*Backtest frais via QC Cloud project 31244186 (compile `BuildSuccess`, 2026-08-06). Métriques vérifiées, pas claim de docstring.*

### Lecture honnête — CAGR supérieur à SPY, drawdown coûteux, skill statistiquement faible

La stratégie **bat le benchmark SPY** en rendement absolu (CAGR 16.91 % vs ~12-13 % pour SPY sur 2015-2024), principalement parce que la rotation momentum garde QQQ (tech, forte hausse de la décennie) dans le top-2 lors des années de bull market. **Mais** :

- **Drawdown de 34.50 %** — considérable. C'est le coût du « No TLT » : sans la duration longue comme refuge *flight-to-quality*, le portefeuille n'avait nulle part où se cacher lors des sell-offs *cross-asset* (2022 : actions, or et obligations intermédiaires ont chuté ensemble). À comparer au Trend-Following AQR (MaxDD 15 %) qui, lui, bascule vers un safe-haven explicite en régime baissier. Le momentum dual **rot** dans les actifs qui tombent ; il ne **fuit** pas.
- **PSR à 5.98 %** — malgré un CAGR supérieur au marché, la probabilité que le ratio de Sharpe soit **statistiquement supérieur à zéro** reste faible (~6 %). Le rendement excédentaire observé n'est **pas** une preuve de compétence prédictive ; il s'explique en grande partie par l'exposition beta au momentum tech (QQQ) durant une décennie haussière atypique.

**Conclusion honnête** : ne PAS présenter cette stratégie comme génératrice d'alpha statistiquement significatif. C'est un **beta de momentum géré** avec un **drawdown élevé** — l'exemple pédagogique de la limite du momentum dual « rotation pure » sans overlay de protection. Le companion naturel est la DualMomentum (avec TLT) — un contre-exemple documenté (TLT a saboté 2020-2023) — cf. [DualMomentum/README](../DualMomentum/README.md). Les deux illustrent le **même compromis** : un diversifiant qui aide dans un régime nuit dans l'autre.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT"`
**QC Cloud :** Déployé comme projet 31244186 (variante Framework avec `alpha_model.py`).

## Architecture

Le projet embarque **deux implémentations** de la même stratégie, qui diffèrent en turnover :

- **`alpha_model.py` + `main.py` (Framework, déployée/backtestée)** — version AlphaModel QC : `DualMomentumAlpha` (émission mensuelle d'insights prix 30 jours) + `InsightWeightingPortfolioConstructionModel` + `ImmediateExecutionModel`. **C'est la version déployée et backtestée ci-dessus.** Le docstring cible explicitement « Sharpe within ±15 % du standalone » — les deux variantes ne sont donc pas identiques par construction.
- **`main.py` (standalone)** — version `QCAlgorithm` directe qui positionne les holdings mensuellement sans passage par insights. Logiquement équivalente mais **turnover plus faible** (pas d'expiration/churn d'insights).
- `config_framework.json` — configuration QC Framework.
- `quantbook.ipynb` — recherche (analyse des signaux momentum).
- `dual_momentum_notl_analysis.png` — figure d'analyse.

**Note doc-honesty** : les métriques ci-dessus sont celles de la **variante Framework** (2238 ordres sur 2516 jours, churn d'expiration d'insights). La variante standalone, à turnover plus faible, donnerait des frais de transaction moindres et possiblement un Sharpe légèrement différent (cible ±15 %). Backtester les deux et comparer est un exercice pédagogique pertinent.

## Concepts enseignés

- **Momentum dual** (Antonacci 2014) : combinaison d'un filtre **absolu** (rendement > 0) et d'un classement **relatif** (top-N).
- **Trade-off de diversification** : un même actif (TLT) peut être nuisance dans un régime (hausses de taux) et refuge dans un autre (flight-to-quality) — retirer un diversifiant est un pari sur le régime futur.
- **Momentum rotation vs safe-haven switch** : comparer le drawdown de cette stratégie (34.5 %, rotation pure) à celui du Trend-Following (15 %, avec bascule safe-haven) isole la valeur de l'overlay défensif.
- **Probabilistic Sharpe Ratio (PSR)** : un CAGR supérieur au marché ≠ skill statistiquement significative (5.98 % ici).
- **Variante Framework vs standalone** : l'architecture AlphaModel + Insight-weighting PCM introduit un turnover (expiration d'insights) que n'a pas la version directe — illustration qu'un même énoncé de stratégie peut donner des métriques différentes selon le harnais QC.
