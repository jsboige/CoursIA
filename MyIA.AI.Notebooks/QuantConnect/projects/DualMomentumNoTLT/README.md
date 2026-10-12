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

## Variante standalone (`main.py`) : rééquilibrage déplacé hors de la tranche de minuit (#20264)

En données journalières, Lean livre les avis de dividende dans une tranche datée de minuit, qui ne porte aucune barre de cotation. IEF verse un dividende chaque mois, et son avis tombe souvent le premier jour de cotation. La garde de mois de `main.py` était alors consommée sur cette tranche : le rééquilibrage décidait sur les cours de la veille, et ses ordres partaient à minuit pour être exécutés à l'ouverture. Sur la fenêtre codée, 109 rééquilibrages sur 120 tombaient à minuit.

Correctif dans `main.py` : le mois n'est consommé que sur une tranche qui porte une barre d'un titre de l'univers. Mesure sur les nœuds QC, frais de courtage inclus, protocole fixé avant les backtests ([#20264, c.6115262186](https://github.com/jsboige/CoursIA/issues/20264#issuecomment-6115262186)) :

| Fenêtre | Variante | Ordres de minuit | Sharpe | CAGR | Drawdown max | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (codée) | avant | 210 (101 jours) | 0.339 | 8.08 % | 23.6 % | 233 | `a09a48809bcb4dc878e84f511dc00d65` |
| | après | 0 | 0.441 | 9.96 % | 21.4 % | 234 | `b2ff070974e440f64029c69473bb7af7` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | avant | 38 (17 jours) | 1.094 | 28.02 % | 14.1 % | 42 | `a5a68f401f9cca13dda2a39dfd02d416` |
| | après | 0 | 1.203 | 30.23 % | 14.0 % | 42 | `bbf5126ce1eac446800cedc56c04f546` |

Sharpe calculé par QC, taux sans risque inclus. Hors échantillon, la règle fixée d'avance donne **pas de dégradation**.

**Limite connue.** Le correctif fait décider le rééquilibrage sur la première barre du mois. En juillet 2017 et en juillet 2023, cette barre est celle du lundi 3 juillet, une demi-séance qui ferme à 13:00. Ces deux mois passent sans rééquilibrage : le code sort sans rien faire quand l'historique est trop court pour tous les titres. Ce défaut des demi-séances est suivi dans [#20286](https://github.com/jsboige/CoursIA/issues/20286) et n'est pas corrigé ici. La variante avant faisait ces deux rééquilibrages, sur la tranche de minuit.

Ces chiffres portent sur la variante standalone, pas sur la variante Framework mesurée plus haut. Ils ne sont pas un verdict de stratégie : il s'agit de la correction d'un défaut, mesurée sur une fenêtre déjà vue. La variante Framework (`alpha_model.py`) porte la même garde de mois et n'est pas mesurée ici.

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
