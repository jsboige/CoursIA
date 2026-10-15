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

Ce README a longtemps affiché pour cette variante un Sharpe de 0.633, un CAGR de 16.91 % et un drawdown de 34.50 % (projet QC 31244186, 2238 ordres, 2026-08-06). Ces chiffres venaient d'un défaut du code, corrigé dans [#20388](https://github.com/jsboige/CoursIA/issues/20388) :

- `InsightWeightingPortfolioConstructionModel` ignore les insights qui ne portent pas de poids. Les insights `FLAT` de `DualMomentumAlpha` n'en portaient pas : la cible `UP` précédente restait en place, et une ligne sortie du top-2 n'était jamais vendue.
- Le compte est sur marge par défaut. Les lignes s'accumulaient donc à crédit : avant 104 émissions sur 120, le portefeuille portait les 5 titres, et son exposition brute atteignait 1.71 fois la valeur nette en fin de période. Une partie des achats dépassait même la marge disponible : 282 ordres d'achat refusés pour pouvoir d'achat insuffisant.
- Correctif : les insights `FLAT` portent `weight=0`. Le même correctif reprend la garde de barres (#20264) et la demande d'historique doublée (#20286) de la variante standalone, décrites plus bas.

Mesure sur les nœuds QC, frais de courtage inclus, sept prédictions fixées avant les backtests ([#20388, c.6200954314](https://github.com/jsboige/CoursIA/issues/20388#issuecomment-6200954314)), toutes tenues ([résultat, c.6201190294](https://github.com/jsboige/CoursIA/issues/20388#issuecomment-6201190294)) :

| Fenêtre | Variante | Sharpe | CAGR | Drawdown max | Ordres | Refusés | Lignes détenues | Exposition brute | Backtest |
|---|---|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (codée) | avant | 0.633 | 16.89 % | 34.4 % | 2225 | 282 | 5 avant 104 émissions sur 120 | 1.71 en fin de période | `0f8e0f58df1b2dc01eeb20d35cde65f9` |
| | après | 0.442 | 10.00 % | 21.5 % | 1410 | 0 | 2 au plus | 0.998 au plus | `02551c21423f1aa958678303eca6ec2b` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | avant | 1.17 | 35.03 % | 16.0 % | 396 | 0 | 4 dans 16 émissions sur 19 | 1.68 au plus | `36c1d64eef77b6a5552ae4616d56e240` |
| | après | 1.20 | 29.94 % | 13.9 % | 374 | 0 | 2 | 0.998 au plus | `c0081f5801967cd1880997c1c67f5b1e` |

Sharpe calculé par QC, taux sans risque inclus. La ligne « avant » de la fenêtre codée est le backtest de référence de #20264, qui tourne le code du projet 31244186 (2225 ordres contre 2238 dans le tableau historique du 6 août ; ces deux exécutions distinctes ne sont pas confondues, et la cause de cet écart n'est pas établie ici). Lignes détenues et exposition brute sont reconstruites à partir des remplissages, juste avant chaque émission ; la trésorerie n'y compte pas les dividendes, si bien que l'exposition est une borne haute.

### Lecture honnête — le CAGR de 16,9 % venait du levier, pas du signal

Une fois le défaut corrigé, la variante Framework rejoint la variante standalone corrigée : Sharpe 0.442 contre 0.446, CAGR 10.00 % contre 10.05 %, drawdown 21.5 % contre 21.4 %. La stratégie **ne bat plus SPY** en rendement absolu sur 2015-2024 (~12-13 % par an pour SPY). Hors échantillon, le CAGR baisse de 35.0 % à 29.9 % pour la même raison, et le Sharpe ne baisse pas.

- **Drawdown de 21.5 %**, contre 34.4 % avant correction : l'écart vient surtout du levier. Il reste au-dessus de celui du Trend-Following AQR (MaxDD 15 %), qui bascule vers un safe-haven explicite en régime baissier. Sans la duration longue comme refuge *flight-to-quality*, le momentum dual **tourne** dans les actifs qui tombent ; il ne **fuit** pas. La date du drawdown n'est pas mesurée ici.
- **PSR à 1.4 %** sur la fenêtre codée : la probabilité que le ratio de Sharpe soit **statistiquement supérieur à zéro** est faible. Le rendement observé n'est **pas** une preuve de compétence prédictive ; il s'explique en grande partie par l'exposition au momentum tech (QQQ) durant une décennie haussière atypique.
- **Frais** : 1 606 $ sur dix ans pour la variante Framework, contre 434 $ pour la variante standalone (`a32a1a24f317c96e5d0fe2bbb00ca583`). Sans fonction de rééquilibrage, le modèle de construction de portefeuille re-cible chaque jour les lignes actives et envoie de petits ajustements : 1410 ordres contre 239, dont 90 % hors des jours d'émission.

**Conclusion honnête** : ne PAS présenter cette stratégie comme génératrice d'alpha statistiquement significatif. C'est un **beta de momentum géré**, avec un drawdown supérieur à celui d'une stratégie à bascule défensive — l'exemple pédagogique de la limite du momentum dual « rotation pure » sans overlay de protection. Le défaut corrigé ci-dessus donne une seconde leçon : un CAGR qui bat le marché se vérifie d'abord sur les positions détenues, avant d'être attribué au signal. Le companion naturel est la DualMomentum (avec TLT) — un contre-exemple documenté (TLT a saboté 2020-2023) — cf. [DualMomentum/README](../DualMomentum/README.md). Les deux illustrent le **même compromis** : un diversifiant qui aide dans un régime nuit dans l'autre.

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

### Demi-séances : les deux mois manquants (#20286)

Le correctif ci-dessus fait décider le rééquilibrage sur la première barre du mois. En juillet 2017 et en juillet 2023, cette barre est celle du lundi 3 juillet, une demi-séance qui ferme à 13:00. Sur cette tranche, une demande d'historique journalier par nombre de barres rend environ 21 barres de moins que demandé. La garde de longueur écartait alors les cinq titres, et ces deux mois passaient sans rééquilibrage.

`main.py` demande désormais deux fois plus de barres et garde les plus récentes. Sur une séance pleine, ce sont les mêmes barres qu'avant. Mesure sur les nœuds QC, protocole et prédictions fixés avant les backtests ([#20286, c.6131650205](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6131650205)). La ligne « avant » est la ligne « après » du tableau précédent :

| Fenêtre | Variante | Mois rééquilibrés | Sharpe | CAGR | Drawdown max | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (codée) | avant | 118 / 120 | 0.441 | 9.96 % | 21.4 % | 234 | `b2ff070974e440f64029c69473bb7af7` |
| | après | 120 / 120 | 0.446 | 10.05 % | 21.4 % | 239 | `a32a1a24f317c96e5d0fe2bbb00ca583` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | avant | 19 / 19 | 1.203 | 30.23 % | 14.0 % | 42 | `bbf5126ce1eac446800cedc56c04f546` |
| | après | 19 / 19 | 1.203 | 30.23 % | 14.0 % | 42 | `91eae7e7741ff46af96b5cd83dbccc5a` |

Les quatre prédictions tiennent :

- les deux lundis de juillet ont désormais leur ligne `REBAL`, et ce sont les seules dates ajoutées ;
- jusqu'au 30 juin 2017, les ordres sont identiques à ceux d'avant ;
- hors échantillon, aucune première barre de mois n'est une demi-séance, et le résultat est identique au centime (mêmes ordres, mêmes statistiques).

Le 3 juillet 2017, la sélection ne change pas (QQQ et SPY) : le rééquilibrage ne fait qu'ajuster les quantités. Le 3 juillet 2023, il vend l'or et passe sur QQQ et SPY un mois plus tôt que la variante avant. L'écart de Sharpe (+0,005) reste sous le seuil de 0,05 fixé d'avance.

Ces chiffres portent sur la variante standalone. Ils ne sont pas un verdict de stratégie : il s'agit de la correction de deux défauts, mesurée sur des fenêtres déjà vues. La variante Framework (`alpha_model.py`) a reçu les deux mêmes correctifs dans #20388, mesurés avec celui des insights `FLAT` dans le tableau du haut.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT"` (variante standalone, `main.py`).
**QC Cloud :** pour la variante Framework, déployer `main_framework.py` sous le nom `main.py`, avec `alpha_model.py`. Le projet QC 31244186 porte cette variante dans sa version d'avant #20388.

## Architecture

Le projet embarque **deux implémentations** de la même stratégie :

- **`main_framework.py` + `alpha_model.py` (Framework)** — version AlphaModel QC : `DualMomentumAlpha` (émission mensuelle d'insights prix 30 jours) + `InsightWeightingPortfolioConstructionModel` + `ImmediateExecutionModel`. C'est la variante mesurée dans le tableau du haut. Son docstring vise un « Sharpe within ±15 % du standalone » ; après #20388, l'écart mesuré est de 1 %.
- **`main.py` (standalone)** — version `QCAlgorithm` directe qui rééquilibre les positions une fois par mois, sans passer par des insights. C'est elle que lance `lean backtest`.
- `config_framework.json` — configuration QC Framework.
- `quantbook.ipynb` — recherche (analyse des signaux momentum).
- `dual_momentum_notl_analysis.png` — figure d'analyse.

**Ce qui distingue encore les deux variantes** : le nombre d'ordres. Sans fonction de rééquilibrage, `InsightWeightingPortfolioConstructionModel` recalcule ses cibles chaque jour tant que les insights sont actifs, et envoie un petit ajustement dès que les prix ont fait dériver les poids : 1410 ordres en dix ans contre 239 pour la variante standalone, et 1 606 $ de frais contre 434 $. Passer une fonction de rééquilibrage mensuelle au modèle de construction de portefeuille est un exercice pédagogique pertinent ; il n'est pas mesuré ici.

## Concepts enseignés

- **Momentum dual** (Antonacci 2014) : combinaison d'un filtre **absolu** (rendement > 0) et d'un classement **relatif** (top-N).
- **Trade-off de diversification** : un même actif (TLT) peut être nuisance dans un régime (hausses de taux) et refuge dans un autre (flight-to-quality) — retirer un diversifiant est un pari sur le régime futur.
- **Momentum rotation vs safe-haven switch** : comparer le drawdown de cette stratégie (21.5 %, rotation pure) à celui du Trend-Following (15 %, avec bascule safe-haven) isole la valeur de l'overlay défensif.
- **Probabilistic Sharpe Ratio (PSR)** : un Sharpe positif ≠ skill statistiquement significative (1.4 % ici).
- **Variante Framework vs standalone** : un même énoncé de stratégie peut donner des métriques différentes selon le harnais QC. Ici, un insight `FLAT` sans poids, ignoré par le modèle de construction de portefeuille, faisait porter au compte jusqu'à 1.7 fois sa valeur nette ; une fois corrigé, il reste l'écart de turnover dû au re-ciblage quotidien.
