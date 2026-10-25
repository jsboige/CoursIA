# DualMomentumNoTLT — Momentum dual sans TLT (variante Antonacci)

**Classe d'actifs :** Multi-actifs (SPY, QQQ, IEF, GLD, XLP)
**Cloud project ID :** 31244186 (variante Framework)
**Projets de la mesure #21669 :** `38183910` (code actuel, avec les modes de référence) · `38183905` (contrôle, code d'origine)
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

Une fois le défaut corrigé, la variante Framework rejoint la variante standalone corrigée : Sharpe 0.442 contre 0.446, CAGR 10.00 % contre 10.05 %, drawdown 21.5 % contre 21.4 %. La stratégie **ne bat plus SPY** en rendement absolu sur 2015-2024 : SPY détenu dans le même algorithme fait 12,97 % par an, et la stratégie ne le bat pas non plus en Sharpe (mesure #21669, section « Verdict contre références détenues »). Hors échantillon, le CAGR baisse de 35.0 % à 29.9 % pour la même raison, et le Sharpe ne baisse pas.

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

## Paramètres de la variante standalone

| Paramètre | Valeurs | Défaut | Rôle |
|---|---|---|---|
| `mode` | `strategy`, `spy`, `6040`, `ew5` | `strategy` | `strategy` garde la décision du code ; `spy` détient SPY à 100 % ; `6040` détient SPY à 60 % et BND à 40 % ; `ew5` détient les cinq titres de l'univers à poids égal. Les références sont rééquilibrées au début de chaque mois, une minute après l'ouverture |
| `start_date` | date `%Y%m%d` | 2015-01-01 | début de la fenêtre |
| `end_date` | date `%Y%m%d` | 2024-12-31 | fin de la fenêtre |

Les quatre modes tracent chaque jour la valeur du portefeuille à l'ouverture de SPY (graphique `shadow`, séries `e0` à `e4`). En mode référence, `on_data` sort aussitôt : la stratégie ne décide rien. BND n'est abonné qu'en mode `6040`. Sans paramètre, la décision de la stratégie ne change pas : le contrôle ci-dessous le vérifie ordre par ordre.

## Verdict contre références détenues (#21669)

Le protocole a été écrit dans #21669 avant le premier backtest, sur le modèle de #21329 et #21594. Les deux références du verdict, SPY détenu et le 60/40, tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Une troisième référence, les cinq titres de l'univers à poids égal (`ew5`), sert de diagnostic et ne compte pas dans le verdict : elle demande si la règle de momentum ajoute quelque chose à la simple détention des mêmes titres.

Quatre propriétés du code sont gardées telles quelles :

- la stratégie détient au plus deux titres : deux à 50 % chacun, ou un seul à 100 % quand un seul rendement sur 12 mois est positif. Son risque est concentré, celui de `ew5` est réparti sur cinq titres ;
- elle n'est pas toujours investie. Sur la fenêtre codée, l'exposition est nulle du 2023-03-02 au 2023-04-04 : un mois entier en liquidités, le seul cas où le code passe en liquidités étant qu'aucun rendement sur 12 mois ne soit positif. Après la fenêtre codée, elle ne l'est que les tout premiers jours, avant le premier remplissage ;
- le compte est déclaré sur marge. Les poids visés somment au plus à 100 %, et l'exposition observée dépasse à peine 1 : au plus 1,0089 sur la fenêtre codée (janvier 2019), au-dessus de 1 sur 182 des 3 654 points quotidiens du graphique d'exposition de QC. Après la fenêtre codée, le maximum est de 1,0006 (avril 2025), sur 30 points de 569 ;
- les ordres de la stratégie sont soumis à la clôture de la première séance du mois : 16 h, heure de New York, et 13 h les deux jours de demi-séance (3 juillet 2017 et 3 juillet 2023, cf. #20286). Lean les passe en ordres au marché à l'ouverture, remplis à la séance suivante. Aucun n'est passé à minuit.

Les séries comparées sont la valeur du portefeuille à chaque ouverture de SPY. Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Le diagnostic est une exécution séparée, avec sa propre correction de Holm sur trois p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit le backtest du code d'origine (`b91de30a86a6396f2782b7e56a86a0ea`, projet 38183905) :

- 239 ordres sur 239, sans écart de date, de symbole ni de quantité ;
- 27 statistiques QC sur 27. Ce sont aussi celles publiées plus haut pour la variante standalone après #20286 (Sharpe QC 0,446, CAGR 10,05 %, 239 ordres).

| Fenêtre | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Codée, 2015-01-02 → 2024-12-31 | 2516 | 0,730 | 0,786 | 0,802 | 1,0 / 1,0 | **NO BEATS** |
| Hors échantillon, 2025-01-02 → 2026-07-22 | 388 | 1,558 | 1,063 | 1,180 | 1,0 / 1,0 | **INCONCLUSIVE** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus.

| Fenêtre | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Écart-type annuel | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| Codée | stratégie | 0,446 | 10,05 % | 21,4 % | 0,122 | 239 | `2bb5cfd719626bf4252a4833f4feaf96` |
| Codée | SPY détenu | 0,533 | 12,97 % | 33,7 % | 0,146 | 1 | `4435593eb600049559cad42ed343f1c7` |
| Codée | 60/40 | 0,442 | 8,41 % | 21,7 % | 0,090 | 201 | `20df703f10f503d24122776e7c609ede` |
| Codée | cinq titres à poids égal | 0,569 | 9,85 % | 19,3 % | 0,087 | 413 | `31518a3b58f0320aa90e08676b4cc037` |
| Hors échantillon | stratégie | 1,103 | 27,96 % | 14,0 % | 0,142 | 42 | `60c267120580e1ad4bdf04cf86bc46b4` |
| Hors échantillon | SPY détenu | 0,646 | 18,37 % | 18,7 % | 0,145 | 2 | `9d779079ddb90e09ca96bce567b16c38` |
| Hors échantillon | 60/40 | 0,546 | 12,68 % | 11,2 % | 0,089 | 30 | `5976aca33047764d68a33189a99e2538` |
| Hors échantillon | cinq titres à poids égal | 0,899 | 17,47 % | 8,8 % | 0,090 | 70 | `b167db74c6736815fbcf55c6b44ff73d` |

Le backtest hors échantillon a été demandé jusqu'au 2026-10-20, mais il s'arrête le 2026-07-22 : les nœuds QC utilisés coupent les backtests environ 90 jours avant la date du jour. Sur ses 388 séances, la fenêtre a peu de puissance. Aucun paramètre n'a été réglé sur cette période.

**Lecture.** Sur la fenêtre codée, la stratégie a le Sharpe ponctuel le plus bas des trois portefeuilles du verdict : 0,730 contre 0,786 pour SPY détenu et 0,802 pour le 60/40. Aucun écart n'est significatif (p brutes de Ledoit-Wolf 0,77 et 0,72, intervalles bootstrap à 95 % de −0,45 à +0,28 contre SPY et de −0,48 à +0,28 contre le 60/40), mais la règle ne demande pas de test pour ce cas : le Sharpe est sous celui de SPY détenu, le verdict est `NO BEATS`. Hors échantillon, la stratégie a le Sharpe ponctuel le plus élevé (1,558 contre 1,063 et 1,180). L'écart n'est significatif contre aucune référence (p brutes 0,49 et 0,60, intervalle bootstrap contre SPY de −1,05 à +1,88) : `INCONCLUSIVE`, comme annoncé dans le protocole pour une fenêtre aussi courte.

**Diagnostic : la règle de momentum n'ajoute rien de mesurable à la détention des cinq titres.** Sur la fenêtre codée, les cinq titres détenus à poids égal ont un Sharpe à taux nul de 0,957, contre 0,730 pour la stratégie. L'écart (−0,227) n'est pas significatif (p de Holm 0,631 pour Ledoit-Wolf, intervalle bootstrap de −0,60 à +0,11) ; selon la règle écrite avant la mesure, un Sharpe inférieur à celui de `ew5` suffit à conclure que la règle n'ajoute rien de mesurable. L'écart vient du risque, pas du rendement : les deux portefeuilles ont un CAGR voisin (10,05 % et 9,85 %), mais la stratégie, concentrée sur deux titres, a un écart-type annuel de 0,122 contre 0,087. Hors échantillon, les deux Sharpe sont presque égaux (1,558 et 1,550, écart +0,008, p de Holm 1,0). Le momentum choisit quels titres détenir ; sur ces deux fenêtres, ce choix ne fait pas mieux que de les détenir tous.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/DualMomentumNoTLT"` (variante standalone, `main.py`).
**QC Cloud :** pour la variante Framework, déployer `main_framework.py` sous le nom `main.py`, avec `alpha_model.py`. Le projet QC 31244186 porte cette variante dans sa version d'avant #20388.
**Mesure du 2026-10-20 (#21669) :** voir la section « Verdict contre références détenues ». Les paramètres `mode`, `start_date` et `end_date` se passent au backtest de la variante standalone.

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
