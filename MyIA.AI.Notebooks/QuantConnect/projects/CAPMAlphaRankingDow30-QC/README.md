# CAPMAlphaRankingDow30-QC

**Classe d'actifs :** Actions US (composantes du Dow Jones)
**ID projet Cloud :** 37467233 (mesure #19680)

## Description

Port de l'article *CAPM Alpha Ranking Strategy On Dow 30 Companies* (Jing Wu, QuantConnect Research 15345, encore au statut de brouillon le 2026-10-07), avec la mise à jour proposée par Derek Melchin (équipe QuantConnect) dans le fil de l'article.

Au premier jour de bourse de chaque mois, `main.py` :

1. lit 21 clôtures quotidiennes des 30 titres et de SPY ;
2. régresse, pour chaque titre, les rendements de l'un sur ceux de l'autre (`np.linalg.lstsq`) et retient la constante de la régression comme « alpha » ;
3. garde les deux titres au plus grand alpha, vend les autres positions et place 100 % du capital sur **chacun** des deux.

Le portefeuille de l'article est donc à levier 2, sur deux actions, sans couverture ni stop. La thèse annoncée est un momentum d'un mois : un titre qui a battu le marché le mois passé continuerait à le battre.

## Ce que le code publié calcule : une régression inversée

La prose de l'article annonce la régression du CAPM : le rendement de l'action expliqué par celui du marché, de pente β et de constante α. Le code fait l'inverse :

```python
returns = np.vstack([returns, np.ones(len(returns))]).T
result = np.linalg.lstsq(returns, benchmark)   # benchmark ≈ pente · action + constante
alphas[symbol] = result[0][1]
```

La matrice de régression porte les rendements de l'**action** et la cible est le **benchmark**. La constante retenue est donc celle du marché régressé sur l'action, et non l'alpha de l'action. Le port reprend ce code tel quel (bras A, `regression=article`) et mesure à côté la régression dans le sens du CAPM (bras B, `regression=capm`).

## Port : ce qui change et ce qui ne change pas

Ce qui est repris de l'article sans changement :

- la régression, le lookback de 21 séances, la sélection des deux premiers et l'exposition de 1,0 par ligne ;
- le rééquilibrage par `month_start` / `after_market_open` ;
- la vente des seules positions qui ne sont plus retenues (`liquidate`, puis `set_holdings`).

Ce qui change :

- **Noms d'API.** Le code publié est écrit pour une version antérieure de l'API Python de Lean. Deux noms ne passent plus en snake_case : `self.benchmark`, aujourd'hui pris par `QCAlgorithm.benchmark` (l'initialisation échoue), devient `self._benchmark` ; `self.portfolio.values` devient la méthode `self.portfolio.values()`. Deux backtests ont échoué sur ces deux noms avant le premier run mesuré ; leurs identifiants sont conservés dans les traces.
- **Courtier.** Le port tourne avec les frais IBKR, en compte sur marge, et un capital de 1 M$.
- **Initialiseur.** Il vient de la mise à jour de l'équipe QuantConnect : chaque titre reçoit son dernier prix connu dès son ajout. Il n'a pas d'effet sur la règle.
- **Instrumentation de mesure.** Un graphique `shadow` porte la valeur du portefeuille à chaque clôture, les frais cumulés et la rotation. Les appels de marge et leurs dates sont comptés. Chaque sélection est écrite au journal (`SEL ...`).
- **Paramètre `timing`, ajouté après la mesure des bras préinscrits.** Par défaut (`article`), ventes et achats partent le même jour, comme dans le code publié. Avec `intent`, les achats attendent la séance suivante. La raison est donnée dans « Exposition effective » ci-dessous.

Paramètres (défauts = code de l'article) :

| Paramètre | Valeurs | Rôle |
|---|---|---|
| `regression` | `article` (défaut), `capm` | sens de la régression |
| `exposure` | 1,0 (défaut) | poids de chacune des deux lignes ; 0,5 pour la variante de l'équipe QuantConnect |
| `mode` | `strategy` (défaut), `spy` | `spy` détient SPY à 100 % sur le même harnais, comme référence |
| `fee_mult` | 1 (défaut) | multiplicateur des frais IBKR |
| `timing` | `article` (défaut), `intent` | `intent` achète à la séance qui suit les ventes |
| `start`, `end` | 2015-03-19, 2026-09-30 | fenêtre |

## Univers figé

Le texte de l'article ne donne pas la liste des 30 titres ; elle ne figure que dans son backtest joint. Le port utilise la composition du Dow Jones au 2015-03-19, date de l'entrée d'Apple dans l'indice, la plus tardive de la liste. La fenêtre principale commence ce jour-là, comme dans l'article.

La liste est connue à la date de départ : elle n'anticipe rien sur la fenêtre principale. En revanche, elle ne suit pas l'indice ensuite. Plusieurs titres l'ont quitté depuis, comme General Electric en 2018, et ses entrants ne sont jamais achetés. Le portefeuille ne mesure donc pas « le Dow 30 », mais 30 grandes capitalisations américaines choisies en 2015.

Le run `y2015` commence le 2015-01-01 pour comparer l'année civile 2015 à l'article. Sur ses onze premières semaines, la liste contient Apple, qui n'était pas encore dans l'indice, à la place d'AT&T. Sur ces semaines, ce run connaît donc la suite.

## Sources

- **Article** : Jing Wu, *CAPM Alpha Ranking Strategy On Dow 30 Companies*, QuantConnect Research 15345 (brouillon), <https://www.quantconnect.com/research/15345/capm-alpha-ranking-strategy-on-dow-30-companies/>
- **Théorie du CAPM** : William F. Sharpe, *Capital Asset Prices with and without Negative Holdings*, Nobel Lecture, 7 décembre 1990. Copie : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\1990 - Sharpe - Capital Asset Prices with and without Negative Holdings (Nobel Lecture).pdf`.
- **Aucune source primaire ne teste le signal.** Sharpe fonde le modèle, pas cette règle de sélection. L'article ne cite aucune étude du classement mensuel par alpha sur 21 séances. L'horizon d'un mois va plutôt à l'encontre de la littérature : le momentum classique sur actions se mesure sur 12 mois en sautant le dernier, et le dernier mois tend à s'inverser.

## Mesure (#19680)

La règle de verdict a été inscrite sur l'issue avant le premier backtest ([commentaire de préinscription](https://github.com/jsboige/CoursIA/issues/19680#issuecomment-6033649014)). Elle est appliquée ici sans changement.

**Protocole.** Fenêtre principale du 2015-03-19 au 2026-09-30, soit 2 900 séances, communes à tous les passages. La statistique est l'écart de Sharpe journalier entre le bras et SPY détenu sur le même harnais, sans taux sans risque. Le p unilatéral vient d'un bootstrap circulaire par blocs, corrigé par Holm sur les trois bras. Un bras ne gagne (**BEATS**) que s'il passe les trois conditions :

- p Holm < 0,05 ;
- écart positif avec des frais doublés ;
- écart positif sur au moins deux des trois sous-fenêtres.

### Résultats

| Passage | Sharpe (sans taux) | Sharpe QC | CAGR | Drawdown max | Rotation / an | Frais / an, en part du capital initial | Ordres |
|---|---|---|---|---|---|---|---|
| `article` (bras A, régression publiée, 1,0 par ligne) | 0,53 | 0,35 | 11,4 % | −51,0 % | 19,2 | 0,18 % | 386 |
| `capm` (bras B, sens du CAPM, 1,0 par ligne) | 0,64 | 0,47 | 16,6 % | −53,5 % | 19,9 | 0,21 % | 391 |
| `staff` (bras C, régression publiée, 0,5 par ligne) | 0,50 | 0,32 | 10,0 % | −47,8 % | 22,0 | 0,28 % | 527 |
| `spy` (référence) | 0,82 | 0,54 | 13,7 % | −33,8 % | 0,09 | 0 | 1 |

Le « Sharpe QC » est celui des statistiques de QuantConnect, calculé avec un taux sans risque. La rotation compte la valeur échangée, rapportée à la valeur du portefeuille.

### Verdict

| Bras | Écart de Sharpe contre SPY | IC 95 % | p Holm | 2015-2018 | 2019-2022 | 2023-2026 | Verdict |
|---|---|---|---|---|---|---|---|
| `article` | −0,29 | [−0,94 ; 0,33] | 1,00 | −0,61 | −0,20 | −0,28 | **NO BEATS** |
| `capm` | −0,18 | [−0,91 ; 0,45] | 1,00 | −0,42 | −0,16 | −0,32 | **NO BEATS** |
| `staff` | −0,32 | [−0,76 ; 0,08] | 1,00 | +0,03 | −0,45 | −0,50 | **NO BEATS** |

Les trois écarts sont négatifs. Aucun bras n'étant significatif, la règle ne demande pas de passage à frais doublés et aucun n'a été lancé. Le CAGR de `capm` dépasse celui de SPY, mais avec un drawdown de −53,5 % : par unité de risque, il fait moins bien que SPY.

### Exposition effective : le levier 2 n'est pas tenu

Les journaux des bras `article` et `capm` portent des refus d'ordres pour pouvoir d'achat insuffisant. Le bras `staff`, à 0,5 par ligne, n'en porte aucun.

| Passage | Rééquilibrages | 2 ordres refusés | 1 ordre refusé | sans refus |
|---|---|---|---|---|
| `article` | 138 | 57 | 41 | 40 |
| `capm` | 138 | 57 | 38 | 43 |
| `staff` | 138 | 0 | 0 | 138 |

En résolution journalière, un ordre au marché passé en séance s'exécute à la clôture. Le jour du rééquilibrage, la vente des titres qui ne sont plus retenus n'est donc pas encore exécutée quand partent les achats : les anciennes lignes occupent toujours la marge. À levier 2, l'achat d'un nouveau titre est alors refusé, et la vente, elle, s'exécute. Le bras `article` passe ainsi 56 mois sur 138 entièrement en liquidités, et 41 sur une seule ligne. Le 57ᵉ mois à deux refus garde une ligne presque pleine : l'écart à la cible y vaut 1,04 fois le poids d'une ligne.

Les bras A et B mesurent donc le code tel qu'il tourne aujourd'hui sur Lean, et non la règle à levier 2 que décrit l'article. Leur verdict NO BEATS vaut pour ce code. Seul le bras C, sans refus, mesure la règle telle qu'elle est écrite, à levier 1. Il ne bat pas SPY non plus.

**Bras ajoutés après coup (`timing=intent`).** Ces deux passages ont été inscrits sur l'issue avant d'être lancés ([commentaire d'ajout](https://github.com/jsboige/CoursIA/issues/19680#issuecomment-6034039690)). Ils sont descriptifs, hors verdict et hors Holm. Les ventes partent toujours le jour du rééquilibrage, mais les achats attendent la séance suivante, une fois les ventes exécutées.

| Passage | Sharpe (sans taux) | CAGR | Drawdown max | Écart contre SPY | IC 95 % | p brut | Mois avec un achat refusé |
|---|---|---|---|---|---|---|---|
| `intent_article` | 0,29 | 2,5 % | −74,6 % | −0,53 | [−1,04 ; −0,08] | 0,99 | 69 sur 138 |
| `intent_capm` | 0,50 | 12,7 % | −62,2 % | −0,32 | [−0,97 ; 0,28] | 0,84 | 71 sur 138 |

Même une fois les ventes exécutées, le modèle IBKR de Lean refuse une ligne entière un mois sur deux : deux lignes à 1,0 dépassent d'un rien le pouvoir d'achat. Ces bras ne passent plus de mois en liquidités, mais leur exposition alterne entre deux lignes et une.

Mieux investie, la règle publiée fait moins bien : le Sharpe de `intent_article` tombe à 0,29, son drawdown atteint −74,6 %, et tout son intervalle contre SPY est négatif. Sur cette fenêtre, être davantage investi dans la règle a coûté. Aucun des cinq passages de stratégie ne bat SPY. Le bras C, à exposition constante et sans refus, reste la mesure la plus propre de la règle.

### Confrontations à l'article

Ces lectures sont descriptives : elles n'entrent pas dans le verdict.

1. **Rendement 2015.** La règle nomme deux comparaisons au −15,463 % publié, et elles ne concluent pas pareil :

   | Comparaison | Rendement mesuré | Écart au chiffre publié | Lecture (seuil de 3 points) |
   |---|---|---|---|
   | `y2015`, année civile | −27,9 % | −12,5 points | ÉCART |
   | `article`, du 2015-03-19 au 2015-12-31 | −17,7 % | −2,3 points | dans le seuil |

   Le passage `y2015` porte aussi, sur ses onze premières semaines, une liste qui n'est pas celle du Dow de l'époque (voir « Univers figé »).
2. **Appel de marge.** L'article signale un appel de marge en janvier. Aucun bras préinscrit n'en reçoit, ni en 2015 (`y2015`) ni en 2016 (`article`) : le compteur reste à 0 sur toute la fenêtre. C'est un **ÉCART**. Sous le modèle de marge IBKR de Lean, le levier 2 bute à la place sur les refus d'achat décrits plus haut. Le passage `y2015` en compte 15, sur 10 des 12 rééquilibrages de l'année. Les bras `intent` ne reçoivent pas non plus d'appel de marge : sous ce modèle de courtier, l'ordre qui dépasserait la marge est refusé à l'envoi, et l'appel de marge publié ne se reproduit pas.
3. **Régression inversée.** Sur 138 rééquilibrages, la paire choisie par `article` et celle choisie par `capm` diffèrent 137 fois, et n'ont aucun titre en commun 129 fois. Les deux sens de régression choisissent donc presque toujours des titres différents. L'écart de Sharpe entre les deux bras (`capm` − `article`) vaut +0,11, IC 95 % [−0,73 ; 0,91], p unilatéral 0,39 : le choix du sens ne change pas le résultat de façon mesurable.

### Limites

- **Univers figé.** La liste de 2015 ne suit pas l'indice ensuite. Elle garde des titres qui en sont sortis et n'achète jamais ses entrants.
- **Levier nominal 2 sur deux titres.** Le résultat tient à quelques titres par mois. Le drawdown maximal dépasse −47 % dans tous les passages de stratégie, et atteint −74,6 % pour `intent_article`, contre −33,8 % pour SPY.
- **Capacité.** QuantConnect estime la capacité à 71 M$ pour `article`, 850 M$ pour `capm` et 97 M$ pour `staff`.
- **Paramètres de l'article.** Le lookback de 21 séances et la sélection de deux titres sont repris tels quels. Aucun autre jeu de paramètres n'a été essayé : la mesure porte sur la règle publiée, pas sur une variante réglée après coup.

Les traces de chaque passage sont rangées hors dépôt, dans `G:\Mon Drive\MyIA\IA\QC-traces\19680-capm-alpha-ranking` : plans, identifiants de backtest, graphiques `shadow`, journaux complets et de sélection, et `results.json`. On y trouve aussi les deux backtests en échec, les scripts d'analyse et la version de `main.py` qui a tourné pour les bras préinscrits (empreinte `aac9ea8b90e8`, avant l'ajout de `timing`, sans autre changement). Ces scripts s'appuient sur `shadow_replay`, `strategy_metrics` et `voltarget_strategy_verdict` de `ML-Training-Pipeline/scripts`.
