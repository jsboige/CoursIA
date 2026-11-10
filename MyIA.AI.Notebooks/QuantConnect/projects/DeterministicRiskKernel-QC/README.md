# DeterministicRiskKernel-QC — le noyau de risque de Steward dans LEAN

Portage LEAN du noyau de risque déterministe décrit par Feng et al. (*Governed Self-Evolution for Autonomous Investing*, arXiv:2610.30557, section 5.5, table 11). C'est l'étape 2 de l'issue #24698. L'étape 1 est le carnet `QuantConnect/Python/QC-Py-45-Noyau-Risque-Deterministe.ipynb` (PR #24728), qui mesure ce noyau avec un moteur vectorisé sur les données yfinance.

Ce projet sert de **vérification indépendante** du carnet sur son chemin momentum. Le carnet et l'algorithme partagent les règles, mais ni les données, ni le moteur d'exécution : ici, ce sont les données QuantConnect et le modèle d'exécution de LEAN.

## Règles

Chaque premier jour de bourse de la semaine, l'algorithme retient les 10 ETF au plus fort momentum (rendement sur 126 séances, en sautant les 5 dernières), signal pris sur la clôture précédente, ordres `MarketOnOpen`. L'univers compte 23 ETF en quatre groupes : actions US, actions hors US, obligations, matières premières et immobilier.

Le noyau ajoute quatre règles, avec les paramètres du papier, sans ajustement :

- **stop** à 2 ATR(14) sous le prix d'entrée, fixé à l'ouverture de la position. C'est un ordre `StopMarket` natif. Une position stoppée reste à plat jusqu'au rebalancement suivant ;
- **plafond de 40 % par groupe**, réduction au prorata ;
- **exposition d'au plus 90 %**, soit 9 % par position au lieu de 10 % ;
- **coupe-circuit** après une séance du portefeuille à −3 % ou pire.

Frais de 5 points de base par côté (`ProportionalFeeModel`), départ à 100 000 USD.

## Variantes

Le paramètre `mode` choisit la variante, avec les mêmes noms que la table `VARIANTES` du carnet :

| `mode` | Poids par position | Stops | Plafond de groupe | Coupe-circuit |
|---|---|---|---|---|
| `nokernel` | 10 % | non | non | non |
| `exposure90` | 9 % | non | non | non |
| `kernel_nocb` | 9 % | oui | oui | non |
| `kernel` (défaut) | 9 % | oui | oui | oui |
| `kernel_sized` | 0,5 % du capital par ligne ÷ distance au stop (2 ATR), exposition plafonnée à 90 % | oui | oui | oui |
| `spy` | SPY acheté une fois et conservé | — | — | — |

Le mode `kernel_sized` implémente la règle de dimensionnement de Steward (point 2 de #25532) : la quantité de chaque ligne est fixée pour **risquer 0,5 % du capital** si son stop (2 ATR sous l'entrée) se déclenche, puis l'exposition totale est plafonnée à 90 %. Les autres modes gardent un poids fixe par ligne.

Le paramètre `stop_handling` choisit le traitement du stop quand un rebalancement redimensionne une ligne déjà détenue :

| `stop_handling` | Ce qui se passe |
|---|---|
| `recreate` (défaut) | le stop est annulé avant l'ordre `MarketOnOpen` et reposé à son exécution, au même niveau. La ligne n'a pas de stop le jour de l'ordre |
| `keep` | le stop reste en place ; sa quantité passe à la quantité cible dès la décision, avant l'ouverture (`UpdateOrderFields`). Seule l'ouverture d'une ligne reste sans stop ce jour-là |

En mode `keep`, le stop couvre la quantité cible avant l'exécution de l'ordre `MarketOnOpen`. S'il se déclenche à l'ouverture, la ligne entière est vendue, quel que soit l'ordre d'exécution des deux ordres : la position finale est nulle, comme dans le carnet.

Les paramètres `start_date` et `end_date` (format `AAAA-MM-JJ`) bornent la fenêtre.

## Résultats

Projet QC 38955440, espace sponsorisé ESGF_School, backtests du 2026-11-05 (mode `recreate`) et du 2026-11-07 (mode `keep`). Fenêtre du 2015-01-02 au 2026-07-31 : l'espace ESGF_School coupe les données à J−90 sans erreur, d'où la date de fin. Le carnet a été relancé sur la même fenêtre pour la comparaison.

Le Sharpe affiché par QC inclut un taux sans risque. Pour comparer au carnet, le Sharpe « sans taux » est recalculé depuis la trace `shadow` de chaque backtest : valeur du portefeuille à l'ouverture de chaque séance de SPY, répartie sur les séries e0 à e4 (contrat #18923), soit 2911 dates. Rendements journaliers, `moyenne / écart-type × √252`, taux nul.

| Variante | Backtest | CAGR | Sharpe (taux nul) | Sharpe QC | Drawdown max | Stops | Coupures |
|---|---|---|---|---|---|---|---|
| Sans noyau | `5272a10ad58c578d457ad657a04f1385` | +7,08 % | 0,59 | 0,28 | −29,4 % | 0 | 0 |
| Exposition 90 % seule | `80e96d5e1366fd1f670ec6e933875445` | +6,45 % | 0,59 | 0,25 | −26,7 % | 0 | 0 |
| Noyau sans coupe-circuit | `eb99dd2511fe8d52d70df9b8f45fc794` | +7,71 % | 0,83 | 0,40 | −13,0 % | 444 | 0 |
| Noyau complet | `0ce2bb3f21753fd513e75daf07ad12f1` | +7,35 % | 0,79 | 0,37 | −15,7 % | 453 | 6 |
| Noyau sans coupe-circuit, stop gardé (`keep`) | `6deedbc668a0cb67adca15641fc26c20` | +7,27 % | 0,80 | 0,37 | −13,3 % | 457 | 0 |
| Noyau complet, stop gardé (`keep`) | `302de9f008649c6776fe83bbb4902cfd` | +6,99 % | 0,77 | 0,34 | −14,6 % | 470 | 4 |
| SPY (référence) | `7249213e4250c71919e3a090511c01e5` | +13,57 % | 0,81 | 0,55 | −33,8 % | — | — |

Le carnet, sur la même fenêtre, liquidités à 0 % comme dans LEAN (entre parenthèses : liquidités rémunérées au rendement de BIL, réglage du carnet) :

| Variante | CAGR | Sharpe | Drawdown max |
|---|---|---|---|
| Sans noyau | +7,15 % | 0,60 | −29,3 % |
| Exposition 90 % seule | +6,50 % (+6,71 %) | 0,60 (0,62) | −26,7 % |
| Noyau sans coupe-circuit | +7,13 % (+7,60 %) | 0,78 (0,83) | −13,4 % (−13,3 %) |
| Noyau complet | +6,83 % (+7,31 %) | 0,75 (0,80) | −14,2 % (−14,1 %) |
| SPY | +13,69 % | 0,82 | −33,7 % |

### Lecture

LEAN retrouve l'ordre du carnet sur ce chemin :

- le noyau divise le drawdown maximal par deux environ (−29,4 % sans noyau, de −13,0 % à −15,7 % avec, selon la variante et le traitement du stop) à CAGR comparable, et le Sharpe à taux nul passe de 0,59 à 0,77-0,83 ;
- l'exposition à 90 % seule ne fait presque rien : c'est le contrôle à exposition égale ;
- le coupe-circuit n'apporte rien sur ce chemin : sans lui, le CAGR et le drawdown sont tous deux meilleurs, avec l'un comme avec l'autre traitement du stop.

**Aucun verdict ici.** Ces chiffres portent sur un seul chemin d'entrées. Le verdict du carnet (BEATS sur le drawdown) repose sur l'ablation à 50 graines d'entrées aléatoires, que ce projet ne rejoue pas. Ce projet dit seulement qu'un moteur d'exécution indépendant, sur d'autres données, reproduit les lectures du carnet sur le chemin momentum.

### D'où vient l'écart de CAGR entre LEAN et le carnet

En mode `recreate`, le CAGR de LEAN dépasse celui du carnet à liquidités nulles de 0,5 à 0,6 point pour les deux variantes à stops. `mesure_ecart_carnet.py` rejoue le moteur du carnet et lui ajoute, une par une, les deux différences d'exécution de LEAN décrites plus bas (même fenêtre, liquidités à 0 %, Sharpe à taux nul, données yfinance du 2026-11-06). En italique, le backtest LEAN que chaque réglage doit reproduire :

| Variante | Réglage du moteur du carnet | CAGR | Sharpe | Drawdown max | Stops | Coupures |
|---|---|---|---|---|---|---|
| Noyau sans coupe-circuit | carnet | +7,13 % | 0,78 | −13,4 % | 466 | — |
| | pas de stop le jour où la ligne est ouverte | +7,27 % | 0,79 | −13,6 % | 462 | — |
| | *backtest LEAN, mode `keep`* | *+7,27 %* | *0,80* | *−13,3 %* | *457* | — |
| | pas de stop le jour d'un ordre sur la ligne | +7,77 % | 0,83 | −12,8 % | 448 | — |
| | *backtest LEAN, mode `recreate`* | *+7,71 %* | *0,83* | *−13,0 %* | *444* | — |
| Noyau complet | carnet | +6,83 % | 0,75 | −14,2 % | 481 | 4 |
| | coupe-circuit le lendemain | +6,78 % | 0,75 | −13,8 % | 482 | 4 |
| | pas de stop le jour où la ligne est ouverte + coupe-circuit le lendemain | +6,94 % | 0,76 | −15,0 % | 475 | 4 |
| | *backtest LEAN, mode `keep`* | *+6,99 %* | *0,77* | *−14,6 %* | *470* | *4* |
| | pas de stop le jour d'un ordre sur la ligne | +7,03 % | 0,76 | −17,2 % | 462 | 5 |
| | pas de stop le jour d'un ordre + coupe-circuit le lendemain | +7,26 % | 0,78 | −16,5 % | 457 | 6 |
| | *backtest LEAN, mode `recreate`* | *+7,35 %* | *0,79* | *−15,7 %* | *453* | *6* |

Ce que la table montre :

- **la cause principale est l'absence de stop le jour de chaque ordre.** En mode `recreate`, `main.py` annule le stop d'une ligne avant tout ordre `MarketOnOpen` sur elle, et le repose à l'exécution. La ligne n'a donc pas de stop le jour de son ouverture, ni le jour d'un rebalancement qui la redimensionne. Les lignes redimensionnées pèsent le plus : les seules ouvertures font +0,14 point de CAGR, tous les ordres +0,64 point (noyau sans coupe-circuit) ;
- **le mode `keep` vérifie cette cause.** Les lignes du moteur du carnet « pas de stop le jour où la ligne est ouverte » ont été calculées avant les backtests `keep` : elles en prédisaient le résultat. Le CAGR mesuré est égal à la prédiction sans coupe-circuit (+7,27 %), à +0,05 point près avec le coupe-circuit (+6,99 % pour +6,94 %), et le nombre de coupures est le même (4) ;
- **le coupe-circuit au lendemain, seul, ne change presque rien** (−0,05 point de CAGR), mais il interagit avec le réglage des stops ;
- **les six coupures du mode `recreate` au lieu de quatre ne sont pas une troisième cause.** Le moteur du carnet les retrouve avec les deux réglages, sur les séances du 2020-03-09, du 2020-03-12, du 2025-04-03, du 2026-01-30, du 2026-03-03 et du 2026-06-05. Avec le stop gardé, LEAN revient à quatre coupures, comme le carnet ;
- **le gain de CAGR du mode `recreate` se paie en drawdown pour le noyau complet** : −15,7 % dans LEAN, −16,5 % dans le moteur du carnet avec les deux réglages, contre −14,2 % dans le carnet ;
- **l'écart résiduel au backtest LEAN** tient en un dixième de point de CAGR dans les quatre cas : 0,00 et +0,05 point en mode `keep`, −0,06 et −0,09 point en mode `recreate`. LEAN compte 4 ou 5 stops de moins que le réglage correspondant du moteur du carnet, dans les quatre cas. Les données et les quantités entières de LEAN en sont des causes possibles, non mesurées.

Le reste de l'écart au carnet, de +0,14 à +0,16 point de CAGR en mode `keep`, vient du jour d'ouverture d'une ligne, qui reste sans stop : en données journalières, le stop est posé à l'exécution de l'ordre `MarketOnOpen`, son niveau dépendant du prix d'entrée.

## Écarts déclarés au carnet

Les données journalières de LEAN imposent des écarts que le carnet n'a pas :

| Point | Carnet QC-Py-45 | Ce projet |
|---|---|---|
| Liquidités | rendement de BIL | 0 % |
| Stop | actif tous les jours où la position est détenue, y compris le jour d'un ordre | mode `recreate` (défaut) : annulé avant chaque ordre sur la ligne et reposé à son exécution, au même niveau, donc pas de stop le jour où la ligne est ouverte, ni le jour où un rebalancement la redimensionne. Mode `keep` : gardé et redimensionné, seul le jour d'ouverture d'une ligne reste sans stop. Effets mesurés plus haut |
| Coupe-circuit | liquidation à la clôture de la séance à −3 %, retour à l'ouverture suivante | séance connue à la clôture, liquidation `MarketOnOpen` le lendemain, retour le surlendemain |
| Compte | sans emprunt par construction | compte sur marge par défaut. La variante sans noyau emprunte un peu : liquidités minimales négatives, exposition maximale 1,05. Cause probable, non mesurée : les ordres sont dimensionnés sur la clôture de la veille et exécutés à l'ouverture, frais en plus, sans réserve sous les 10 % par position |
| Plafond de groupe | mesuré après rebalancement | tenu au rebalancement. Le poids de groupe mesuré chaque jour monte jusqu'à 0,4198 par dérive des prix entre deux rebalancements |
| Exécution | moteur vectorisé, prix yfinance ajustés | modèle d'exécution de LEAN, données QuantConnect |
| Trace | valeur en fin de séance | valeur à l'ouverture, au dernier prix connu, c'est-à-dire la clôture précédente |

## Contrôles

Statistiques d'exécution publiées par l'algorithme :

| Variante | Stops au plus bas de l'ouverture et du stop | Ordres invalides | Exposition max | Poids de groupe max |
|---|---|---|---|---|
| Sans noyau | — | 0 | 1,0517 | 0,9003 |
| Exposition 90 % seule | — | 0 | 0,9321 | — |
| Noyau sans coupe-circuit | 444 sur 444 | 0 | 0,9047 | 0,4198 |
| Noyau complet | 453 sur 453 | 0 | 0,9137 | 0,4198 |
| Noyau sans coupe-circuit, stop gardé (`keep`) | 457 sur 457 | 0 | 0,9043 | 0,4198 |
| Noyau complet, stop gardé (`keep`) | 470 sur 470 | 0 | 0,9151 | 0,4198 |

Le premier contrôle vérifie la règle d'exécution du papier : chaque stop s'exécute au plus bas de l'ouverture et du niveau du stop. C'est le modèle d'exécution natif de LEAN qui l'applique, sans code ajouté.

En mode `keep`, l'algorithme compte aussi les redimensionnements de stop : 4365 stops gardés (noyau sans coupe-circuit) et 4307 (noyau complet), sans aucune mise à jour refusée par LEAN. Le repli prévu dans `main.py`, qui annule et repose le stop si la mise à jour échoue, n'a donc jamais servi.

Contrôle de série, avant toute lecture : la plus forte variation journalière de chaque trace a été relevée. −8,0 % le 2020-03-10 (sans noyau), −7,2 % le même jour (exposition 90 %), +4,5 % le 2025-04-10 (les deux variantes à noyau, dans l'un et l'autre mode), −11,0 % le 2020-03-17 pour SPY, soit la clôture du 16 mars. Toutes correspondent à des séances connues, sans date en double dans les traces (2911 points pour chacune des traces `keep`).

### Dénominateur des séances vues par `on_data` (suivi #25532)

Deux statistiques d'exécution ont été ajoutées pour lever la réserve du README de #25499 : `Dates vues par on_data` (dates distinctes traitées par `on_data`, période de mise en route exclue) et `Seances a plat` (séances où aucune position de l'univers n'est détenue).

Sur les deux fenêtres du protocole #25499, le nombre de dates vues par `on_data` est **strictement égal** au nombre de dates négociables que QC rapporte pour le même backtest (`tradeableDates`) : 1761 = 1761 (2018-01-01 → 2025-01-01) et 4780 = 4780 (2007-01-01 → 2026-01-01). Il n'y a donc **aucun écart** entre la cadence de `on_data` et le calendrier boursier.

Le dénominateur des parts de séances à plat doit être le nombre de dates négociables du calendrier boursier, et non un comptage brut de « séances vues par `on_data` » : celui-ci peut gonfler silencieusement avec la période de mise en route (warm-up) ou des dates frontalières, là où le calendrier est fixe. Les mesures ci-dessus (1761 et 4780) établissent que, sur ce noyau, `on_data` traite **exactement** les dates négociables, sans écart : le comptage brut coïncide ici avec le calendrier, et les parts de séances à plat s'expriment rigoureusement sur ce dénominateur. La fenêtre longue de #25499 (2007-2026, 4946 dates négociables) n'est pas la même que la mienne (2007-01-01 → 2026-01-01, 4780) ; je ne compare donc pas les deux chiffres à l'unité près, et le dénominateur ci-dessus se lit sur les mesures propres de ce noyau.

### Suivi #25532 — dimensionnement à risque et dénominateur

Six backtests (mode × fenêtre), mode `recreate`, frais 5 bps, départ 100 000 USD, espace QC 38955440, exécutés le 2026-11-09. Le Sharpe affiché est le Sharpe QC (taux sans risque inclus).

| Variante | Fenêtre | CAGR | Sharpe (QC) | Drawdown max | Ordres | Séances à plat |
|---|---|---|---|---|---|---|
| `kernel` | 2018-2025 | +6,16 % | 0,24 | −15,7 % | 6 821 | 3 / 1761 |
| `kernel` | 2007-2026 | +6,54 % | 0,34 | −28,8 % | 19 411 | 6 / 4780 |
| `kernel_sized` | 2018-2025 | +5,48 % | 0,18 | −15,2 % | 7 547 | 3 / 1761 |
| `kernel_sized` | 2007-2026 | +6,85 % | 0,37 | −23,2 % | 20 620 | 6 / 4780 |
| `spy` (témoin) | 2018-2025 | +13,66 % | 0,50 | −33,8 % | 1 | 0 / 1761 |
| `spy` (témoin) | 2007-2026 | +10,65 % | 0,41 | −55,4 % | 1 | 0 / 4780 |

Lecture :

- le dimensionnement à risque (`kernel_sized`) n'améliore le noyau que sur la fenêtre longue : sur 2007-2026, Sharpe 0,37 contre 0,34, CAGR +6,85 % contre +6,54 %, drawdown −23,2 % contre −28,8 % ; sur 2018-2025 il est légèrement en retrait (CAGR +5,48 % contre +6,16 %) à drawdown comparable. La fenêtre longue inclut 2008-09, où le dimensionnement ATR (positions plus petites quand la volatilité est élevée) protège le drawdown ;
- le témoin `spy` (buy-and-hold) a le CAGR et le Sharpe les plus élevés mais de loin le drawdown le plus fort (−33,8 % / −55,4 %) : c'est la référence **sans** gestion du risque ;
- le noyau standalone est investi à ~90 % en permanence : 3 à 6 séances à plat sur 1761 / 4780, toutes avant le premier rebalancement hebdomadaire. La « part des séances à plat » est donc quasi nulle ici — elle est le fait du wrapper Cloud-VolTargeting de #25499, pas du noyau.

## Pourquoi des ordres stop et pas un `RiskManagementModel`

L'étape 1 annonçait un portage en `RiskManagementModel` du framework LEAN. Le portage a pris une autre forme, pour trois raisons :

- en données journalières, un modèle de risque n'agit que sur la tranche de données de la clôture. Il ne peut pas exécuter un stop au plus bas de l'ouverture et du stop. L'ordre `StopMarket` natif le fait, et le contrôle ci-dessus le vérifie sur chaque stop ;
- `MaximumDrawdownPercentPortfolio` mesure le drawdown depuis le plus haut du portefeuille, pas une séance à −3 % ;
- `MaximumSectorExposureRiskManagementModel` groupe les titres par le code d'industrie de leurs données fondamentales (`company_reference.industry_template_code`, source LEAN lue le 2026-11-05) et lève une exception si aucun titre de l'univers n'en porte. Les quatre groupes du papier sont une partition d'ETF par classe d'actifs, que ce code ne représente pas.

Le framework reste un outil parmi d'autres, pas un passage obligé : le noyau tient en une classe d'algorithme.

## Fichiers

- `main.py` : l'algorithme, un seul fichier.
- `mesure_ecart_carnet.py` : copie déclarée du moteur du carnet QC-Py-45, avec deux réglages qui rejouent les écarts d'exécution de LEAN ; produit la table de décomposition ci-dessus. Lancer : `python mesure_ecart_carnet.py` (numpy, pandas, yfinance).

## Liens

- Issue #24698 (étape 1 : carnet QC-Py-45 ; étape 2 : ce projet).
- Article archivé : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Trading\2026 - Feng Dai Pan Lau Xu Liu - Governed Self-Evolution for Autonomous Investing, Steward (arXiv 2610.30557).pdf`.
