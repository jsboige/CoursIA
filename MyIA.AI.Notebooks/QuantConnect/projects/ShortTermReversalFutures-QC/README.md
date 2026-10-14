# ShortTermReversalFutures-QC

Banc de mesure de l'article de recherche QuantConnect **« Short Term Reversal With Futures »** (Jing Wu, [research 15366](https://www.quantconnect.com/research/15366/short-term-reversal-with-futures/), statut **draft / pending review**, re-mesuré le 2026-10-07). Issue #18466, EPIC #11698 (moisson qc-research). Projet Cloud : **37465962** (`ShortTermReversalFutures-18466`).

## Pourquoi ce portage existe alors que le semis verdictait IGNORE

Le semis (#18466, lane po-2025) avait clos **l'article** en `IGNORE` sur cinq axes, tous **re-mesurés encore vrais le 2026-10-07** :

1. l'article est toujours `pending review` / `draft post` ;
2. il ne rend **aucune métrique de performance** (pas de Sharpe, CAGR, drawdown, période) ;
3. les backtests liés sont toujours **morts** (404, commentaire Chetan Prabhu) ;
4. **aucune source primaire** — le seul pointeur est Quantpedia (agrégateur) ;
5. le coût d'un port (8 futures continus, rollovers, classements OI) pour répliquer un draft sans claim.

Le 2026-10-07, le coordinateur (ai-01) a dispatché le portage malgré ce verdict : c'est le seul grain qc-research semé sans être porté, et la famille « reversal court terme sur futures » manque au bouquet. La règle du dernier arbitre s'applique — le dispatch (07/10 06:52Z) est postérieur au verdict de semis. **Ce projet exécute le dispatch en documentant les deux** : les cinq axes ci-dessus restent les bornes de mesure du livrable, et aucun `BEATS` n'est claimable puisque l'article n'affiche aucun chiffre à battre.

## Ce que l'article fait

Reversal court terme sur **8 futures CME continus** — 4 devises (CHF, GBP, CAD, EUR) et 4 indices (NQ, RTY, ES, YM) — carte par open interest, résolution quotidienne, normalisation `BACKWARDS_RATIO`, levier 1. Fenêtre hebdomadaire mercredi → mercredi : des `ROC(1)` sur le volume, l'open interest et la clôture consolidés servent à classer les 8 contrats. Le code de l'article sélectionne l'**union** des 4 plus **bas** volume-ROC et des 4 plus **hauts** OI-ROC, trie ce groupe par rendement hebdomadaire, **achète le plus bas rendement et vend le plus haut** (`±0.3` de la valeur du portefeuille, divisés par le `contract_multiplier`). Rollover par `symbol_changed_events`.

## Deux divergences prose/code, mesurées à la lecture

| # | Prose de l'article | Code de l'article | Ce que le port fait |
|---|---|---|---|
| 1 | « We take the **intersection** of the top volume group and bottom open interest group » | **union** des 4 plus bas volume-ROC et des 4 plus hauts OI-ROC (`[:4]` volume + `[-4:]` OI, `set(...)`) — le commentaire du code (« lowest volume change and highest OI change ») corrobore le code | suit le **code** (a5) |
| 2 | — | au rollover, `portfolio[old].quantity // contract_multiplier` divise par le multiplicateur une quantité **déjà en contrats** : la position reportée est écrasée vers ~0 à chaque changement de mappage | **porté tel quel**, défaut borné : le rééquilibrage hebdomadaire re-cible `±0.3` la semaine suivante |

## Adaptations du portage (a1–a5)

| # | Nature | Contenu |
|---|---|---|
| a1 | mot réservé | la propriété `return` de l'article est impossible en Python (`def return(self)` : erreur de syntaxe) — renommée `return_value` |
| a2 | reconstruction | l'article montre le bloc d'ordres sans son déclencheur ; le port trade à l'émission du consolidateur hebdomadaire (mercredi) quand tous les `SymbolData` sont prêts — sans ce portillon, `is_ready` collant ferait trader chaque jour des valeurs périmées |
| a3 | update STAFF | garde `qty != 0` avant chaque ordre (Derek Melchin, STAFF, fil de l'article) |
| a4 | non spécifié par l'article | fenêtre/capital en paramètres (`start`/`end`), cash 1 M, brokerage **IBKR marge** (frais courtier), `seed_initial_prices` — convention du dépôt (campagne #1630) |
| a5 | prose ≠ code | sélection par **union** bas-volume/haut-OI, comme le code (voir tableau ci-dessus) |
| a6 | mesuré au run 1 | `portfolio.keys` (propriété dans l'article) se lie en **méthode** sur LEAN courant — `'MethodBinding' object is not iterable` au premier rebalancement (bras A : crash 2017-07-19, bras B : crash 2018-01-03, 0 ordres chacun) ; remplacé par `list(self.portfolio.keys())` |

## Plan de backtests préinscrit (écrit avant toute exécution)

Deux bras, même code, mêmes frais IBKR marge, même capital 1 M :

| Bras | Fenêtre | Rôle |
|---|---|---|
| **A — longue** | 2016-01-01 → 2026-06-30 | mesure principale : survit-elle sur dix ans de régimes ? |
| **B — alignée #1630** | 2018-01-01 → 2025-01-01 | comparabilité avec la campagne du dépôt « sous frais réels » |

Métriques rapportées : Sharpe, CAGR, drawdown max, rendement net, nombre d'ordres, statut d'exécution.

**Verdict préinscrit, avant mesure.** Aucun `BEATS` n'est claimable — l'article n'affiche aucun chiffre à battre (axes 2 et 3). Le verdict rendu sera celui de la **viabilité autonome sous frais** : un Sharpe ≤ 0 sur les deux bras rend `NO BEATS` (contre le cash) ; un Sharpe > 0 reste **sans claim d'edge** tant qu'aucune référence n'est mesurable. Les cinq axes du semis bornent ce que ce portage peut prouver : il vérifie que le code de l'article **tourne, trade et se mesure**, pas qu'il gagne.

## Résultats

**Historique d'exécution.** Run 1 (`v1`) : les deux bras crashent au premier rééquilibrage sur `self.portfolio.keys` (adaptation a6) — bras A au 2017-07-19, bras B au 2018-01-03, 0 ordres chacun ; ce premier run établit au passage que la route OI de l'article (`future.open_interest` + `oi_consolidator.update(OpenInterest(...))`) **lie et s'exécute** sans erreur sur LEAN courant. Run 2 (`v2`, fix a6) : les deux bras complètent.

Mesures du run 2, frais IBKR marge inclus, cash 1 M :

| Bras | Fenêtre | Séances | Statut | Ordres | Sharpe | CAGR | Drawdown max | Rendement net | PSR |
|---|---|---|---|---|---|---|---|---|---|
| **A — longue** | 2016-01-01 → 2026-06-30 | 2710 | `Completed.` | 1126 | **−0.474** | −3.57 % | 44.9 % | **−31.73 %** (−316 368 $) | 0.0 % |
| **B — alignée #1630** | 2018-01-01 → 2025-01-01 | 1808 | `Completed.` | 884 | **−0.345** | −1.48 % | 37.9 % | **−9.90 %** (−106 659 $) | 0.0 % |

**Backtests** : `strf-18466-brasA-v2-long-2016-2026-ibkr` et `strf-18466-brasB-v2-aligne-2018-2025-ibkr` (projet 37465962).

**Ce que le nombre d'ordres dit du portage.** 1126 ordres sur 530 semaines ≈ 2 par semaine plus les rollovers : le circuit de sizing de l'article (`calculate_order_quantity(±0.3)` puis division par le `contract_multiplier`) produit des tailles de contrats non nulles — `CalculateOrderQuantity` n'amortit pas le multiplicateur, la division de l'article est donc nécessaire au rééquilibrage (et n'est un défaut qu'au rollover, cf. divergence 2).

## Verdict : NO BEATS

Le verdict préinscrit s'applique tel quel : **Sharpe ≤ 0 sur les deux bras → `NO BEATS` contre le cash.** La stratégie perd de l'argent sur les deux fenêtres sous frais IBKR — −31.7 % sur dix ans et demi (drawdown max 44.9 % sur un livre `±0.3`, le risque dominant), −9.9 % sur la fenêtre alignée — avec un ratio de Sharpe probabiliste de 0 % partout : aucun régime de la période ne rend ce signal viable tel quel.

**Ce que ce verdict ne dit pas.** Il ne dit pas que la prose de l'article aurait mieux fait que son code (divergence a5 : la prose décrit une **intersection** volume-haut/OI-bas que le code n'implémente pas — la variante prose n'a pas été testée, elle n'était pas dans le code mesuré). Il ne dit rien non plus d'un éventuel edge avant frais : la mesure est nette, sous brokerage IBKR, comme le demandait le dispatch. Et conformément aux cinq axes du semis, il ne confronte **aucun chiffre de l'article** — il n'en affiche aucun (axes 2 et 3) : ce portage vérifie que le code de l'article **tourne, trade et se mesure** — c'est fait — pas qu'il gagne. La famille « reversal court terme sur futures » reste ouverte à un article publié, sourcé et mesuré.

## Fichiers

- `main.py` — portage fidèle (adaptations a1–a5 en tête de fichier)

## Références

- Article : [research 15366](https://www.quantconnect.com/research/15366/short-term-reversal-with-futures/) (Jing Wu ; mise à jour PEP8 annoncée par Derek Melchin, STAFF)
- Quantpedia — Short Term Reversal with Futures (screener/71) — **agrégateur**, pas une source primaire
- Issue #18466 (semis, verdict IGNORE 5 axes) · EPIC #11698
