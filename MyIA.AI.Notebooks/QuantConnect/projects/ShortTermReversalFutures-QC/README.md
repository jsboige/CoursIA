# ShortTermReversalFutures-QC

Banc de mesure de l'article de recherche QuantConnect **« Short Term Reversal With Futures »** (Jing Wu, [research 15366](https://www.quantconnect.com/research/15366/short-term-reversal-with-futures/), statut **draft / pending review**, re-mesuré le 2026-10-07). Issue #18466, EPIC #11698 (moisson qc-research). Projet Cloud : **37465962** (`ShortTermReversalFutures-18466`) ; mesure du dimensionnement (#23689) : **38701872** (`ShortTermReversalFutures-23689`).

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
| 2 | — | au rollover, `portfolio[old].quantity // contract_multiplier` divise par le multiplicateur une quantité **déjà en contrats** ; l'arrondi vers −∞ garde −1 contrat sur une position courte et ramène une position longue à 0 (bras B, `fix=off` : 59 reports, 6 à zéro, 15 réduits) | `fix=off` : porté tel quel, comme témoin ; `fix=on` (défaut, a7) : quantité reportée telle quelle (bras B : 99 reports, aucun réduit) |

## Adaptations du portage (a1–a7)

| # | Nature | Contenu |
|---|---|---|
| a1 | mot réservé | la propriété `return` de l'article est impossible en Python (`def return(self)` : erreur de syntaxe) — renommée `return_value` |
| a2 | reconstruction | l'article montre le bloc d'ordres sans son déclencheur ; le port trade à l'émission du consolidateur hebdomadaire (mercredi) quand tous les `SymbolData` sont prêts — sans ce portillon, `is_ready` collant ferait trader chaque jour des valeurs périmées |
| a3 | update STAFF | garde `qty != 0` avant chaque ordre (Derek Melchin, STAFF, fil de l'article) |
| a4 | non spécifié par l'article | fenêtre/capital en paramètres (`start`/`end`), cash 1 M, brokerage **IBKR marge** (frais courtier), `seed_initial_prices` — convention du dépôt (campagne #1630) |
| a5 | prose ≠ code | sélection par **union** bas-volume/haut-OI, comme le code (voir tableau ci-dessus) |
| a6 | mesuré au run 1 | `portfolio.keys` (propriété dans l'article) se lie en **méthode** sur LEAN courant — `'MethodBinding' object is not iterable` au premier rebalancement (bras A : crash 2017-07-19, bras B : crash 2018-01-03, 0 ordres chacun) ; remplacé par `list(self.portfolio.keys())` |
| a7 | mesuré (#23689) | dimensionnement, paramètre `fix` (défaut `on`). `calculate_order_quantity` rend déjà des **contrats**, dimensionnés à la marge initiale ; l'article les divise encore par le `contract_multiplier`. `on` : cible au notionnel, `±0.3 × valeur / (prix × multiplicateur)` en contrats entiers, et report tel quel au rollover. `off` : code de l'article, témoin. Compteurs passifs (jambes, ordres, pas de temps détenus par racine, reports, exposition brute et nette) publiés en statistiques d'exécution, sans effet sur les ordres |

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

**Ce que le nombre d'ordres ne dit pas.** La lecture du run 2 déduisait du nombre d'ordres (1126 sur 530 semaines) que la division par le `contract_multiplier` était nécessaire au rééquilibrage. Les compteurs de la section suivante la réfutent. Sur les 884 ordres du bras B, 112 sont des reports au rollover et 772 viennent du rééquilibrage : 367 sur la jambe **courte**, que l'arrondi vers −∞ garde à −1 contrat, 70 seulement sur la jambe **longue** (YM, et en partie NQ et RTY), le reste en liquidations des positions sorties du signal.

## Dimensionnement (#23689)

**Ce que fait le code de l'article.** Sur un contrat à terme, `calculate_order_quantity(symbole, ±0.3)` rend un nombre de **contrats**, dimensionné à la **marge initiale** : le notionnel correspondant vaut plusieurs fois la valeur du portefeuille. L'article divise ce nombre par le `contract_multiplier` (125 000 pour CHF et EUR, 62 500 pour GBP, 100 000 pour CAD, 50 pour ES et RTY, 20 pour NQ, 5 pour YM), et la division entière de Python arrondit vers −∞. `calculate_order_quantity` rend en outre l'**écart** à la cible, pas la cible : tant que l'écart reste négatif, la jambe courte reçoit −1 contrat **chaque semaine où elle est reconduite** et s'empile ; une jambe longue tombe à 0 dès que l'écart est inférieur au multiplicateur.

**Protocole.** Cinq backtests du projet 38701872, mêmes frais et même capital que le run 2, lus à `completed: true` avec leur journal d'ordres :

| Run | Code | Bras | Ordres | Sharpe (QC) | Sharpe séances ouvrées, taux nul | CAGR | Drawdown max | Rendement net | PSR |
|---|---|---|---|---|---|---|---|---|---|
| `23689-ctl-B` | `main.py` de `main` avant #23689 | B | 884 | −0.345 | −0.08 | −1.48 % | 37.9 % | −9.90 % | 0.0 % |
| `23689-diag-B` | `fix=off` | B | 884 | −0.345 | −0.08 | −1.48 % | 37.9 % | −9.90 % | 0.0 % |
| `23689-diag-A` | `fix=off` | A | 1125 | −0.486 | −0.25 | −3.55 % | 44.0 % | −31.60 % | 0.0 % |
| `23689-fix-A` | `fix=on` | A | 1616 | **−1.118** | −0.82 | −6.68 % | 51.6 % | **−51.60 %** | 0.0 % |
| `23689-fix-B` | `fix=on` | B | 1314 | **−0.994** | −0.78 | −7.16 % | 47.7 % | **−40.56 %** | 0.0 % |

Le Sharpe de QC déduit le taux sans risque ; la colonne « séances ouvrées » le recalcule à taux nul sur la dernière valeur de chaque séance de New York (√252). Les deux concluent dans le même sens.

**Témoins.** `diag-B` rejoue `ctl-B` ordre par ordre : 884 ordres identiques (symbole, quantité, prix, heure de remplissage, statut), donc les compteurs ne changent aucun ordre ; et `ctl-B` reproduit le run 2 du bras B (884 ordres, Sharpe −0.345, rendement −9.90 %). Sur le bras A, le même code rend 1125 ordres et un Sharpe de −0.486, contre 1126 et −0.474 au run 2 : un écart d'une exécution à l'autre dont la cause n'est pas établie ici (la réécriture des séries ajustées entre deux dates est la piste connue), sans effet sur le verdict.

**Ce que disent les compteurs (bras B, `fix=off`).** Jambes proposées par le signal, et parmi elles celles qui ont envoyé un ordre ; pas de temps où la position est détenue :

| Racine | Longues (ordres) | Courtes (ordres) | Détenue longue | Détenue courte |
|---|---|---|---|---|
| CHF (6S) | 52 (0) | 35 (35) | 0 | 235 |
| GBP (6B) | 48 (0) | 36 (36) | 0 | 227 |
| CAD (6C) | 45 (0) | 33 (33) | 0 | 217 |
| EUR (6E) | 46 (0) | 28 (28) | 0 | 173 |
| ES | 10 (0) | 26 (26) | 0 | 154 |
| NQ | 60 (16) | 100 (100) | 69 | 677 |
| RTY | 75 (23) | 68 (68) | 115 | 486 |
| YM | 31 (31) | 41 (41) | 161 | 224 |

Sur 367 rééquilibrages, la jambe courte envoie un ordre 367 fois, la jambe longue 70 fois : sur les quatre devises et sur ES, le livre n'est **que court**. Les positions courtes s'empilent : l'exposition nette descend jusqu'à −3.36 fois la valeur du portefeuille (médiane −0.20), pendant que l'exposition brute médiane reste à 0.28 pour 0.6 visés. Le bras A montre le même motif (ES : 2 ordres longs sur 13 jambes ; nette entre −3.90 et 1.90, brute médiane 0.23).

La prévision de l'issue (« seul YM garde une taille non nulle ») est donc **réfutée en partie** : elle vaut pour la jambe longue, à NQ et RTY près ; elle ne vaut pas pour la jambe courte, que l'arrondi vers −∞ fait toujours trader.

**Sous `fix=on`.** L'exposition atteint ce que le code vise : brute médiane 0.58 (bras A) et 0.60 (bras B), nette entre −0.49 et 0.51 (bras A) et entre −0.40 et 0.40 (bras B), les deux côtés détenus sur chaque racine (bras B, CHF : 297 pas de temps long, 209 court), aucun report réduit au rollover.

## Verdict : NO BEATS

Le verdict préinscrit s'applique tel quel : **Sharpe ≤ 0 sur les deux bras → `NO BEATS` contre le cash.** La stratégie perd de l'argent sur les deux fenêtres sous frais IBKR — −31.7 % sur dix ans et demi (drawdown max 44.9 % sur un livre `±0.3`, le risque dominant), −9.9 % sur la fenêtre alignée — avec un ratio de Sharpe probabiliste de 0 % partout : aucun régime de la période ne rend ce signal viable tel quel.

**Le dimensionnement réparé ne change pas le verdict : il l'aggrave** (#23689). À l'exposition que le code vise, la stratégie perd davantage : Sharpe −1.118 sur le bras A et −0.994 sur le bras B, rendement net −51.60 % et −40.56 %, drawdown max 51.6 % et 47.7 %. Le résultat négatif du code de l'article était donc en partie amorti par son défaut : la jambe longue ne tradait presque pas, et le livre ne portait qu'une fraction de l'exposition prévue. `NO BEATS` contre le cash, pour le code de l'article comme pour le dimensionnement réparé.

**Ce que ce verdict ne dit pas.** Il ne dit pas que la prose de l'article aurait mieux fait que son code (divergence a5 : la prose décrit une **intersection** volume-haut/OI-bas que le code n'implémente pas — la variante prose n'a pas été testée, elle n'était pas dans le code mesuré). Il ne dit rien non plus d'un éventuel edge avant frais : la mesure est nette, sous brokerage IBKR, comme le demandait le dispatch. Et conformément aux cinq axes du semis, il ne confronte **aucun chiffre de l'article** — il n'en affiche aucun (axes 2 et 3) : ce portage vérifie que le code de l'article **tourne, trade et se mesure** — c'est fait — pas qu'il gagne. La famille « reversal court terme sur futures » reste ouverte à un article publié, sourcé et mesuré.

## Fichiers

- `main.py` — portage (adaptations a1–a7 en tête de fichier ; `fix=off` rejoue le code de l'article)

## Références

- Article : [research 15366](https://www.quantconnect.com/research/15366/short-term-reversal-with-futures/) (Jing Wu ; mise à jour PEP8 annoncée par Derek Melchin, STAFF)
- Quantpedia — Short Term Reversal with Futures (screener/71) — **agrégateur**, pas une source primaire
- Issue #18466 (semis, verdict IGNORE 5 axes) · EPIC #11698
