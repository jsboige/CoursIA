# SectorMomentum

**Classe d'actifs :** Actions US + Bonds + Or (SPY, TLT, GLD)
**ID projet Cloud :** Aucun (local uniquement)
**Statut :** ARCHIVÉE (plafond de Sharpe ~0,56)

## Description

Stratégie de dual momentum avec score composite multi-lookback (1, 3, 6, 12 mois, poids 0,4/0,2/0,2/0,2) sur 3 actifs : SPY (risk-on), TLT (bonds), GLD (or).

Quand SPY a un momentum absolu positif ET se situe au-dessus de sa SMA200 ET surperforme TLT/GLD : position 100 % SPY.
Sinon : rotation vers l'actif défensif le plus performant (TLT ou GLD).
Protection de sortie SMA200 quotidienne (stops intra-mensuels si SPY passe sous la SMA200).

**Archivée car :** plafond de Sharpe ~0,56 pour le dual momentum sur 3-5 actifs. La cible de 0,8 exige une approche fondamentalement différente. Voir ARCHIVE.md pour le détail complet.

## Comment exécuter

**Lean CLI :** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/SectorMomentum"`
```bash
lean backtest --project .
```

**QC Cloud :** Pas encore déployée. Copier les fichiers dans un nouveau projet QC Cloud pour l'exécuter.

## Métriques de backtest

### Tableau historique : non reproduit

Ce README annonçait, pour « 2015-2026 », un Sharpe de 0,555, un CAGR de 13,0 % et une pire baisse de 22,8 % (rééquilibrage mensuel des entrées, sortie SMA200 quotidienne). Ces valeurs ne se reproduisent pas (#20264). Le code de `main` à `0d7487cec6`, exécuté sur les nœuds QC, donne :

- sur la fenêtre 2015-01-01 → 2026-07-10 : Sharpe 0,480, CAGR 11,48 %, pire baisse 22,8 % ;
- sur la fenêtre codée dans `main.py` (2015-01-01 → 2024-12-31) : Sharpe 0,275, CAGR 6,85 %, pire baisse 22,8 %.

### Garde de mois et tranche de minuit (#20264)

En résolution journalière, Lean livre l'avis de dividende mensuel de TLT seul, dans une tranche datée de minuit, sans barre. Le garde `rebalance_month` consommait le mois sur cette tranche : l'ordre partait à minuit et s'exécutait à l'ouverture du jour même, avec les clôtures de la veille. Les autres mois, il partait à la clôture de la première séance et s'exécutait à l'ouverture suivante. Le correctif ne consomme le mois que sur une tranche qui porte une barre de SPY, TLT ou GLD. La sortie quotidienne SMA200 n'est pas touchée.

Mesure pré-enregistrée sur #20264 avant tout backtest. Avant = `main` à `0d7487cec6`, après = ce correctif ; hors fenêtre codée, seules les deux lignes de date changent. Six backtests sur les nœuds QC, chacun lu à `completed: true`, ordres relus à la source jusqu'à retrouver le nombre des statistiques.

| Fenêtre | Dates | Ordres de minuit avant → après | Ordres | Sharpe QC | CAGR | Pire baisse |
|---|---|---|---|---|---|---|
| codée | 2015-01-01 → 2024-12-31 | 71 (44 mois) → 0 | 95 → 111 | 0,275 → −0,096 | 6,85 → 0,53 % | 22,8 → 38,2 % |
| hors échantillon | 2025-01-01 → 2026-07-10 | 4 (3 mois) → 0 | 5 → 6 | 1,419 → 1,261 | 45,96 → 40,83 % | 19,2 → 19,2 % |
| du tableau historique | 2015-01-01 → 2026-07-10 | 75 (47 mois) → 0 | 100 → 118 | 0,480 → 0,157 | 11,48 → 5,26 % | 22,8 → 38,2 % |

Hors échantillon, le verdict fixé d'avance est **`DEGRADATION`** : l'écart de Sharpe (−0,158) et celui de CAGR (−5,13 pt) dépassent les seuils (−0,10 et −0,5 pt).

**Un second défaut pèse sur les deux colonnes.** `set_holdings(..., 1.0)` est envoyé alors que la position précédente n'est pas encore vendue : les ventes partent en `MarketOnOpen` et ne sont pas exécutées au moment de l'achat. Le compte sur marge refuse alors l'achat (« Insufficient buying power »), et le livre reste en liquidités jusqu'au rééquilibrage suivant, alors que `in_spy` le croit investi. Achats refusés, avant → après : 8 → 10 sur la fenêtre codée, 0 → 1 hors échantillon, 8 → 11 sur la fenêtre du tableau historique. Ce ne sont pas les mêmes mois.

Une estimation hors QC (clôtures ajustées, rendement de l'actif visé pendant chaque période en liquidités) chiffre ces refus. Sur la fenêtre codée, ils ont épargné 5,2 % à la variante avant et coûté 14,8 % à la variante après. Ils expliquent environ un tiers de l'écart de richesse finale. Le reste vient de décisions prises un jour plus tard, sur des clôtures différentes. Hors échantillon, l'écart tient presque entièrement à un seul achat de SPY refusé le 2026-05-01 dans la variante après (rendement de SPY manqué : 5,4 %).

Un Sharpe qui bouge de 0,37 pour un décalage d'un jour du calendrier ne décrit pas une stratégie robuste. Ces chiffres mesurent les défauts, pas la stratégie, qui reste archivée. Le défaut de pouvoir d'achat est suivi en #20388.

Identifiants de backtest QC, avant / après :
- codée : `f324e3f5b1ad19720069b8619e4c41f6` / `d1169673f6ec0f798cb1cd644de0993b`
- hors échantillon : `5df75d4a31c556aeca917cc0b0d2540e` / `db52460299013407854f1a83940d37fa`
- tableau historique : `c696e01af0a4feb63ea32fac06fa8507` / `b307b836ccde0930031371b122fc3af8`

### Demi-séances (#20286)

Quand le 3 juillet tombe un lundi, c'est à la fois le premier jour de cotation du mois et une demi-séance qui ferme à 13:00, heure de New York : en 2017 et en 2023 sur les fenêtres ci-dessus. Sur la tranche de clôture d'une demi-séance, `history()` rend environ 21 barres journalières de moins que demandé (mesuré dans #20286 sur un autre projet). `_composite_momentum` demandait `max_lookback` barres (252) et rendait `None` en dessous. Le mois était déjà marqué comme traité, et `on_data` sortait sans rien écrire dans le journal : juillet 2017 et juillet 2023 passaient sans rééquilibrage. La sortie quotidienne SMA200 appelle la même fonction pour TLT et GLD : sur une demi-séance, elle était reportée à la séance suivante.

Correctif dans `main.py` : `_composite_momentum` demande le double de barres et garde les 252 dernières. Sur une séance pleine, ce sont les mêmes barres qu'avant. Aucune ligne du journal ne montre l'historique court : la cause se déduit du code, et le retour des mois manquants avec ce seul changement la confirme.

Mesure sur les nœuds QC, frais de courtage inclus, protocole fixé avant les backtests ([#20286, c.6117521094](https://github.com/jsboige/CoursIA/issues/20286#issuecomment-6117521094)). La variante avant reprend les backtests « après » de la section précédente, dont le code est celui de `main` (empreintes comparées) :

| Fenêtre | Variante | Mois rééquilibrés | Sharpe | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|---|
| 2015-01-01 → 2024-12-31 (codée) | avant | 118 / 120 | −0,096 | 0,53 % | 38,2 % | 111 | `d1169673f6ec0f798cb1cd644de0993b` |
| | après | 120 / 120 | −0,081 | 0,78 % | 38,2 % | 112 | `a90623a7e25fe53321d26d9228d4a3a1` |
| 2025-01-01 → 2026-07-10 (hors échantillon) | avant | 19 / 19 | 1,261 | 40,83 % | 19,2 % | 6 | `db52460299013407854f1a83940d37fa` |
| | après | 19 / 19 | 1,261 | 40,83 % | 19,2 % | 6 | `bbf4f63bc43a7e460835b39057542615` |
| 2015-01-01 → 2026-07-10 (tableau historique) | avant | 137 / 139 | 0,157 | 5,26 % | 38,2 % | 118 | `b307b836ccde0930031371b122fc3af8` |
| | après | 139 / 139 | 0,169 | 5,49 % | 38,2 % | 119 | `c62cedc7e6b7a29582d9a3c6bb2fb933` |

Sharpe calculé par QC, taux sans risque inclus. Les quatre prédictions fixées d'avance ont tenu :

- les rééquilibrages des lundis 3 juillet 2017 et 2023 reviennent sur les deux fenêtres qui les contiennent, en `[RISK ON]` les deux fois ;
- avant le 2017-07-03, les ordres sont identiques (date, titre, quantité : 38 sur 38) ; l'exception admise pour une sortie SMA200 sur une demi-séance n'a pas servi, les 11 sorties SMA200 ont les mêmes dates avant et après ;
- les dates de rééquilibrage sont celles d'avant, plus les deux lundis ;
- hors échantillon, aucun mois ne commence par une demi-séance, et les deux variantes sont identiques au centime.

Le rééquilibrage du 2017-07-03 n'envoie aucun ordre : le livre est déjà investi en SPY. Celui du 2023-07-03 achète du SPY. Avant le correctif, le livre restait en liquidités depuis l'achat refusé du 2023-06-01 (#20388) et ne rachetait du SPY que le 2023-08-01 : le défaut de demi-séance prolongeait d'un mois une période en liquidités ouverte par le défaut de pouvoir d'achat. Les ordres ne diffèrent qu'à partir de ce lundi. Le nombre d'achats refusés ne change pas (10, 1 et 11). L'écart de Sharpe (+0,015 sur la fenêtre codée, +0,012 sur celle du tableau historique) reste sous le seuil de 0,05 fixé d'avance : les chiffres de la section précédente ne sont pas réécrits. Ce n'est pas un verdict de stratégie : il s'agit de la correction d'un défaut, mesurée sur des fenêtres déjà vues.

## Fichiers

- `main.py` - Stratégie (v3.2, confirmée comme la meilleure)
- `research.ipynb` - Optimisation multi-lookback et tests d'univers étendu

## Références

- Antonacci (2014), « Dual Momentum Investing »
- Faber (2007), « A Quantitative Approach to Tactical Asset Allocation »
- ARCHIVE.md - Historique complet des itérations et analyse du plafond
