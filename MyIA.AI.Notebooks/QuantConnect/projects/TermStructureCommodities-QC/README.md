# TermStructureCommodities-QC

**Classe d'actifs :** contrats à terme sur matières premières (21 racines : céréales, softs, viandes, énergie, métaux)
**Source :** QuantConnect Strategy Library n° 26, Quantpedia n° 22, clonée le 2026-04-05

## Ce que fait la stratégie

Une fois par mois, l'algorithme mesure la forme de la courbe de chaque matière première. Pour chaque racine, il compare le contrat le plus proche et le plus lointain parmi ceux qui expirent dans les 90 jours :

```text
R = (ln P_proche - ln P_lointain) * 365 / (T_lointain - T_proche)
```

Un R positif signale une courbe en **déport** (*backwardation*) : le contrat proche est plus cher que le lointain, et tenir le contrat rapporte un rendement de roulement. Un R négatif signale un **report** (*contango*), qui coûte au détenteur.

La stratégie achète le quintile le plus en déport et vend le quintile le plus en report, à parts égales. C'est un portefeuille long-court en coupe transversale, et non un pari sur la direction des prix : la littérature (Gorton et Rouwenhorst, 2006 ; Erb et Harvey, 2006) y voit une prime de structure par terme.

## Le diagnostic #23594 : un levier non voulu, pas le signal

Le registre (`docs/qc/qc-strategies-status.md`, tranche 15) classait la stratégie en BROKEN sur 2018-2025 : Sharpe −0,244, MaxDD 96,8 %, résultat net −92,9 %. Il attribuait la perte à la courbe des matières premières après 2020.

Le journal des ordres de ce backtest dit autre chose. Rejoué jour par jour avec les multiplicateurs des contrats, il montre que le code visait ±0,1/count par côté, soit un notionnel brut de 0,2 fois la valeur du portefeuille. Le notionnel mesuré valait 3,6 fois la valeur au premier rééquilibrage, 1,42 fois en médiane et 4,98 fois au maximum. Le premier ordre vendait à lui seul l'équivalent de 1,16 fois le capital initial.

La cause : sur un contrat à terme, `set_holdings` dimensionne la position par la **marge initiale**, pas par le notionnel. Une cible de 2,5 % de marge ouvre une position dix à vingt fois plus grosse en exposition.

Deux défauts secondaires s'y ajoutaient :

- le contrat traité était le plus proche (échéance de 0 à 90 jours), tenu un mois sans roulement. Une partie du livre expirait avant le rééquilibrage suivant et restait en liquidités ;
- les dictionnaires `positive_roll_returns` et `negative_roll_returns` n'étaient définis que dans la boucle, ce qui fait échouer `_rebalance` si aucune chaîne n'a deux contrats.

## Paramètres de mesure

`main.py` lit quatre paramètres QuantConnect :

| Paramètre | Valeurs | Effet |
|---|---|---|
| `fix` | `off` | code d'origine, ordres inchangés, compteurs passifs en plus |
| | `on` (défaut) | même signal, trois corrections : dimensionnement au notionnel (±0,5/count par côté, portefeuille entièrement collatéralisé), contrat traité expirant au moins 35 jours après le rééquilibrage, dictionnaires initialisés avant la boucle |
| `ref` | `dbc` | bras de référence : l'ETF DBC détenu, sans contrat à terme |
| `start`, `end`, `cash` | `AAAA-MM-JJ`, entier | fenêtre et capital (10 M par défaut avec `on`, pour que l'arrondi au contrat entier ne déforme pas les poids) |

Le signal reste calculé sur les seuls contrats à 90 jours dans les deux bras. Les compteurs publiés en statistiques d'exécution sont `gross_median` et `gross_max` (notionnel brut sur valeur, 90 minutes après chaque rééquilibrage), `expiry_cuts`, `delist_orders`, `invalid_orders`, `no_tradable`, `no_price` et `rebalances`.

## Résultats (#23594)

Six backtests QC Cloud du 2026-10-30 (projet 38682809), lus à `completed: true`, journal des ordres relu pour chacun. Le protocole et les règles de verdict ont été fixés sur l'issue avant toute exécution. Le Sharpe est calculé à taux nul (√252) sur les séances communes à la stratégie et à la référence ; la significativité vient de `Paradox46Benchmarks/significance.py` (Ledoit-Wolf, bootstrap stationnaire).

### Diagnostic du dimensionnement (w1, 2018-01-01 → 2025-01-01)

| Bras | Notionnel brut / valeur, médiane | maximum | Positions coupées par une échéance |
|---|---|---|---|
| `off` | 2,36 | 4,95 | 243 |
| `on` | 1,00 | 1,31 | 11 |

Le compteur est relevé 90 minutes après chaque rééquilibrage. Le rejeu du journal des ordres donne 1,37 en médiane pour `off` (5,01 au premier rééquilibrage) et 1,00 pour `on`. Le défaut est **confirmé** (médiane supérieure à 1 dans `off`) et **corrigé** (médiane entre 0,8 et 1,2 dans `on`).

### Verdict contre DBC détenu

| Fenêtre | Bras | Sharpe taux nul | CAGR | MaxDD | PSR | Écart de Sharpe contre DBC (p Ledoit-Wolf) | Verdict |
|---|---|---|---|---|---|---|---|
| w1 : 2018-01-01 → 2025-01-01 | `on` | −0,21 | −7,36 % | 57,9 % | 0,001 % | −0,53 (p = 0,20) | **NO BEATS** |
| | `off` (pour information) | −0,08 | −26,04 % | 95,5 % | 0,010 % | −0,40 (p = 0,32) | — |
| | DBC détenu | 0,32 | 5,56 % | 41,7 % | 0,35 % | — | — |
| w2 : 2025-01-01 → 2026-07-31 | `on` | 0,12 | 1,29 % | 29,3 % | 5,55 % | −0,93 (p = 0,16) | **NO BEATS** |
| | `off` (pour information) | 0,66 | 25,79 % | 43,4 % | 21,41 % | −0,40 (p = 0,59) | — |
| | DBC détenu | 1,05 | 24,32 % | 16,5 % | 37,27 % | — | — |

CAGR, MaxDD et PSR sont ceux de QuantConnect. Le bootstrap stationnaire (2000 tirages, blocs de 10 séances) donne un intervalle à 95 % de l'écart de Sharpe qui contient zéro dans les quatre comparaisons.

### Lecture

- **Le levier explique la ruine, pas la perte.** Ramené à un notionnel égal à la valeur, le livre long-court perd encore 41,5 % sur 2018-2024 (MaxDD 57,9 %). Le BROKEN de la tranche 15 confondait les deux effets : la ruine était un artefact de dimensionnement, la perte appartient au signal.
- **Le même levier amplifie aussi les hausses.** Sur 2025-2026, la version d'origine gagne 43,7 % avec un notionnel brut médian de 2,71 fois la valeur, contre 2,05 % pour la version corrigée. Son Sharpe reste sous celui de DBC : le gain mesure l'exposition, pas une prime.
- **Aucune prime de structure par terme n'apparaît sur ces 21 racines.** L'écart de Sharpe contre DBC est négatif dans les quatre comparaisons, et aucune n'est significative.

### Limites

- Le bras `on` porte trois corrections à la fois. La comparaison `on` contre `off` ne mesure donc pas le seul effet du dimensionnement ; seul le diagnostic du notionnel lui est attribuable.
- Dans `on`, le signal reste lu sur les contrats à 90 jours, mais la position est prise sur un contrat plus lointain (au moins 35 jours). Le rendement de roulement encaissé n'est donc pas exactement celui qui a classé la racine.
- Un seul jeu de paramètres est mesuré : quintiles sur 21 racines, soit quatre contrats par côté, rééquilibrage mensuel.
- Le bras `off` ne reproduit pas exactement la mesure de la tranche 15 : −87,9 % contre −92,9 %, et 516 ordres contre 468, sur la même fenêtre. L'écart n'est pas expliqué ici.

## Exécuter

**QC Cloud** : copier `main.py` dans un projet, puis passer les paramètres ci-dessus dans l'onglet des paramètres du backtest.

**Lean CLI** : `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/TermStructureCommodities-QC" --parameter fix on`. Les données de contrats à terme en minute ne sont pas fournies avec le dépôt.

## Références

- Gorton, G. et Rouwenhorst, K. G. (2006), « Facts and Fantasies about Commodity Futures », *Financial Analysts Journal* 62(2).
- Erb, C. et Harvey, C. (2006), « The Strategic and Tactical Value of Commodity Futures », *Financial Analysts Journal* 62(2).
- QuantConnect Strategy Library, « Term Structure Effect in Commodities ».
