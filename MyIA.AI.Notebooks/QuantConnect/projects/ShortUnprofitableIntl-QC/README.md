# ShortUnprofitableIntl-QC

La vente à découvert des grandes sociétés étrangères peu rentables, couverte par SPY, mesurée contre SPY détenu et le 60/40 au protocole de la ligue de stratégies (#19821). Le protocole a été écrit dans #24228 avant le premier backtest.

## Description

**Source.** Article de recherche QuantConnect n° 21634, « Shorting unprofitable international stocks against the S&P 500 » (2026). L'article reprend l'idée du facteur de rentabilité, qu'il attribue à Hou, Xue et Zhang (RFS 2015) et à Fama et French (JFE 2015). Il la porte hors des États-Unis et ne garde que la jambe courte.

**La règle**, reprise du code de l'article :

- SPY à 50 % de la valeur du portefeuille ;
- vente à découvert, à poids égaux (−0,5/N chacune), des N sociétés retenues ;
- sont éligibles les sociétés cotées aux États-Unis, hors constituants de SPY, dont le pays n'est pas les États-Unis et dont la capitalisation dépasse 10 milliards de dollars ;
- sont retenues celles dont la rentabilité des capitaux propres est sous la médiane des éligibles. Elle vaut le résultat net des douze derniers mois divisé par les capitaux propres, et n'est définie que pour des capitaux propres positifs ;
- sélection et rééquilibrage chaque jour, ordres envoyés à 8 h ET et remplis à l'ouverture.

**Écart à la source académique.** Chez Hou, Xue et Zhang, le facteur de rentabilité est un écart entre sociétés à rentabilité haute et basse, à l'intérieur du marché américain. L'article mesure autre chose : une jambe courte sur des sociétés étrangères, couverte par l'indice américain. Son résultat mélange donc l'effet de rentabilité et l'écart entre les États-Unis et le reste du monde. Le diagnostic `half`, décrit ci-dessous, isole la contribution de la jambe courte.

Le paramètre `mode` choisit le portefeuille :

| Mode | Portefeuille | Rôle |
|---|---|---|
| `strategy` (défaut) | la règle de l'article | la règle |
| `all` | même éligibilité, toutes les sociétés éligibles vendues à découvert, sans le découpage à la médiane | diagnostic du filtre de rentabilité |
| `half` | SPY à 50 %, le reste en liquidités, rééquilibré chaque jour | diagnostic de la jambe courte |
| `spy` | SPY détenu | référence du verdict |
| `6040` | SPY 60 %, BND 40 %, rééquilibré le premier jour de bourse du mois | référence du verdict |

Seuls `strategy` et `all` souscrivent l'univers fondamental et l'univers des constituants de SPY. Une garde a été ajoutée au code de l'article : tant que l'univers n'a rien sélectionné, le rééquilibrage ne vend rien à découvert.

## How to Run

Projet QC Cloud : un `main.py` sans dépendance hors de Lean. Paramètres :

- `mode` : `strategy`, `all`, `half`, `spy` ou `6040` ;
- `start_date`, `end_date` : format `%Y-%m-%d` (défauts 2009-10-01 et 2026-07-31) ;
- `min_market_cap` : plancher de capitalisation en dollars (défaut 10 milliards).

Le graphique `shadow` porte la valeur du portefeuille à l'ouverture de chaque séance de SPY, hors préchauffage, répartie sur les séries `e0` à `e4` (contrat #18923). C'est la série que comparent les tests. Les statistiques d'exécution publient `invalid_orders` et, pour `strategy` et `all`, le nombre moyen, minimal et maximal de lignes courtes par rééquilibrage (`shorts_mean`, `shorts_min`, `shorts_max`, `shorts_empty_days`).

## Protocole (#24228)

Le protocole complet, avec les prédictions, est le commentaire de pré-enregistrement de #24228. En résumé :

- **une fenêtre**, 2009-10-01 → 2026-07-31, celle de l'article raccourcie de trois mois. La fin est fixée dans le code, pour que la coupure d'environ 90 jours de certains nœuds de backtest ne la raccourcisse pas en silence. **C'est la fenêtre de l'article : la mesure est une reproduction, pas un test hors échantillon** ;
- **contrôle de reproduction** : le CAGR QC de `strategy` doit être compris entre 1,5 % et 5 %, et son bêta QC inférieur à 0,1 en valeur absolue ;
- **contrôle de propriété** : le nombre moyen de lignes courtes de `strategy` doit valoir entre 0,45 et 0,50 fois celui de `all` ;
- **tests** : `Paradox46Benchmarks/significance.py`, taux sans risque nul (écart de Sharpe de Ledoit-Wolf, bootstrap stationnaire, écart de moyennes de Newey-West). Verdict : `strategy` contre `spy` et `6040`, Holm sur six p-valeurs. Diagnostics : `strategy` contre `half` et contre `all`, Holm sur trois p-valeurs chacun ; ils ne modifient pas le verdict ;
- **règle de verdict** : `BEATS` si l'écart de Sharpe est positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ; `NO BEATS` si le Sharpe de la stratégie est inférieur à celui de SPY détenu ; `INCONCLUSIVE` dans tous les autres cas.

Propriétés du code :

- dans Lean, les liquidités et le produit des ventes à découvert ne rapportent rien, et le coût d'emprunt des titres n'est pas modélisé ;
- pas de modèle de courtage explicite : l'article n'en montre pas, et les cinq modes partagent le modèle par défaut de Lean. Le rééquilibrage quotidien multiplie les petits ordres, dont les frais sont comptés.

## Verdict

**En cours de mesure.** Les cinq backtests tournent sur QC Cloud. Le verdict, les contrôles et les diagnostics seront publiés ici et sur #24228, à la lecture des résultats complets.
