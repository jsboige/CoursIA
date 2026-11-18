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
- `start`, `end` : format `%Y-%m-%d`, obligatoires, sans valeur par défaut (la fenêtre du protocole est 2009-10-01 → 2026-07-31) ;
- `min_market_cap` : plancher de capitalisation en dollars (défaut 10 milliards).
- `exclude` : symboles retirés de l'univers éligible, séparés par des virgules (défaut `LBTYB`, voir le protocole ; `exclude=` vide rejoue la série d'origine).

Le graphique `shadow` suit le contrat du rejeu en ombre (#18923) : à la clôture de chaque séance de SPY, hors préchauffage, il porte la valeur du portefeuille, répartie sur les séries `e0` à `e4`, les frais cumulés divisés par la valeur de départ (`fees`) et la rotation cumulée, en fraction du portefeuille (`turnover`). La valeur du portefeuille est la série que comparent les tests ; ceux du verdict ont été lus sur la version 1, qui la prenait à l'ouverture (voir « Version 2 »). Les statistiques d'exécution publient `invalid_orders` et, pour `strategy` et `all`, le nombre moyen, minimal et maximal de lignes courtes par rééquilibrage (`shorts_mean`, `shorts_min`, `shorts_max`, `shorts_empty_days`).

## Protocole (#24228)

Le protocole complet, avec les prédictions, est le commentaire de pré-enregistrement de #24228. En résumé :

- **une fenêtre**, 2009-10-01 → 2026-07-31, celle de l'article raccourcie de trois mois. La fin est passée en paramètre, pour que la coupure d'environ 90 jours de certains nœuds de backtest ne la raccourcisse pas en silence. **C'est la fenêtre de l'article : la mesure est une reproduction, pas un test hors échantillon** ;
- **contrôle de reproduction** : le CAGR QC de `strategy` doit être compris entre 1,5 % et 5 %, et son bêta QC contre SPY inférieur à 0,1 en valeur absolue ;
- **contrôle de propriété** : le nombre moyen de lignes courtes de `strategy` doit valoir entre 0,45 et 0,50 fois celui de `all` ;
- **tests** : `Paradox46Benchmarks/significance.py`, taux sans risque nul (écart de Sharpe de Ledoit-Wolf, bootstrap stationnaire, écart de moyennes de Newey-West). Verdict : `strategy` contre `spy` et `6040`, Holm sur six p-valeurs. Diagnostics : `strategy` contre `half` et contre `all`, Holm sur trois p-valeurs chacun ; ils ne modifient pas le verdict ;
- **règle de verdict** : `BEATS` si l'écart de Sharpe est positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ; `NO BEATS` si le Sharpe de la stratégie est inférieur à celui de SPY détenu ; `INCONCLUSIVE` dans tous les autres cas.
- **amendement, déclaré sur #24228 avant la lecture des tests** : sur la série d'origine, un prix erroné de LBTYB (rempli à 51 329,82 le 2014-02-18, pour un cours d'environ 51) porte 94 % de la valeur finale de `strategy`. Le titre est retiré de l'univers éligible et seuls `strategy` et `all` sont relancés, sans autre changement. La plus forte variation de séance de la nouvelle trace est de 2,40 %.

Propriétés du code :

- dans Lean, les liquidités et le produit des ventes à découvert ne rapportent rien, et le coût d'emprunt des titres n'est pas modélisé ;
- pas de modèle de courtage explicite : l'article n'en montre pas, et les cinq modes partagent le modèle par défaut de Lean. Le rééquilibrage quotidien multiplie les petits ordres, dont les frais sont comptés.

## Verdict

**`NO BEATS`** (QC Cloud, 2026-11-02, #24228). Le Sharpe annualisé de `strategy`, avec un taux sans risque nul, vaut 0,53 : il est inférieur à celui de SPY détenu (0,87) et du 60/40 (0,95). L'écart de Sharpe n'est pas significatif (p de Holm 0,98 contre les deux références). Le rendement moyen est, lui, significativement inférieur : −12,2 % par an contre `spy` (p de Holm 0,013), −7,1 % contre `6040` (0,044).

| Mode | CAGR | Sharpe QC | Perte max. |
|---|---|---|---|
| `strategy`, série d'origine | 21,55 % | 0,288 | 13,0 % |
| `strategy`, LBTYB exclu | 2,62 % | −0,009 | 13,2 % |
| `all`, LBTYB exclu | 2,22 % | −0,093 | 11,8 % |
| `half` | 7,20 % | 0,469 | 18,3 % |
| `spy` | 14,32 % | 0,633 | 33,7 % |
| `6040` | 9,67 % | 0,596 | 21,6 % |

- **Contrôles.** Reproduction tenue sur la série relancée (CAGR 2,62 %, bêta QC contre SPY 0,022 ; l'article publie 3,16 %), échouée sur la série d'origine. Propriété tenue : le nombre moyen de lignes courtes vaut 44,02 pour `strategy` contre 88,56 pour `all`, soit un rapport de 0,497.
- **Jambe courte : elle n'apporte rien.** L'écart de rendement moyen `strategy` − `half` est négatif, −4,6 % par an (p de Holm 0,13). Sur la fenêtre, vendre à découvert les grandes sociétés étrangères peu rentables coûte du rendement.
- **Filtre de rentabilité : question ouverte.** L'écart `strategy` − `all` est positif mais minime, +0,43 % par an (p de Holm 1,0), avec une corrélation de 0,93.
- **Ce que reproduit la mesure** : un rendement d'environ 3 % par an à bêta quasi nul, qui ne rémunère pas le risque mieux que les références. Le coût d'emprunt n'étant pas modélisé, la mesure est favorable à la stratégie.

**Sous-période postérieure à la publication.** Calculée sur la trace `shadow` déjà produite, sans nouveau backtest. La coupure est le numéro de mars 2015 de la RFS (vol. 28, n° 3), où paraît l'article de Hou, Xue et Zhang : 2015-03-02 → 2026-07-31, 2872 séances. L'article QC n° 21634 est postérieur à la fin de la trace, aucune séance ne le suit. La sous-période est donc hors échantillon pour la source académique, pas pour l'article QC, dont elle reste dans la fenêtre.

| Bras (trace, taux sans risque nul) | CAGR | Sharpe | Perte max. |
|---|---|---|---|
| `strategy`, LBTYB exclu | 2,24 % | 0,44 | 13,2 % |
| `spy` | 13,53 % | 0,81 | 33,7 % |
| `6040` | 8,89 % | 0,84 | 21,6 % |

Le verdict ne change pas. L'écart de Sharpe n'est pas significatif (p de Holm 1,0 contre les deux références). Le rendement moyen reste inférieur, −11,9 % par an contre `spy` et −6,8 % contre `6040`, mais l'écart n'est plus significatif après correction (p de Holm 0,094 et 0,24). Les trois pertes max. tombent après mars 2015 : ce sont celles de la fenêtre entière.

Le détail des tests est sur #24228.

## Version 2 (2026-11-11)

La version mesurée par le verdict lisait `start_date` et `end_date` avec des valeurs par défaut et ne traçait que la valeur du portefeuille, à l'ouverture de chaque séance. Elle ne tenait pas le contrat du rejeu en ombre : le graphique ne portait ni `fees` ni `turnover`, que l'ingestion exige, et la valeur prise à l'ouverture n'était pas celle de la clôture que demande le contrat.

La version 2 lit `start` et `end` sans valeur par défaut et trace, à la clôture de chaque séance de SPY, la valeur du portefeuille, `fees` et `turnover`. La règle de trading ne change pas. Elle est gelée au registre d'ombre le 2026-11-12, sous l'identifiant `short-intl-v2`, sur le projet QC 39243884, au SHA `fa1d63e`.

Deux contrôles :

- **ingestion** : un backtest court (2026-09-01 → 2026-11-10, projet QC 39243884) est accepté par `ingest_qc` du rejeu, essayé en local sans toucher au registre : 50 points pour 50 séances négociables, du 2026-09-01 au 2026-11-10 à 16 h ET ;
- **mêmes ordres** : le rejeu de la fenêtre du protocole en mode `strategy` (projet QC 39243931) et celui de la version 1 (projet 38795329), lancés le même jour, rendent les mêmes statistiques d'exécution de Lean au centime près : rendement total 54,54 %, CAGR 2,618 %, perte max. 13,2 %, frais égaux à 8,95 % de la valeur de départ, volume égal à 70,52 fois cette valeur, 44,02 positions courtes en moyenne (de 21 à 70), aucun ordre invalide. Le run du verdict, le 2026-11-02, finit 0,09 % plus haut, avec 0,75 % de volume en plus. Les deux versions coïncidant à date égale, cet écart vient des données de QC entre les deux dates, pas de la version 2.

Sur la fenêtre complète (4233 séances), QC rééchantillonne les séries `fees` et `turnover` du graphique : 3407 points rendus, environ un tous les 1,34 jour. Le contrôle d'ingestion, sur 50 séances, rend un point par séance, comme un passage d'ombre mensuel.
