# Split Events, variante long seul (évaluation #19242)

Projet d'évaluation dérivé de [`Positive-Negative-Splits-ML`](../Positive-Negative-Splits-ML/), lui-même issu de l'exercice 07 du chapitre 6 de *Hands-On AI Trading* (Jared Broad et al.). La règle de verdict et la grille de paramètres ont été fixées dans l'[issue #19242](https://github.com/jsboige/CoursIA/issues/19242) avant le premier backtest.

## La règle d'origine

- **Univers** : toutes les actions du secteur Technologie (classification Morningstar), en données horaires, sans filtre de liquidité ni de capitalisation.
- **Signal** : à chaque annonce de division d'actions (`SplitType.WARNING`), une régression linéaire prédit le rendement à 3 jours à partir de deux variables : le facteur de division et le taux de variation de XLK sur 22 séances.
- **Position** : dans le sens de la prédiction (achat si elle est positive, vente à découvert si elle est négative), 25 % du portefeuille par position, au plus 4 positions ouvertes, sortie à l'ouverture après 3 jours.
- **Modèle** : réentraîné chaque mois sur les divisions des 4 dernières années de l'univers.

## Ce qui change ici

Le code de la classe est repris ligne à ligne. Trois ajouts, aucun changement de règle :

1. **Paramètres** (tableau ci-dessous). Avec `long_only=0`, `fee_mult=1` et les autres valeurs par défaut, c'est la règle d'origine.
2. **Variante long seul** (`long_only=1`, valeur par défaut) : une prédiction négative ne donne aucun ordre. Elle est journalisée comme `skip`.
3. **Garde contre un modèle non ajusté** : si aucun entraînement n'a encore réussi, l'annonce de division est ignorée. Le code d'origine lèverait une erreur à cet endroit.

Les ordres passent par le modèle de frais par défaut de Lean pour ce courtier, multiplié par `fee_mult`. Comme dans l'original, la marge est autorisée. La variante long seul détient au plus 4 positions de 25 % : son exposition ne dépasse jamais 100 % du portefeuille.

## Paramètres de backtest

| Paramètre | Défaut | Rôle |
|-----------|--------|------|
| `start`, `end` | aucun (obligatoires) | fenêtre, contrat du rejeu en ombre (#18923) |
| `long_only` | 1 | `1` : achats seulement ; `0` : règle d'origine, achats et ventes à découvert |
| `fee_mult` | 1 | multiplicateur des frais (2 = frais doublés) |
| `hold_days` | 3 | durée de détention, en jours calendaires |
| `max_open` | 4 | nombre maximal de positions ouvertes ; chacune pèse 1/`max_open` |
| `lookback_years` | 4 | profondeur de l'historique d'entraînement |
| `min_dollar_volume` | 0 | volume quotidien minimal en dollars pour entrer dans l'univers |
| `sector_prices` | `raw` | `raw` : XLK en prix bruts, comme l'original ; `adjusted` : prix ajustés, pour le seul run de diagnostic (hors règle de verdict) |

Les quatre runs préinscrits ont tourné sur la version du code sans `sector_prices` (empreinte SHA-256 `08ec0bb49fc0…`). Le paramètre a été ajouté ensuite pour le diagnostic ; à sa valeur par défaut, XLK reste en prix bruts, comme dans ces quatre runs.

## Sorties

Contrat du rejeu en ombre (`ML-Training-Pipeline/shadow/README.md`) : après chaque clôture, la valeur du portefeuille est écrite dans le graphique `shadow` (séries `e0` à `e4` à tour de rôle). S'y ajoutent les frais cumulés (`fees`, en fraction du capital de départ) et la rotation cumulée (`turnover`). Les mesures se calculent sur ces séries, pas sur les statistiques du rapport QuantConnect.

Le journal de l'algorithme écrit :

- `sig <date> <ticker> f=<facteur> roc=<taux XLK> pred=<prédiction> long|short|skip` pour chaque annonce évaluée ;
- `fill <date> <ticker> <quantité> @ <prix>` pour chaque exécution ;
- en fin de run, `end closes=<séances> invested=<séances investies> long=… short=… skip=…`.

## Résultats

Backtests QuantConnect du 2026-10-05, modèle de frais par défaut de Lean pour ce courtier. Mesures sur les séries du rejeu en ombre (Sharpe à taux sans risque nul), sauf mention « QC ». Références : SPY détenu et 60/40 SPY/IEF du projet `FourSleeve774Benchmarks` (#19139), mêmes séances (2 194 rendements, aucune séance manquante d'un côté ou de l'autre).

### Fenêtre principale, 2018-01-01 → 2026-09-25

| Run | Sharpe | CAGR | Pire baisse | Rotation / an | Frais / an | Ordres | Part du temps investie |
|-----|--------|------|-------------|---------------|------------|--------|------------------------|
| **long seul** (`long_only=1`) | **0,45** | 11,0 % | 34,1 % | 4,5 | 1,78 % | 156 | 12,3 % |
| long seul, frais doublés | 0,42 | 10,1 % | 34,1 % | 4,5 | 3,40 % | 156 | 12,3 % |
| règle d'origine (`long_only=0`) | ruine | — | 133 % (QC) | — | — | 482 | — |
| SPY détenu | 0,79 | 13,9 % | 33,6 % | 0,1 | 0,00 % | — | 100 % |
| 60/40 SPY/IEF | 0,81 | 8,9 % | 21,2 % | 0,3 | 0,02 % | — | 100 % |

Frais et rotation sont exprimés en fraction du capital de départ.

**La règle d'origine se ruine.** Le 2025-12-04, elle vend à découvert TGL à 0,29 dollar par action pour 25 % du portefeuille, juste avant un regroupement de 20 actions en une. Le titre monte ensuite à 27,56 puis 35,87 dollars (prix après regroupement), et les appels de marge rachètent la position. La pire baisse mesurée par QC atteint 133 % : le portefeuille passe sous zéro, et l'algorithme s'arrête le 2026-03-16. Le signal de TGL est normal (taux de variation de XLK à −3,6 %), donc la ruine ne vient pas du défaut décrit plus bas. Elle vient du risque propre à la vente à découvert de micro-valeurs : aucun modèle d'emprunt de titres n'est configuré dans le code, et le backtest suppose donc que ces titres s'empruntent sans limite.

### Verdict préinscrit : `NO BEATS`

Différence de Sharpe de la variante long seul contre chaque référence, par bootstrap circulaire par blocs de 21 séances (10 000 tirages, graine 18921, correction de Holm) :

| Référence | Différence | IC 95 % | p unilatérale | p Holm | Frais doublés | 2018-2020 | 2021-2023 | 2024 → 2026-09 |
|-----------|-----------:|---------|--------------:|-------:|--------------:|----------:|----------:|---------------:|
| SPY détenu | −0,34 | [−1,13 ; +0,42] | 0,80 | 1,00 | −0,36 | −0,18 | +0,23 | −0,70 |
| 60/40 SPY/IEF | −0,37 | [−1,16 ; +0,41] | 0,81 | 1,00 | −0,39 | −0,44 | +0,47 | −0,69 |

Les deux différences sont négatives et aucune n'est significative : c'est le cas `NO BEATS` de la règle. La grille de cinq points n'a pas été lancée, comme prévu : elle ne pouvait plus changer le verdict.

Corrélations hebdomadaires de la variante long seul sur la fenêtre principale : −0,02 avec `vt2`, −0,01 avec `aw` (paniers proxys du projet compagnon de #18904), −0,05 avec la 774, −0,04 avec la [676](../MultiHorizonMomentum676/), 0,00 avec SPY. La stratégie diversifierait ; elle ne rapporte pas assez pour mériter la place.

### Ce que les journaux montrent

1. **Trois ans sans un seul achat.** De 2023 à 2025, le modèle prédit un rendement négatif pour les 171 annonces de division qu'il évalue, dont 150 regroupements. La variante long seul reste donc en liquidités, ce que la règle d'origine compense par des ventes à découvert.
2. **Le résultat vient des titres à quelques centimes.** Sur les 77 positions fermées de la variante long seul, les 39 entrées à moins d'un dollar par action portent 92 % du résultat. Pour la reproduction 2018 → 2024-04 de la règle d'origine, c'est 69 % (85 positions sur 123). QC estime la capacité de la règle d'origine à 3 000 dollars sur cette fenêtre, et à 14 000 dollars sur la fenêtre principale. Pour la variante long seul, QC affiche 1,1 milliard de dollars, chiffre incompatible avec ces prix d'entrée : nous ne le retenons pas.
3. **Un défaut de données dans le code d'origine.** XLK hérite de la normalisation `RAW` de l'univers. Sa division de décembre 2025 apparaît donc comme une baisse de 50 % : le taux de variation sur 22 séances passe de −2,5 % (2025-11-20) à −50,3 % (2025-12-17), y reste un mois, puis revient à +1,2 % (2026-01-16). Le modèle, réentraîné chaque mois sur quatre ans, garde ces points dans son historique. Les achats de 2026 portent 62 % du résultat de la variante long seul.

   **Run de diagnostic, hors règle de verdict** (`sector_prices=adjusted`, XLK en prix ajustés). Le taux de variation reste normal en décembre 2025 (entre −0,5 % et +3,6 %) et les achats de janvier 2026 disparaissent. De 2018 à 2025, le run est identique au précédent : mêmes signaux, même croissance. Le résultat de 2026 ne disparaît pas pour autant. Il tient à une seule position : MASK, achetée à 0,115 dollar le 2026-03-13 et revendue trois jours plus tard à 3,52 dollars, après un regroupement de facteur 2. Le backtest y lit +1 430 %, soit 152 % du résultat de ce run. Ce rendement suppose que le facteur enregistré dans les données est le bon ; nous ne l'avons pas vérifié hors QC. Le Sharpe de ce run est de 0,36 (0,45 en prix bruts), sa pire baisse de 47,5 %. Dans les deux traitements, la variante long seul reste sous SPY et sous le 60/40 : le verdict ne dépend pas de ce choix. Dans le run en prix bruts aussi, trois positions de 2026 entrées sous un dollar (FCUV, HKIT, AGBA) portent 88 % du résultat.

### Écart avec les chiffres déjà publiés

Règle d'origine sur 2018-01-01 → 2024-04-01, statistiques QC (Sharpe avec taux sans risque) :

| Mesure | Registre comparatif | Ce run |
|--------|--------------------:|-------:|
| Sharpe | 1,51 | 1,16 |
| PSR | 82,3 % | 43,6 % |
| CAGR | 75,7 % | 52,4 % |
| Pire baisse | 37,6 % | 42,2 % |

La fenêtre exacte du chiffre publié n'est pas documentée ; la mesure n'atteint ici le seuil de 50 % de PSR sur aucune fenêtre. 89 % du résultat de cette reproduction vient de 2023 et du premier trimestre 2024. Le statut « robuste » du registre est retiré, et la description du modèle est corrigée dans [`qc-strategies-status.md`](../../../../docs/qc/qc-strategies-status.md) : le code n'utilise aucune donnée de résultats d'entreprise.

### Suivi en ombre

Le code est gelé à la date du verdict, avec `sector_prices=raw` : c'est la règle préinscrite, défaut compris. Il est inscrit au registre du suivi en ombre (#18923) après merge, comme les autres stratégies évaluées.

Traces (plans, identifiants de backtest, journaux, `results.json`) : hors dépôt, dossier `QC-traces/19242-split-events` du partage du cluster.
