# Cloud-SectorRotation-Momentum

**Classe d'actifs :** Actions, Obligations, Matières premières (rotation d'ETF)

**ID projet Cloud :** 30821748

## Description

Trend-following pondéré par momentum sur un univers de 5 ETF (QQQ, SPY, EFA, GLD, IWM) avec SHY comme équivalent cash défensif. Utilise un double filtre (prix au-dessus du SMA200 **et** momentum positif sur 6 mois / 126 jours de cotation) pour sélectionner les actifs en tendance, puis alloue proportionnellement à leurs scores de momentum mesurés par taux de variation (ROC). Rebalance tous les 21 jours de bourse. Brokerage Interactive Brokers (frais réels), benchmark SPY.

## Comment exécuter

### Lean CLI
```bash
lean backtest --algorithm Cloud-SectorRotation-Momentum/main.py
```

### QC Cloud
Projet 30821748. Téléverser `main.py`, compiler et lancer un backtest. Période codée en dur : **2018-01-01 → 2025-01-01** (alignée sur la baseline cross-stratégie #1630 ; le code ne fixe pas de date de fin mobile, donc la fenêtre est figée par les dates du source).

Trois paramètres optionnels servent à la mesure contre références détenues (#21371). Absents, ils ne changent rien :

- `mode` : `strategy` (défaut, la stratégie), `spy` (SPY détenu) ou `6040` (SPY 60 %, BND 40 %, rééquilibré au début de chaque mois, une minute après l'ouverture) ;
- `start_date` et `end_date` (`%Y%m%d`), qui remplacent les dates codées.

Dans les trois modes, le graphique `shadow` trace la valeur du portefeuille à chaque ouverture de SPY.

## Métriques de backtest

Mesure du 2026-10-10 sur les nœuds QC, fenêtre codée 2018-01-01 → 2025-01-01, **avant et après** le correctif de la tranche de minuit (#20264). Le protocole a été pré-enregistré sur l'issue avant les deux runs (commentaire `c.6099402027`). La colonne « avant » est le code de `main` au commit `a492cda2b3`, exécuté tel quel. La troisième colonne, mesurée le 2026-10-11, est le code actuel : il corrige en plus les demi-séances (#20286, protocole pré-enregistré sur l'issue, commentaires `c.6105254259` et `c.6105308987`).

| Indicateur | Avant correctif | Après #20264 | Code actuel (#20286) |
|---|---|---|---|
| Ratio de Sharpe | −0,026 | 0,224 | **0,196** |
| CAGR | 2,141 % | 6,837 % | **6,291 %** |
| Drawdown max | 42,600 % | 27,600 % | **27,600 %** |
| Profit net total | 15,998 % | 58,917 % | **53,316 %** |
| PSR (Probabilistic Sharpe Ratio) | 0,052 % | 0,637 % | **0,496 %** |
| Ordres | 343 | 309 | 307 |
| Frais | 447,94 USD | 377,80 USD | 360,43 USD |
| Ordres datés de minuit, heure de New York | **27**, sur 5 jours | **0** | **0** |
| Backtest QC | `a772737bfde57dad91cb64801eb0939c` (projet 37630569) | `a8e7809afb021ce8b42e8b59d61e9e1b` (projet 37630571) | `5661dc625175652677c63daa90074862` (projet 37654337) |

La colonne « avant » reproduit le run publié auparavant (2026-08-07, `SectorRotation-honest-read-2026-08` : Sharpe −0,029, CAGR 2,118 %, drawdown 42,700 %, 345 ordres). L'écart de deux ordres vient des révisions de données entre les deux dates.

### Le défaut corrigé (#20264)

En résolution journalière, Lean livre les avis de dividende et de division dans une tranche datée de minuit, sans barre de cotation. Le compteur `days_since_rebalance` comptait ces tranches comme des séances, avec deux effets.

1. **Liquidation forcée.** Quand la 21ᵉ unité du compteur tombait sur une tranche de minuit, aucun des cinq titres n'y avait de donnée. La liste qualifiée était vide et `_go_defensive()` vendait tout pour passer à 100 % en SHY jusqu'au rééquilibrage suivant, soit environ un mois. C'est arrivé cinq fois : 2018-03-01, 2018-11-01, 2023-06-01, 2024-04-01 et 2024-06-24.
2. **Calendrier qui glisse.** SHY verse un dividende chaque mois, QQQ, SPY, IWM et EFA plusieurs fois par an : le compteur avançait donc plus vite que les séances. Quatre des cinq liquidations forcées tombent d'ailleurs un premier jour ouvré du mois, au rythme des dividendes de SHY. Les rééquilibrages de 2018 tombaient les 26/03, 24/04, 22/05 et 18/06 avant correctif, et tombent les 03/04, 02/05, 01/06 et 02/07 après.

Le correctif ajoute, en tête de `on_data` et avant l'incrément du compteur, un garde qui ignore toute tranche où aucun des cinq titres n'a de barre. Le compteur compte désormais des séances, comme l'annonce la description. Les paramètres ne changent pas.

### Ce que l'écart mesure, et ce qu'il ne mesure pas

L'écart entre les deux premières colonnes **n'est pas le coût des cinq liquidations seules**. Le calendrier corrigé déplace aussi tous les rééquilibrages, et pour une rotation mensuelle la date seule pèse lourd. L'écart se concentre sur 2018-2020, alors que les années suivantes restent proches (rendements annuels lus sur la courbe d'équité QC) :

| Année | 2018 | 2019 | 2020 | 2021 | 2022 | 2023 | 2024 |
|---|---|---|---|---|---|---|---|
| Avant correctif | −16,8 % | −1,8 % | +1,1 % | +20,7 % | −19,6 % | +22,2 % | +18,2 % |
| Après #20264 | −2,5 % | +7,1 % | +22,1 % | +20,5 % | −25,6 % | +20,3 % | +15,5 % |
| Code actuel (#20286) | −2,5 % | +3,4 % | +22,0 % | +20,4 % | −25,6 % | +20,3 % | +15,5 % |

En mars 2020, par exemple, le code avant correctif rééquilibrait le 20/03 (passage en SHY près du point bas) puis le 16/04 ; le code corrigé le fait le 04/03 puis le 02/04. C'est une différence de date, pas de règle : **aucun verdict de stratégie ne se tire de cet écart**, conformément au pré-enregistrement.

### Demi-séances (#20286)

Une demi-séance US ferme à 13:00, heure de New York : le 3 juillet, le lendemain de Thanksgiving et le 24 décembre. Ces jours-là, `history()` rend 104 à 106 barres journalières pour 126 demandées, et l'historique commence environ un mois trop tard. Sur 2018-2024, c'est le cas des 15 demi-séances, et d'aucune séance pleine. La garde `len(closes) < momentum_lookback` écartait alors les cinq titres. `_go_defensive()` passait tout en SHY alors que le marché montait : le 2019-11-29 avant #20264, le 2019-07-03 après. Pourquoi Lean raccourcit la requête n'est pas établi ici. Seul l'effet est mesuré.

Le correctif demande deux fois la fenêtre et garde les 126 dernières clôtures. Sur une séance pleine, ce sont les mêmes barres qu'avant.

Une première version, qui demandait 5 barres de plus, n'a rien changé : elle recevait encore moins de 126 barres, et son run était identique à celui d'avant. La version retenue a été pré-enregistrée avant son run, avec quatre prédictions, qui ont toutes tenu :

- les ordres antérieurs au 2019-07-03 sont identiques ;
- le 2019-07-03, le portefeuille s'investit dans les cinq titres au lieu de SHY ;
- aucun achat de SHY ne tombe sur une demi-séance ;
- les 83 rééquilibrages tombent aux mêmes dates.

Seule l'année 2019 change vraiment (+7,1 % → +3,4 %) : le passage en SHY à tort de juillet 2019 avait fait mieux que la position investie. L'écart de Sharpe (−0,028) reste sous le seuil de 0,05 fixé d'avance. C'est un effet de trajectoire, pas un verdict.

Le verdict NO-BEATS du 2026-08-07 avait été rendu sur le code avant correctif, et les mesures des 10 et 11 octobre n'en rendaient pas de nouveau. Le verdict sur le code actuel est rendu dans la section suivante.

### Verdict contre références détenues (#21371)

**Verdict : NO BEATS**, sur la fenêtre codée et sur la fenêtre hors échantillon.

Mesure du 2026-10-19 sur les nœuds QC. Le protocole a été pré-enregistré sur #21371 avant le premier backtest, sur le modèle de #21329. La stratégie (code actuel, décision inchangée) est comparée à deux références détenues dans le même algorithme, sous le même modèle de courtage et le même préchauffage de 200 séances : SPY détenu, et un 60/40 SPY/BND rééquilibré au début de chaque mois.

**Contrôle d'innocuité : tenu.** En mode `strategy`, sur la fenêtre codée, le code instrumenté reproduit `5661dc62` ordre par ordre (307 ordres, même date, même symbole, même quantité) et sur ses 27 statistiques QC.

**Tests.** Les séries sont la valeur du portefeuille à chaque ouverture de SPY. Le script `Paradox46Benchmarks/significance.py` les compare avec un taux sans risque nul : écart de Sharpe de Ledoit-Wolf, bootstrap stationnaire, écart de moyennes de Newey-West, puis correction de Holm sur les six p-valeurs de chaque fenêtre.

**Règle de verdict, écrite avant la mesure :**

- `BEATS` : l'écart de Sharpe est positif et significatif (Holm < 0,05) contre les deux références ;
- `NO BEATS` : le Sharpe de la stratégie est inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

| Fenêtre | Séances | Sharpe stratégie | SPY détenu | 60/40 | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|
| Codée, 2018-01-02 → 2024-12-31 | 1761 | 0,464 | 0,758 | 0,751 | 1,0 / 1,0 | **NO BEATS** |
| Hors échantillon, 2025-01-02 → 2026-07-21 | 387 | 0,908 | 1,034 | 1,158 | 1,0 / 1,0 | **NO BEATS** |

Statistiques QC des mêmes runs (projet 38081193, taux sans risque de QC) :

| Fenêtre | Mode | Sharpe QC | CAGR | Pire baisse | Ordres | Backtest |
|---|---|---|---|---|---|---|
| Codée | stratégie | 0,196 | 6,29 % | 27,6 % | 307 | `40af1c25d64c80a77a574de56ce000ba` |
| Codée | SPY détenu | 0,496 | 13,58 % | 33,7 % | 3 | `ae15f6714a2c156dfc5b822bcf03a954` |
| Codée | 60/40 | 0,378 | 8,66 % | 21,7 % | 147 | `09e7ae2e198134dcd163da2d2e889e27` |
| Hors échantillon | stratégie | 0,551 | 16,19 % | 14,5 % | 79 | `afa13c14daf65aa0447bc8419724a104` |
| Hors échantillon | SPY détenu | 0,651 | 18,49 % | 18,7 % | 2 | `19ae7d2186db8a01379dc0a65806050a` |
| Hors échantillon | 60/40 | 0,554 | 12,80 % | 11,2 % | 30 | `4faedf9e53a2666e623cf7e7fc657fff` |

**Ce que montrent les verdicts.** Sur la fenêtre codée, le verdict confirme le NO-BEATS du 2026-08-07, cette fois sur le code corrigé et avec un test. Hors échantillon, la fin effective est le 2026-07-21 : les nœuds QC coupent les backtests environ 90 jours avant la date demandée (`end_date=20261019`). Sur cette fenêtre courte, aucun écart n'est significatif. La règle range pourtant le cas en NO BEATS, puisque le Sharpe ponctuel reste sous celui de SPY.

**À titre descriptif**, sans effet sur les verdicts :

- sur les deux fenêtres, la pire baisse de la stratégie est inférieure à celle de SPY détenu, mais supérieure à celle du 60/40 ;
- le compteur de rééquilibrage part de zéro : la stratégie reste en liquidités pendant ses 21 premières séances, dans chaque fenêtre. Cette propriété du code est gardée telle quelle. Elle pèse surtout sur la fenêtre courte.

## Lecture honnête

Sur le code actuel, le double filtre (SMA200 + momentum 126 j positif) et la pondération proportionnelle au momentum ne protègent toujours pas dans les régimes adverses du 2018-2025. La pire baisse va du 2021-12-28 au 2022-12-29 :

- **Concentration.** Quand un seul titre passe le double filtre, il reçoit 100 % du portefeuille. En 2022, la position est entièrement en SPY en février, entièrement en GLD en mars, puis en mai et juin. De février à décembre 2022, le portefeuille ne détient jamais plus de deux lignes.
- **Défensif tardif.** Le repli sur SHY ne se produit que lorsqu'**aucun** actif ne passe le double filtre. En 2022, il n'arrive que le 05/07, après la baisse de SPY du premier semestre. La sortie, le 01/12 vers SPY et IWM, précède de peu la baisse de décembre.
- **PSR ≈ 0.** Avec un PSR de 0,496 %, le Sharpe observé n'est pas statistiquement significatif : on ne peut pas distinguer ce résultat d'un tirage aléatoire. Tout claim de bord serait trompeur (règle C, PR-review-discipline §C).

**Pas de re-tuning.** Re-optimiser les paramètres (lookback momentum, période de rebalancement, univers) pour récupérer un Sharpe sur cette seule fenêtre serait du surapprentissage jusqu'à preuve du contraire, le biais dénoncé dans l'EPIC #9768 (D2 « fenêtre non figée »). Les correctifs de #20264 et #20286 ne sont pas des réglages : ils font faire au code ce que sa description annonce (rééquilibrer toutes les 21 séances, sur 126 jours de momentum), sans toucher aux paramètres.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation sectorielle avec allocation pondérée par momentum et double filtre de tendance (v4) ; modes de mesure `spy` et `6040`, trace `shadow` (#21371) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
- EPIC de consolidation QC / Trading : #1621
- Discipliné par l'EPIC #9768 (dérive des métriques de backtest à travers les révisions)
- Mesure contre références détenues : #21371, sur le protocole de #21329

See #1621 (contribution partielle : honest-read d'une stratégie non auditée).
