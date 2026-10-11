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

## Métriques de backtest

Mesure du 2026-10-10 sur les nœuds QC, fenêtre codée 2018-01-01 → 2025-01-01, **avant et après** le correctif de la tranche de minuit (#20264). Le protocole a été pré-enregistré sur l'issue avant les deux runs (commentaire `c.6099402027`). La colonne « avant » est le code de `main` au commit `a492cda2b3`, exécuté tel quel.

| Indicateur | Avant correctif | Code corrigé |
|---|---|---|
| Ratio de Sharpe | −0,026 | **0,224** |
| CAGR | 2,141 % | **6,837 %** |
| Drawdown max | 42,600 % | **27,600 %** |
| Profit net total | 15,998 % | **58,917 %** |
| PSR (Probabilistic Sharpe Ratio) | 0,052 % | **0,637 %** |
| Ordres | 343 | 309 |
| Frais | 447,94 USD | 377,80 USD |
| Ordres datés de minuit, heure de New York | **27**, sur 5 jours | **0** |
| Backtest QC | `a772737bfde57dad91cb64801eb0939c` (projet 37630569) | `a8e7809afb021ce8b42e8b59d61e9e1b` (projet 37630571) |

La colonne « avant » reproduit le run publié auparavant (2026-08-07, `SectorRotation-honest-read-2026-08` : Sharpe −0,029, CAGR 2,118 %, drawdown 42,700 %, 345 ordres). L'écart de deux ordres vient des révisions de données entre les deux dates.

### Le défaut corrigé (#20264)

En résolution journalière, Lean livre les avis de dividende et de division dans une tranche datée de minuit, sans barre de cotation. Le compteur `days_since_rebalance` comptait ces tranches comme des séances, avec deux effets.

1. **Liquidation forcée.** Quand la 21ᵉ unité du compteur tombait sur une tranche de minuit, aucun des cinq titres n'y avait de donnée. La liste qualifiée était vide et `_go_defensive()` vendait tout pour passer à 100 % en SHY jusqu'au rééquilibrage suivant, soit environ un mois. C'est arrivé cinq fois : 2018-03-01, 2018-11-01, 2023-06-01, 2024-04-01 et 2024-06-24.
2. **Calendrier qui glisse.** SHY verse un dividende chaque mois, QQQ, SPY, IWM et EFA plusieurs fois par an : le compteur avançait donc plus vite que les séances. Quatre des cinq liquidations forcées tombent d'ailleurs un premier jour ouvré du mois, au rythme des dividendes de SHY. Les rééquilibrages de 2018 tombaient les 26/03, 24/04, 22/05 et 18/06 avant correctif, et tombent les 03/04, 02/05, 01/06 et 02/07 après.

Le correctif ajoute, en tête de `on_data` et avant l'incrément du compteur, un garde qui ignore toute tranche où aucun des cinq titres n'a de barre. Le compteur compte désormais des séances, comme l'annonce la description. Les paramètres ne changent pas.

### Ce que l'écart mesure, et ce qu'il ne mesure pas

L'écart entre les deux colonnes **n'est pas le coût des cinq liquidations seules**. Le calendrier corrigé déplace aussi tous les rééquilibrages, et pour une rotation mensuelle la date seule pèse lourd. L'écart se concentre sur 2018-2020, alors que les années suivantes restent proches (rendements annuels lus sur la courbe d'équité QC) :

| Année | 2018 | 2019 | 2020 | 2021 | 2022 | 2023 | 2024 |
|---|---|---|---|---|---|---|---|
| Avant correctif | −16,8 % | −1,8 % | +1,1 % | +20,7 % | −19,6 % | +22,2 % | +18,2 % |
| Code corrigé | −2,5 % | +7,1 % | +22,1 % | +20,5 % | −25,6 % | +20,3 % | +15,5 % |

En mars 2020, par exemple, le code avant correctif rééquilibrait le 20/03 (passage en SHY près du point bas) puis le 16/04 ; le code corrigé le fait le 04/03 puis le 02/04. C'est une différence de date, pas de règle : **aucun verdict de stratégie ne se tire de cet écart**, conformément au pré-enregistrement.

### Défaut résiduel connu (#20286)

Dans les deux runs, un rééquilibrage tombé sur une demi-séance (clôture à 13:00, heure de New York) passe aussi tout en SHY alors que le marché monte : le 2019-11-29 avant correctif, le 2019-07-03 après. Une garde sur la longueur de l'historique est suspectée, sans encore être vérifiée. Ce défaut n'est pas corrigé ici (un sujet par PR) : les chiffres « code corrigé » comprennent donc encore un mois passé en SHY à tort, juillet 2019.

**Verdict : NO-BEATS**, rendu le 2026-08-07 sur le code avant correctif. Cette mesure n'en rend pas de nouveau. À titre descriptif, le code corrigé reste loin de SPY détenu sur la même fenêtre en rendement (CAGR à deux chiffres pour SPY, contre 6,8 % ici). Son drawdown max de 27,6 % n'est en revanche plus supérieur à celui de SPY, de l'ordre de 34 % au krach de 2020.

## Lecture honnête

Sur le code corrigé, le double filtre (SMA200 + momentum 126 j positif) et la pondération proportionnelle au momentum ne protègent toujours pas dans les régimes adverses du 2018-2025. La pire baisse va du 2021-12-28 au 2022-12-29 :

- **Concentration.** Quand un seul titre passe le double filtre, il reçoit 100 % du portefeuille. En 2022, la position est entièrement en SPY en février, entièrement en GLD en mars, puis en mai et juin. De février à décembre 2022, le portefeuille ne détient jamais plus de deux lignes.
- **Défensif tardif.** Le repli sur SHY ne se produit que lorsqu'**aucun** actif ne passe le double filtre. En 2022, il n'arrive que le 05/07, après la baisse de SPY du premier semestre. La sortie, le 01/12 vers SPY et IWM, précède de peu la baisse de décembre.
- **PSR ≈ 0.** Avec un PSR de 0,637 %, le Sharpe observé n'est pas statistiquement significatif : on ne peut pas distinguer ce résultat d'un tirage aléatoire. Tout claim de bord serait trompeur (règle C, PR-review-discipline §C).

**Pas de re-tuning.** Re-optimiser les paramètres (lookback momentum, période de rebalancement, univers) pour récupérer un Sharpe sur cette seule fenêtre serait du surapprentissage jusqu'à preuve du contraire, le biais dénoncé dans l'EPIC #9768 (D2 « fenêtre non figée »). Le correctif de #20264 n'est pas un réglage : il fait faire au code ce que sa description annonce (rééquilibrer toutes les 21 séances), sans toucher aux paramètres.

## Fichiers

| Fichier | Description |
|---------|-------------|
| `main.py` | Rotation sectorielle avec allocation pondérée par momentum et double filtre de tendance (v4) |

## Références

- [Documentation QuantConnect](https://www.quantconnect.com/docs/)
- EPIC de consolidation QC / Trading : #1621
- Discipliné par l'EPIC #9768 (dérive des métriques de backtest à travers les révisions)

See #1621 (contribution partielle : honest-read d'une stratégie non auditée).
