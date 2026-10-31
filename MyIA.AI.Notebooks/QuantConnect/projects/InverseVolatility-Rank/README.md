# InverseVolatility-Rank (HandsOn Ex11)

**Asset class:** Futures (12 contrats souscrits ; 10 reçoivent une prédiction, voir plus bas)
**Cloud project ID:** 38690172 (mesure #23630, 2026-10-31) · 37313767 (version dépôt d'avant #23630, mesurée 2026-10-03) · 29463533 (ancien code Cloud, voir l'historique)

## Description

Régression Ridge qui prédit la volatilité de la semaine suivante (6 séances) sur un panier de contrats à terme (indices, énergies, grains), puis répartit le portefeuille en inverse de la volatilité prédite, avec un rééquilibrage hebdomadaire.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/InverseVolatility-Rank"`
**QC Cloud:** projet 38690172 (« IVR-23630 ») = copie exacte du `main.py` du dépôt. Les paramètres `fix`, `ref`, `start` et `end` sont décrits en tête du fichier.

## Dimensionnement des contrats à terme (#23630)

Jusqu'à #23630, le poids de chaque contrat était divisé par son multiplicateur, puis passé à `set_holdings`, qui dimensionne une position sur contrat à terme par la marge initiale et non par le notionnel. Le journal des ordres du bras d'origine (`fix=off`, 2015-2024) montre deux effets :

- seuls trois contrats sont traités : Dow 30, Nasdaq 100 et S&P 500 (454, 283 et 215 ordres remplis). Les énergies et les grains, à gros multiplicateur, ne reçoivent aucun ordre alors qu'ils ont une prédiction à presque chaque rééquilibrage ;
- le notionnel brut vaut 1,58 fois la valeur du portefeuille en médiane, et 4,67 fois au maximum.

Le Sharpe publié auparavant pour la version dépôt (0,529) mesurait donc un portefeuille long d'indices actions américains, avec un levier de 1,6 en médiane, et non l'allocation en inverse de la volatilité décrite ci-dessus.

Le code par défaut (`fix=on`) garde le même signal et la même part `(1/vol) / Σ(1/vol)`, plafonnée à 15 % par contrat, et la dimensionne au notionnel : quantité = part × valeur / (prix × multiplicateur), arrondie au contrat entier, sans levier. Sur 2015-2024, il détient 11 contrats en médiane et dix racines sont traitées ; le notionnel brut sur la valeur vaut 1,02 en médiane et 1,35 au maximum, entre deux rééquilibrages. `fix=off` rejoue le dimensionnement d'origine.

Le VIX et le Brent ne reçoivent aucune prédiction sur 2015-2026, dans les deux bras : l'univers effectif est de dix contrats. La cause n'est pas encore diagnostiquée.

## Backtest Metrics

Mesure #23630 sur QC Cloud, projet 38690172 : capital 100 M, modèle de courtier et compte sur marge tels que définis dans `initialize`, comparée à SPY détenu sur la même fenêtre. Le Sharpe à taux nul (√252) est calculé sur les séances de New York communes avec SPY ; Sharpe QC (qui retranche le taux sans risque), CAGR, MaxDD et PSR sont ceux de QC.

| Fenêtre | Bras | Sharpe taux nul | Sharpe QC | CAGR | MaxDD | PSR |
|---------|------|-----------------|-----------|------|-------|-----|
| w1 : 2015-01-01 → 2024-04-01 | `fix=on` (défaut) | 0,229 | 0,038 | 2,37 % | 26,0 % | 0,02 % |
| | `fix=off` (origine) | 0,692 | 0,522 | 14,72 % | 43,0 % | 3,18 % |
| | SPY détenu | 0,743 | 0,527 | 12,59 % | 33,6 % | 3,44 % |
| w2 : 2024-04-01 → 2026-07-15 | `fix=on` (défaut) | 0,379 | −0,049 | 4,87 % | 12,5 % | 2,74 % |
| | `fix=off` (origine) | 0,332 | −0,022 | 3,61 % | 26,0 % | 3,06 % |
| | SPY détenu | 1,193 | 0,694 | 19,06 % | 18,6 % | 24,58 % |

**Verdict : NO BEATS sur les deux fenêtres**, selon la règle fixée sur #23630 avant la mesure. Le bras `fix=on` a un Sharpe inférieur à celui de SPY détenu : écart −0,51 sur w1 (Ledoit-Wolf p = 0,078), −0,81 sur w2 (p = 0,29). Le bras d'origine ne bat pas SPY non plus : −0,05 sur w1 (p = 0,83), −0,86 sur w2 (p = 0,065).

Les deux bras reçoivent les mêmes prédictions, avec des comptes par racine presque identiques : l'écart entre eux mesure le dimensionnement, pas le signal Ridge.

Le bras `off` reproduit la mesure du 2026-10-03 à peu près, sans l'égaler : Sharpe QC 0,522 contre 0,529, CAGR 14,72 % contre 14,86 %, MaxDD 43,0 % contre 40,5 %, 952 ordres contre 957. L'écart n'est pas expliqué. La réécriture des prix ajustés entre deux runs est une cause probable, non vérifiée.

| Paramètre | Valeur |
|-----------|--------|
| Model | Ridge |
| Rebalance | Weekly (`date_rules.week_start`) |
| Dimensionnement | `fix=on` : au notionnel, part plafonnée à `max_position_pct` 15 %, notionnel brut 1,0 · `weight_multiplier` 2,0 ne sert qu'au bras `fix=off` |

**Historique (#19018).** Le projet Cloud 29463533 ne contient pas le `main.py` du dépôt : il démarre le 2018-12-31, sans modèle de courtier, et ses chiffres (Sharpe 0,124, CAGR 4,13 %, MaxDD 41,0 %) décrivent ce code-là.

## Files

- main.py - Strategy (inverse vol futures, dimensionnement au notionnel depuis #23630) — la source mesurée ci-dessus
- research.ipynb - **awaiting QC Cloud execution** (project 29463533). Research node unavailable on 2026-05-11 ("No spare research nodes"). Ridge regression: 12 futures indices/energy/grains, vol features 60/90/180d, inverse-vol allocation vs equal-weight, lookback sensitivity.

## References

- Hands-On AI Trading, Section 06, Example 11
