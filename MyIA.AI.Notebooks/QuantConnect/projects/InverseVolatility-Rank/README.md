# InverseVolatility-Rank (HandsOn Ex11)

**Asset class:** Futures (12 contrats souscrits, tous prédits depuis #23638 ; voir plus bas)
**Cloud project ID:** 38690172 (mesures #23630 et #23638, 2026-10-31) · 37313767 (version dépôt d'avant #23630, mesurée 2026-10-03) · 29463533 (ancien code Cloud, voir l'historique)

## Description

Régression Ridge qui prédit la volatilité de la semaine suivante (6 séances) sur un panier de contrats à terme (indices, énergies, grains), puis répartit le portefeuille en inverse de la volatilité prédite, avec un rééquilibrage hebdomadaire.

## How to Run

**Lean CLI:** `lean backtest "MyIA.AI.Notebooks/QuantConnect/projects/InverseVolatility-Rank"`
**QC Cloud:** projet 38690172 (« IVR-23630 ») = copie exacte du `main.py` du dépôt. Les paramètres `fix`, `ref`, `universe`, `start` et `end` sont décrits en tête du fichier.

## Dimensionnement des contrats à terme (#23630)

Jusqu'à #23630, le poids de chaque contrat était divisé par son multiplicateur, puis passé à `set_holdings`, qui dimensionne une position sur contrat à terme par la marge initiale et non par le notionnel. Le journal des ordres du bras d'origine (`fix=off`, 2015-2024) montre deux effets :

- seuls trois contrats sont traités : Dow 30, Nasdaq 100 et S&P 500 (454, 283 et 215 ordres remplis). Les énergies et les grains, à gros multiplicateur, ne reçoivent aucun ordre alors qu'ils ont une prédiction à presque chaque rééquilibrage ;
- le notionnel brut vaut 1,58 fois la valeur du portefeuille en médiane, et 4,67 fois au maximum.

Le Sharpe publié auparavant pour la version dépôt (0,529) mesurait donc un portefeuille long d'indices actions américains, avec un levier de 1,6 en médiane, et non l'allocation en inverse de la volatilité décrite ci-dessus.

Le code par défaut (`fix=on`) garde le même signal et la même part `(1/vol) / Σ(1/vol)`, plafonnée à 15 % par contrat, et la dimensionne au notionnel : quantité = part × valeur / (prix × multiplicateur), arrondie au contrat entier, sans levier. Sur 2015-2024, avec l'univers d'origine, il détient 11 contrats en médiane et dix racines sont traitées ; le notionnel brut sur la valeur vaut 1,02 en médiane et 1,35 au maximum, entre deux rééquilibrages. `fix=off` rejoue le dimensionnement d'origine.

## Univers : le VIX et le Brent (#23638)

Jusqu'à #23638, deux des douze racines ne recevaient jamais de prédiction. Un compteur passif des motifs de sortie de `_trade`, lu sur 2016-01 → 2016-04 et 2025-01 → 2025-04, montre deux causes distinctes :

- le Brent était souscrit sous la racine `B`, le Brent d'ICE, pour laquelle QC ne fournit aucun contrat : le motif est `no_contract` à chaque rééquilibrage. Il est désormais souscrit comme `BZ`, le Brent Last Day Financial du NYMEX (`Futures.Energy.BRENT_LAST_DAY_FINANCIAL`) ;
- les contrats VIX (`VX`) sont bien souscrits et reçoivent leurs barres, mais l'historique `OpenInterest` de QC ne renvoie aucune ligne pour eux, et le code écartait tout contrat privé de ce troisième facteur. Ils sont désormais ajustés sur les deux facteurs de prix seuls.

Avec `universe=fixed` (défaut), les douze racines reçoivent une prédiction à presque chaque rééquilibrage : entre 427 et 483 fois sur 483 de 2015 à 2024, sans ordre invalide. Le portefeuille détient 13 contrats en médiane, avec un notionnel brut de 1,03 fois la valeur en médiane et 1,36 au maximum. `universe=book` garde l'univers d'origine : sur 2016-01 → 2016-04, il rejoue à l'identique les 152 ordres du code d'avant #23638.

## Backtest Metrics

Mesures #23630 et #23638 sur QC Cloud, projet 38690172 : capital 100 M, modèle de courtier et compte sur marge tels que définis dans `initialize`, comparées à SPY détenu sur la même fenêtre. Le Sharpe à taux nul (√252) est calculé sur les séances de New York communes avec SPY ; Sharpe QC (qui retranche le taux sans risque), CAGR, MaxDD et PSR sont ceux de QC. Les lignes `universe=book` sont celles de #23630, mesurées avant la réparation de l'univers.

| Fenêtre | Bras | Sharpe taux nul | Sharpe QC | CAGR | MaxDD | PSR |
|---------|------|-----------------|-----------|------|-------|-----|
| w1 : 2015-01-01 → 2024-04-01 | `fix=on`, `universe=fixed` (défaut) | 0,069 | −0,104 | −0,01 % | 35,5 % | 0,003 % |
| | `fix=on`, `universe=book` | 0,229 | 0,038 | 2,37 % | 26,0 % | 0,02 % |
| | `fix=off`, `universe=book` (origine) | 0,692 | 0,522 | 14,72 % | 43,0 % | 3,18 % |
| | SPY détenu | 0,743 | 0,527 | 12,59 % | 33,6 % | 3,44 % |
| w2 : 2024-04-01 → 2026-07-15 | `fix=on`, `universe=fixed` (défaut) | 0,599 | 0,122 | 7,64 % | 12,0 % | 5,19 % |
| | `fix=on`, `universe=book` | 0,379 | −0,049 | 4,87 % | 12,5 % | 2,74 % |
| | `fix=off`, `universe=book` (origine) | 0,332 | −0,022 | 3,61 % | 26,0 % | 3,06 % |
| | SPY détenu | 1,193 | 0,694 | 19,06 % | 18,6 % | 24,58 % |

**Verdict : NO BEATS sur les deux fenêtres**, selon la règle fixée sur #23630 avant la mesure. Le code par défaut a un Sharpe inférieur à celui de SPY détenu : écart −0,67 sur w1 (Ledoit-Wolf p = 0,037 ; l'intervalle à 95 % du bootstrap stationnaire, [−1,34 ; −0,11], exclut zéro), −0,59 sur w2 (p = 0,51 ; intervalle [−2,45 ; 0,97]). Avec l'univers d'origine, le bras `fix=on` ne bat pas SPY : −0,51 sur w1 (p = 0,078), −0,81 sur w2 (p = 0,29) ; le bras d'origine non plus : −0,05 sur w1 (p = 0,83), −0,86 sur w2 (p = 0,065).

Les deux bras de #23630 (`fix=on` et `fix=off`, univers d'origine) reçoivent les mêmes prédictions, avec des comptes par racine presque identiques : l'écart entre eux mesure le dimensionnement, pas le signal Ridge.

Les deux racines ajoutées par #23638 tirent dans des sens opposés selon la fenêtre. La contribution de chaque racine est rejouée depuis le journal des ordres : flux des remplissages, plus la position ouverte en fin de fenêtre valorisée au dernier prix, frais exclus. C'est une approximation qui classe les racines, sans reconstituer le résultat net. Sur w1, le VIX coûte 27,5 % du capital initial et le Brent en rapporte 5,1 % ; les dix autres racines gardent à peu près leurs contributions d'avant la réparation, si bien que la dégradation du Sharpe vient du VIX. Sur w2, le VIX rapporte 4,5 % et le Brent 1,2 %, et l'univers complet fait mieux que l'univers d'origine (Sharpe 0,60 contre 0,38). Le coût de roulement d'une position longue en contrats VIX, en contango la plupart du temps, est une explication plausible de la perte sur w1, non mesurée ici.

Le bras `off` reproduit la mesure du 2026-10-03 à peu près, sans l'égaler : Sharpe QC 0,522 contre 0,529, CAGR 14,72 % contre 14,86 %, MaxDD 43,0 % contre 40,5 %, 952 ordres contre 957. L'écart n'est pas expliqué. La réécriture des prix ajustés entre deux runs est une cause probable, non vérifiée.

| Paramètre | Valeur |
|-----------|--------|
| Model | Ridge |
| Rebalance | Weekly (`date_rules.week_start`) |
| Dimensionnement | `fix=on` : au notionnel, part plafonnée à `max_position_pct` 15 %, notionnel brut 1,0 · `weight_multiplier` 2,0 ne sert qu'au bras `fix=off` |
| Univers | `universe=fixed` : 12 racines, Brent en `BZ`, VIX ajusté sans open interest · `universe=book` : univers d'origine, dix racines prédites |

**Historique (#19018).** Le projet Cloud 29463533 ne contient pas le `main.py` du dépôt : il démarre le 2018-12-31, sans modèle de courtier, et ses chiffres (Sharpe 0,124, CAGR 4,13 %, MaxDD 41,0 %) décrivent ce code-là.

## Files

- main.py - Strategy (inverse vol futures, dimensionnement au notionnel depuis #23630, univers réparé depuis #23638) — la source mesurée ci-dessus
- research.ipynb - **awaiting QC Cloud execution** (project 29463533). Research node unavailable on 2026-05-11 ("No spare research nodes"). Ridge regression: 12 futures indices/energy/grains, vol features 60/90/180d, inverse-vol allocation vs equal-weight, lookback sensitivity.

## References

- Hands-On AI Trading, Section 06, Example 11
