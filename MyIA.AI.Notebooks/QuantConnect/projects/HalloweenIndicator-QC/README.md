# HalloweenIndicator-QC

L'indicateur Halloween (« Sell in May and go away ») mesuré contre SPY détenu et le 60/40, au protocole de la ligue de stratégies (#19821). Le protocole a été écrit dans #24069 avant le premier backtest.

## Description

L'indicateur Halloween est une anomalie saisonnière : les actions rapporteraient davantage de novembre à avril que de mai à octobre.

**Source.** Sven Bouman et Ben Jacobsen, *The Halloween Indicator, "Sell in May and Go Away": Another Puzzle*, American Economic Review, vol. 92, n° 5 (2002). Seule la version de travail de juillet 2001 a été lue ; sa première page l'annonce « à paraître dans l'American Economic Review ». Ce qui suit en est repris :

- **la règle** (annexe A, p. 21) : acheter un portefeuille de marché fin octobre, le revendre début mai, et placer en actif sans risque (bons du Trésor à court terme) de fin avril à fin octobre. La référence « Buy and Hold » détient le marché toute l'année ;
- **le constat** (p. 2-3) : l'effet se retrouve dans 36 des 37 pays de l'échantillon. Aux États-Unis, les rendements de novembre à avril dépassent en moyenne de plus de 5 points ceux de mai à octobre (p. 8) ;
- **le tableau A** (p. 22), États-Unis 1973-1996 : Buy and Hold, rendement annuel moyen 11,37 %, écart-type 16,40 % ; stratégie Halloween, 11,61 % et 11,38 %.

Les données de l'article s'arrêtent en 1998. Les deux fenêtres mesurées ici commencent en 2016.

**Le code.** SPY tient lieu de marché et BIL (SPDR Bloomberg 1-3 Month T-Bill ETF) d'actif sans risque. La décision se prend au début de chaque mois, une minute après l'ouverture de SPY. Un ordre ne part qu'au changement de régime ou à l'entrée dans la fenêtre, et le portefeuille bascule alors à 100 % sur la ligne du régime, sans levier.

Le paramètre `mode` choisit le portefeuille :

| Mode | Portefeuille | Rôle |
|---|---|---|
| `strategy` (défaut) | SPY de novembre à avril, BIL de mai à octobre | la règle |
| `spy` | SPY détenu | référence du verdict |
| `6040` | SPY 60 %, BND 40 %, rééquilibré au début de chaque mois | référence du verdict |
| `inverse` | SPY de mai à octobre, BIL de novembre à avril | diagnostic de l'asymétrie saisonnière |

## How to Run

Projet QC Cloud : un `main.py` sans dépendance hors de Lean. Paramètres :

- `mode` : `strategy`, `spy`, `6040` ou `inverse` ;
- `start_date`, `end_date` : format `%Y-%m-%d` (défauts 2016-01-01 et 2026-07-01).

Le graphique `shadow` porte la valeur du portefeuille à l'ouverture de chaque séance de SPY, répartie sur les séries `e0` à `e4` (contrat #18923). C'est la série que comparent les tests.

## Verdict contre références détenues (#24069)

Le protocole a été écrit dans #24069 avant le premier backtest, sur le modèle de #22828. Les deux références du verdict, SPY détenu et le 60/40 (SPY 60 %, BND 40 %), tournent dans le même algorithme que la stratégie, sous le même modèle de courtage. Le diagnostic `inverse` ne compte pas dans le verdict.

Propriétés du code :

- en résolution journalière, Lean remplit à la clôture de la séance un ordre décidé une minute après l'ouverture. La stratégie bascule donc à la clôture de la première séance de novembre et à celle de mai. Elle manque la première séance de novembre et garde la première séance de mai. L'article raisonne en rendements mensuels, de clôture d'octobre à clôture d'avril : l'écart est d'une séance à chaque bascule. Le protocole annonçait un écart d'une nuit ; la précision a été postée sur #24069 avant le premier backtest. Les références se remplissent de la même façon ;
- la moitié de l'année est placée en BIL. Avec le taux sans risque nul des tests, ce rendement compte dans le Sharpe, comme il compte dans la comparaison de l'annexe A. Le Sharpe QC, qui retranche le taux sans risque de son modèle, est publié à titre d'information ;
- une bascule coûte deux ordres ;
- le levier maximal autorisé vaut 4 sur chaque ligne (code corrigé, voir l'écart ci-dessous). Les cibles restent à 100 % de la valeur du portefeuille : l'exposition ne dépasse pas 100 %.

Le projet est neuf : il n'a pas de code antérieur à reproduire, donc pas de contrôle d'innocuité. Un contrôle de propriété le remplace. Les ordres de `strategy` et `inverse` ne doivent tomber qu'à la première séance de novembre, à celle de mai et à la première séance de la fenêtre.

Les fenêtres sont coupées au 1er janvier 2025 :

- fenêtre 1, 2016-01-01 → 2024-12-31 ;
- fenêtre 2, 2025-01-01 → 2026-07-01. Elle ne contient qu'un semestre de chaque régime : sa puissance est très faible.

Les tests passent par `Paradox46Benchmarks/significance.py`, avec un taux sans risque nul :

- écart de Sharpe de Ledoit-Wolf ;
- bootstrap stationnaire ;
- écart de moyennes de Newey-West.

Sur chaque fenêtre, la correction de Holm porte sur les six p-valeurs du verdict. Le diagnostic est une exécution séparée, avec sa propre correction de Holm sur trois p-valeurs.

Règle de verdict, écrite avant la mesure :

- `BEATS` : écart de Sharpe positif et significatif (Holm < 0,05, Ledoit-Wolf) contre les deux références ;
- `NO BEATS` : Sharpe de la stratégie inférieur à celui de SPY détenu ;
- `INCONCLUSIVE` : tous les autres cas.

**Contrôle de propriété : tenu, sur les deux codes.** Sur les deux fenêtres, aucun ordre de `strategy` ni d'`inverse` ne tombe hors des dates permises, et chaque date permise porte un ordre.

**Écart au protocole : des rachats refusés dans le code gelé.** Le compteur `invalid_orders` du code gelé signale des achats refusés par Lean, avec le motif `Insufficient buying power` :

- `strategy`, fenêtre 1 : 4 rachats de BIL refusés, en mai 2019, 2020, 2021 et 2024 ;
- `inverse`, fenêtre 1 : 2 rachats de BIL refusés, en novembre 2016 et 2022 ;
- fenêtre 2 et références : aucun refus.

Une bascule envoie deux ordres remplis à la même clôture : la vente de la ligne détenue et l'achat de la nouvelle. Le contrôle de marge de l'achat ne déduit pas la vente encore en attente. Avec le levier de 2 du modèle de courtage, acheter 100 % de BIL en détenant encore 100 % de SPY tombe à la limite de la marge, d'un côté ou de l'autre selon la séance. Après un refus, le portefeuille reste en liquidités jusqu'à la bascule suivante : la stratégie a détenu des liquidités au lieu de BIL pendant quatre semestres d'été, et `inverse` pendant deux semestres d'hiver.

Le code corrigé porte le levier maximal autorisé à 4 sur chaque ligne, dans les quatre modes. Les cibles restent à 100 % de la valeur du portefeuille : l'exposition ne change pas. Avec ce code, tous les ordres de `strategy` et d'`inverse` sont remplis. L'écart a été posté sur #24069 avant la lecture des résultats corrigés. Le verdict pré-enregistré est celui du code gelé ; le verdict du code corrigé est rapporté à côté, sans le remplacer.

**Effet de bord sur le 60/40.** Le contrôle annoncé sur #24069 demandait aux deux références de rendre la même série de valeur avec les deux codes. Il tient pour SPY détenu : la série est identique. Il ne tient pas à l'identique pour le 60/40, parce que le code corrigé saute de petits ordres de rééquilibrage :

- fenêtre 1 : 38 ordres du code gelé n'ont pas de pendant à la même date dans le code corrigé, et 2 ordres n'existent que dans le code corrigé ;
- fenêtre 2 : 9 et 3 ;
- sur la fenêtre 1, le code gelé passe des ordres dès 0,17 % de la valeur du portefeuille. Le code corrigé n'en passe qu'un sous 0,37 %, à 0,22 %.

Explication probable, non vérifiée dans le source de Lean : Lean écarte un ordre dont la marge est sous un seuil fixé en part de la valeur du portefeuille. Passer le levier de 2 à 4 divise par deux la marge d'un ordre, et double donc sa taille minimale en valeur. L'effet sur la mesure est faible. L'écart maximal entre les deux séries de valeur du 60/40 est de 0,063 % sur la fenêtre 1 et de 0,031 % sur la fenêtre 2. Le Sharpe du 60/40 passe de 0,868 à 0,867 sur la fenêtre 1, et de 1,224 à 1,223 sur la fenêtre 2.

| Fenêtre | Code | Séances | Sharpe stratégie (taux nul) | SPY détenu (taux nul) | 60/40 (taux nul) | p Holm (Ledoit-Wolf, SPY / 60/40) | Verdict |
|---|---|---|---|---|---|---|---|
| 1, 2016-01-04 → 2024-12-31 | gelé (pré-enregistré) | 2264 | 0,619 | 0,856 | 0,868 | 1,0 / 1,0 | **NO BEATS** |
| 1, 2016-01-04 → 2024-12-31 | corrigé | 2264 | 0,645 | 0,856 | 0,867 | 1,0 / 1,0 | **NO BEATS** |
| 2, 2025-01-02 → 2026-07-01 | gelé (pré-enregistré) | 374 | 0,259 | 1,080 | 1,224 | 0,126 / 0,107 | **NO BEATS** |
| 2, 2025-01-02 → 2026-07-01 | corrigé | 374 | 0,259 | 1,080 | 1,223 | 0,126 / 0,106 | **NO BEATS** |

Statistiques QC (calculées par QC avec son propre taux sans risque). Leurs Sharpe ne se comparent pas à ceux de la table du dessus : QC retranche un taux sans risque non nul et part de ses propres séries quotidiennes, alors que le protocole prend un taux nul sur la valeur du portefeuille à l'ouverture. Le verdict se lit sur la table du dessus. La colonne « Ordres » reprend le compte de QC ; les ordres refusés sont comptés à part.

| Fenêtre | Code | Mode | Sharpe QC (taux de QC, autre échelle) | CAGR | Pire baisse | Ordres | Ordres refusés | Backtest |
|---|---|---|---|---|---|---|---|---|
| 1 | gelé | stratégie | 0,331 | 8,09 % | 33,9 % | 33 | 4 | `2f15b10e48390ea579e43a11bd6aaa4e` |
| 1 | gelé | SPY détenu | 0,588 | 14,53 % | 33,7 % | 2 | 0 | `61d0f6bbb546b957ffa09ed96fd50b69` |
| 1 | gelé | 60/40 | 0,487 | 9,35 % | 21,7 % | 181 | 0 | `820dd7d6e1e3ad514c8e42ac79d5e673` |
| 1 | gelé | inverse | 0,327 | 7,03 % | 16,7 % | 35 | 2 | `dc5ecf2ed191f3aad44c159261172d8a` |
| 1 | corrigé | stratégie | 0,354 | 8,49 % | 33,9 % | 37 | 0 | `0fce733257d00e1384533ec8d9b891b9` |
| 1 | corrigé | SPY détenu | 0,588 | 14,53 % | 33,7 % | 2 | 0 | `7e217a255a4c416bf0771a9eaa505784` |
| 1 | corrigé | 60/40 | 0,487 | 9,35 % | 21,7 % | 145 | 0 | `0a608d515493fa3f794fad055bf8b340` |
| 1 | corrigé | inverse | 0,347 | 7,29 % | 16,7 % | 37 | 0 | `8957dc6130f6157d2315615d82faf07b` |
| 2 | gelé | stratégie | −0,102 | 2,88 % | 18,6 % | 7 | 0 | `95ff4046b965cf733bc906e0cf303dd3` |
| 2 | gelé | SPY détenu | 0,665 | 18,96 % | 18,7 % | 2 | 0 | `67c83b4a077e6f974cb109ce3dcca0b0` |
| 2 | gelé | 60/40 | 0,590 | 13,37 % | 11,2 % | 30 | 0 | `6bb2db3d6114638ae9ee35d62e952df6` |
| 2 | gelé | inverse | 1,405 | 20,21 % | 4,5 % | 7 | 0 | `2186e0a5c0890ba13dadd1a1289c0591` |
| 2 | corrigé | stratégie | −0,102 | 2,88 % | 18,6 % | 7 | 0 | `7cf95f0d31289eacfaa40aafa0443fa3` |
| 2 | corrigé | SPY détenu | 0,665 | 18,96 % | 18,7 % | 2 | 0 | `d021e4ecb94671d35468fcfd1437b024` |
| 2 | corrigé | 60/40 | 0,590 | 13,38 % | 11,2 % | 24 | 0 | `c387fca96b73a92e71f997794ba87d0f` |
| 2 | corrigé | inverse | 1,405 | 20,21 % | 4,5 % | 7 | 0 | `26ce00c3a44bd994a34ba2655c3d4657` |

Le backtest de la fenêtre 2 va jusqu'à sa date codée : sa dernière séance est le 2026-07-01, et la coupure d'environ 90 jours que les nœuds QC utilisés appliquent à la fin des backtests ne l'a pas atteint. Sur ses 374 séances, la fenêtre a peu de puissance.

**Lecture.** Sur les deux fenêtres et avec les deux codes, la stratégie a un Sharpe ponctuel inférieur à celui de SPY détenu et à celui du 60/40 : `NO BEATS`. Sur la fenêtre 1, l'écart n'est pas significatif (p de Holm 1,0). Sur la fenêtre 2, les p brutes de Ledoit-Wolf passent sous 0,05 (0,031 contre SPY, 0,021 contre le 60/40), mais pas les p de Holm : l'écart n'est pas significatif. Comme dans le tableau A de l'article, la stratégie a un écart-type annuel plus bas que SPY détenu sur la fenêtre 1 (14,35 % contre 17,81 % avec le code gelé). Mais son rendement baisse plus que son risque : son CAGR QC est de 8,09 %, contre 14,53 % pour SPY détenu, alors que l'article trouvait un rendement moyen proche de celui du Buy and Hold.

**Diagnostic : l'asymétrie saisonnière n'apparaît pas sur ces fenêtres.**

| Fenêtre | Code | Sharpe de `inverse` (taux nul) | Écart stratégie − `inverse` | Intervalle bootstrap 95 % | p Holm (Ledoit-Wolf) | Corrélation | Lecture |
|---|---|---|---|---|---|---|---|
| 1 | gelé | 0,695 | −0,077 | −1,03 à +0,89 | 1,0 | −0,00 | rien de mesurable |
| 1 | corrigé | 0,719 | −0,074 | −1,03 à +0,90 | 1,0 | −0,00 | rien de mesurable |
| 2 | gelé | 2,300 | −2,041 | −3,77 à −0,13 | 0,098 | −0,00 | rien de mesurable |
| 2 | corrigé | 2,300 | −2,041 | −3,77 à −0,13 | 0,098 | −0,00 | rien de mesurable |

Sur les deux fenêtres, `inverse`, qui détient SPY de mai à octobre, a un Sharpe ponctuel plus élevé que la stratégie : le signe est l'inverse de celui de l'article. Aucun écart n'est significatif. Sur la fenêtre 2, l'intervalle bootstrap exclut zéro, mais la p de Holm (0,098) reste au-dessus du seuil. Ces fenêtres ne tranchent donc ni pour ni contre l'asymétrie. La corrélation est proche de zéro, ce qu'on attend : chaque portefeuille détient BIL pendant que l'autre détient SPY.

**Prédictions écrites avant la mesure :**

- contrôle de propriété tenu : juste ;
- fenêtre 1, pas `BEATS` : juste, `NO BEATS` avec les deux codes ;
- écart-type annuel de la stratégie inférieur à celui de SPY détenu sur la fenêtre 1 : juste (14,35 % avec le code gelé, 14,34 % avec le code corrigé, contre 17,81 %) ;
- diagnostic `inverse` sur la fenêtre 1, Sharpe de la stratégie supérieur à celui d'`inverse` : faux. Il est inférieur (0,619 contre 0,695 avec le code gelé, 0,645 contre 0,719 avec le code corrigé). L'écart n'est pas significatif, comme prévu ;
- fenêtre 2 : pas de prédiction.

## Files

- main.py — la règle de l'annexe A, avec le paramètre `mode` et la trace `shadow` de la mesure #24069

## References

- Bouman, S. et Jacobsen, B. (2002), *The Halloween Indicator, "Sell in May and Go Away": Another Puzzle*, American Economic Review 92(5) ; version de travail de juillet 2001 lue
- Issue #24069 (protocole pré-enregistré), EPIC #19821 (ligue de stratégies), #22828 (protocole modèle), #18923 (trace `shadow`)
