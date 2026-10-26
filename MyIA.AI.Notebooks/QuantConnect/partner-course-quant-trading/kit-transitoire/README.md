# Kit de Transition — Stratégies ML & Framework

Trois stratégies QuantConnect progressives pour la rotation sectorielle, validées sur backtests cloud (2015-2024).

## Objectif

Fournir 3 approches progressives de rotation sectorielle :

1. **ML RandomForest** (classification) — Introduction au ML appliqué
2. **ML XGBoost** (régression) — Modèle avancé avec plus de features
3. **Framework Composite** (alpha models) — Architecture QC Framework propre

Chaque stratégie inclut un notebook de recherche (QuantBook) documentant les itérations et le calibrage.

## Stratégies

### 01 — ML RandomForest Sector Rotation

| Paramètre | Valeur |
|-----------|-------|
| Univers | 9 ETF sectoriels (XLK..XLRE) |
| Features | 14 indicateurs techniques |
| Modèle | RandomForestClassifier |
| Arbres / Profondeur | 200 / 6 |
| Entraînement | Rolling 4 ans, ré-entraînement mensuel |
| Filtre baissier | SPY < SMA200 -> max 2 positions |
| Positions max | 4 (2 en marché baissier) |
| Allocation | 95 % |

**Backtest de référence** (étiquettes corrigées, graine 42) : Sharpe 0.387, CAGR 9.92 %, MaxDD 46.6 %. Sur les graines 0, 1, 7, 42 et 99 : Sharpe 0.334 à 0.453, CAGR 8.86 % à 11.52 %, MaxDD 46.5 % à 46.6 %.

`main.py` accepte deux paramètres optionnels :

| Paramètre | Défaut | Rôle |
|---|---|---|
| `label_mode` | `forward` | `forward` retire de l'entraînement les séances dont le rendement à 20 séances est inconnu ; `legacy` rétablit les anciennes étiquettes |
| `rf_seed` | `42` | graine de la forêt aléatoire |

#### Étiquettes des 20 dernières séances : mesure QC Cloud (#22429), 2026-10-25

Le modèle apprend à prédire si le rendement à 20 séances sera positif. Pour les 20 dernières séances de chaque fenêtre d'entraînement, ce rendement n'existe pas encore. Comme `NaN > 0` vaut `False`, l'ancien code les étiquetait « baisse ». Sur l'ensemble des ré-entraînements, cela touche 2,0 % des exemples d'entraînement (21 300 sur 1 054 312). Le code corrigé retire ces exemples avant l'entraînement, et la part de cibles « hausse » passe de 61,35 % à 62,62 %.

La règle de mesure a été inscrite dans #22429 avant le premier backtest. Dix runs, sur la même compilation et le même jour, couvrent la fenêtre du kit, du 2015-01-01 au 2024-12-31 : les deux modes d'étiquetage, chacun sous les graines 0, 1, 7, 42 et 99.

**Non-régression.** En mode `legacy`, graine 42, le run retrouve la pire baisse publiée, 17,2 %, mais pas le Sharpe ni le CAGR : 0,604 et 12,25 %, contre 0,556 et 11,43 % publiés. Le code de négociation de ce mode est celui d'avant le correctif. L'écart reste inexpliqué : QC réécrit ses prix ajustés d'une date de mesure à l'autre, ce qui pourrait suffire, mais rien ne le démontre ici.

| Graine | Sharpe `legacy` | Sharpe `forward` | CAGR `legacy` | CAGR `forward` | Pire baisse `legacy` | Pire baisse `forward` |
|---|---|---|---|---|---|---|
| 0 | 0,245 | 0,423 | 6,76 % | 10,73 % | 50,7 % | 46,5 % |
| 1 | 0,634 | 0,334 | 12,51 % | 8,86 % | 17,9 % | 46,5 % |
| 7 | 0,275 | 0,453 | 7,46 % | 11,52 % | 50,7 % | 46,5 % |
| 42 | 0,604 | 0,387 | 12,25 % | 9,92 % | 17,2 % | 46,6 % |
| 99 | 0,223 | 0,368 | 6,30 % | 9,50 % | 50,7 % | 46,5 % |

Le Sharpe est celui affiché par QC.

**Lecture.**
- Le signe de l'effet n'est pas établi. La différence de Sharpe `forward` − `legacy` est positive pour 3 graines sur 5, avec une médiane de +0,145. La règle demandait le même signe sur les 5 graines : l'effet est donc non mesurable à cette résolution.
- La graine pèse plus que le correctif. En mode `legacy`, l'écart-type du Sharpe entre graines vaut 0,204, au-dessus de cette médiane.
- La pire baisse de 17,2 % publiée jusqu'ici dépendait de la graine. En mode `legacy`, les graines 1 et 42 ont leur pire baisse fin 2018, autour de 17 %. Les trois autres perdent 50,7 % pendant le krach de février-mars 2020. En mode `forward`, les cinq graines perdent 46,5 % à 46,6 % pendant ce même krach, plus que SPY détenu sur la fenêtre (−33,7 %, section 03).
- Une observation hors de la règle, donnée à titre descriptif : en mode `forward`, l'écart-type du Sharpe entre graines tombe à 0,046. Avec les étiquettes corrigées, le résultat dépend beaucoup moins de la graine. Ce mode passe aussi plus d'ordres : 625 à 638, contre 556 à 569.

Les traces des runs (plans, empreintes, graphiques, statistiques) sont conservées hors dépôt, sous `QC-traces/22429-kit-rf-labels/`.

### 02 — ML XGBoost Sector Rotation

| Paramètre | Valeur |
|-----------|-------|
| Univers | 9 ETF sectoriels (XLK..XLRE) |
| Features | 20 indicateurs techniques |
| Modèle | GradientBoostingRegressor |
| Arbres / Profondeur / LR | 100 / 4 / 0.05 |
| Entraînement | Rolling 3 ans, entraînement bi-hebdomadaire |
| Filtre baissier | SPY < SMA200 -> max 2 positions |
| Positions max | 5 (2 en marché baissier) |
| Allocation | 95 % |

**Meilleur backtest** : Sharpe 0.521, CAGR 12.81 %, MaxDD 39.1 %

### 03 — Framework Composite

| Paramètre | Valeur |
|-----------|-------|
| Alpha 1 | SectorMomentum (SMA200 + momentum 126j) |
| Alpha 2 | Defensive (TLT, GLD, XLU quand SPY < SMA200) |
| PCM | MultiStrategyPCM (70 % momentum / 30 % defensive) |
| Risque | MaxDrawdownCircuitBreaker (15 %) |
| Exécution | ImmediateExecutionModel |

**Meilleur backtest** : Sharpe 0.376, CAGR 7.60 %, MaxDD 20.6 %, Win Rate 80 %

`main.py` accepte deux paramètres optionnels, sans effet par défaut :

| Paramètre | Défaut | Rôle |
|---|---|---|
| `pcm_mode` | `base` | `base` garde le comportement d'origine ; `intent` additionne les deux tranches sur `XLU` (voir ci-dessous) |
| `trace` | `0` | `1` trace chaque séance la valeur du portefeuille et la clôture de SPY dans un graphique `shadow` (séries entrelacées `e0`..`e4` et `b0`..`b4`, format de la ligue de stratégies #19821) ; aucun ordre ne change |

#### `XLU` dans les deux tranches : mesure QC Cloud (#20188), 2026-10-10

`XLU` appartient aux deux tranches : `SectorMomentum` (70 %) et `Defensive` (30 %). Le modèle de construction de base de Lean ne transmet à `determine_target_percent` qu'un insight actif par titre. Une tranche peut donc masquer l'autre sur `XLU`.

La mesure montre que le masquage joue toujours dans le même sens. Les deux modèles émettent au même instant, et l'insight transmis pour `XLU` est, à chaque appel, celui de `Defensive`. En mode `base`, `XLU` ne reçoit donc que la part défensive : 10 % du portefeuille quand SPY est sous sa SMA200, rien sinon. Le vote de `SectorMomentum` sur `XLU` n'est jamais appliqué, alors qu'il est UP dans 68 % des appels. Sa part ne reste pas en liquidités pour autant : les 70 % de la tranche se répartissent sur les autres secteurs retenus.

Le mode `intent` reprend le correctif additif de #19740 : il reconstruit le dernier insight actif par couple (titre, tranche), puis additionne les poids par titre. La cible moyenne de `XLU` passe de 1,8 % à 10,5 % du portefeuille.

La règle de mesure a été inscrite dans #20188 avant le premier backtest. Trois runs couvrent la fenêtre du kit, du 2015-01-01 au 2024-12-31 :
- `orig` : le `main.py` d'avant ces paramètres ;
- `base` et `intent` : le nouveau `main.py`, avec `trace=1`.

**Non-régression.** `base` reproduit `orig` à l'identique : les 27 statistiques QC, dont la rotation cumulée, et les 2149 ordres, comparés un à un. Le résultat du kit se retrouve : Sharpe QC 0.377, CAGR 7.59 %, MaxDD 20.6 %.

| Run | Sharpe | CAGR | Pire baisse | Ordres | Frais cumulés, en % du capital de départ |
|---|---|---|---|---|---|
| `base` | 0,72 | 7,6 % | −20,6 % | 2149 | 3,0 % |
| `intent` | 0,71 | 7,4 % | −21,9 % | 2320 | 3,3 % |
| SPY détenu (référence, sans frais) | 0,78 | 13,0 % | −33,7 % | — | — |

Le Sharpe de ce tableau est calculé sur les rendements journaliers, à taux sans risque nul, annualisé sur 252 séances. Le Sharpe affiché par QC (0.377 pour `base`, 0.366 pour `intent`) retranche un taux sans risque.

| `intent` − `base`, différence de Sharpe | Écart | IC 95 % | p unilatérale | 2015-2018 | 2019-2021 | 2022-2024 |
|---|---|---|---|---|---|---|
| toute la fenêtre | −0,01 | [−0,21 ; 0,19] | 0,51 | +0,16 | −0,34 | +0,04 |

Le test est un bootstrap circulaire par blocs de 21 séances (10 000 tirages, graine 18921), donné à titre descriptif.

**Lecture.** Le défaut existe bien : en mode `base`, `XLU` est presque absent du portefeuille alors que la tranche momentum le retient. Son effet sur le résultat, en revanche, n'est pas mesurable sur cette fenêtre. L'écart de Sharpe est nul à l'échelle de son intervalle, et son signe change d'une sous-période à l'autre. Le correctif ajoute des ordres et des frais. Le défaut reste `pcm_mode=base` ; changer le défaut du kit relève d'une issue du kit.

Les traces des runs (plans, empreintes, graphiques, ordres, statistiques, `results.json`) sont conservées hors dépôt, sous `QC-traces/20188-kit03-xlu-shared/`.

## Structure

```
kit-transitoire/
  README.md
  01-ML-RandomForest/
    main.py           # Stratégie QC Cloud
    research.ipynb    # Notebook de recherche QuantBook
  02-ML-XGBoost/
    main.py
    research.ipynb
  03-Framework-Composite/
    main.py
    research.ipynb
```

## Exécution

### Backtests QC Cloud

Chaque `main.py` tourne directement sur QuantConnect Cloud :

1. Créer un projet QC
2. Uploader `main.py`
3. Compiler et lancer le backtest (2015-01-01 à 2024-12-31)

### Notebooks de Recherche

Les notebooks `research.ipynb` utilisent `QuantBook` et nécessitent l'environnement QC Lab :

1. Ouvrir le projet dans QC Lab
2. Créer un notebook dans le projet
3. Copier le contenu de research.ipynb
4. Exécuter cellule par cellule

## Comparaison

| Aspect | RandomForest | XGBoost | Framework |
|--------|-------------|---------|-----------|
| Type | Classification | Régression | Alpha Models |
| Features | 14 | 20 | Indicateurs simples |
| Complexité | Moyenne | Moyenne | Haute (architecture) |
| Ré-entraînement | Mensuel | Bi-hebdomadaire | N/A (pas de ML) |
| Positions max | 4 (2 en baissier) | 4 (2 en baissier) | Dynamique |
| Apprentissage | Entraînement modèle | Entraînement modèle | Règles expertes |
| Sharpe | 0.387 | 0.521 | 0.376 |
| CAGR | 9.92 % | 12.81 % | 7.60 % |
| MaxDD | 46.6 % | 39.1 % | 20.6 % |

La colonne RandomForest reprend le backtest de référence (graine 42, mesure du 2026-10-25). Les deux autres colonnes reprennent les meilleurs backtests publiés pour ces stratégies.

---

**Version anglaise (snapshot pré-bascule)** : [README.en.md](README.en.md)
