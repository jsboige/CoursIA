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

**Meilleur backtest** : Sharpe 0.556, CAGR 11.43 %, MaxDD 17.2 %

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
| Sharpe | 0.556 | 0.521 | 0.376 |
| CAGR | 11.43 % | 12.81 % | 7.60 % |
| MaxDD | 17.2 % | 39.1 % | 20.6 % |

---

**Version anglaise (snapshot pré-bascule)** : [README.en.md](README.en.md)
