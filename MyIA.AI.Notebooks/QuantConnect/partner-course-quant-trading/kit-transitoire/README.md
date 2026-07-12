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
