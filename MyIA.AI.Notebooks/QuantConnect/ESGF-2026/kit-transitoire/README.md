# Kit Transitoire ESGF 2026 - Strategies ML & Framework

Trois strategies QuantConnect pour la soutenance ESGF (19/05/2026), validees sur backtest cloud 2015-2024.

## Objectif

Fournir 3 approaches progressives de rotation sectorielle :

1. **ML RandomForest** (classification) - Introduction au ML applique
2. **ML XGBoost** (regression) - Modele plus avance, plus de features
3. **Framework Composite** (alpha models) - Architecture QC Framework propre

Chaque strategie est accompagne d'un notebook de recherche (QuantBook) documentant les iterations et la calibration.

## Strategies

### 01 - ML RandomForest Sector Rotation

| Parametre | Valeur |
|-----------|--------|
| Universe | 9 sector ETFs (XLK..XLRE) |
| Features | 14 indicateurs techniques |
| Model | RandomForestClassifier |
| Trees / Depth | 200 / 6 |
| Training | 4 ans rolling, monthly retrain |
| Bear filter | SPY < SMA200 -> max 2 positions |
| Max positions | 4 (2 en bear) |
| Allocation | 95% |

**Resultat backtest v1** : Sharpe 0.544, CAGR 10.85%, MaxDD 16.3%
**Resultat backtest v2** : Sharpe 0.286, CAGR 6.73%, MaxDD 26.2% (threshold 0.65 trop eleve)
**Resultat backtest v3** : Sharpe 0.556, CAGR 11.43%, MaxDD 17.2% (alloc 95%) -- BEST

### 02 - ML XGBoost Sector Rotation

| Parametre | Valeur |
|-----------|--------|
| Universe | 9 sector ETFs (XLK..XLRE) |
| Features | 20 indicateurs techniques |
| Model | GradientBoostingRegressor |
| Trees / Depth / LR | 100 / 4 / 0.05 |
| Training | 3 ans rolling, bi-weekly train |
| Bear filter | SPY < SMA200 -> max 2 positions |
| Max positions | 5 (2 en bear) |
| Allocation | 95% |

**Resultat backtest v1** : Sharpe 0.521, CAGR 12.81%, MaxDD 39.1% -- BEST
**Resultat backtest v2** : Sharpe 0.442, CAGR 11.70%, MaxDD 37.9% (max_pos 4, alloc 95%, threshold 0.01 - pire)

### 03 - Framework Composite

| Parametre | Valeur |
|-----------|--------|
| Alpha 1 | SectorMomentum (SMA200 + 126j momentum) |
| Alpha 2 | Defensive (TLT, GLD, XLU quand SPY < SMA200) |
| PCM | MultiStrategyPCM (70% momentum / 30% defensive) |
| Risk | MaxDrawdownCircuitBreaker (15%) |
| Execution | ImmediateExecutionModel |

**Resultat backtest v1** : Sharpe 0.376, CAGR 7.60%, MaxDD 20.6%, 2157 orders, Win Rate 80%

## Structure

```
kit-transitoire/
├── README.md
├── 01-ML-RandomForest/
│   ├── main.py           # Strategie QC Cloud
│   └── research.ipynb    # Notebook de recherche QuantBook
├── 02-ML-XGBoost/
│   ├── main.py
│   └── research.ipynb
└── 03-Framework-Composite/
    ├── main.py
    └── research.ipynb
```

## Execution

### Backtests QC Cloud

Chaque `main.py` est executable directement sur QuantConnect Cloud :
1. Creer un projet QC
2. Uploader `main.py`
3. Compiler et lancer le backtest (2015-01-01 a 2024-12-31)

### Notebooks de recherche

Les notebooks `research.ipynb` utilisent `QuantBook` et necessitent l'environnement QC Lab :
1. Ouvrir le projet dans QC Lab
2. Creer un notebook dans le projet
3. Copier le contenu du research.ipynb
4. Executer cellule par cellule

## Comparaison des approaches

| Aspect | RandomForest | XGBoost | Framework |
|--------|-------------|---------|-----------|
| Type | Classification | Regression | Alpha Models |
| Features | 14 | 20 | Indicateurs simples |
| Complexite | Moyenne | Moyenne | Elevee (architecture) |
| Retrain | Monthly | Bi-weekly | N/A (sans ML) |
| Positions max | 4 (2 en bear) | 4 (2 en bear) | Dynamique |
| Apprentissage | Entrainement modele | Entrainement modele | Regles expertes |
| Sharpe | 0.556 (v3) | 0.521 (v1) | 0.376 (v1) |
| CAGR | 11.43% (v3) | 12.81% (v1) | 7.60% (v1) |
| MaxDD | 17.2% (v3) | 39.1% (v1) | 20.6% (v1) |

## Calibration pour la soutenance

Pour chaque strategie, le notebook de recherche documente :
- L'exploration des donnees sectorielles
- Le feature engineering et l'analyse d'importance
- 2 iterations de calibration avec metriques comparatives
- La correspondence research -> main.py
- Les pistes d'amelioration pour iteration N+1
