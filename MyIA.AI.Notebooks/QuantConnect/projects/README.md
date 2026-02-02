# QuantConnect Community Projects

Cette section contient des projets complets au format communautaire QuantConnect, prêts à être uploadés sur le forum ou partagés.

## Structure d'un Projet Communautaire

Chaque projet suit le format standard utilisé sur les blogs et forums QuantConnect :

```
MonProjet/
├── main.py              # Algorithme principal (obligatoire)
├── research.ipynb       # Notebook de recherche (recommandé)
├── alpha.py             # Alpha model (optionnel)
├── universe.py          # Universe selection (optionnel)
├── README.md            # Documentation projet
└── backtest_results/    # Résultats de backtest (optionnel)
```

## Projets Disponibles

| Projet | Description | Notebook Source | Difficulté |
|--------|-------------|-----------------|------------|
| [MomentumStrategy](MomentumStrategy/) | Sélection d'univers momentum 12 mois | QC-Py-05 | Intermédiaire |
| [OptionsIncome](OptionsIncome/) | Stratégies génération de revenus (Covered Call, Iron Condor) | QC-Py-06 | Avancé |
| [FuturesTrend](FuturesTrend/) | Trend following sur futures (Donchian breakout) | QC-Py-07 | Intermédiaire |
| [AllWeather](AllWeather/) | Portfolio multi-asset style Ray Dalio | QC-Py-08 | Débutant |

## Comment Utiliser

### 1. Sur QuantConnect Cloud

```bash
# 1. Créer un nouveau projet
File → New Project → Python

# 2. Copier le contenu de main.py

# 3. Uploader le notebook research.ipynb (optionnel)
File → Upload

# 4. Backtester
Cliquer sur "Backtest"
```

### 2. Avec LEAN CLI (Local)

```bash
# Créer un projet depuis le template
lean project-create --language python MonProjet

# Copier les fichiers
cp projects/MomentumStrategy/* MonProjet/

# Backtester
lean backtest MonProjet
```

## Contribuer

Pour ajouter un nouveau projet :

1. Créer un dossier dans `projects/`
2. Inclure au minimum `main.py` et `README.md`
3. Documenter les paramètres et performances attendues
4. Ajouter un notebook de recherche si applicable

## Ressources

- [QuantConnect Community](https://www.quantconnect.com/forum)
- [Algorithm Lab](https://www.quantconnect.com/terminal)
- [Documentation](https://www.quantconnect.com/docs)
