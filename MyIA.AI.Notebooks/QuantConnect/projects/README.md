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

| Projet | Description | Cloud ID | Sharpe | Difficulte |
|--------|-------------|----------|--------|------------|
| [MomentumStrategy](MomentumStrategy/) | Rotation momentum 11 ETFs sectoriels | 28657837 | 0.216 | Intermediaire |
| [OptionsIncome](OptionsIncome/) | Covered Call SPY (premium income) | 28657838 | 0.288 | Avance |
| [FuturesTrend](FuturesTrend/) | Donchian breakout E-mini S&P 500 | 28657834 | 0.019 | Intermediaire |
| [AllWeather](AllWeather/) | Portfolio multi-asset Ray Dalio | 28657833 | 0.25 | Debutant |
| [FamaFrench](FamaFrench/) | Factor ETF rotation (Fama-French) | 28657910 | 0.365 | Intermediaire |
| [MeanReversion](MeanReversion/) | RSI mean reversion long-only | 28657904 | -0.042 | Intermediaire |
| [TurnOfMonth](TurnOfMonth/) | Anomalie calendaire (Turn of Month) | 28657905 | 0.127 | Debutant |
| [VIX-TermStructure](VIX-TermStructure/) | Contango/backwardation VIX | 28657907 | -0.97 | Avance |
| [ForexCarry](ForexCarry/) | FX momentum G7 currencies | 28657908 | -1.80 | Intermediaire |

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
