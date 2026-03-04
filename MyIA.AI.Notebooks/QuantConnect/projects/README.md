# QuantConnect Community Projects

Strategies de trading algorithmique backtestees sur QuantConnect Cloud, avec notebooks de recherche standalone (yfinance/pandas).

## Projets

| Projet | Description | Sharpe | CAGR | Max DD | Niveau |
|--------|-------------|--------|------|--------|--------|
| [SectorMomentum](SectorMomentum/) | Dual Momentum SPY/TLT/GLD (Antonacci) | **0.554** | 13.1% | 23.0% | Intermediaire |
| [FamaFrench](FamaFrench/) | Factor ETF rotation (VLUE/MTUM/SIZE/QUAL/USMV) | **0.471** | 11.7% | 33.7% | Intermediaire |
| [MomentumStrategy](MomentumStrategy/) | Rotation momentum 11 ETFs sectoriels | **0.411** | 10.8% | 30.1% | Intermediaire |
| [AllWeather](AllWeather/) | Portfolio multi-asset Dalio (SPY/TLT/IEF/GLD) | **0.365** | 7.2% | 24.1% | Debutant |
| [MeanReversion](MeanReversion/) | RSI multi-asset mean reversion | **0.294** | - | - | Intermediaire |
| [FuturesTrend](FuturesTrend/) | Donchian breakout ETFs (trend following) | **0.280** | - | - | Intermediaire |
| [OptionsIncome](OptionsIncome/) | Covered Call SPY + VIX filter | **0.747** | 17.3% | 8.3% | Avance |
| [TurnOfMonth](TurnOfMonth/) | Anomalie calendaire (Turn of Month) | 0.127 | - | - | Debutant |
| [VIX-TermStructure](VIX-TermStructure/) | Contango/backwardation VIX (SVXY) | -0.27 | - | - | Avance |
| [ForexCarry](ForexCarry/) | FX momentum G7 currencies | -0.654 | - | - | Intermediaire |

*Sharpe et metriques issus des backtests QC Cloud (2015-2025 sauf OptionsIncome: 2024 seulement, MINUTE resolution).*

## Structure d'un Projet

```
MonProjet/
├── main.py              # Algorithme (deploye sur QC Cloud)
├── research.ipynb       # Notebook standalone (yfinance, executable partout)
└── README.md            # Documentation (optionnel)
```

Chaque `research.ipynb` est **autonome** : il telecharge les donnees via yfinance et ne necessite ni QuantConnect ni Docker.

## Lecons Apprises

Patterns transversaux decouverts pendant l'optimisation :

- **TLT risk-off detruit la valeur** sur 2015-2025 (hausse des taux 2022). Alternatives: XLP+XLU, USMV, GLD, cash.
- **12m simple lookback >= composite** pour la plupart des strategies de rotation.
- **SMA overlay + low-vol** tue le Sharpe quand CAGR ~ risk-free rate.
- **VIX filter pour options** : ne vendre que quand VIX > 15.
- **ETFs > Futures** pour la simplicite (pas de rollover).

## Utilisation

### Sur QuantConnect Cloud

1. Creer un nouveau projet Python
2. Copier le contenu de `main.py`
3. Lancer le backtest

### En Local (research)

```bash
pip install yfinance pandas matplotlib
jupyter notebook projects/MomentumStrategy/research.ipynb
```

## Ressources

- [QuantConnect Community](https://www.quantconnect.com/forum)
- [Algorithm Lab](https://www.quantconnect.com/terminal)
- [Documentation](https://www.quantconnect.com/docs)
