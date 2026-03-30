# Sector Dual Momentum Strategy (ID: 20216980)

Strategie de momentum sectoriel sur les constituants du SPY.

## Architecture
- `main.py` - Algorithme principal avec universe ETF SPY top 200
- `DualMomentumAlphaModel.py` - Alpha model momentum sectoriel
- `MyPcm.py` - Risk Parity Portfolio Construction avec leverage
- `CustomImmediateExecutionModel.py` - Execution avec leverage ajustable
- `FredRate.py` - Custom data: taux Fed Funds (FRED)
- `research.ipynb` - Analyse performances sectorielles

## Concepts enseignes
- Dual momentum (sector + individual)
- Universe selection dynamique
- Custom data (FRED)
- Risk Parity
