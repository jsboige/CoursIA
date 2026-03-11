# Rapport de Nettoyage - Organisation Jean-Sylvain Boige (Researcher PAID)

**Date**: 2026-03-10
**Organisation**: Jean-Sylvain Boige (Researcher PAID)
**Obj**: Vérifier la correspondance local/cloud et identifier les doublons/temporaires

---

## Inventaire

### Projets locaux (27 + 2 C# = 29)

| Projet local | Projet cloud correspondant | Statut |
|--------------|---------------------------|--------|
| FamaFrench | FamaFrench-Researcher | ✓ |
| MeanReversion | MeanReversion-Researcher | ✓ |
| SectorMomentum | Sector-Momentum-Researcher | ✓ |
| AdaptiveAssetAllocation | AdaptiveAssetAllocation | ✓ |
| AllWeather | AllWeather-Researcher | ✓ |
| BTC-ML | BTC-ML-Researcher | ✓ |
| **Crypto-MultiCanal** | **Crypto-MultiCanal + Crypto-MultiCanal-Researcher** | ⚠️ **DOUBLON** |
| DualMomentum | DualMomentum | ✓ |
| DualMomentumNoTLT | DualMomentumNoTLT | ✓ |
| EMA-Cross-Crypto | EMA-Cross-Crypto | ✓ |
| EMA-Cross-Index | EMA-Cross-Index | ✓ |
| EMA-Cross-Stocks | EMA-Cross-Stocks | ✓ |
| ETF-Pairs | ETF-Pairs-Researcher | ✓ |
| ForexCarry | ForexCarry-Researcher | ✓ |
| FuturesTrend | FuturesTrend-Researcher | ✓ |
| MomentumStrategy | MomentumStrategy-Researcher | ✓ |
| Multi-Layer-EMA | Multi-Layer-EMA-Researcher | ✓ |
| Option-Wheel | Option-Wheel-Researcher | ✓ |
| Options-VGT | Options-VGT | ✓ |
| OptionsIncome | OptionsIncome-Researcher | ✓ |
| PairsTrading | PairsTrading | ✓ |
| RegimeSwitching | RegimeSwitching | ✓ |
| RiskParity | RiskParity | ✓ |
| Trend-Following | Trend-Following | ✓ |
| TrendStocksLite | TrendStocksLite | ✓ |
| TurnOfMonth | TurnOfMonth-Researcher | ✓ |
| VIX-TermStructure | VIX-TermStructure-Researcher | ✓ |
| Framework_Composite_TrendWeather | Framework_Composite_TrendWeather | ✓ |
| TrendFilteredMeanReversion | TrendFilteredMeanReversion | ✓ |
| **CSharp-BTC-EMA-Cross** | **N/A** | ➕ **À DÉPLOYER** |
| **CSharp-CTG-Momentum** | **N/A** | ➕ **À DÉPLOYER** |

---

## Doublons Identifiés

### ⚠️ Crypto-MultiCanal vs Crypto-MultiCanal-Researcher

| Critère | Crypto-MultiCanal | Crypto-MultiCanal-Researcher |
|---------|-------------------|------------------------------|
| Project ID | 28733256 | 28679473 |
| Modified | 1 day ago | 5 days ago |
| Fichiers | channel_helpers.py, main.py, research.ipynb | channel_helpers.py, **channel_mixin.py**, main.py, research.ipynb |

**Analyse**: La version "-Researcher" est **plus complète** (contient `channel_mixin.py` en plus).

**Recommandation**: Supprimer `Crypto-MultiCanal` (28733256), garder `Crypto-MultiCanal-Researcher` (28679473).

---

## Projets à Déployer (C#)

1. **CSharp-BTC-EMA-Cross** - Stratégie EMA Cross sur BTC en C#
2. **CSharp-CTG-Momentum** - Stratégie Momentum CTG en C#

---

## Nettoyage Recommandé

### À supprimer (1 projet):
- `Crypto-MultiCanal` (ID: 28733256) - Version incomplète du doublon

### À déployer (2 projets):
- `CSharp-BTC-EMA-Cross` (Main.cs)
- `CSharp-CTG-Momentum` (Main.cs)

---

## Statistiques

- **Projets locaux**: 29 (27 Python + 2 C#)
- **Projets cloud**: 33 (incluant 1 doublon)
- **Projets à supprimer**: 1
- **Projets à déployer**: 2
- **Projets correspondants**: 27/27 (100%)
