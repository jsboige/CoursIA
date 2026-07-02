# Alpha Correlation Analysis

**Type:** Research (analytical notebook, no trading algorithm)

## Objectif

Identifier les combinaisons d'alpha réellement complémentaires pour les stratégies composites QuantConnect.

## Problème

Les composites actuels combinent des alphas correles:
- TrendWeather (Sharpe 1.155) = TrendStocks + AllWeather, mais TrendStocks domine
- FamaFrench + AllWeather: sweep monotone vers AllWeather
- MomentumSector + RegimeSwitching: double-defense en période de stress

## Méthodologie

1. **Return Stream Collection**: Collecter les returns de chaque alpha
2. **Correlation Matrix**: Identifier les stratégies non-corrélées
3. **Regime Analysis**: Mapper la performance par regime (bull/bear/sideways, high/low vol)
4. **Complementarity Score**: Classer les paires par performance asymétrique
5. **Downside Protection**: Mesurer la protection en drawdown

## Résultats préliminaires

| Composite potentiel | Correlation | Sharpe combine | Synergie |
|---------------------|-------------|----------------|----------|
| EMA-Cross + All-Weather | ~0.3 | > 0.8 | Positive |
| Dual-Momentum + Mean-Reversion | ~0.1 | > 0.7 | Positive |
| Trend-Following + Mean-Reversion | ~0.0 | > 0.6 | Positive |

## Fichiers

- `quantbook.ipynb` - Analyse complete avec correlation, regime, complementarity scoring

## Prochaines etapes

1. **Composites QC**: Implementer les top pairs comme Algorithm Framework
2. **Dynamic Weighting**: Allocation basee sur le regime
3. **Risk Management**: Position sizing base sur correlation regime
4. **Validation**: Backtests complets sur paires recommandees

## Issue GitHub

[#140 - Complementary Alpha Combinations](https://github.com/jsboige/CoursIA/issues/140)
