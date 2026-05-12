# M11f Transaction cost sensitivity — kelly_har_mu60 edge survives to ~50 bps, dies at 100 bps

**Date** : 2026-05-12 (Cycle 28 prep)
**Author** : ai-01 BG ML track
**Wallclock** : 100.1s (CPU, ai-01)
**Script** : `scripts/m11f_tx_cost_sweep.py`
**Coins** : BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD (7 coins × 5 horizons = 35 combos)
**Strategy** : `kelly_har_mu60` (only — M11a/b/c dominant)
**Fees swept** : 5, 10, 20, 50, 100 bps

## Question

> À quel coût de transaction l'edge de `kelly_har_mu60` vs `buy_hold` (sign-test p≈0.001 à 10 bps M11c) disparaît-il ?

**Réponse** : edge population SURVIVE jusqu'à ~50 bps (sign-test p=0.045) puis DISPARAÎT à 100 bps (sign-test p=0.155). Aucun combo individuel à p<0.05 même à 5 bps.

## Méthodologie

- HAR forecasts deterministic (OLS) → calculés une fois par (coin, horizon), réutilisés
- Pour chaque fee level : recalcul Kelly fraction + position sizing + net return avec `fee_bps/1e4 * |Δw|`
- Per-combo Ledoit-Wolf 2008 paired Sharpe-diff p-value (Newey-West q=floor(T^¼))
- Sign-test binomial sur (Δ Sharpe > 0) — null = ½

## Fee-sensitivity curve

| fee_bps | BEATS_Δ>0 | BEATS p<0.10 | BEATS p<0.05 | Median Δ Sharpe | Sign-test p |
|---------|-----------|--------------|--------------|-----------------|-------------|
| **5** | 29/35 | 6/35 | 0/35 | +0.313 | **0.0001** |
| **10** | 27/35 | 5/35 | 0/35 | +0.299 | **0.0009** |
| **20** | 26/35 | 4/35 | 0/35 | +0.270 | **0.0030** |
| **50** | 23/35 | 2/35 | 0/35 | +0.186 | **0.0448** |
| **100** | 21/35 | 0/35 | 0/35 | +0.044 | 0.1553 |

**Break-even** :
- BEATS_p005 = 0 dès **5 bps** (signal per-combo trop faible vs SE même à coût minimal)
- Sign-test p>0.05 entre 50 et 100 bps (edge population disparaît dans cette fourchette)
- Médiane Δ Sharpe passe de +0.31 (5 bps) à +0.044 (100 bps) — décroissance ~quasi-linéaire

## Lecture économique

### Coût "réaliste" pour le panel crypto

| Plateforme | Spot | Futures perp |
|-----------|------|--------------|
| Binance VIP-0 (taker) | 10 bps | 5 bps |
| Coinbase (taker) | 60 bps | n/a |
| Kraken (taker) | 26 bps | 5 bps |
| FTX (legacy) | 7 bps | 5 bps |

→ Pour un trader retail crypto Binance/Kraken (10-26 bps), l'edge K60 vs BH SURVIT (sign-test p<0.005).
→ Pour un trader retail crypto Coinbase (60 bps), l'edge population est à la limite de signification (sign-test entre 50 et 100 bps).
→ Pour un trader retail USA forcé à des spreads plus larges (ex Robinhood crypto effective ~75 bps via spread markup), l'edge disparaît avant le statistical significance.

### À comparer aux equity baselines

- SPY ETF retail moderne : 1-3 bps round-trip via IBKR/Schwab — l'edge survie largement.
- Alt-coins illiquides (DOT, ADA) : spreads effectifs souvent > 30 bps en retail → edge limite.

## Top combos par fee-robustness

| Combo | 5 bps Δ | 100 bps Δ | Δ-decay | Verdict |
|-------|---------|-----------|---------|---------|
| LTC h=20 | +1.06 | +0.83 | -22% | ROBUSTE |
| ADA h=20 | +1.43 | +1.21 | -15% | ROBUSTE |
| BTC h=15 | +0.49 | +0.21 | -57% | sensible |
| BTC h=20 | +0.47 | +0.20 | -57% | sensible |
| SOL h=15 | +0.78 | +0.55 | -29% | ROBUSTE |
| XRP h=20 | +0.74 | +0.55 | -26% | ROBUSTE |
| DOT h=20 | +0.87 | +0.75 | -13% | TRÈS ROBUSTE |

→ Les longs horizons (h=20) sont systématiquement plus robustes au coût (turnover plus faible). Les courts horizons (h=1-5) sur BTC/ETH sont plus sensibles (turnover élevé pour Kelly fraction réactive).

## Conclusion ESGF / pédagogique

- **Edge K60 vs BH économiquement viable jusqu'à ~50 bps** au niveau population (sign-test p<0.05). Cohérent avec spread crypto Binance/Kraken (~10-25 bps).
- **Per-combo p<0.05 = 0/35 même à 5 bps** : confirme M11c — signal faible par combo individuel, fort en agrégat.
- **Long horizons (h=20) plus robustes** que courts horizons (h=1-5) au coût — turnover ↓ → fee-drag ↓.
- **Caveat** : à 100 bps (retail US/Robinhood/Coinbase taker), l'edge population perd sa significativité.

### Narrative honnête

> "HAR-RV + Kelly sizing avec mu rolling 60d a un edge AGGREGATE significatif (sign-test p≈0.001 à 10 bps, p=0.045 à 50 bps) sur un panel crypto 35-combo. Per-combo, aucun combo n'atteint p<0.05 même à 5 bps — c'est un effet de population, pas d'un coin/horizon spécifique. Au-delà de 50 bps de coût (taker retail US), l'edge population se dissout. C'est honnête, c'est mesuré, c'est une contribution. Pas de marketing transformer."

## How to apply

- **Pour kit ESGF** : afficher la fee-sensitivity curve. Ne pas vendre K60 comme "garanti à toute condition de coût".
- **Pour utilisation prod** : préférer h=20 (plus fee-robust) sur alt-coins downtrend (LTC, ADA, DOT).
- **Pour deeper research** : tester (a) fee-aware Kelly (ne trader que si |Δw| > seuil), (b) volatility-aware position sizing (réduire fraction quand vol forecast bouge peu) — pourrait pousser break-even au-delà de 100 bps.

## Fichiers

- Verdict (this) : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/M11f_TX_COST_SWEEP.md`
- Script : `scripts/m11f_tx_cost_sweep.py` (~250 lines, reuses `simulate_har_kelly` + LW2008 SE)
- Results : `results/m11f_tx_cost_sweep/results.{csv,json}` (35 combos × 5 fee levels = 175 rows)

## Cross-references

- M11a/b : K60 raw BEATS (`project_m11a_har_kelly_beats.md`)
- M11c : DM test rétroactif (`M11c_DM_SIGNIFICANCE.md`) — base pour méthodo LW2008 réutilisée
- M11d : HMM regime conditioning HURTS (`M11d_HMM_REGIME_KELLY.md`)
- M11e : ensemble equal-weight DILUE (`M11e_ENSEMBLE.md`)
