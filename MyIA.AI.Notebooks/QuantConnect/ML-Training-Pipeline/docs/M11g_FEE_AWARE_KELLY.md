# M11g Fee-aware Kelly — threshold band does NOT push break-even past 100 bps

**Date** : 2026-05-12 (Cycle 28)
**Author** : ai-01 BG ML track
**Wallclock** : 112.0s (CPU, ai-01)
**Script** : `scripts/m11g_fee_aware_kelly.py`
**Coins** : BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD (7 × 5 horizons = 35 combos)
**Strategy** : `kelly_har_mu60` with no-trade band: hold previous weight if `|w_t - w_{t-1}| < threshold`

## Question

> M11f a montré que l'edge K60 vs BH meurt entre 50 et 100 bps. Si l'on suppress
> les petits rebalances (no-trade band), peut-on pousser le break-even au-delà
> de 100 bps en réduisant la fee-drag ?

**Réponse** : **NON — null result**. Le seuil n'a aucun effet matériel sur la
fee-curve. Médiane Δ Sharpe inchangée à ±0.005 sur toute la grille fee × threshold.

## Méthodologie

- Sweep : `threshold ∈ {0.00, 0.025, 0.05, 0.10, 0.20}` × `fee_bps ∈ {10, 50, 100}`
- Pour chaque (coin, horizon) : calculer Kelly weights, appliquer la no-trade band,
  recalculer net daily returns avec `fee_bps × |Δw| post-band`, paired Sharpe-diff
  LW2008 vs `buy_hold`.
- Sign-test binomial 35-combo population.

## Grille BEATS aggregate

| threshold | 10 bps | 50 bps | 100 bps |
|-----------|--------|--------|---------|
| **0.000** (M11f baseline) | 27/35 p=0.001 med=+0.299 | 23/35 p=0.045 med=+0.186 | 21/35 p=0.155 med=+0.044 |
| **0.025** | 27/35 p=0.001 med=+0.299 | 23/35 p=0.045 med=+0.186 | 21/35 p=0.155 med=+0.044 |
| **0.050** | 27/35 p=0.001 med=+0.298 | 23/35 p=0.045 med=+0.185 | 21/35 p=0.155 med=+0.044 |
| **0.100** | 27/35 p=0.001 med=+0.295 | 23/35 p=0.045 med=+0.186 | 21/35 p=0.155 med=+0.044 |
| **0.200** | 27/35 p=0.001 med=+0.302 | 22/35 p=0.088 med=+0.190 | 21/35 p=0.155 med=+0.049 |

→ Sign-test p-values **identiques** à 3 décimales sur 4 des 5 niveaux de seuil.
Médiane Δ Sharpe varie de ±0.005 — bruit numérique. Break-even reste entre 50 et 100 bps.

## Diagnostic : pourquoi la band ne mord pas

Turnover ratio (post-band / raw) :

| threshold | mean ratio | min | max |
|-----------|-----------|-----|-----|
| 0.000 | 1.0000 | 1.0000 | 1.0000 |
| 0.025 | 0.9989 | 0.9945 | 1.0000 |
| 0.050 | 0.9962 | 0.9895 | 1.0000 |
| 0.100 | 0.9843 | 0.9594 | 0.9988 |
| **0.200** | **0.9441** | 0.8750 | 0.9923 |

À threshold = 0.20 (suppress trades de moins que 20% de la position cible), le turnover
ne baisse que de **5.6% en moyenne** sur 35 combos. Conséquence : pas de réduction
significative de la fee-drag, pas de shift du break-even.

**Cause structurelle** : la Kelly fraction `f = mu / sigma²` avec cap=1.0 est
quasi-**bang-bang**. La distribution empirique des weights K60 est bimodale, fortement
concentrée à `w=0` (mu négatif → Kelly clipped à 0) ou `w≈1.0` (mu positif large → Kelly
saturé à kelly_cap). Les "petits rebalances" entre 0 et 1.0 sont rares ; la plupart des
trades sont des sauts complets 0→1 ou 1→0, lesquels dépassent toujours threshold=0.20.

→ La no-trade band ne peut donc fonctionner que sur une **stratégie continue** (vol-target
non clippée, par exemple), pas sur Kelly capé.

## Conclusion ESGF / pédagogique

- **Hypothèse « fee-aware Kelly via no-trade band »** : REJETÉE pour `kelly_har_mu60`
  capé. La stratégie est trop bang-bang pour que le seuil capture des trades supprimables.
- **Break-even reste entre 50 et 100 bps** (M11f verdict inchangé).
- **Pistes non-explorées (futur cycle)** :
  - **Kelly non-capé** ou cap relaxé (kelly_cap=2.0 ou 3.0) — produirait plus de variation
    intermédiaire dans les weights, où le band pourrait mordre.
  - **Volatility-target sans Kelly** — distribution des weights plus diffuse, band utile.
  - **Fee-aware Kelly via Lagrangien** : minimiser `−Sharpe + λ × fee_drag` au lieu d'un
    seuil binaire post-hoc.
  - **Aggregation cross-asset** : combiner plusieurs Kelly bang-bang corrélés négativement
    pour lisser les sauts.

## Narrative honnête

> "L'hypothèse 'threshold no-trade band pousse le break-even au-delà de 100 bps' est
> testée empiriquement sur 35 combos × 5 seuils × 3 fees = 525 cellules. Verdict :
> aucun effet matériel (med Δ Sharpe ±0.005, sign-test identique). Raison structurelle :
> Kelly capé est bang-bang, peu de petits rebalances à supprimer. La piste fee-aware
> reste ouverte mais nécessiterait de relâcher le cap Kelly ou de passer à un objectif
> Lagrangien explicite — direction reportée à Cycle 29+."

## Fichiers

- Verdict (this) : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/M11g_FEE_AWARE_KELLY.md`
- Script : `scripts/m11g_fee_aware_kelly.py` (~250 lignes, réutilise LW2008 de m11c)
- Results : `results/m11g_fee_aware_kelly/results.{csv,json}` (525 rows)

## Cross-references

- [M11f_TX_COST_SWEEP.md](M11f_TX_COST_SWEEP.md) — fee-sweep baseline (break-even 50-100bps)
- [M11e_ENSEMBLE.md](M11e_ENSEMBLE.md) — ensemble equal-weight DILUTION
- [project_m11ef_ensemble_txcost.md](../../../C:/Users/MYIA/.claude/projects/d--CoursIA/memory/project_m11ef_ensemble_txcost.md) — mémoire M11e+f

## Pattern récurrent M11

| Tentative | Résultat |
|-----------|----------|
| M11a/b/c/c K60 raw | **BEATS** (p≈0.001 à 10bps) |
| M11d HMM regime conditioning | **HURTS** K60 |
| M11e ensemble equal-weight | **DILUTION** (sign-test ens-vs-K60 p=0.250) |
| M11f fee-curve | break-even 50-100 bps |
| M11g threshold band | **NULL** (no shift) |

→ K60 est un local optimum honnête. Toute variation simple le dégrade au mieux,
ne l'améliore jamais à p<0.05 aggregate.
