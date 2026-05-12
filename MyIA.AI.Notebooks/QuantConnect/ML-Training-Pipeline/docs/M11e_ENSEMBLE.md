# M11e Ensemble strategy — DILUTION confirmée, pas d'edge ajouté vs single best

**Date** : 2026-05-12 (Cycle 28 prep)
**Author** : ai-01 BG ML track
**Wallclock** : 111.9s (CPU, ai-01)
**Script** : `scripts/m11e_ensemble.py`
**Args** : `--horizons 1 5 10 15 20 --fee-bps 10`
**Coins** : BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD (7 coins × 5 horizons = 35 combos)
**Components** : `kelly_har_mu60` + `kelly_naive30_mu120` + `vol_target_har` (equal-weight arithmetic mean of daily position weights)

## Question

> Combiner les 3 stratégies actives top-rang de M11a/M11b en un ensemble equal-weight (mean of position weights) ajoute-t-il du Sharpe vs le single best (`kelly_har_mu60`) ?

**Réponse** : NON — **DILUTION confirmée**. Ensemble noyé dans K60 single (20/35 vs K60, sign-test p=0.250, 0/35 p<0.05).

## Méthodologie

- Pour chaque (coin, horizon, t) : `w_ens(t) = mean(w_K60(t), w_K30_mu120(t), w_VTH(t))`
- Net daily return : `r_ens(t) = w_ens(t) * r(t) - fee_bps/1e4 * |w_ens(t) - w_ens(t-1)|`
- Test : Ledoit-Wolf 2008 paired Sharpe-diff HAC SE (Newey-West q=floor(T^¼))
  - vs `buy_hold` : ensemble bat-il passive ?
  - vs `kelly_har_mu60` : ensemble ajoute-t-il qqch au single best ?
- Sign-test population sur compte (Δ Sharpe > 0) — null = ½

## Résultats agrégés

| Test | Δ>0 / N | Sign-test p | p<0.05 / N | Median Δ Sharpe |
|------|---------|-------------|------------|-----------------|
| Ensemble vs buy_hold | 21/35 | **0.155** (NOT sig) | 1/35 | +0.066 |
| Ensemble vs kelly_har_mu60 | 20/35 | **0.250** (NOT sig) | 0/35 | +0.023 |

**À comparer M11c K60 alone vs buy_hold** : 27/35 sign-test p≈0.001 (significant)

→ **L'ensemble dégrade le signal aggregate vs K60 alone**. Raison structurelle : `vol_target_har` et `kelly_naive30_mu120` ont des coverage rates ~50% chacun en M11a/b, donc averaging dilue les périodes où K60 prendrait full Kelly fraction.

## Top combos ensemble vs K60

Aucun combo ne franchit p<0.05. Top "positifs" :
- LTC-USD h=5 : Δ=+0.356 p=0.085 (le seul significatif p<0.10 pour ens vs K60)
- ADA-USD h=5 : Δ=+0.264 p=0.138
- SOL-USD h=1 : Δ=+0.263 p=0.188

Top "négatifs" (ensemble HURTS vs K60) :
- LTC-USD h=20 : Δ=-0.475 (K60 +1.325 Sharpe, ensemble +0.85) — alt-coin downtrend, K60 capture parfaitement, ens dilue
- LTC-USD h=15 : Δ=-0.348
- DOT-USD h=20 : Δ=-0.421
- ADA-USD h=20 : Δ=-0.152

## Pourquoi l'ensemble échoue

### 1. K60 est déjà optimal sur les coins-horizons où Kelly+HAR a un edge

M11a/b ont identifié K60 comme dominante (27/35 raw BEATS combiné). Les autres composantes (`kelly_naive30_mu120`, `vol_target_har`) sont systématiquement plus faibles ou égales. Equal-weight mean = pulling K60 vers des poids plus modérés = moins de fraction Kelly aux moments opportuns.

### 2. Pas d'effet diversification cross-strat

Les 3 stratégies prennent toutes des positions long-only via vol scaling. Leurs weights sont fortement corrélés (toutes baissent quand vol monte, toutes montent quand vol redescend). Ensemble ≠ portfolio diversifié — c'est juste une moyenne pondérée d'un signal common-mode.

### 3. Le label script "HELPS" est trompeur

Le script imprime `VERDICT: HELPS vs kelly_har_mu60 (ensemble adds value)` parce que median Δ > 0. Mais median = +0.023 (négligeable) et sign-test p=0.250 (rien de significatif). Ce label sera retiré en patch.

## Conclusion ESGF / pédagogique

- **Direction "ensemble simple HAR-Kelly" fermée** comme M11d (HMM regime conditioning fermée).
- **Cohérent avec littérature finance** : un ensemble naïf de stratégies corrélées dilue plutôt que diversifie. Pour gain réel : décorréler les composantes (ex : K60 sur vol crypto + momentum sur equity + carry sur FX) ou utiliser un meta-learner (stacking, OOS re-weighting).
- **Recommandation kit ESGF** : enseigner K60 single comme référence honnête. Ne pas vendre l'ensemble simple comme amélioration.

## Pourquoi M11e échoue là où M11a/b/c convainquent

- M11a (raw BEATS 14/21) + M11b (13/14) + M11c (sign-test p≈0.001) : **K60 single** porte le signal au niveau population (cf `project_m11a_har_kelly_beats.md`)
- M11d : conditionnement HMM HURTS K60 (anti-mémoire sur alt-coins)
- M11e : averaging avec composantes moins optimales DILUE K60

→ **Pattern** : K60 est un local optimum honnête. Tout ce qui s'en éloigne (HMM regime, ensemble equal-weight) le dégrade au mieux à p~0.25, jamais ne l'améliore à p<0.05.

## How to apply

- **Ne pas relancer** d'ensemble equal-weight sur ce panel.
- **Hypothèses ouvertes** (à tester si futur cycle ML) :
  - Stacking meta-learner OOS (logistic regression sur features de marché → weights dynamiques entre K60/K30/VTH)
  - Cross-asset ensemble (K60 crypto + autre stratégie equity/FX)
  - Regime-conditional ensemble (K60 en haut-vol, K30 en bas-vol — hypothèse spéculative)

## Fichiers

- Verdict (this) : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/M11e_ENSEMBLE.md`
- Script : `scripts/m11e_ensemble.py` (~280 lines, reuses `simulate_har_kelly` + LW2008 from `m11c_sharpe_test`)
- Results : `results/m11e_ensemble/results.{csv,json}` (35 combos × 1 strategy)

## Cross-references

- M11a/b : `project_m11a_har_kelly_beats.md` + `m11b_har_kelly_long_horizons/_verdict.md` (K60 27/35 raw BEATS)
- M11c : `M11c_DM_SIGNIFICANCE.md` (DM test rétroactif, sign-test p≈0.001)
- M11d : `M11d_HMM_REGIME_KELLY.md` (HMM HURTS K60)
- M11f : `M11f_TX_COST_SWEEP.md` (fee sensitivity K60)
