# M13 Markov-Switching HAR -- Hamilton 2-Regime on RV Process

**Status:** NO BEATS (Cycle 32) -- 39/84 (46.4%, p=0.7774)

## Verdict

M13 MS-HAR **fails to beat HAR Classic** Kelly. Win rate 46.4% (below 50% random), p=0.7774 (far from significance). Median delta-Sharpe -0.0157. MSE catastrophically worse (+994.6% median).

**Recommendation**: Do not adopt regime-switching HAR for crypto volatility forecasting. The EM estimation cost (11 params) outweighs any regime signal on rolling windows of 200-400 obs.

## Results Summary (Cycle 32, 2026-05-13)

| Metric | Value |
|--------|-------|
| Verdict | NO BEATS |
| Sign-test p-value | 0.7774 |
| Win rate (MS-HAR > HAR) | 39/84 (46.4%) |
| Median delta-Sharpe | -0.0157 |
| Median MSE change | +994.6% |
| Combos | 84 (7 coins x 3 horizons x 4 seeds) |
| Runtime | 3785s |

### Per-Coin Summary

| Coin | Win% | Med delta-Sharpe | Med MSE change |
|------|------|-------------------|----------------|
| BTC-USD | 0/12 (0%) | -0.1468 | +722.9% |
| ETH-USD | 0/12 (0%) | -0.4245 | +57133.0% |
| SOL-USD | 8/12 (66.7%) | +0.0974 | +300.0% |
| LTC-USD | 0/12 (0%) | -0.0783 | +559.0% |
| XRP-USD | 12/12 (100%) | +0.4920 | +1026.7% |
| ADA-USD | 11/12 (91.7%) | +0.4926 | +3580.7% |
| DOT-USD | 8/12 (66.7%) | +0.7658 | +3703.6% |

Major coins (BTC, ETH, LTC) show zero wins. Only mid-cap altcoins (XRP, ADA, DOT, SOL) show wins, but MSE is catastrophically worse across all coins.

### Per-Horizon Summary

| Horizon | Win% | Med delta-Sharpe |
|---------|------|-------------------|
| h=1 | 9/28 (32.1%) | -0.0227 |
| h=5 | 16/28 (57.1%) | +0.1941 |
| h=10 | 14/28 (50.0%) | -0.0041 |

h=5 is the only horizon above 50%, driven by XRP/ADA/DOT wins. h=1 is strongly negative (32.1%).

## Model

Markov-Switching HAR (Hamilton 1989 + Corsi 2009):
```
Regime s_t in {0, 1} (0=calm, 1=turbulent)
Transition: P(s_t = j | s_{t-1} = i) = p_ij

In regime k:
    log(RV_{t+1}) = b0_k + b_d_k * log(RV_d) + b_w_k * log(RV_w) + b_m_k * log(RV_m) + e

Forecast = E[log(RV_{t+1})] = sum_k pi_k * forecast_k
```
where pi_k = steady-state regime probabilities.

Implementation: `statsmodels.tsa.regime_switching.markov_regression.MarkovRegression`
- `switching_variance=False` (shared sigma2, 11 params) for numerical stability
- `switching_trend=True, switching_exog=True` (all coefficients regime-dependent)
- Walk-forward 5-fold, refit every 22 days
- Kelly cap=1.0, fee=50bps, mu_window=60d

## Setup

- 7 coins: BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD
- 3 horizons: h=1, 5, 10
- 4 seeds: 0, 1, 7, 42
- Total: 84 combos
- Comparison: MS-HAR Kelly vs HAR Classic Kelly (sign-test on paired Sharpe)
- Data: yfinance hourly (2024-05-14 to 2026-05-13)

## Key Technical Finding: switching_variance

- `switching_variance=True` (12 params, regime-specific sigma2): produces pathological solutions with near-zero sigma2 in one regime (e.g., sigma2_0 = 3.2e-28 for BTC). Makes the model effectively single-regime.
- `switching_variance=False` (11 params, shared sigma2): produces non-degenerate, stable solutions with reasonable sigma2 (0.47-0.81). BUT the resulting forecasts are still worse than plain HAR for major coins.

## Why MS-HAR Fails

1. **Estimation cost outweighs regime benefit**: Fitting 11 parameters (2 intercepts, 6 betas, 2 transition probs, 1 sigma2) on rolling windows of ~200-400 daily obs introduces more noise than the regime signal provides.

2. **Steady-state forecast averaging**: The walk-forward forecast uses steady-state regime probabilities (pi_0, pi_1), which averages away the regime-specific signal. Using filtered/real-time probabilities would be better but requires a different implementation.

3. **EM instability**: Many EM restarts fail to converge (ConvergenceWarning), and the surviving solutions vary across restarts. This inconsistency propagates into unreliable forecasts.

4. **MSE blowup**: Median MSE +994.6% vs HAR. Regime-switching adds massive forecast variance, particularly for ETH (+57133%).

5. **Coin-dependent**: BTC/ETH/LTC (high liquidity) show zero benefit. XRP/ADA/DOT (mid-cap) show Sharpe improvements but catastrophically worse MSE -- the improvement is likely from Kelly position sizing on noisier forecasts, not better volatility prediction.

## Caveats (G.2 Honesty)

1. **search_reps=100 only**: Reduced from [50,100,150] for sweep feasibility. Some combos may find different solutions with more restarts, but the BTC/ETH/LTC zero-win pattern is robust across all 4 seeds.

2. **Shared sigma2 limitation**: Using shared variance across regimes constrains the model's ability to capture calm/turbulent distinction. However, regime-specific variance leads to pathological solutions.

3. **Steady-state vs filtered probabilities**: Using real-time filtered probabilities could improve performance for mid-cap coins, but unlikely to reverse the BTC/ETH zero-win pattern.

4. **XRP/ADA/DOT wins are suspect**: These coins show Sharpe improvements with catastrophically worse MSE (+1000-3700%). The Kelly framework amplifies noise into position sizing "edge" that is unlikely to survive out-of-sample.

## Comparison with Prior Models

| Model | Params | BEATS | Key finding |
|-------|--------|-------|-------------|
| M11 HAR Kelly (cap=1.0) | 4 | BEATS BH @50bps | Sharpe +0.313 vs buy-hold |
| M12 HAR-RV-J | 7 | BEATS (p=7.9e-7) | Jump-augmented RV |
| M11j Multi-Asset Kelly | ~10 | 0/36 vs single BTC | NO BEATS (delta=-1.05) |
| M13 MS-HAR | 11 | 39/84 (46.4%, p=0.7774) | NO BEATS, MSE +995% |

Regime-switching adds complexity but degrades forecast quality relative to single-regime HAR.

## Files

- `scripts/m13_ms_har.py`: Main sweep script
- `results/m13_ms_har/results.json`: Full results (84 combos)
- `results/m13_ms_har/m13_results.csv`: CSV export

## Reference

Hamilton, J.D. (1989) "A New Approach to the Economic Analysis of Nonstationary Time Series and the Business Cycle", Econometrica, 57(2), 357-384.
Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility", Journal of Financial Econometrics, 7(2), 174-196.



## Revalidation cluster appariée par origine (2026-10-04)

Le protocole #18190 (appariement par origine, porté depuis M4/#18650 puis M15/#18664) a été
appliqué au run cluster 7 actifs x 3 horizons x 4 seeds (84 combos, `mse`). Les jambes DM joignent
les deux walk-forwards sur leurs dates d'origine communes et **refusent** sur mismatch de cible
partagée — jamais de troncature positionnelle.

### Ce que le port change sur M13

Contrairement à M15 — où le garde a refusé deux fois avant toute mesure valide et a mis au jour un
défaut de convention réel — M13 produit ses deux jambes depuis la **même série `rv`** sur le
**même découpage** : l'appariement y est attendu **l'identité**, et le garde est ici la **preuve**
que la comparaison porte bien sur les mêmes jours, pas un correctif.

Ce que le port ajoute est ailleurs, et il porte sur le **verdict publié** :

1. **Le verdict publié est un sign-test binomial** (`_binomial_pvalue_one_sided` ; l'original
   n'importe ni DM ni `bias_metrics`, vérifié à la source) sur **84 combos traités comme
   indépendants** (`NO BEATS`, 39/84, p=0,7774), et il porte sur le **Sharpe** — pas sur le MSE.
   Deux réserves distinctes : (a) quatre graines d'un EM déterministe sur la même fenêtre ne sont
   pas quatre réplications indépendantes (même constat que la ligne REGISTRY M17 : « les 4 graines
   OLS sont bit-identiques, pas des réplications indépendantes »), donc le dénominateur 84
   sur-déclare la puissance ; (b) aucune jambe DM, aucune jambe dé-biaisée, aucun rapport de biais
   par modèle. Le port **ajoute** donc une lecture §C sur le **MSE** ; il ne réfute pas le verdict
   Sharpe publié, qui porte sur une autre métrique.
2. **La cible de la jambe HAR servait aux DEUX prévisions** — `target = har_out["targets"]...`
   puis `ms_pred = ms_fc.reindex(target.index)` (`origin/main` lignes 441-443, vérifié) : toute
   divergence entre les cibles réalisées des deux jambes était silencieusement ignorée. Le port
   donne à chaque jambe **sa propre cible** et fait refuser le join si les deux divergent
   (`target_tol=1e-8`). Le défaut était **latent** — les deux jambes partageant la même série `rv`
   et le même découpage, les cibles coïncident — et le garde le **prouve** au lieu de le supposer.

### Diagnostic d'alignement

Le garde shared-target a refusé **0** fois sur les 21 agrégats coin x horizon ; gap max sur les cibles partagées **0,0** ; longueurs appariées 538–1890. L'appariement est donc l'identité, mesurée et non supposée.

### Verdicts cluster (jambe brute / jambe dé-biaisée)

Agrégé par horizon (7 actifs chacun), et par cellule (21 couples coin x horizon) :

| Horizon | edge MSE moyen | edge MSE hors biais | dm_p_median | verdicts par actif (brut) | verdicts par actif (dé-biaisé) |
|---|---|---|---|---|---|
| h=1 | -803,9 % | -812,3 % | 0,0000 | NO BEATS 7/7 | NO BEATS 7/7 |
| h=5 | -15388,6 % | -16090,6 % | 0,0000 | NO BEATS 7/7 | NO BEATS 7/7 |
| h=10 | -304566,5 % | -325016,7 % | 0,0000 | NO BEATS 6/7 ; INCONCLUSIVE 1/7 | NO BEATS 6/7 ; INCONCLUSIVE 1/7 |

Par cellule : **BEATS** 0/21 ; **NO BEATS** 20/21 ; **refuted-de-biased** 0/21 ; **INCONCLUSIVE** 1/21.

Manifeste compact committé : `scripts/results/m13_ms_har_cluster_aligned.json` (politique #15890, 13819 octets). Artefact complet (hors dépôt) : `m13_ms_har_cluster_full.json`, 152346 octets, sha256 `e78561eb06a7…` ; runtime mesuré 1795 s. Le champ `elapsed_s` mesure le groupe le plus long, pas la somme des trois groupes parallèles.
