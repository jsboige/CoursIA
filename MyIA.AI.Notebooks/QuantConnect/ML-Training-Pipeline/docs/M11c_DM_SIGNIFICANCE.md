# M11c Diebold-Mariano Significance Test on M11 Sharpe Deltas — Verdict

**Date** : 2026-05-12
**Wallclock** : 183.1s (CPU, ai-01, single thread)
**Script** : `scripts/m11c_sharpe_test.py`
**Args** : `--strategies kelly_har_mu60 kelly_har_mu250 --horizons 1 5 10 15 20 --bootstrap-top 5`
**Coins** : BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD
**Tests** : 7 coins × 5 horizons × 2 strategies = 70 paired comparisons vs `buy_hold`
**Env** : `coursia-ml-training` (Python 3.11, numpy 2.4, pandas 3.0, scipy 1.17)

---

## Question answered

> "M11a + M11b reported that `kelly_har_mu60` BEATS `buy_hold` on **27/35 = 77%** combos by raw Δ Sharpe. Is this statistically significant per CLAUDE.md G.2 (explicit p-value, not just 'promising') ?"

**Answer** : **NO at conventional thresholds.** With Ledoit-Wolf (2008) paired Sharpe-difference standard errors :

| Threshold | kelly_har_mu60 | kelly_har_mu250 |
|-----------|----------------|-----------------|
| Raw Δ Sharpe > 0 | **27/35 (77%)** | 17/35 (49%) |
| One-sided p < 0.10 | **5/35 (14%)** | 5/35 (14%) |
| One-sided p < 0.05 | **0/35 (0%)** | **0/35 (0%)** |
| One-sided p < 0.01 | **0/35 (0%)** | **0/35 (0%)** |
| Median t-stat | +0.682 | -0.025 |
| Median p-value | 0.2475 | 0.5099 |

**Honest verdict** : the BEATS claim of M11a/M11b is **INCONCLUSIVE** at α=0.05 in single-combo terms. The economic edge (Δ Sharpe annualised median ≈ +0.3 on kelly_har_mu60) is real **in the sense of point-estimate sign consistency** (27/35 combos positive) but the per-combo SE on Sharpe differences is too large with T ≈ 1800-1900 daily returns and fat-tailed crypto to reject H0 at conventional levels.

This is exactly the G.2 distinction the rule is designed to enforce: positive Δ Sharpe on a single backtest is **necessary but not sufficient** ; significance testing or multi-seed agreement is required to upgrade "BEATS" to defensible.

---

## Methodology

### Ledoit-Wolf 2008 closed-form (primary)

Per Ledoit & Wolf (2008) *"Robust performance hypothesis testing with the Sharpe
ratio"* §3.2, for two paired daily return streams $r_a$ (active strategy) and
$r_b$ (buy-and-hold) of length T :

$$
\hat S_a - \hat S_b \xrightarrow{a} \mathcal{N}\!\left(S_a - S_b, \frac{1}{T}\nabla'\Omega\nabla\right)
$$

where $\nabla = (1/\sigma_a, -\mu_a/(2\sigma_a^3), -1/\sigma_b, \mu_b/(2\sigma_b^3))$
is the delta-method gradient and $\Omega$ is the Newey-West HAC covariance of
$\theta_t = (r_a - \mu_a,\,(r_a-\mu_a)^2 - \sigma_a^2,\,r_b - \mu_b,\,(r_b-\mu_b)^2 - \sigma_b^2)$
with truncation lag $q = \lfloor T^{1/4} \rfloor$ (paper's default auto rule).

The test statistic $t = (\hat S_a - \hat S_b) / \widehat{SE}$ is asymptotically
standard normal under H0 ; one-sided p-value $= 1 - \Phi(t)$ for H1 : $S_a > S_b$.

### Stationary bootstrap (sanity check)

Politis & Romano (1994) stationary bootstrap with random geometric block length
(mean = 5 days ≈ one trading week, captures daily-return short-memory).
B = 1000 resamples on the strongest 5 combos. One-sided empirical p-value =
$\Pr(\hat S_a^* - \hat S_b^* - (\hat S_a - \hat S_b) \geq \hat S_a - \hat S_b)$
(re-centred under H0).

---

## Bootstrap sanity-check (top-5 combos by t-stat)

| Combo | p_LW2008 | p_bootstrap | Verdict |
|-------|----------|-------------|---------|
| ADA-USD h=20 kelly_har_mu250 | 0.0563 | 0.0680 | LW slightly tighter |
| LTC-USD h=20 kelly_har_mu60 | 0.0713 | 0.0740 | concordant |
| BTC-USD h=10 kelly_har_mu250 | 0.0716 | 0.0550 | boot slightly tighter |
| XRP-USD h=20 kelly_har_mu60 | 0.0731 | 0.0700 | concordant |
| DOT-USD h=20 kelly_har_mu60 | 0.0849 | 0.0970 | concordant |

All 5 |Δp| ≤ 0.02. The LW2008 closed-form and the stationary bootstrap converge
to essentially the same p-value, so the LW2008 result is **NOT** an artefact of
the asymptotic-normal assumption — it reflects genuine uncertainty given T and
the cross-correlation between active and passive returns.

---

## Top-10 strongest combos (kelly_har_mu60 + kelly_har_mu250 pooled)

| Coin | h | Strategy | Δ Sharpe (ann) | t-stat | p (1-sided) |
|------|---|----------|----------------|--------|-------------|
| ADA-USD | 20 | kelly_har_mu250 | +1.400 | +1.587 | 0.0563 |
| LTC-USD | 20 | kelly_har_mu60 | +0.671 | +1.466 | 0.0713 |
| BTC-USD | 10 | kelly_har_mu250 | +0.426 | +1.464 | 0.0716 |
| XRP-USD | 20 | kelly_har_mu60 | +0.734 | +1.453 | 0.0731 |
| DOT-USD | 20 | kelly_har_mu60 | +0.861 | +1.373 | 0.0849 |
| ADA-USD | 15 | kelly_har_mu250 | +1.147 | +1.370 | 0.0853 |
| LTC-USD | 20 | kelly_har_mu250 | +1.021 | +1.366 | 0.0860 |
| DOT-USD | 1 | kelly_har_mu60 | +0.724 | +1.347 | 0.0890 |
| BTC-USD | 15 | kelly_har_mu250 | +0.386 | +1.290 | 0.0986 |
| XRP-USD | 5 | kelly_har_mu60 | +0.479 | +1.286 | 0.0991 |

The "winning" combos cluster at long horizons (h=15/20) and on downtrend
coins (ADA/LTC/DOT) — same pattern flagged in M11b §"Coin-level". But every
single one has p > 0.05, so none individually crosses the conventional bar.

---

## Comparison vs M11a/M11b raw verdicts

| Metric | M11a+b raw (Δ Sharpe) | M11c LW2008 (p<0.05) | Δ |
|--------|----------------------|----------------------|---|
| kelly_har_mu60 BEATS | 27/35 (77%) | **0/35 (0%)** | -77pp |
| kelly_har_mu250 BEATS | 17/35 (49%) | **0/35 (0%)** | -49pp |
| Combos with p ∈ [0.05, 0.10] | — | 10/70 (14%) | — |

**Interpretation** : the M11a/M11b "BEATS" verdicts are **directionally consistent** with the data (27/35 = 77% is far above the 50% null) but the **per-combo evidence is too thin** to support a per-combo p<0.05 claim. The aggregate sign-consistency is itself non-trivial — a binomial test of "≥27 out of 35 positive under H0=½" gives p ≈ 0.001 — so there is collective evidence of an edge across the panel, just not per-coin/horizon.

---

## What's the rigorous claim, then ?

Two defensible re-statements that respect G.2 :

1. **"On 27/35 coin × horizon combos, kelly_har_mu60 has positive Δ Sharpe vs buy_hold ; binomial sign-test against null=½ rejects with p ≈ 0.001."** — this is a population-level statement, not a per-combo significance.

2. **"On the 5 strongest combos (ADA/LTC/BTC/XRP/DOT at long horizons), kelly_har_mu60/250 achieves p<0.10 one-sided ; none crosses p<0.05."** — this is a small-N marginally-significant cluster, useful for pedagogy ("real edge but not bankable").

The unqualified "BEATS buy_hold by Δ Sharpe" should be **dropped** from the
ESGF pedagogy slides in favour of either #1 or #2.

---

## Caveats

- **Sample size** : T ≈ 1800-1900 daily obs per combo. Even with a "true" Sharpe edge of 0.30 annual (typical of our point estimates), the asymptotic SE on a daily Sharpe difference is around 0.3/sqrt(7.5) ≈ 0.11 daily-equivalent, i.e. t ≈ 1.0-1.5 on these sample sizes. To reach t > 2 with the same point estimate, T would need to ~quadruple — 6-8 years of daily crypto vs the 7 years we have. **The test correctly says we don't have enough data**, not that the strategy is bad.
- **Fat tails** : crypto returns have ex-post kurtosis 8-15. Ledoit-Wolf 2008 SE is asymptotic but their Monte-Carlo (paper §4) shows reasonable size at T=1000 even with t-distributed returns df=4. Our bootstrap sanity-check is the explicit guard against tail-induced LW size distortion ; |p_LW - p_boot| ≤ 0.02 indicates the LW SE is not materially under-estimated.
- **Cross-strategy correlation** : we test 70 combos. Bonferroni-adjusted critical p is 0.05/70 ≈ 0.0007. Even after FDR (Benjamini-Hochberg q<0.10), none of our raw p-values would survive multiple-testing correction.
- **Conservative-of-two** : LW2008 is the more conservative of the two ; bootstrap is descriptive. Reporting LW as the official p-value is the right call.
- **Horizon-clustering** : long horizons (h=15/20) dominate the top-10. This is consistent with the M11b finding that Kelly stabilises at long holds. Could be a regime that doesn't generalize ; out-of-sample 2026+ data would help.

---

## G.2 + G.3 compliance

- **G.2 — Metrics honest, not binary** : p-values are explicit, not "promising". Aggregate count: kelly_har_mu60 BEATS 0/35 at p<0.05, BEATS 5/35 at p<0.10, BEATS 27/35 by Δ Sharpe sign — **all three numbers reported, none of which is alone a "BEATS"**.
- **G.3 — No DONE on marginal progress** : 0/35 at p<0.05 is the honest headline. The raw 27/35 verdict is acknowledged but down-weighted to "directional, not significant per-combo".
- **G.4 — Composite size** : single-script PR, 1 file (~325 lines), 1 doc, 1 results dir. Single domain (ML/trading). Under all thresholds.
- **G.6 — Coordinator scrutiny** : claim verifiable from `dm_results.json` + `dm_results.csv` ; reproducible from `coursia-ml-training` env in one command.

---

## Files

- This verdict : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/docs/M11c_DM_SIGNIFICANCE.md`
- Script : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/scripts/m11c_sharpe_test.py` (325 lines)
- Results JSON : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11c_dm_test/dm_results.json` (70 rows + 5 bootstrap rows)
- Results CSV : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11c_dm_test/dm_results.csv`

## Cross-references

- M11a (h=1/5/10) : `m11a_har_kelly_simulation/_verdict.md` (14/21 raw BEATS)
- M11b (h=15/20) : `docs/M11b_HAR_KELLY_LONG_HORIZONS.md` (13/14 raw BEATS) + `m11b_har_kelly_long_horizons/_verdict.md`
- M10 HAR vs GARCH vol prediction : `m10_har_garch_per_coin/_verdict.md` (12/21 BEATS — same caveat about per-combo significance applies)
- M8 SOTA direction prediction : 0/96 BEATS — direction prediction was the wrong primitive for transformers, but Δ-Sharpe-significance applies symmetrically (none would have crossed p<0.05 even if a "winner" had emerged).

## Reproducibility

```bash
# From d:/CoursIA/MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline
"C:/Users/MYIA/miniconda3/envs/coursia-ml-training/python.exe" -u \
    scripts/m11c_sharpe_test.py \
    --strategies kelly_har_mu60 kelly_har_mu250 \
    --horizons 1 5 10 15 20 \
    --bootstrap-top 5
```

Deterministic (HAR is OLS, bootstrap is seeded `rng_seed=42`). Wallclock ≈ 3 minutes on a single CPU core.
