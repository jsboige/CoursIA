# M15: Log-LSTM RV

**Model:** LSTM (Hochreiter & Schmidhuber 1997) applied to log-realized variance.
**Date:** 2026-05-14
**Updated:** 2026-08-17 — hidden=32 re-run §C (issue #11395): **NO BEATS**, claim "deployable" retracted.
**Script:** `scripts/m15_lstm_rv.py`

## Architecture

```
Input:  sliding window W=22 days x 3 features [log(RV), returns, sign(returns)]
Model:  LSTM(hidden=H, 1 layer) + FC(H, 1)
Target: log(RV_{t+h}), h in {1, 5, 10}
Loss:   MSE on log-RV
Decode: exp(pred) -> RV level, then log(RV) for Kelly comparison
```

Three capacities were tested historically:
- **hidden=128**: ~68,225 params -- NO BEATS (historical run, not tracked)
- **hidden=64**: ~17,729 params -- NO BEATS (tracked runs: `m15_lstm_rv_btc_sc`, BTC only)
- **hidden=32**: ~4,769 params -- historical "BEATS" **invalidated by the §C test** (NO BEATS)

## Methodology

- Walk-forward 5-fold expanding window, refit every 22 days
- Early stopping (patience=10, max epochs=100)
- Expanding normalization (mean/std from training fold only)
- 7 coins (BTC, ETH, SOL, LTC, XRP, ADA, DOT) x 3 horizons (h=1,5,10) x 4 seeds (0,1,7,42) = 84 combos
- Kelly cap=1.0, fee=50bps, mu_window=60
- Sign-test: binomial one-sided (historical gate, NOT the §C gate)
- **§C gate (issue #11395):** conjunction edge >= 2σ cross-seed **AND** dm_p_median < 0.05 on the **precision loss** (loss_fn="mse"), plus dominance guard

## Results: hidden=32 (~4.8K params) -- §C re-run (issue #11395)

**VERDICT: NO BEATS** (44/84, p=0.372, win_rate=52.4%)

| Metric | Value |
|--------|-------|
| LSTM beats HAR | 44/84 (52.4%) |
| p-value (sign-test) | 0.3718 |
| Median delta-Sharpe (LSTM - HAR) | +0.0029 |
| Median MSE change | +11.2% (LSTM worse) |
| Runtime | 4.5h (16036s, GPU) |
| Results file | `scripts/results/m15_lstm_rv_h32/results.json` (tracked) |

### §C conjunction per horizon (loss = mse)

| Horizon | edge (MSE) | σ cross-seed | dm_p_median | beaten | Verdict §C |
|---------|------------|--------------|-------------|--------|------------|
| h=1 | -9.1% | 6.50 | 0.027 | 18/28 | NO BEATS |
| h=5 | -9.0% | 11.43 | 0.083 | 7/28 | NO BEATS |
| h=10 | -10.9% | 15.41 | 0.112 | 7/28 | NO BEATS |

The Diebold-Mariano test is significant at h=1 (p=0.027) but **in the direction LSTM worse**: the
HAR baseline is significantly more precise at the short horizon. A significant p-value is not a
BEATS -- the sign of the edge decides.

### Per-coin results (hidden=32, §C run)

| Coin | Median delta-Sharpe | MSE change | Beats |
|------|-------------------|------------|-------|
| BTC-USD | +0.0123 | -11.9% | 12/12 |
| ETH-USD | -0.0286 | +8.3% | 4/12 |
| SOL-USD | +0.0131 | +17.1% | 9/12 |
| LTC-USD | -0.0744 | +14.9% | 0/12 |
| XRP-USD | +0.0331 | +17.4% | 8/12 |
| ADA-USD | +0.0192 | +9.4% | 7/12 |
| DOT-USD | -0.0530 | +8.7% | 4/12 |

Only BTC shows a median MSE reduction (-11.9%). The historical per-coin claims (DOT 12/12, ADA 11/12,
XRP 9/12) do **not** reproduce on the tracked §C run.

### Per-horizon results (hidden=32, §C run)

| Horizon | Median delta-Sharpe | Beats |
|---------|-------------------|-------|
| h=1 | +0.0123 | 18/28 |
| h=5 | -0.0253 | 13/28 |
| h=10 | -0.0077 | 13/28 |

### Historical run (NOT tracked, claims only)

The original hidden=32 run (2026-05) claimed BEATS (52/84, p=0.0188, median delta-Sharpe +0.0121,
DOT 12/12, h=1 23/28). These numbers were based on a **sign-test of Kelly Sharpe alone** -- never
validated by the §C conjunction. The run is not tracked; the §C run above is the reproducible
reference and it **infirms** the BEATS.

## Results: hidden=64 and hidden=128 (historical, not tracked)

Historical claims (2026-05, 84-combo runs not tracked in the repo):
- hidden=64: NO BEATS (45/84, p=0.2928)
- hidden=128: NO BEATS (38/84, p=0.8369)

Tracked substitutes: `scripts/results/m15_lstm_rv_btc_sc` (hidden=64, loss_fn="linear") and
`m15_lstm_rv_btc_sc_mse` (hidden=64, loss_fn="mse"), both BTC-only, both **NO BEATS** in their
§C verdict. The historical 84-combo numbers above are **not reproducible** (runs never tracked)
and should not be cited as evidence.

## Capacity comparison (revised)

| Metric | h=32 (§C run) | h=64 (tracked BTC) | h=128 (historical) |
|--------|--------------|--------------------|--------------------|
| Win rate | 52.4% (44/84) | 58.3% / 66.7% (12 BTC combos) | 45.2% (not tracked) |
| Median MSE change | +11.2% | -12.2% / -11.5% | +7.0% (not tracked) |
| Verdict | **NO BEATS** | NO BEATS | NO BEATS |

The historical "monotonic capacity sweep" interpretation (smaller = better, overfitting signature)
is **not supported**: the tracked h=64 BTC runs were actually **more precise** in MSE (-12%) yet
still failed the §C conjunction on significance. The correct reading: at every tracked capacity,
the LSTM fails the §C gate.

## Caveats (G.2 Honesty)

### C.1 -- MSE worse despite Sharpe better

Median MSE change is +11.2% (LSTM worse). The historical BEATS verdict came entirely from Kelly
Sharpe, not forecast accuracy. The §C re-run shows the Sharpe gain (+0.0029) is **indistinguishable
from noise** (p=0.372) -- the MSE paradox is real but the Sharpe side is not statistically significant.

### C.2 -- Weak coins drag

ETH, LTC and DOT show negative median delta-Sharpe on the §C run. The overall Sharpe win rate
(52.4%) is carried by BTC (12/12) and, more weakly, SOL/XRP/ADA.

### C.3 -- No horizon holds the §C conjunction

The edge on the precision loss is negative at all three horizons. h=5 is essentially a coin flip
(13/28, delta-Sharpe -0.0253). No horizon qualifies as an edge.

## Comparison with M-series

| Model | Verdict | Win rate | p-value | Notes |
|-------|---------|----------|---------|-------|
| M2 HAR Classic | **Baseline** | -- | -- | Sharpe +0.313 vs BH |
| M10 Realized GARCH | NO BEATS | -- | -- | MSE +62% |
| M12 HAR-RV-J | **BEATS** | -- | p=0.0015 | Jump-augmented, deployed (`HAR-RV-J-Kelly`) |
| M13 MS-HAR | NO BEATS | 39/84 | p=0.7774 | Markov-Switching |
| M14 HEAVY | NO BEATS | 48/84 | p=0.1149 | Bivariate |
| M15 LSTM h=32 | **NO BEATS** | 44/84 | p=0.372 | §C re-run (issue #11395) |
| M15 LSTM h=64 (BTC) | NO BEATS | 7-8/12 | -- | §C tracked runs |

## Conclusion

The historical BEATS of M15 hidden=32 (p=0.0188, "deployable") was based on a sign-test of Kelly
Sharpe only. The §C re-run (issue #11395, DM on the mse precision loss, seeds 0/1/7/42, 84 combos)
**infirms** it: edge negative at all horizons (-9.1% / -9.0% / -10.9%), Sharpe gain not significant
(p=0.372). M15 h=32 is **removed from the KEEPERS** (`RECAP_KEEPERS_V2.md`).

The lesson: a Sharpe gain without a precision gain is **indistinguishable from noise** on 84 combos.
The §C conjunction (edge >= 2σ AND dm_p_median < 0.05 on the precision loss) exists exactly for this
case. A distinct §C-conformant M15 entry exists for BTC-only hidden=64 refit-110 (2/3 BEATS at
h=5/h=10, issue #11034) -- see `REGISTRY.md`; it is a different configuration, not the retracted claim.

Runtime (§C run): h=32 ~4.5h (16036s, RTX 3070 Laptop).

## Revalidation cluster appariée par origine (2026-10-01)

Le protocole #18190 (appariement par origine, porté depuis M4/#18650) a été appliqué au run cluster
7 actifs x 3 horizons x 4 seeds (84 combos, mse, refit 110, hidden 64, GPU). Les jambes DM joignent
les deux walk-forwards sur leurs dates d'origine communes et **refusent** sur mismatch de cible
partagée — jamais de troncature positionnelle.

### Défaut de convention mesuré (le résultat principal du port)

Le garde shared-target a refusé **deux fois** avant toute mesure valide — c'est le protocole qui
fait son travail :

1. **Join naïf refusé** (BTC h=1, gap max 4,25) : les deux walk-forwards adressent des fenêtres
   réalisées différentes. Cible LSTM à l'origine `i` = `log_rv.rolling(h).mean().shift(-h)` ->
   fenêtre `[i+1, i+h]` (features jusqu'à `i-1`, via `seq = feat_vals[i-window:i]`). Cible HAR à
   l'origine `t` = `log_rv.iloc[t:t+h].mean()` -> fenêtre `[t, t+h-1]` (info `rv[:t]`).
2. **Relabel positionnel refusé** (gap max 3,51) : les boucles s'arrêtent à `test_end - horizon`,
   donc la sortie HAR concaténée **saute h positions à chaque frontière de fold** — un décalage
   positionnel (`values[1:]`) franchit la frontière et apparie des fenêtres décalées d'un jour sur
   les dates de frontière.

**Correctif** : chaque entrée HAR est relabelisée sur la **date boursière précédente de l'index
complet** (`_relabel_har_to_lstm_origin(..., full_index)`), jamais sur l'entrée précédente de la
sortie. Diagnostic indépendant : gap exactement 0,0 sur 2 276 dates BTC h=1 ; sur le run complet,
gap max 3,6e-15 (ULP flottant) et 0 cellule TARGET_MISMATCH sur 21. Test de régression avec sortie
HAR à trou de fold (`test_relabel_survives_fold_boundaries_in_the_har_output`).

**Conséquence sur l'historique** : les verdicts §C antérieurs de M15 comparaient les prévisions
next-window du LSTM aux cibles origin-window du HAR — convention mixte. En particulier le BTC-only
hidden=64 refit-110 « 2/3 BEATS » (#11034) ne survit pas à l'appariement corrigé : ses cellules
h=5/h=10 sont INCONCLUSIVE en jambe brute (p=0,195 / 0,053) et NO BEATS en jambe calibrée.

**Asymétrie résiduelle documentée** : à l'origine appariée, la jambe HAR connaît `rv` jusqu'à
`t-1` tandis que la jambe LSTM connaît ses features jusqu'à `t-2` (la convention M15 garde un jour
de trou entre frontière d'information et fenêtre cible). Direction conservatrice : un verdict BEATS
n'en serait que plus fort ; le verdict BEATEN ci-dessous n'est jamais lu comme une déficience LSTM
seule.

### Verdicts cluster (3 jambes : brute / calibrée / centrée-variance)

Agrégé par horizon (28 combos chacun) :

| Horizon | edge MSE | sigma | dm_p_median | brute | calibrée | centrée (variance) |
|---|---|---|---|---|---|---|
| h=1  | -20,8 % | 7,04  | 0,0001 | NO BEATS | NO BEATS (p=0,0006) | BEATEN (p=0,0024) |
| h=5  | -30,3 % | 18,04 | 0,0004 | NO BEATS | NO BEATS (p=0,0104) | BEATEN (p=0,0026) |
| h=10 | -45,2 % | 32,79 | 0,0003 | NO BEATS | NO BEATS (p=0,0525) | BEATEN (p=0,0089) |

Par cellule (21 coin x horizon) : brute NO BEATS 19/21 (INCONCLUSIVE BTC h=5/h=10) ; calibrée NO
BEATS 18/21 (INCONCLUSIVE SOL h=10, XRP h=5/h=10) ; centrée BEATEN (variance) 18/21 (INCONCLUSIVE
XRP h=5/h=10). **var_ratio LSTM/HAR > 1 sur les 21 cellules (1,12-1,34)** : le déficit est de la
**variance** — même après retrait du biais, le LSTM est uniformément moins précis que HAR.

Ceci étend au cluster 7 actifs le verdict `refuted-de-biased` BTC du 2026-08-24, avec une structure
plus tranchée : là où l'edge BTC publié était le biais² de HAR, la mesure corrigée montre un
déficit de précision (variance) qui ne dépend pas de la convention de biais.

Manifeste compact committé : `scripts/results/m15_lstm_rv_cluster_aligned.json` (politique #15890) ;
séries complètes hors dépôt :
`G:\Mon Drive\MyIA\Dev\Trading\ML-Training-Pipeline\m15_lstm_rv_cluster_full.json`
(12,3 Mo ; sha256 LF 909244cb...d67d818, octets bruts 4e7167e5...d79abd). Runtime réel ~82 min
(84 combos, RTX 3070 Laptop ; le champ `elapsed_s` du manifeste mesure le dernier process,
restart checkpoint inclus).
