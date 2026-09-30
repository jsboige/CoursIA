# M4 -- DLinear-vol: Linear Deep Learning vs HAR for Volatility Forecasting

**Status:** COMPLETE (Cycle 25 Wave 3, po-2024 Track 2).

## Why

M2-M3 established HAR (Corsi 2009) as the gold-standard baseline for crypto RV forecasting.
M3b showed asymmetric semivariance decomposition benefits BTC. A natural question: can the
simplest possible deep learning model -- DLinear (Zeng et al. AAAI 2023) -- beat HAR?

DLinear was proposed as a surprising result: a single `nn.Linear` layer that matches or
outperforms complex Transformers on long-term time series benchmarks. For volatility
forecasting, the question is whether a learned linear map from `log-RV_{t-seq_len...t}` to
`log-RV_{t+1...t+h}` captures dynamics that HAR's hand-crafted (1d/5d/22d) features miss.

## Model

**HAR (Corsi 2009):**
```
log RV_{t+h} = b0 + b_d*log(RV_t) + b_w*mean(log RV_{t-5..t-1}) + b_m*mean(log RV_{t-22..t-6}) + e
```

**DLinear (Zeng et al. 2023, adapted):**
```
y_hat = Linear(seq_len -> horizon)
```

Where:
- Input: last `seq_len=22` daily log-RV values (normalized)
- Output: next `horizon` log-RV values
- Optional decomposition: trend (AvgPool1d) + seasonal, with separate linear layers

## Methodology

- Walk-forward 5-fold expanding window, refit every 22 days
- 4 seeds (0, 7, 42, 99)
- 3 horizons (h=1, 5, 10 days)
- 7 coins (BTC, ETH, SOL, LTC, XRP, ADA, DOT)
- Diebold-Mariano HAC test vs HAR baseline
- AdamW optimizer, 100 epochs, gradient clipping 1.0, batch size 32
- Normalization: expanding-window mean/std on log-RV

## Files

| File | Role |
|------|------|
| `scripts/dlinear_vol.py` | DLinear-vol model + walk-forward runner |
| `scripts/results/m4_dlinear_vol_full.json` | Full 7-coin results (9082s runtime) |
| `scripts/results/m4_dlinear_vol_test.json` | Quick BTC+ETH test |
| `docs/M4_DLINEAR_VOL.md` | This document |

## Full Results (7 coins, 3 horizons, 4 seeds, 9082s runtime)

### DM verdict summary

| Verdict | Count | Configs |
|---------|-------|---------|
| **BEATS** | 5/21 | BTC h=1, h=5, h=10; ETH h=1; SOL h=1 |
| INCONCLUSIVE | 16/21 | All other (coin, horizon) pairs |
| NO BEATS | 0/21 | -- |

### Per-coin results (aggregated over 4 seeds)

| Coin | Horizon | DLinear MSE | HAR MSE | Reduction | DM p-value | Verdict |
|------|---------|-------------|---------|-----------|------------|---------|
| BTC-USD | 1 | 0.7518 | 0.8877 | -15.3% | <0.0001 | **BEATS** |
| BTC-USD | 5 | 0.3740 | 0.5220 | -28.3% | <0.0001 | **BEATS** |
| BTC-USD | 10 | 0.3521 | 0.5707 | -38.3% | <0.0001 | **BEATS** |
| ETH-USD | 1 | 0.6619 | 0.6844 | -3.3% | 0.036 | **BEATS** |
| ETH-USD | 5 | 0.3590 | 0.3736 | -3.9% | 0.285 | INCONCLUSIVE |
| ETH-USD | 10 | 0.3519 | 0.3745 | -6.0% | 0.316 | INCONCLUSIVE |
| SOL-USD | 1 | 0.5534 | 0.6132 | -9.8% | 0.001 | **BEATS** |
| SOL-USD | 5 | 0.2711 | 0.2835 | -4.4% | 0.221 | INCONCLUSIVE |
| SOL-USD | 10 | 0.2324 | 0.2378 | -2.2% | 0.679 | INCONCLUSIVE |
| ADA-USD | 1 | 0.6561 | 0.6925 | +5.3% | 0.050 | INCONCLUSIVE |
| ADA-USD | 5 | 0.3798 | 0.4114 | +7.7% | 0.206 | INCONCLUSIVE |
| ADA-USD | 10 | 0.3690 | 0.3725 | +0.9% | 0.894 | INCONCLUSIVE |
| LTC-USD | 1 | 0.6258 | 0.6564 | +4.7% | 0.086 | INCONCLUSIVE |
| LTC-USD | 5 | 0.3912 | 0.4304 | +9.1% | 0.100 | INCONCLUSIVE |
| LTC-USD | 10 | 0.3850 | 0.4225 | +8.9% | 0.236 | INCONCLUSIVE |
| DOT-USD | 1 | 0.6182 | 0.6383 | +3.2% | 0.141 | INCONCLUSIVE |
| DOT-USD | 5 | 0.3791 | 0.3802 | +0.3% | 0.931 | INCONCLUSIVE |
| DOT-USD | 10 | 0.3613 | 0.3587 | -0.7% | 0.922 | INCONCLUSIVE |
| XRP-USD | 1 | 0.8516 | 0.8501 | -0.2% | 0.670 | INCONCLUSIVE |
| XRP-USD | 5 | 0.4975 | 0.5227 | +4.8% | 0.353 | INCONCLUSIVE |
| XRP-USD | 10 | 0.5056 | 0.5246 | +3.6% | 0.615 | INCONCLUSIVE |

(Positive reduction = DLinear beats HAR. Bold = statistically significant across all 4 seeds.)

### Per-coin summary

| Coin | h=1 | h=5 | h=10 | Data source | RV days | Preds/fold |
|------|-----|-----|------|-------------|---------|------------|
| BTC-USD | BEATS | BEATS | BEATS | Bitstamp | ~2278 | ~378 |
| ETH-USD | BEATS | INC | INC | Binance | ~1495 | ~248 |
| SOL-USD | BEATS | INC | INC | yfinance | ~725 | ~119 |
| ADA-USD | INC* | INC | INC | yfinance | ~725 | ~119 |
| LTC-USD | INC* | INC | INC | yfinance | ~725 | ~119 |
| DOT-USD | INC | INC | INC | yfinance | ~725 | ~119 |
| XRP-USD | INC | INC | INC | yfinance | ~725 | ~119 |

INC* = 2-3 seeds pass DM but not all 4 (ADA h=1: 3/4, LTC h=1: 2/4).

### MSE reduction vs HAR (DLinear - HAR, negative = DLinear wins)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | -15.3% | -28.3% | **-38.3%** |
| ETH-USD | -3.3% | -3.9% | -6.0% |
| SOL-USD | -9.8% | -4.4% | -2.2% |
| ADA-USD | +5.3% | +7.7% | +0.9% |
| LTC-USD | +4.7% | +9.1% | +8.9% |
| DOT-USD | +3.2% | +0.3% | -0.7% |
| XRP-USD | -0.2% | +4.8% | +3.6% |

## Key findings

1. **DLinear BEATS HAR on BTC at all horizons (15-38% MSE reduction).** All 4 seeds pass
   the DM test at p<0.0001. The effect grows with horizon: a learned 22-day linear projection
   captures substantially more information than HAR's 3 hand-crafted features at h=10.

2. **ETH and SOL: significant at h=1 only.** ETH (1495 RV days) and SOL (725 RV days) both
   show 4/4 seeds passing DM at h=1, but the advantage does not extend to h=5 or h=10.
   This suggests DLinear captures short-horizon dynamics missed by HAR, but the signal
   weakens at longer horizons without enough data.

3. **Data quantity is the primary bottleneck.** BTC (2278 RV days, ~10 years) is the only
   coin where DLinear significantly beats HAR at ALL horizons. Coins with ~725 days
   (yfinance) show numerical improvements at some horizons (LTC h=5: -9.1%, ADA h=5: -7.7%)
   but none reach significance across all 4 seeds.

4. **XRP is the exception: DLinear slightly worse at h=1.** The only coin where DLinear
   does not consistently improve on HAR at the shortest horizon (MSE -0.2% at h=1, one
   seed worse at p=0.36). XRP's different microstructure (RV+ > RV-) may produce
   dynamics less suited to a global linear projection.

5. **DLinear is remarkably stable across seeds.** For BTC, the MSE spread across 4 seeds
   is <0.002 at any horizon. The model's simplicity (single linear layer) makes it
   inherently low-variance, which is an advantage over more complex architectures for
   small-sample financial data.

6. **HAR's hand-crafted features are a ceiling.** HAR uses 3 features (1d, 5d, 22d means).
   DLinear learns 22 free parameters (seq_len -> 1), effectively learning optimal weights
   on the full 22-day history. When data is sufficient, this flexibility wins. When data
   is scarce, the regularization of HAR's 3-parameter model may be preferable.

7. **Cross-reference with M3b (asymmetric HAR).** M3b found asymmetric HAR beats classic
   HAR for BTC (5-37% reduction). This M4 run shows DLinear also beats HAR for BTC
   (15-38% reduction). The two improvements are complementary: M3b exploits sign
   asymmetry (leverage effect), while M4 exploits full-path information. A natural next
   step would be a DLinear with asymmetric inputs (RV+ and RV- separately).

## References

- Zeng, A., Chen, M., Zhang, L. & Xu, Q. (2023) "Are Transformers Effective for Time Series Forecasting?", AAAI 2023.
- Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility", Journal of Financial Econometrics 7, 174-196.

## Re-validation hors biais (2026-09-22, Epic #1454)

Les résultats ci-dessus comparent deux MSE **bruts**. Or `MSE = biais² + variance` : un écart de MSE
peut être en partie la **mauvaise calibration de la baseline**, et non un gain de précision du
modèle. C'est ce que #10938 a levé sur M4, ce que #12684/#12734 ont formalisé, ce que
`pr-review-discipline` §C exige depuis (rapport de biais par modèle, DM sur une perte de
précision), et ce que M5 a appliqué le premier (2026-09-02).

Le harnais persiste désormais, par seed et par config : le biais OOS signé des **deux** modèles, la
décomposition `MSE = biais² + variance`, l'écart contre une baseline **dé-biaisée**, et un DM sur
**erreurs recentrées** (`e − mean(e)` de chaque côté — le centrage annule le biais, le DM ne
compare plus que les variances). La machine à quatre états est **partagée** avec M5 et M6
(`_aggregate_state` dans `scripts/bias_metrics.py`, extraite pour ce run). Aucune valeur publiée
ci-dessus n'a été modifiée : les jambes brutes sont recalculées à l'identique pour BTC (Bitstamp,
2278 jours de RV) et ETH (Binance, 1495 jours) — ancre M5 vérifiée au 6e chiffre : BTC h=1
`mean_har_bias_oos = −0,226587` reproduit à l'identique par le keeper run — et les colonnes
ci-dessous s'y ajoutent. **SOL fait exception** : seule ligne tirée de yfinance (source non
épinglée, fenêtre glissante au jour du run), son échantillon a dérivé — 724 jours de RV contre
~725 dans la table de provenance ci-dessus, MSE DLinear 0,5534 → 0,5796 (h=1) et 0,2324 → 0,2787
(h=10), et l'horizon 10 **change de signe** : 2,2 % d'amélioration publiée ci-dessus, 10,2 % de
dégradation mesurée par ce run. Les lignes SOL ci-dessous sont donc le verdict d'un échantillon
légèrement différent de celui du doc — dérive **déclarée** et non alignée à la main, ce qui
figerait un nombre non reproductible au lieu de dire qu'il a bougé.

Keeper run 2026-09-22 (BTC+ETH+SOL, 4 seeds 0/7/42/99, h=1/5/10, 6060 s,
`scripts/results/m4_dlinear_vol_debiased_3coin.json` ; séries par observation régénérables par
`python dlinear_vol.py --horizons 1 5 10 --seeds 0 7 42 99 --coins BTC-USD ETH-USD SOL-USD --out-json …`) :

| Coin | h | biais HAR OOS | biais DLinear OOS | edge vs HAR **dé-biaisée** | seeds BEATS (rec.) | dm_p_median (rec.) | Verdict brut | Verdict hors biais |
|------|---|--------------:|------------------:|---------------------------:|:------------------:|-------------------:|--------------|--------------------|
| BTC-USD | 1  | −0,2266 | −0,0052 | **+10,11 %** | 4/4 | 2,27e-09 | BEATS | **BEATS** |
| BTC-USD | 5  | −0,3432 | +0,0074 | **+7,48 %**  | 4/4 | 9,14e-05 | BEATS | **BEATS** |
| BTC-USD | 10 | −0,4502 | +0,0009 | **+4,31 %**  | 1/4 | 5,98e-02 | BEATS | **refuted-de-biased** |
| ETH-USD | 1  | −0,0810 | +0,0300 | **+2,49 %**  | 0/4 | 1,27e-01 | BEATS (doc) | **refuted-de-biased** |
| ETH-USD | 5  | −0,1290 | +0,0588 | +0,40 %  | 0/4 | 8,68e-01 | INCONCLUSIVE | INCONCLUSIVE |
| ETH-USD | 10 | −0,1727 | +0,0765 | −0,39 %  | 0/4 | 8,94e-01 | INCONCLUSIVE | INCONCLUSIVE |
| SOL-USD | 1  | +0,0659 | +0,1045 | **+5,82 %**  | 1/4 | 9,80e-02 | INCONCLUSIVE | **INCONCLUSIVE** |
| SOL-USD | 5  | +0,0951 | +0,1603 | +1,65 %  | 0/4 | 6,72e-01 | INCONCLUSIVE | INCONCLUSIVE |
| SOL-USD | 10 | +0,1113 | +0,1897 | −0,93 %  | 0/4 | 8,39e-01 | INCONCLUSIVE | INCONCLUSIVE |

La colonne « Verdict hors biais » **est** le champ `aggregate_verdict_debiased` de l'artefact JSON,
et non une lecture faite à la main par-dessus : les neuf lignes ci-dessus sont rejouées depuis
`_aggregate_state` dans `scripts/tests/test_m4_dlinear_bias_replay.py` (23 tests, verts), qui
rejoue chaque ligne à la fois depuis l'artefact et depuis les nombres recopiés ici. La machine à
quatre états est celle de M5 (`BEATS` / `NO BEATS` / `refuted-de-biased` / `INCONCLUSIVE`,
`NO BEATS` l'emporte sur `refuted-de-biased` quand les deux s'appliquent).

**Lecture honnête.** Trois enseignements que la seule jambe brute ne portait pas :

1. **BTC h=1 et h=5 : l'edge est réel, mais il est divisé par ~2.** Brut : −15,3 % et −28,3 %
   de réduction MSE ; dé-biaisé : +10,1 % et +7,5 % d'edge de précision. HAR sous-estime
   systématiquement la volatilité BTC (biais OOS −0,23 à −0,45, croissant avec l'horizon),
   DLinear est quasi non biaisé (−0,005 à +0,007) : une part substantielle de l'avantage brut
   était la mauvaise calibration de HAR, pas la précision de DLinear. L'edge qui survit au
   centrage reste significatif (4/4 seeds, `dm_p_median < 1e-04`) — la conclusion « DLinear
   bat HAR sur BTC » tient, chiffrée plus bas.
2. **BTC h=10 : réfuté par le centrage** (`refuted-de-biased`). L'edge brut le plus spectaculaire
   (−38,3 %) est exactement celui où le biais HAR est le plus grand (−0,4502, soit 35,5 % de la
   MSE HAR en `biais²`, contre 5,8 % à h=1 et 22,6 % à h=5). Dé-biaisée, la médiane des p passe
   à 5,98e-02 et une seule graine gagne.
   Le « l'effet croît avec l'horizon » du finding 1 ci-dessus était en réalité « **le biais HAR
   croît avec l'horizon** » — et DLinear n'y est pour rien.
3. **ETH h=1 : la signature doc « BEATS » ne survit pas non plus** (`refuted-de-biased` : 0/4
   graine gagnante sur la jambe recentrée, edge dé-biaisé +2,5 % non significatif). **SOL h=1**
   est `INCONCLUSIVE` **déjà sur la jambe brute** de ce run (0/4 graine gagnante, DM brut
   p = 0,158) : le « BEATS » de la table brute ci-dessus provenait du champ `verdict` hérité,
   calculé contre la baseline **calibrée** — un verdict dé-biaisé présenté sous un en-tête brut.
   Une fois le biais de HAR (+0,0659, de signe opposé à BTC — HAR *sur*-estime la vol SOL)
   neutralisé, elle le reste. Aucune conclusion des sections précédentes n'est modifiée rétroactivement :
   elles sont le verdict de la jambe brute, et cette section est le verdict de la jambe de
   précision — les deux sont publiées côte à côte, comme sur M5.

**Biais de DLinear, de signe opposé selon la pièce.** DLinear est non biaisé sur BTC
(|biais| < 0,01) mais **surestime** la volatilité ETH (+0,03 à +0,08) et surtout SOL (+0,10 à
+0,19, croissant avec l'horizon) : entraîné sur des fenêtres incluant le régime haute-vol 2022,
il projette un niveau que la fin d'échantillon ne confirme pas. Ce biais ne sauve aucun verdict
— il le plombe : sur SOL, la baseline HAR *surestime aussi*, et leurs biais s'annulent presque,
ce qui rend la comparaison brute moins défavorable à HAR qu'elle ne devrait.
