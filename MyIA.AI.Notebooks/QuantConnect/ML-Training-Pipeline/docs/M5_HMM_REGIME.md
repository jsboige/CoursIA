# M5 -- HMM Regime-Switching HAR: Volatility Regime Detection + Conditional Forecasting

**Status:** COMPLETE (Cycle 25 Wave 3, po-2024 Track C2).

## Why

M3 established HAR as the gold-standard baseline for crypto RV forecasting. M3b showed
asymmetric semivariance benefits BTC. M4 showed DLinear beats HAR on BTC at all horizons.
A natural extension: can regime-switching models, where different HAR coefficients apply
in different volatility regimes (low-vol vs high-vol), improve on the single HAR model?

The economic intuition: volatility dynamics may differ between calm and turbulent periods.
A model that adapts its coefficients to the current regime could capture this asymmetry.

## Model

**Classic HAR (Corsi 2009):**
```
log RV_{t+h} = b0 + b_d*rv_d + b_w*rv_w + b_m*rv_m + e
```

**Regime-Switching HAR (this work):**
```
log RV_{t+h} = b0 + b_d*rv_d + b_w*rv_w + b_m*rv_m
             + g0 * I(regime=high)
             + g_d * rv_d * I(regime=high)
             + g_w * rv_w * I(regime=high)
             + g_m * rv_m * I(regime=high)
             + e
```

Where:
- Regime decoded by K=2 Gaussian HMM (Viterbi) on log-RV
- 8 OLS coefficients (4 base + 4 regime interaction terms)
- At prediction time, HMM decodes current regime, selecting the interaction term values

## Methodology

- K=2 Gaussian HMM (hmmlearn) on log-RV, Viterbi-decoded
- Regime-switching HAR with interaction terms (8 coefficients)
- Walk-forward 5-fold expanding window, refit every 22 days
- 4 seeds (0, 7, 42, 99) for HMM initialization
- 2 coins (BTC-USD, ETH-USD), 3 horizons (h=1, 5, 10)
- Diebold-Mariano HAC test vs classic HAR baseline (`loss_fn="mse"` — perte de précision, jamais `linear`)
- Aggregate verdict: BEATS only if 4/4 seeds pass DM
- Jambe hors biais (ajoutée 2026-09-02) : décomposition `MSE = biais² + variance` par modèle, edge
  contre baseline dé-biaisée, et DM sur erreurs recentrées des deux côtés

## Files

| File | Role |
|------|------|
| `scripts/hmm_regime_vol.py` | HMM regime-switching HAR model + walk-forward runner + instrumentation de biais |
| `scripts/tests/test_hmm_regime_vol.py` | Tests du contrat de sortie, de la jambe recentrée et de la machine d'états agrégée (45 tests) |
| `scripts/results/m5_hmm_regime.json` | Full results (609s runtime) |
| `docs/M5_HMM_REGIME.md` | This document |

Le runner expose un CLI (`--coins`, `--horizons`, `--seeds`, `--out`, `--dump-series`). Les séries de
prévision alignées ne sont écrites que sur `--dump-series` (CSV séparé) : l'artefact JSON reste léger
et ne porte que des agrégats et des décompositions, sur le modèle de #12745.

## Results (BTC+ETH, 4 seeds, 609s runtime)

### DM verdict summary

| Verdict | Count | Configs |
|---------|-------|---------|
| **BEATS** | 1/6 | ETH h=1 (4/4 seeds) |
| INCONCLUSIVE | 1/6 | BTC h=1 (3/4 seeds) |
| **BEATEN BY** | 4/6 | BTC h=5, BTC h=10, ETH h=5, ETH h=10 |

### Per-coin results (aggregated over 4 seeds)

| Coin | Horizon | Regime MSE | Classic MSE | Reduction | DM p-value | Verdict |
|------|---------|------------|-------------|-----------|------------|---------|
| BTC-USD | 1 | 0.825 | 0.888 | +7.0% | 3/4 seeds p<0.001 | INCONCLUSIVE |
| BTC-USD | 5 | 0.580 | 0.522 | -11.1% | 2/4 BEATEN BY | BEATEN BY |
| BTC-USD | 10 | 0.732 | 0.571 | -28.3% | 3/4 BEATEN BY | BEATEN BY |
| ETH-USD | 1 | 0.619 | 0.684 | +9.6% | 4/4 p<0.005 | **BEATS** |
| ETH-USD | 5 | 0.441 | 0.374 | -17.9% | 3/4 BEATEN BY | BEATEN BY |
| ETH-USD | 10 | 0.573 | 0.375 | -53.0% | 4/4 BEATEN BY | BEATEN BY |

### MSE reduction vs classic HAR (regime - classic, positive = regime wins)

| Coin | h=1 | h=5 | h=10 |
|------|-----|-----|------|
| BTC-USD | +7.0%* | -11.1% | -28.3% |
| ETH-USD | **+9.6%** | -17.9% | -53.0% |

(*3/4 seeds significant, not all 4)

## Re-validation hors biais (2026-09-02, Epic #1454)

Les résultats ci-dessus comparent deux MSE **bruts**. Or `MSE = biais² + variance` : un écart de MSE
peut être entièrement la **mauvaise calibration de la baseline**, et non un gain de précision du
modèle. C'est ce que #10938 a levé sur M4, ce que #12684/#12734 ont formalisé, et ce que
`pr-review-discipline` §C exige depuis (rapport de biais par modèle, DM sur une perte de précision).

Le harnais persiste désormais, par seed et par config : le biais OOS signé des **deux** modèles, la
décomposition `MSE = biais² + variance`, l'écart contre une baseline **dé-biaisée**, et un DM sur
**erreurs recentrées** (`e − mean(e)` de chaque côté — le centrage annule le biais, le DM ne compare
plus que les variances). Aucune valeur publiée ci-dessus n'a été modifiée : les jambes brutes sont
recalculées à l'identique et les colonnes ci-dessous s'y ajoutent.

| Coin | h | edge brut | edge vs classic **dé-biaisée** | σ cross-seed | edge/σ | seeds BEATS (rec.) | seeds BEATEN (rec.) | dm_p_median (rec.) | Verdict hors biais |
|------|---|----------:|-------------------------------:|-------------:|-------:|:------------------:|:-------------------:|-------------------:|--------------------|
| BTC-USD | 1  |  +7,0 % |  **+1,3 %** |  4,04 pt | **0,3σ** | 3/4 | 0/4 | 1,47e-03 | **INCONCLUSIVE** |
| BTC-USD | 5  | −11,1 % | **−43,5 %** |  9,37 pt | 4,6σ | 0/4 | 4/4 | 6,21e-06 | **NO BEATS** |
| BTC-USD | 10 | −28,3 % | **−99,0 %** | 21,18 pt | 4,7σ | 0/4 | 4/4 | 1,75e-09 | **NO BEATS** |
| ETH-USD | 1  |  +9,6 % |  **+8,7 %** |  2,11 pt | **4,1σ** | 4/4 | 0/4 | 1,14e-05 | **BEATS** |
| ETH-USD | 5  | −17,9 % | **−23,4 %** |  3,85 pt | 6,1σ | 0/4 | 4/4 | 6,16e-04 | **NO BEATS** |
| ETH-USD | 10 | −53,0 % | **−66,2 %** | 14,70 pt | 4,5σ | 0/4 | 4/4 | 4,10e-05 | **NO BEATS** |

La colonne « Verdict hors biais » **est** le champ `aggregate_verdict_debiased` de l'artefact JSON, et
non une lecture faite à la main par-dessus : les six lignes ci-dessus sont rejouées depuis
`_aggregate_debiased_state` dans `scripts/tests/test_hmm_regime_vol.py`. La machine a quatre états —

| État | Condition | Sens |
|------|-----------|------|
| `BEATS` | 4/4 seeds BEATS sur la jambe recentrée **et** `dm_p_median < 0,05` | l'edge survit au contrôle de précision |
| `NO BEATS` | 4/4 seeds BEATEN **et** `dm_p_median < 0,05` | le modèle perd, significativement |
| `refuted-de-biased` | la jambe **brute** était 4/4 BEATS, la recentrée ne confirme pas | l'edge n'existait que contre une ligne de base mal calibrée (formulation #12788) |
| `INCONCLUSIVE` | tout le reste (dont 3/4 d'un côté ou l'autre) | pas d'unanimité |

`NO BEATS` l'emporte sur `refuted-de-biased` quand les deux s'appliquent : « réfuté » dit qu'une
prétention n'est pas confirmée, la mesure dit que le modèle perd — et la réfutation reste lisible
puisque chaque ligne imprime le verdict brut à côté du recentré. Le décompte des pertes est persisté
(`n_beaten_seeds_centered`), donc la colonne « seeds BEATEN (rec.) » se relit depuis l'artefact.

Le champ `aggregate_verdict` (jambe **brute**) garde délibérément sa convention publiée à deux états
(« BEATS exige 4/4 seeds, sinon INCONCLUSIVE ») : `m5_hmm_regime_research.ipynb` la documente et en
dérive sa propre lecture `DEGRADE`, qu'un élargissement invaliderait en silence (il faudrait
re-générer l'artefact puis ré-exécuter le notebook). L'asymétrie est assumée et suivie en **#14388**,
pas un oubli.

**Rapport de biais signé, par modèle (contrôle §C(7))** — le biais est celui du log-RV OOS :

| Coin | h | biais régime | biais classic | biais²(classic) en % de MSE(classic) |
|------|---|-------------:|--------------:|-------------------------------------:|
| BTC-USD | 1  | −0,1811 | −0,2266 |  **5,8 %** |
| BTC-USD | 5  | −0,2728 | −0,3432 | **22,6 %** |
| BTC-USD | 10 | −0,3624 | −0,4502 | **35,5 %** |
| ETH-USD | 1  | −0,0718 | −0,0810 |  **1,0 %** |
| ETH-USD | 5  | −0,1091 | −0,1290 |  **4,5 %** |
| ETH-USD | 10 | −0,1519 | −0,1727 |  **8,0 %** |

Les deux modèles sous-prévoient le log-RV partout (biais négatif), le régime un peu moins que la
baseline. La part de biais² dans le MSE de la baseline **croît fortement avec l'horizon** : à
BTC h=10, plus du tiers du MSE de la HAR classique est du biais pur, pas de l'imprécision.

### Ce que la relecture hors biais change

1. **ETH h=1 survit — c'est un vrai gain de précision.** L'edge passe de +9,6 % à **+8,7 %** une fois
   la baseline dé-biaisée : seulement 0,9 pt de l'écart venait du biais. La conjonction §C est
   complète — 4/4 seeds BEATS sur la jambe recentrée, `dm_p_median` = 1,14e-05 < 0,05, et
   **4,1σ ≥ 2σ** de dispersion cross-seed. Le seul BEATS de M5 **tient hors biais**.

2. **BTC h=1 tombe, et pour une raison mesurée.** L'edge brut +7,0 % se réduit à **+1,3 %** : environ
   **82 % de l'écart apparent était la mauvaise calibration de la HAR**, dont le biais² pèse 5,8 % de
   son MSE. Le verdict brut le disait déjà INCONCLUSIVE, mais en imputant l'échec à la seule graine 7
   (« HMM initialization sensitivity »). La mesure est plus dure : à **0,3σ**, l'edge dé-biaisé est
   trois fois plus petit que la dispersion entre graines. Ce n'est pas une graine aberrante, c'est un
   effet qui n'existe pas.

3. **Le biais de la baseline masquait l'ampleur de la dégradation aux horizons longs.** Dé-biaiser la
   HAR classique la rend meilleure, donc creuse l'écart : BTC h=10 passe de −28,3 % à **−99,0 %**,
   BTC h=5 de −11,1 % à −43,5 %. Les quatre configs longues sont **4/4 seeds BEATEN** sur la jambe de
   précision. La conclusion d'origine (« le modèle de régime est nuisible à h≥5 ») est confirmée et
   renforcée, pas infirmée.

4. **L'asymétrie BTC/ETH à h=1 est une propriété de la baseline, pas du modèle de régime.** Le même
   modèle, le même instrument : la HAR BTC porte 5,8 % de biais², la HAR ETH seulement 1,0 %. C'est
   pourquoi l'edge BTC était à 82 % du biais et l'edge ETH à 9 % seulement. Ce que M5 « gagnait » sur
   BTC h=1, c'était surtout de corriger une baseline mal calée.

**Note de comparabilité** — la HAR classique de ce harnais et la baseline HAR de M4 sont le **même
objet** : `hmm_regime_vol.py` et la chaîne `btc_vol.py → dlinear_vol.py` importent toutes deux
l'unique `har_model.HARModel`. Le biais OOS BTC mesuré ici (−0,2265869503892514 / −0,34317822065868814 /
−0,45022101989096786 pour h=1/5/10) est **bit-identique** à `har_bias_oos` de l'artefact #12745. Ce
n'est donc pas une corroboration indépendante — c'est le même calcul — mais cela vérifie que
l'instrumentation de biais ajoutée ici est câblée comme celle de la famille, et cela rend les edges
M5 et M4 directement comparables sur BTC.

## Key findings

*(Lecture d'origine, Cycle 25, sur MSE bruts. Conservée telle quelle ; la section « Re-validation
hors biais » ci-dessus précise les points 1 et 2 et confirme le point 3.)*

1. **ETH h=1: only significant win.** The regime-switching HAR beats classic HAR by 9.6%
   (4/4 seeds, p<0.005). ETH's shorter data history (1495 RV days) with more pronounced
   regime shifts benefits from the conditional model at the shortest horizon.

2. **BTC h=1: promising but not conclusive.** 3/4 seeds show 8-10% improvement (p<10^-5),
   but seed 7 produces near-zero improvement (0.1%). The aggregate verdict is INCONCLUSIVE.
   The HMM initialization sensitivity is a concern.

3. **Longer horizons: regime model is harmful.** At h=5 and h=10, the regime-switching
   model is significantly WORSE than classic HAR for both coins. The MSE degradation grows
   with horizon: BTC h=10 sees 28% worse, ETH h=10 sees 53% worse. The interaction terms
   introduce noise that compounds over multi-step forecasts.

4. **HMM initialization sensitivity is severe.** Different seeds produce wildly different
   regime decompositions. Seed 0 and 99 might classify 60%/40% low/high, while seed 7
   might produce 80%/20%. This variance translates directly into prediction instability.

5. **The regime interaction approach has a fundamental flaw at longer horizons.** The
   iterative h-step prediction uses a single regime indicator R for ALL forecast steps.
   But the regime may switch during the forecast window. The model cannot adapt mid-forecast,
   leading to compounding errors.

## Conclusion

**Verdict hors biais (2026-09-02, Epic #1454) : `confirmed` sur ETH h=1, `NO BEATS` 4/6, INCONCLUSIVE
1/6.** Le seul BEATS de M5 tient une fois la baseline dé-biaisée (+8,7 %, 4/4 seeds, 4,1σ,
`dm_p_median` 1,14e-05) — contrairement à M15, réfuté par le même instrument (`refuted-de-biased`
3/3, #11041). Le verdict brut ci-dessous reste exact et n'est pas révisé ; la relecture hors biais
le **précise** : BTC h=1 n'était pas « prometteur mais sensible aux graines », son edge était à 82 %
le biais de la HAR ; et la dégradation à h≥5 est plus sévère qu'elle ne le paraissait.

**M5 verdict (brut, tel que publié en Cycle 25) : INCONCLUSIVE overall. 1/6 configs BEATS (ETH h=1).**

The HMM regime-switching HAR provides marginal improvement at h=1 for some configurations
but is actively harmful at h>=5. The approach adds complexity (8 coefficients + HMM
decoding) without consistent benefit. The classic 3-parameter HAR remains the better
default for most use cases.

Compared to M3b (asymmetric HAR, 3/21 BEATS, BTC-only) and M4 (DLinear, 5/21 BEATS),
the HMM regime approach (1/6 BEATS) is the weakest extension. The DLinear model, which
learns optimal temporal weights without explicit regime decomposition, is strictly superior.

## References

- Hamilton, J.D. (1989) "A New Approach to the Economic Analysis of Nonstationary
  Time Series and the Business Cycle", Econometrica 57, 357-384.
- Corsi, F. (2009) "A Simple Approximate Long-Memory Model of Realized Volatility",
  Journal of Financial Econometrics 7, 174-196.
