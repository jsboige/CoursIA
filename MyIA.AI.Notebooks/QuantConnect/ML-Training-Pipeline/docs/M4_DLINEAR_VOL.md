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

## Revalidation cluster appariée par origine — 2026-09-30

Le run Cycle 25 ci-dessus et le keeper run 2026-09-22 partagent un défaut de protocole que la
revalidation cluster M17 (#18190) a exposé puis corrigé pour sa famille : les jambes DM **brute**
et **calibrée** appariaient les erreurs des deux walk-forwards par **troncation positionnelle**
(`errors[:min_len]`). Tant que DLinear et HAR émettent exactement les mêmes dates d'origine, la
troncation est invisible ; dès qu'un fold est sauté d'un côté (`dropna` HAR, garde
`train_slice_end < 10` DLinear), elle compare silencieusement des jours — donc des cibles —
différents. La jambe recentrée (`dm_centered_*`, #12684) jointait déjà sur les dates ; les deux
autres jambes non.

Le correctif porte le protocole #18190 sur M4 :

1. **Jointure par date d'origine** — `joined_pair_errors` (organe partagé `bias_metrics.py`)
   joint les deux séries d'erreurs sur leurs dates communes (inner join), comme la jambe
   recentrée le faisait déjà.
2. **Validation des cibles partagées, fail-closed** — sur les dates jointes, les deux cibles
   doivent être la même quantité réalisée (moyenne des `horizon` prochains log-RV) à 1e-8 près.
   Un écart lève un verdict `TARGET_MISMATCH` explicite sur la combo (enregistré, jamais une
   comparaison silencieuse de pertes incommensurables). La tolérance couvre l'ordre d'association
   flottant (`np.mean` vs moyenne pandas), pas un vrai écart de cible.
3. **Purge des cibles apprises** — vérifiée par construction : `train_slice_end = train_end -
   seq_len - horizon + 1` borne la dernière cible d'entraînement à `train_end - 1`, avant la
   frontière test (`test_start = train_end`). Aucune cible apprise ne franchit sa frontière.

Run cluster : 7 actifs (BTC, ETH, SOL, LTC, XRP, ADA, DOT) × 3 horizons (1/5/10) × 4 graines
(0/7/42/99), `--debias --loss-fn mse`, config publiée inchangée (`seq_len` 22, 5 folds, refit 22,
100 époques, `decompose=False`). 84 combinaisons, 21 couples actif-horizon, 12 291 s. Diagnostic
d'alignement : `dm_target_gap_max` = 0,0 sur les 21 couples, 0 refus, jointures stables across
graines (BTC 1890/1870/1845, ETH 1240/1220/1195, cinq autres actifs 595/575/550).

### Verdicts cluster

| Actif | h | jambe calibrée (verdict doc) | jambe brute (4 états) | jambe précision (recentrée) | edge calibré | biais HAR OOS |
|-------|---|------------------------------|-----------------------|-----------------------------|-------------:|--------------:|
| BTC | 1  | **BEATS** (4/4, p 8,7e-11) | BEATS | **BEATS** (4/4, p 2,2e-09) | +10,9 % | −0,227 |
| BTC | 5  | **BEATS** (4/4, p 8,7e-04) | BEATS | **BEATS** (4/4, p 8,9e-05) | +10,5 % | −0,343 |
| BTC | 10 | INCONCLUSIVE (p 7,3e-02) | BEATS | refuted-de-biased | +9,6 % | −0,450 |
| ETH | 1  | INCONCLUSIVE | BEATS | refuted-de-biased | +2,3 % | −0,081 |
| ETH | 5  | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | +1,5 % | −0,129 |
| ETH | 10 | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | +3,0 % | −0,173 |
| SOL | 1  | **BEATS** (4/4, p 3,8e-03) | INCONCLUSIVE | INCONCLUSIVE (1/4) | +9,0 % | +0,063 |
| SOL | 5  | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | +5,2 % | +0,095 |
| SOL | 10 | INCONCLUSIVE | **NO BEATS** | INCONCLUSIVE | +1,1 % | +0,127 |
| LTC | 1/5/10 | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | −0,3/+1,2/+4,1 % | +0,03 à +0,09 |
| XRP | 1  | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | −0,7 % | −0,012 |
| XRP | 5  | INCONCLUSIVE | **NO BEATS** | INCONCLUSIVE | −0,2 % | −0,018 |
| XRP | 10 | INCONCLUSIVE | **NO BEATS** | **NO BEATS** (4/4, p 3,3e-02) | +0,2 % | −0,016 |
| ADA | 1/5 | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | +1,0/+0,2 % | +0,07/+0,10 |
| ADA | 10 | INCONCLUSIVE | **NO BEATS** | INCONCLUSIVE | −6,2 % | +0,138 |
| DOT | 1  | INCONCLUSIVE | INCONCLUSIVE | INCONCLUSIVE | −2,0 % | +0,012 |
| DOT | 5  | INCONCLUSIVE | **NO BEATS** | INCONCLUSIVE | −0,3 % | +0,014 |
| DOT | 10 | INCONCLUSIVE | **NO BEATS** | INCONCLUSIVE | +0,8 % | +0,028 |

**Verdict cluster : l'edge de précision de M4 est un phénomène BTC.** Sur la jambe recentrée,
seuls BTC h=1 et BTC h=5 passent la conjonction (4/4 graines, p médian < 1e-04) ; **0/18 couples
BEATS sur les six autres actifs**, dont XRP h=10 en `NO BEATS` significatif. Le « 5/21 BEATS » du
run Cycle 25 ne survit pas au-delà de BTC : **ETH h=1** est `refuted-de-biased` (le BEATS brut
était porté par le biais HAR, comme le keeper 2026-09-22 l'avait mesuré sur 3 pièces) et **SOL
h=1** ne bat que la baseline *calibrée* — jambe brute 0/4 (p 0,20) et recentrée 1/4 : un edge
qui n'existe que contre une baseline corrigée n'est pas un edge du modèle. Aux horizons longs
(h=10 surtout), la jambe brute bascule : 7 couples `NO BEATS` (SOL, XRP×2, ADA, DOT×2, LTC h=10)
— là où HAR ajoute le plus de structure, DLinear perd.

Le mécanisme est lisible dans les biais : HAR sous-estime massivement la vol BTC (biais OOS
−0,23 à −0,45, croissant avec l'horizon) mais est quasi neutre sur les petits actifs (|biais|
< 0,13 partout, < 0,03 sur DOT/XRP) — le levier « dé-biaser la baseline » qui fabriquait l'edge
apparent n'existe pas hors BTC. DLinear, lui, **surestime** les six autres actifs (+0,03 à
+0,28 selon pièce et horizon) : le même profil de biais qu'en 2026-09-22, confirmé cluster.

**Ce que cette section ne rétro-modifie pas** : les sections précédentes restent le verdict de
leurs jambes respectives (brute pour Cycle 25, recentrée pour le keeper) ; la présente ajoute la
lecture cluster aux jambes appariées par origine. Les verdicts publiés de BTC h=1/h=5 sont
**confirmés** ; ETH h=1 et SOL h=1 sont **rétrogradés** (refuté / calibré-seulement) par la
mesure la plus complète du dépôt sur M4.

Artefacts :

| Fichier | Rôle |
|---------|------|
| `scripts/results/m4_dlinear_vol_cluster_aligned.json` | Manifeste compact in-repo (31 406 octets) : verdicts par couple, diagnostics d'alignement, SHA-256 par pièce des lignes complètes |
| `G:\Mon Drive\MyIA\Dev\Trading\ML-Training-Pipeline\m4_dlinear_vol_cluster_full.json` | JSON complet avec séries par observation (11 753 743 octets, > 512 Ko → hors dépôt #15890) |

Empreinte du manifeste (SHA-256, CRLF normalisé LF) : `1d25cbc7948e2a16` (préfixe — valeur
complète dans le champ `artifact.sha256`). Régénération :
`python scripts/dlinear_vol.py --coins BTC-USD ETH-USD SOL-USD LTC-USD XRP-USD ADA-USD DOT-USD --horizons 1 5 10 --seeds 0 7 42 99 --debias --loss-fn mse --out-json <full.json> --manifest-out results/m4_dlinear_vol_cluster_aligned.json` (reprise sur checkpoint : chaque combo terminé est appendé en JSONL et sauté au redémarrage).
