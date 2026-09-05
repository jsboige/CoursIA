# Checkpoint Registry

Auto-generated: 2026-05-03 22:29
Updated: 2026-05-06 — Stage -1 Panier baselines: 18 BEATS, 32 FAILS across 50 experiments (26 symbols x 2 models)
Updated: 2026-06-12 — Ladder #1409 verdicts consolidated; legacy SPY-single checkpoints marked ARCHIVED
Updated: 2026-08-14 — M4 DLinear-vol §C entry (issue #10908): NO BEATS (biais révélé par loss_fn=linear)
Updated: 2026-08-15 — M4 DLinear-vol §C re-run perte de précision (issue #11011): BEATS 3/3 (linear → mse : changement de jambe, pas de modèle)
Updated: 2026-08-14 — M15 LSTM-vol §C entry (issue #10941): NO BEATS (biais différentiel LSTM−HAR, même structure que M4)
Updated: 2026-08-15 — M15 LSTM-vol §C re-run perte de précision (issue #11034): 2/3 BEATS, 1/3 INCONCLUSIVE, 0/3 NO BEATS
Updated: 2026-08-24 — M4 DLinear-vol §C re-run dé-biaisé + DM recentré (issue #12734): 2/3 BEATS, 1/3 INCONCLUSIVE — le 3/3 de #11011 était gonflé par le biais de HAR
Updated: 2026-08-24 — M4 DLinear-vol §C extension ETF (Epic #1454): **NO BEATS** — l'edge brut (+16,75 %) est le biais² de la baseline HAR ; hors biais +0,3 %, dm_p_median 0,41
Updated: 2026-08-23 — backlog à déposer : M15 h=32 NO BEATS (#11468) et barreau ETF direction 9/9 NO BEATS (#11427) absents du header — cf sections respectives
Updated: 2026-08-24 — Re-validation hors-biais des keepers BTC (issues #11041/#11034/#11036) : M15 `refuted-de-biased` 3/3 (l'edge publié = biais² de HAR, var_ratio > 1 partout) ; M4 confirmé h=1/h=5, INCONCLUSIVE h=10 (p_median 0,0598, var_ratio < 1)
Updated: 2026-08-24 — M15 LSTM-vol patch persistance biais + slice 2/2 dé-biaisé symétrique (issue #12734): patch livré, run complet dispatché au prochain cycle
Updated: 2026-09-01 — PatchTST BTC log-RV revalidé contre HAR débiaisé train-only (#14081) : h=1 INCONCLUSIVE, h=5/h=10 NO BEATS ; var_ratio > 1 aux trois horizons
Updated: 2026-09-02 — M16 HAR asymétrique BTC revalidé contre HAR débiaisé train-only (#1454) : h=1 INCONCLUSIVE, h=5/h=10 BEATS ; verdict brut 3/3 réfuté
Updated: 2026-09-02 — M5 HMM regime-switching HAR, première entrée + revalidation hors biais (Epic #1454) : ETH h=1 **BEATS confirmé** (+8,7 % hors biais, 4/4 seeds, 4,1σ) ; BTC h=1 s'effondre de +7,0 % à +1,3 % (~82 % de l'edge était le biais de HAR) ; 4/6 NO BEATS
Updated: 2026-09-04 — M17 HAR-LJ-Asym BTC revalidé contre HAR débiaisé train-only (Epic #1454, lane myia-po-2026, c.951) : h=1 BEATS 4/4 confirmé (var_ratio 0,778 — gain de précision, pas un offset) ; h=5/h=10 INCONCLUSIVE 0/4 (var_ratio > 1) ; vs M12 4/4 BEATS aux trois horizons ; verdict BTC inchangé, base non-artéfactée par le biais HAR
Updated: 2026-09-04 — M17 HAR-LJ-Asym BTC REPAIR P0 c.953 (PR #14592, preflight po-2025 adjoint `msg-20260904T105224-z6f9d7` head 8167044f) : **calibration symétrique** sur LJ/HAR/M12 + `var(ddof=0)` + sanity `mse = bias²+var` à 1e-9 + `panel_hash` SHA256 sur fenêtre canonique 360 bars (BTC 4 seeds → 1 hash `86f36cb46f539c6d`) + naming `mse_har_raw`/`mse_har_debiased` (NaN si non-débiaisé). **Verdict révisé** : h=1 BEATS 4/4 (inchangé, var_ratio=0,778) ; h=5 INCONCLUSIVE 0/4 contre HAR **et** M12 (était 4/4 BEATS vs M12) ; h=10 BEATEN BY 0/4 contre HAR (MSE 0,464 > 0,366 HAR-débiaisé ; était INCONCLUSIVE 0/4). Le claim c.951 « 4/4 BEATS vs M12 aux trois horizons » ne tient plus sous calibration symétrique : la tête précédente de M17 sur M12 aux h=5/h=10 était portée par le gap de calibration, pas par un gain de précision. Detail dans `docs/M17_HAR_LJ_ASYM.md` section c.953. `panel_hashes_consistent=True`, OLS bit-identique par seed (DM-MSE p-values identiques 6 décimales).
Updated: 2026-09-05 — M17 HAR-LJ-Asym round-3 calibration (PR #14592, preflight po-2025 adjoint re-review head `b974f2721`, DM `msg-20260904T141944`) : **nombres c.953 ci-dessus SUPERSEDES** (signe du biais inversé `yhat - bias` → corrigé `yhat + bias`, application per-fold, M12 calibré `calibrate_bias=debias`, deux jambes HAR `mse_har_raw` != `mse_har_debiased`, `panel_hash` sur index+valeurs avec manifeste per (coin,horizon)). Détail dans `docs/M17_HAR_LJ_ASYM.md` section « Round-3 calibration (this PR) ». [M17 HAR-LJ-Asym BTC run] — pending live run post-merge; round-3 calibration implemented, code PR #14592.
Updated: 2026-09-05 — M17 HAR-LJ-Asym round-4 (PR #14592, adjoint re-review DM `msg-20260905T001520`, 3/6 PASS / 3/6 PARTIAL) : test OOS multi-fold discriminant `test_walk_forward_lj_asym_oos_target_invariance_multi_fold` (n_splits=3, biais per-fold **distincts**, invariance per-fold bit-identique rtol 1e-12, folds antérieurs inchangés, folds postérieurs = expanding-window retrain légitime asserté comme sensibilité, train-tail > 1.0 par fold) + provenance `bounds_train_test` (`{train_end_idx = n_splits·(n//(n_splits+1)), oos_start_idx = train_end+horizon, oos_end_idx}`) relayée par `_eval_one_coin` / `aggregate_verdicts` / manifeste (`bounds_per_coin_horizon`, `fc_lj_hash_per_fold` alignés sur `per_fold_bias`) ; placeholder `if False else None` supprimé. Tests 22 → 24 verts, suite 1194 passed / 0 failed. **[M17 HAR-LJ-Asym BTC run] LIVRÉ (round-4 code) — `python har_lj_asym.py --coins BTC-USD --skip-remote --debias --horizons 1 5 10 --seeds 0 7 42 99` en 467.9 s** : h=1 **BEATS 4/4** vs HAR et M12 (p<1e-6, mean_loss_diff<0, `_coherent_beats()` strict ✓) ; h=5/h=10 INCONCLUSIVE 0/4 (p>0.05, mean_loss_diff>0 ⇒ cohérent INCONCLUSIVE). Bornes effectives BTC : `train_end=1890` (5 folds × 378 jours), `n_oos=378-382`, `n_total=2272` jours. Bit-identity cross-seed OK (`per_fold_bias` et `fc_lj_hash_per_fold` identiques sur les 4 seeds, `bounds_consistent_across_seeds=True`). Précédent c.953 `h=1 BEATS p=0.839708` réfuté — sous round-3+4 calibration le verdict reste BEATS mais devient réellement significatif. Détail dans `docs/M17_HAR_LJ_ASYM.md` section « Live BTC run (concern b — this PR) ». Manifest `scripts/results/m17_har_lj_asym.json` régénéré ; meta `manifest_m17_har_lj_asym.json` mis à jour avec `concern_addressing` round-3 + round-4.
Updated: 2026-09-05 — M18 TimesFM 2.5 zero-shot première entrée §C (issue #14768, lane myia-po-2026) : **vs Log-HAR 5/6 BEATS, 1/6 INCONCLUSIVE (BTC h=22, log-HAR numériquement meilleur mais p=0,23), 0/6 NO BEATS** — réserves : ETH h=22 p=0,0445 limite. Horizons 1/5/22 j, walk-forward 5 folds, seeds bit-identiques (GPU déterministe), débiais symétrique, DM conjonction MSE (#11010). Vrai checkpoint attesté (SHA 1d952420fba8, 43 720 séries, fail-explicit). Calibration quantile native : couverture 80 % à ±0,026 du nominal. HAR en niveaux dégénère en quasi-persistence (MSE identiques à 6 décimales, hashs distincts). Détail section M18 + `docs/M18_TimesFM.md`.

Total checkpoints: 70 (20 legacy ARCHIVED + 50 panier baselines)

## M18 TimesFM 2.5 zero-shot — première entrée §C (2026-09-05) — issue #14768

Benchmark TimesFM 2.5-200M (`google/timesfm-2.5-200m-pytorch` SHA
`1d952420fba8`, 43 720 séries servies, contrat fail-explicit sans fallback)
contre persistence / EWMA / Log-HAR / HAR-RV sur RV crypto quotidienne,
horizons **1/5/22 j** (protocole #14768), walk-forward 5 folds, seeds
{0,7,42,99} **bit-identiques** (inférence GPU déterministe — jambe σ
dégénérée, précédent M17 OLS), débiais symétrique per-fold (queue
d'entraînement 60 j, `yhat + bias`), DM deux jambes (#11010) : conjonction
sur MSE, `linear` = diagnostic biais. Script `scripts/m18_tsfm_benchmark.py`
(+31 tests), manifeste `scripts/results/m18_tsfm_benchmark.json`, doc
`docs/M18_TimesFM.md`.

| Coin | h | vs persistence | vs ewma | vs log_har | vs har_rv |
|---|---:|---|---|---|---|
| BTC | 1 | **BEATS** +40,7 % | **BEATS** +20,1 % | **BEATS** +19,7 % | **BEATS** +40,7 % |
| BTC | 5 | **BEATS** +56,2 % | INCONCLUSIVE +5,4 % (p=0,116) | **BEATS** +8,5 % (p=0,0015) | **BEATS** +56,2 % |
| BTC | 22 | **BEATS** +46,5 % | **BEATS** +10,7 % | INCONCLUSIVE −4,8 % (p=0,232) | **BEATS** +46,5 % |
| ETH | 1 | **BEATS** +30,6 % | **BEATS** +10,5 % | **BEATS** +7,6 % | **BEATS** +30,6 % |
| ETH | 5 | **BEATS** +49,7 % | INCONCLUSIVE +4,1 % | **BEATS** +10,7 % | **BEATS** +49,7 % |
| ETH | 22 | **BEATS** +47,2 % | **BEATS** +11,9 % | **BEATS** +12,5 % (p=0,0445 ⚠ limite) | **BEATS** +47,2 % |

**Verdict contre la baseline de référence (Log-HAR) : 5/6 BEATS, 1/6
INCONCLUSIVE, 0/6 NO BEATS** — solide sur 4 cellules (p ≤ 0,0015), deux
réserves honnêtes : BTC h=22 INCONCLUSIVE (log-HAR numériquement meilleur
−4,8 % mais non significatif), ETH h=22 BEATS au bord du seuil (p=0,0445).
Calibration quantile native remarquable : couverture 80 % mesurée
0,774-0,814 pour nominal 0,80, zero-shot sans ajustement. Trou empirique :
HAR en niveaux dégénère en quasi-persistence sur ce panel (MSE égales à
6 décimales, hashs distincts — artefact connu, pas un bug). Coûts :
non applicables au forecast pur, aucun claim Sharpe/P&L. Aucun claim
d'alpha : TimesFM entre comme forecasteur de volatilité, l'étape
économique est hors scope #14768.

## M16 HAR asymétrique — re-test débiaisé BTC (2026-09-02) — Epic #1454

Le keeper historique M16 annonçait **3/3 BEATS** sur BTC face à HAR classique brut. Le re-test applique
la même calibration train-only de 60 observations aux deux modèles, persiste leurs prévisions OOS sur
les mêmes dates et évalue `dm_verdict(..., loss_fn="mse")`. Walk-forward expanding 5 folds, horizons
{1,5,10}, quatre seeds {0,7,42,99}. OLS étant déterministe, les seeds sont bit-identiques : `edge/σ`
cross-seed est **non applicable**, pas artificiellement infini.

| Horizon | MSE HAR débiaisé | MSE asym. débiaisé | edge | biais asym. | biais HAR | dm_p_median | Verdict |
|---:|---:|---:|---:|---:|---:|---:|---|
| h=1 | 0,843774 | 0,848154 | −0,52 % | −0,005109 | −0,003880 | 0,244862 | **INCONCLUSIVE** |
| h=5 | 0,417886 | 0,403593 | +3,42 % | −0,003967 | −0,001552 | 0,011363 | **BEATS** |
| h=10 | 0,389457 | 0,369614 | +5,10 % | −0,004194 | −0,002419 | 0,005123 | **BEATS** |

**Décomposition `MSE = biais² + variance`** : les biais résiduels sont proches de zéro (biais² ≤ 2,6e-5),
donc l'écart restant porte essentiellement sur la variance. Le résultat brut était gonflé, surtout aux
horizons longs (+23,6 %/+36,7 % → +3,4 %/+5,1 %), mais le signal ne disparaît pas : **2/3 BEATS,
1/3 INCONCLUSIVE, 0/3 NO BEATS**. M16 BTC reste un keeper moyen/long horizon ; h=1 est retiré du claim.

- **Run** : `python scripts/har_asymmetric.py --coins BTC-USD --horizons 1 5 10 --seeds 0 7 42 99 --n-splits 5 --skip-remote --debias --calibration-size 60 --out-json scripts/results/m16_har_asymmetric_btc_debiased.json`
- **Notebook** : `m3_har_asymmetric_semivariance.ipynb`, 8/8 cellules code exécutées, recalcul indépendant depuis les séries persistées
- **Coûts** : non applicables au verdict de forecast pur ; aucun claim Sharpe/P&L

## M4 DLinear-vol — entrée §C (2026-08-14) — issue #10908

Première entrée du registre conforme **intégralement** au barème `pr-review-discipline.md` §C :
walk-forward ≥ 5 folds, ≥ 4 seeds, Diebold-Mariano `loss_fn="linear"` (perte signée), conjonction
edge ≥ 2σ **et** `dm_p_median < 0,05` (reportés séparément), baselines + coûts documentés, verdict
honnête. Notebook : `m4_dlinear_vol_sc_validation.ipynb` (outputs C.2, 0 erreur).

**Modèle** : DLinear (Zeng et al. AAAI 2023) — `y_hat = Linear(seq_len=22 -> horizon)`, ~22 params.
**Univers** : BTC-USD (Bitstamp hourly 2014→2024, 2278 jours de RV). Coin le plus riche du panel
M4 (les autres ~725 j restent hors barème §C).
**Cible** : log-RV quotidien. **Baselines** : HAR (Corsi 2009, benchmark de référence) +
persistence (random walk, mesurée section 4 du notebook). **DM** : `scripts/dm_test.py`,
HAC Newey-West + correction HLN, `loss_fn="linear"` (#10228).

| Horizon | edge (red MSE moy, %) | σ cross-seed | dm_p_median | Verdict §C |
|---------|----------------------|--------------|-------------|------------|
| h=1 | +15,3 % | 0,04 | 0,00e+00 | **NO BEATS** |
| h=5 | +28,3 % | 0,10 | 0,00e+00 | **NO BEATS** |
| h=10 | +38,3 % | 0,20 | 0,00e+00 | **NO BEATS** |

**Lecture honnête (le piège §C, mesure #10938)** : DLinear bat HAR de 15 à 38 % en MSE (perte
symétrique). Sous la perte **signée** (`linear`), `d_mean = biais_DL − biais_HAR` (identité
dm_test.py L123-135) : le différentiel `dm_mean_loss_diff ≈ +0,22` log-RV (h=1) est **porté par
le biais de HAR**, pas par DLinear. Mesuré (run dé-biaisé #10938) : `har_bias_oos = −0,227`
(h=1, HAR **sous-prévient** log-RV), `bias_DL = dm_mean_loss_diff + har_bias_oos ≈ 0` (DLinear
**non biaisé**). L'hypothèse initiale « retirer le biais² porterait l'edge à ~21/52/74 % » est
**réfutée** : le biais² (~0,051 h=1) est dans le MSE de **HAR**, pas dans celui de DLinear —
dé-biaiser DLinear ne libère rien (MSE brut = dé-biaisé, bit-identique), dé-biaiser HAR ramènerait
son MSE à ~0,836 et l'edge à ~10 %. Sous §C tel qu'écrit, la conjonction n'est pas tenue.
**Verdict §C : NO BEATS (3/3 horizons)** — règle de dominance (seed BEATEN → NO BEATS) appliquée.
**Coûts de transaction** : prévision (MSE log-RV), **aucune stratégie dérivée** → coût non imputé ;
borne crypto 10 bps si conversion future en overlay de vol-timing (note, pas un claim).
**Persistence MSE** (même série, même découpage) : h=1 `1,173` · h=5 `0,968` · h=10 `0,930` —
DLinear et HAR battent tous deux le plancher naïf.

- **Data hash** : `sha256 38a4e973955cf9f8527c3096931aa958bfae09580737c909450504b21502c573`
  (`Bitstamp_BTCUSD_1h_2014-20240808.csv`, CryptoDataDownload)
- **Run** : `python dlinear_vol.py --horizons 1 5 10 --seeds 0 7 42 99 --loss-fn linear --skip-remote --coins BTC-USD --out-json results/m4_dlinear_vol_btc_sc.json` (3508 s)
- **Verdict global** : 0/3 BEATS, 0/3 INCONCLUSIVE, **3/3 NO BEATS**

### M4 DLinear-vol — re-run §C dé-biaisé (2026-08-14, issue #10938)

Re-run du barème §C avec dé-biaisage explicite (mesure acceptance #1 de #10938 : attribution du
`dm_mean_loss_diff` sous perte signée). Verdict inchangé — l'attribution de la « Lecture honnête »
ci-dessus est la **correction** mesurée.

**Méthode** : `_train_bias` estime le biais signé moyen modèle-vs-cible **sur fold train uniquement**
(jamais sur test, acceptance #2) ; il est soustrait aux prédictions de test ; le biais OOS de HAR
(`har_bias_oos`) est persisté par horizon. Config identique au run brut (`refit_every` 22, 4 seeds,
5 folds).

| Horizon | `dm_mean_loss_diff` | `har_bias_oos` | ⇒ `bias_DL` dérivé | MSE DL dé-biaisé vs brut |
|---------|--------------------:|---------------:|--------------------|--------------------------|
| h=1 | +0,2282 | −0,2266 | ≈ 0 (+0,002) | 0,7516 = 0,7516 (bit-identique) |
| h=5 | +0,3512 | −0,3432 | ≈ 0 (+0,008) | 0,3740 = 0,3740 |
| h=10 | +0,4513 | −0,4502 | ≈ 0 (+0,001) | 0,3521 = 0,3521 |

**Lecture** : `d_mean = biais_DL − biais_HAR` — le différentiel linéaire est porté par le biais de
**HAR** (sous-prévision log-RV −0,23 à −0,45 selon l'horizon) ; DLinear est **non biaisé**
(`bias_DL ≈ 0` sur les 3 horizons). Dé-biaiser DLinear ne change rien (son MSE est déjà dé-biaisé
au 1/1000ᵉ) ; dé-biaiser HAR ramènerait son MSE de ~0,888 à ~0,836 (h=1) et l'edge de ~15 % à
~10 %. L'hypothèse « retirer le biais² → edge ~21/52/74 % » est **réfutée** par la mesure.

- **Run** : `python dlinear_vol.py --horizons 1 5 10 --seeds 0 7 42 99 --loss-fn linear --skip-remote --coins BTC-USD --debias --out-json results/m4_dlinear_vol_btc_sc_debiased.json` (3963,8 s)
- **Notebook** : section 7 de `m4_dlinear_vol_sc_validation.ipynb` (recalcul indépendant de la conjonction + décomposition, outputs C.2)
- **Verdict §C dé-biaisé** : **3/3 NO BEATS** — identique au brut (la dominance seed-BEATEN est une propriété du MSE, pas du biais).

### M4 DLinear-vol — re-run §C perte de précision (2026-08-15, issue #11011)

Re-run du barème §C **amendé** (#11010) sous `--loss-fn mse` (jambe de précision). Le verdict
NO BEATS de #10930 était instrumenté sur `linear`, désormais **contrôle de biais séparé** — la
conjonction doit porter sur une perte de précision (`mse`/`mae`). Cette entrée rend la conjonction
§C sur MSE : edge ≥ 2σ cross-seed **et** `dm_p_median < 0,05`.

| Horizon | edge (red MSE moy, %) | σ cross-seed | dm_p_median | Verdict §C |
|---------|----------------------|--------------|-------------|------------|
| h=1 | +15,3 % | 0,04 | 0,00e+00 | **BEATS** |
| h=5 | +28,3 % | 0,10 | 2,25e-10 | **BEATS** |
| h=10 | +38,3 % | 0,20 | 2,39e-09 | **BEATS** |

**Lecture** : sous `mse`, le DM teste l'égalité des pertes quadratiques (précision pure) — le
`d_mean = biais_DL − biais_HAR` de la jambe linéaire n'intervient plus dans le verdict. Les
4 seeds de chaque horizon passent **BEATS baseline** (0 BEATEN) et la conjonction est tenue 3/3 :
l'edge de précision (+15 à +38 %) est **significatif** sous la perte quadratique. Le changement de
verdict (NO BEATS → BEATS) vs #10930 est **mécanique** : mêmes MSE, mêmes seeds, même découpage —
ce qui change est la question posée au DM (biais sous `linear`, précision sous `mse`), pas le
modèle. Rapport de biais séparé (mesuré #10938, inchangé) : `har_bias_oos` −0,2266/−0,3432/−0,4502
(h=1/5/10), `bias_DL ≈ 0` — le différentiel linéaire reste porté par le biais de HAR, DLinear
non biaisé.

- **Run** : `python dlinear_vol.py --horizons 1 5 10 --seeds 0 7 42 99 --loss-fn mse --skip-remote --coins BTC-USD --out-json scripts/results/m4_dlinear_vol_btc_sc_mse.json` (2341,4 s)
- **Notebook** : section 8 de `m4_dlinear_vol_sc_validation.ipynb` (recalcul indépendant de la conjonction mse, outputs C.2)
- **Verdict §C (jambe de précision)** : **3/3 BEATS** (contre 3/3 NO BEATS sous linear — changement de jambe, pas de modèle)

### M4 DLinear-vol — re-run §C dé-biaisé + DM recentré (2026-08-24, issue #12734)

Run **symétrique** demandé par #12734 : baseline HAR **débiaisée** (soustraction de `har_bias_oos`
des prévisions HAR OOS, jamais du biais train — pas de fuite, acceptance #2 de #10938) **et**
DM sur **erreurs recentrées** `loss_fn="mse"` (centrage `e − mean(e)` par prévisionneur). Le
centrage annule le biais (`mean(loss_fn="linear") = 0`) donc le DM compare les variances
uniquement — c'est la jambe **précision** que l'amendement §C #11010 rend obligatoire pour
porter le verdict `BEATS`, appliquée ici **après dé-biaisage symétrique**.

Pourquoi ce n'est pas une redite du mse de la section 8 / REGISTRY précédent : la section 8
mesure la précision mais sur HAR **biaisée** — la baseline gonfle son MSE par son propre biais
(`MSE = biais² + variance`, donc MSE brut surestime la variance de HAR). Cette entrée élimine
le biais **sur les deux côtés** : DLinear brut, HAR débiaisée, puis DM recentré.

| Horizon | edge (red MSE vs HAR deb, %) | σ cross-seed | dm_p_median (centered) | var ratio DL/HAR_deb | Verdict §C |
|---------|----------------------------|--------------|------------------------|----------------------|-------------|
| h=1  | +10,1 % | 0,15 | 1,5e-09 | 0,899 | **BEATS** |
| h=5  | +7,3 %  | 0,23 | 9,7e-05 | 0,927 | **BEATS** |
| h=10 | +3,7 %  | 0,19 | 1,0e-01 | 0,963 | **INCONCLUSIVE** |

**Décomposition biais² + variance** : `har_bias_oos` −0,2266 / −0,3432 / −0,4502 log-RV
(h=1/5/10, MESURÉ sur test OOS — biais `HAR` en sous-prévision de log-RV). Après dé-biaisage
HAR, le résiduel biais²/variance chute à 5,8 % (h=1) → 22,6 % (h=5) → 35,5 % (h=10) — le
dé-biaisage élimine bien le biais dominant sur h=1 mais le résiduel augmente avec l'horizon
(le biais OLS d'une régression HAR est plus dispersé sur des fenêtres longues). `var_ratio =
var_DL / var_HAR_debiased` reste < 1 sur les 3 horizons ⇒ DLinear **plus précis** (variance
plus petite) que HAR une fois son biais soustrait.

**Verdict M4 BTC (#12734 acceptance)** : M4 **survit hors biais sur h=1 et h=5**, devient
**INCONCLUSIVE sur h=10** après dé-biaisage symétrique. Lecture honnête : le verdict
**3/3 BEATS** de la section 8 (#11011, mse asymétrique) était **gonflé par le biais de
HAR** — sans le biais, l'edge MSE se réduit de +38 % à +3,7 % (h=10) et le DM centered
n'atteint plus le seuil `p < 0,05` (`p = 0,10`, juste au-dessus). Le verdict §C recentré
est **2/3 BEATS, 1/3 INCONCLUSIVE, 0/3 NO BEATS** — mesurable, défendable, et **plus strict**
que les 3/3 BEATS de la mse asymétrique. M4 BTC keeper reste défendable : 2 horizons
passent la conjonction, le 3ᵉ est statistiquement insuffisant (pas un échec).

- **Run** : `python scripts/btc_vol.py --horizons 1 5 10 --seeds 0 7 42 99 --epochs 50 --out-json scripts/results/m4_dlinear_vol_btc_sc_debiased_recentered.json` (1776,4 s ≈ 30 min CPU, 12 combos — artefact régénéré par #14362, cf. correction ci-dessous ; le run initial #12734 mesurait 1786,9 s)
- **Notebook** : section 9 de `m4_dlinear_vol_sc_validation.ipynb` (recalcul indépendant de la conjonction recentrée, décomposition biais²+variance, outputs C.2)
- **Verdict §C recentré** : **2/3 BEATS, 0/3 NO BEATS, 1/3 INCONCLUSIVE** (vs 3/3 BEATS mse asymétrique #11011 — la symétrie du dé-biaisage **réduit** l'edge sur h longs, ne le fabrique pas)

**Correction #14362 (2026-09-02) — la jambe de sanité était silencieusement recentrée.** L'entrée
ci-dessus décrit une seconde jambe DM « RAW » censée reproduire le keeper #11011 sur pertes
brutes. Elle passait par `_dm_centered_mse`, comme la jambe de verdict. Or les deux séries HAR ne
diffèrent que d'une **constante** (`har_errors_debiased = har_errors − har_bias_oos`) et le
recentrage par la moyenne propre l'annule exactement — les deux jambes rendaient le **même
nombre**, bit-identiques sur **12 lignes sur 12** de l'artefact publié. Ses p-médianes
(1,545e-09 / 9,660e-05 / 1,021e-01) reproduisaient `dm_centered_p_median`, pas le keeper ; à h=10
elle affichait `INCONCLUSIVE` là où le keeper qu'elle devait retrouver publie **BEATS** à
p = 2,39e-09. Un contrôle qui suit la mauvaise cible n'en est pas un.

Après correction (champ renommé `dm_uncentered_vs_har_raw_*`, DM **non centré** sur erreurs
intactes), artefact régénéré à configuration identique — la jambe **retrouve** le keeper :

| h | jambe corrigée p_median | keeper #11011 publié | verdicts |
|---|---|---|---|
| 1  | **0,000e+00** | 0,00e+00 | BEATS 4/4 |
| 5  | 1,435e-10 | 2,25e-10 | BEATS 4/4 |
| 10 | 3,083e-09 | 2,39e-09 | **BEATS 4/4** (était INCONCLUSIVE) |

L'accord est **de rang de grandeur et de verdict, pas bit-à-bit** sur h=5/h=10 (facteur < 2) : le
keeper provient d'un entraînement DLinear distinct, les erreurs du modèle ne sont pas les mêmes
séries. C'est l'accord attendu d'une reproduction indépendante, pas d'un rejeu.

**Ce que la correction ne change pas** : `dm_centered_stat` revient **bit-identique sur 12/12
lignes** (Δ max = 0,000e+00) sur le run régénéré — le défaut portait sur un champ de **diagnostic**,
jamais sur la conjonction §C. Le **verdict §C recentré reste 2/3 BEATS, 1/3 INCONCLUSIVE**, et M15
reste `refuted-de-biased` 3/3. Ce qui était perdu, c'est la capacité de le contrôler. Le champ n'est
agrégé nulle part (`aggregated` ne porte que `dm_centered_p_median`) — c'est ce qui a laissé le
défaut invisible ; suivi en **#14390**.

**Confirmation indépendante #11036 (re-validation ai-01, lane #1454, 2026-08-24)** : re-validation
sur les séries du run mse #11011 persistées par combo (M4 déterministe, CPU) — MSE/DM
**bit-identiques au keeper sur les 12 combos** (moyennes 0,7518/0,3740/0,3521 = valeurs publiées).
Jambe recentrée : h=1 **+10,11 %** (σ 0,04, p_median 2,3e-09, 0 beaten) ; h=5 **+7,48 %** (σ 0,13,
p_median 9,1e-05, 0 beaten) ; h=10 +4,31 % (edge/2σ = 6,9 MAIS **p_median 0,0598** — 3 seeds
p > 0,05, un seul 0,047). **Verdict #11036 : `confirmed` h=1/h=5, `INCONCLUSIVE` h=10** — la
conjonction échoue de justesse sur la jambe DM à h long, cohérent avec la mesure #12734 ci-dessus
(p 0,10 sur run ré-entraîné indépendant).

**Note sur M15 BTC (slice 2/2 de #12734)** : le constat d'invérifiabilité post-hoc est **levé** —
rerun complet 12/12 avec persistance des séries `pred_lstm`/`pred_har`/`pred_target` par combo
(instrument PR #12745), verdict mesuré : **`refuted-de-biased` 3/3** — section dédiée ci-dessous
(issues #11041/#11034).

## M15 LSTM-vol — entrée §C (2026-08-14) — issue #10941

2e entrée du registre conforme au barème `pr-review-discipline.md` §C (suite #10908/#10930) :
walk-forward ≥ 5 folds, ≥ 4 seeds, Diebold-Mariano `loss_fn="linear"` (perte signée), conjonction
edge ≥ 2σ **et** `dm_p_median < 0,05` (reportés séparément), baselines + coûts documentés, verdict
honnête. Notebook : `m15_lstm_rv_sc_validation.ipynb` (outputs C.2, 0 erreur).

**Modèle** : LSTM (Hochreiter & Schmidhuber 1997) — `LSTM(hidden=64, layers=1, window=22) -> horizon`,
~17 729 params, Adam lr=1e-3, 100 epochs max (patience 10).
**Univers** : BTC-USD (Bitstamp hourly 2014→2024, 2278 jours de RV). Coin le plus riche du panel
M15 (les autres ~725 j restent hors barème §C).
**Cible** : log-RV quotidien. **Baselines** : HAR (Corsi 2009, benchmark de référence) +
persistence (random walk, mesurée section 4 du notebook). **DM** : `scripts/dm_test.py`,
HAC Newey-West + correction HLN, `loss_fn="linear"` (#10228).
**Cadence de refit** : `--refit-every 110` (vs 22 legacy) — à 22 j, ~85 LSTM retraînés par combo
(~50 min/combo sur RTX 3070) serait infeasible pour un sweep multi-seed §C de 12 combos. La cadence
110 j est un hyperparamètre de walk-forward légitime, reproductible, documenté dans le notebook.

| Horizon | edge (red MSE moy, %) | σ cross-seed | dm_p_median | Verdict §C |
|---------|----------------------|--------------|-------------|------------|
| h=1 | −0,4 % | 3,67 | 3,08e-09 | **NO BEATS** |
| h=5 | +13,3 % | 4,46 | 0,00e+00 | **NO BEATS** |
| h=10 | +20,1 % | 4,11 | 0,00e+00 | **NO BEATS** |

**Lecture honnête (le piège §C, même structure que M4)** : LSTM bat HAR de 13 à 20 % en MSE sur
h=5/h=10 (perte symétrique) mais la perte **signée** (`linear`) révèle un **biais différentiel**
LSTM−HAR — les 4 seeds de chaque horizon sont **BEATEN BY baseline** (`dm_p_median < 3,1e-09`).
h=1 est plus ambigu : 2 seeds améliorent le MSE (−2,7/−3,9 %) mais 2 seeds le dégradent (+3,6/+4,4 %)
→ edge moyen ≈ 0 (−0,4 %). Le DM signé détecte ce biais de niveau des prévisions (différentiel
LSTM−HAR) exactement comme pour DLinear : sous `loss_fn="linear"`, un modèle qui sous-prévoit
log-RV est mécaniquement « battu » — l'edge MSE réel ne se convertit pas en verdict §C. Conjonction
non tenue partout. **Attribution du biais non mesurée dans ce run** (`mean_loss_diff = bias_LSTM −
bias_HAR`, `har_bias_oos` non persisté ici) : cf #10938/#10966 où HAR porte l'essentiel sur la même
cible.
**Verdict §C : NO BEATS (3/3 horizons)** — règle de dominance (seed BEATEN → NO BEATS) appliquée.
**Coûts de transaction** : prévision (MSE log-RV), **aucune stratégie dérivée** → coût non imputé ;
borne crypto 10 bps si conversion future en overlay de vol-timing (note, pas un claim).
**Persistence MSE** (même série, même découpage) : h=1 `1,173` · h=5 `0,968` · h=10 `0,930` —
LSTM et HAR battent tous deux le plancher naïf.

- **Data hash** : `sha256 38a4e973955cf9f8527c3096931aa958bfae09580737c909450504b21502c573`
  (`Bitstamp_BTCUSD_1h_2014-20240808.csv`, CryptoDataDownload)
- **Run** : `python m15_lstm_rv.py --coins BTC-USD --seeds 0 1 7 42 --horizons 1 5 10 --loss-fn linear --refit-every 110 --output results/m15_lstm_rv_btc_sc` (2096 s, resume depuis checkpoint 5/12)
- **Verdict global** : 0/3 BEATS, 0/3 INCONCLUSIVE, **3/3 NO BEATS**

### M15 LSTM-vol — re-run §C perte de précision (2026-08-15, issue #11034)

Re-run du barème §C **amendé** (#11010) sous `--loss-fn mse` (jambe de précision). Le verdict
NO BEATS de #10941 était instrumenté sur `linear`, désormais **contrôle de biais séparé** — la
conjonction doit porter sur une perte de précision (`mse`/`mae`). Cette entrée rend la conjonction
§C sur MSE : edge ≥ 2σ cross-seed **et** `dm_p_median < 0,05`.

| Horizon | edge (red MSE moy, %) | σ cross-seed | dm_p_median | Verdict §C |
|---------|----------------------|--------------|-------------|------------|
| h=1 | -0,7 % | 3,70 | 3.63e-01 | **INCONCLUSIVE** |
| h=5 | +14,9 % | 4,64 | 4.06e-02 | **BEATS** |
| h=10 | +18,8 % | 4,72 | 1.83e-02 | **BEATS** |

**Lecture** : sous `mse`, le DM teste l'égalité des pertes quadratiques (précision pure) — le
`d_mean = biais_LSTM − biais_HAR` de la jambe linéaire n'intervient plus dans le verdict, et la
règle de dominance (seed BEATEN) ne se déclenche plus : les seeds BEATEN du run linear étaient
l'artefact du biais différentiel. Contrairement au re-run M4 (#11036, MSE bit-identiques), ce
sweep ré-entraîne les LSTM (cuDNN non déterministe sur GPU) : les edges restent proches de #10941
(± 1,6 pt) — l'écart dominant entre les deux runs est bien la **jambe DM**, pas le modèle.
Rapport de biais séparé (contrôle §C(7), conservé) : la jambe linear #10941 reste le contrôle
(`dm_p_median < 3,1e-09`, seeds BEATEN sur h=5/h=10) ; l'attribution du biais n'est pas mesurée
dans le run M15 (`har_bias_oos` non persisté ici) — sur la même cible, #10938/#10966 montrent
que HAR porte l'essentiel (`har_bias_oos` −0,23/−0,34/−0,45).

- **Run** : `python m15_lstm_rv.py --coins BTC-USD --seeds 0,1,7,42 --horizons 1,5,10 --loss-fn mse --refit-every 110 --output results/m15_lstm_rv_btc_sc_mse` (1563 s, resume depuis checkpoint 9/12)
- **Notebook** : section 7 de `m15_lstm_rv_sc_validation.ipynb` (recalcul indépendant de la conjonction mse, outputs C.2)
- **Verdict §C (jambe de précision)** : **2/3 BEATS, 1/3 INCONCLUSIVE, 0/3 NO BEATS** (contre 3/3 NO BEATS sous linear — changement de jambe, pas de modèle)

### M15 LSTM-vol — re-validation hors-biais (2026-08-24, issues #11041/#11034) — `refuted-de-biased` 3/3

Re-validation du keeper M15 BTC sur la jambe que #12684/#12695 ont rendue obligatoire : DM
`loss_fn="mse"` sur **erreurs recentrées** (`e − mean(e)` par prévisionneur — le centrage annule
le biais, le DM compare les variances) + décomposition `MSE = biais² + variance` par seed.
Rerun complet **12/12 combos** (3 horizons × 4 seeds 0/1/7/42, config harness #11034 :
`refit-every 110`, walk-forward, GPU RTX 4090, 2782 s) avec persistance des séries par combo —
l'invérifiabilité post-hoc notée dans les entrées M15 précédentes est levée.

| Horizon | edge brut (mse) | edge recentré | var_ratio LSTM/HAR | seeds BEATEN (rec) | dm_p_median (rec) | Verdict recentré |
|---------|-----------------|---------------|--------------------|--------------------|-------------------|------------------|
| h=1  | −0,21 % (INCONCLUSIVE) | **−5,73 %**  | **1,057** | 1/4 (p 0,040) | 0,205 | **NO BEATS** |
| h=5  | +13,95 % (BEATS)        | **−10,70 %** | **1,107** | 2/4 (p 0,0036/0,014) | 0,090 | **NO BEATS** |
| h=10 | +17,28 % (BEATS)        | **−27,22 %** | **1,272** | 3/4 (p 0,028/0,0015/0,0047) | 0,016 | **NO BEATS** |

**Rapport de biais signé (contrôle §C(7))** — LSTM : −0,064/−0,039/−0,056 ; HAR :
−0,227/−0,343/−0,450 (h=1/5/10). HAR sous-prévoit le log-RV sur les 3 horizons ; le LSTM est
moins biaisé mais **plus dispersé** (`var_ratio > 1` partout).

**Lecture** : la jambe brute **reproduit le keeper publié** avant relecture hors-biais — h=5
+13,95 % (vs +14,9 % #11034), h=10 +17,28 % (vs +18,8 %), h=1 INCONCLUSIVE (−0,2 % vs −0,7 %) :
le rerun est fidèle, il n'a pas été sélectionné pour favoriser la réfutation. Mais une fois le
biais² retiré symétriquement (erreurs recentrées des deux côtés), l'edge s'inverse : **3/3 NO
BEATS** par la règle de dominance (1, 2 puis 3 seeds BEATEN avec l'horizon). L'edge publié était
le **biais² de la baseline HAR** — même structure exacte que la réfutation ETF #12684/#12695.
**Verdict #11041/#11034 : `refuted-de-biased` (3/3 horizons)** — le M15 LSTM-vol n'est pas un
keeper : sa seule propriété réelle est d'être moins biaisé que HAR, au prix d'une variance
supérieure.

**Le discriminant est le ratio de variance, pas la p-value brute.** M4 DLinear BTC survit hors
biais parce que `var_DL / var_HAR = 0,899/0,925/0,957 < 1` — l'edge recentré h=1/h=5 (+10,1 %/
+7,5 %, DM p ≤ 9,1e-05) est une vraie réduction de variance. Le M15 échoue parce que
`var_LSTM / var_HAR = 1,057/1,107/1,272 > 1` — le LSTM n'est **pas plus précis** que HAR, seulement
moins biaisé. Toute la différence entre les deux verdicts de keepers était lisible dans cette
colonne avant tout test de significativité ; c'est elle que toute nouvelle entrée vol doit
désormais rapporter (cf instrument #12745 : la décomposition est exécutable sans ré-entraînement
sur les séries persistées).

**Portée — et ce que cette entrée ne couvre PAS** : le renversement M15 est mesuré sur **BTC**
(ce run) et **ETF SPY/TLT/GLD** (#12695 : 9/9 cellules négatives hors biais), les deux terrains
log-RV du pipeline ; il est général à la famille M15 (LSTM h=64, window 22) sur la cible log-RV.
En revanche cette entrée **ne couvre pas** : (1) les autres architectures deep-seq (transformer,
mamba, iTransformer, MoE régimes, GNN — non re-validées hors biais ; leurs éventuels edges
restent à décomposer par le même instrument). PatchTST est désormais couvert séparément par
#14081 ci-dessous ; (2) la cible direction/rendement (ladder
#1409 L4 Decision Transformer, validation XRP DT — cible différente, verdict non touché) ;
(3) M4 DLinear lui-même, qui **survit** sur BTC (`confirmed` h=1/h=5) mais échoue sur ETF
(#12695) — l'edge M4 est spécifique au terrain crypto (RV BTC agrège 24 h de bars horaires vs
1 bar OHLC/jour en GK daily ETF), pas une propriété générale de DLinear ; (4) toute conversion
en stratégie de vol-timing avec coûts de transaction — verdict de prévision (MSE log-RV)
uniquement, aucune stratégie dérivée, borne crypto 10 bps non imputée.

- **Run** : rerun 12/12 → `results/m15_lstm_rv_btc_sc_mse_persist/` (2782 s) ; re-validation
  `results/btc_revalidation_recentred/revalidate_recentred.py` (jambes RAW/REC/LIN câblées
  explicitement — RAW = sanité reproduisant le keeper, REC = jambe verdict, LIN = contrôle de
  biais uniquement ; décomposition `mse = biais² + var` vérifiée au 1e-12 par seed). Artefacts
  hors repo (`results/` gitignoré) — instrument de persistance : PR #12745.
- **Verdict §C recentré** : **0/3 BEATS, 0/3 INCONCLUSIVE, 3/3 NO BEATS** — `refuted-de-biased`.

## PatchTST-vol BTC — revalidation hors biais (2026-09-01) — issue #14081

Première revalidation deep-seq hors M15 contre la baseline corrigée issue de #12684/#12734.
Le harnais `scripts/btc_patchtst.py` réutilise le modèle PatchTST (Nie et al., ICLR 2023), mais
porte sa propre cible log-RV et son vrai walk-forward expanding : le CLI directionnel historique
n'appliquait pas réellement son drapeau `--walk-forward`. Le défaut `--device` déclaré deux fois,
qui faisait échouer ce CLI avant tout entraînement, est corrigé et couvert par un test subprocess.

**Protocole réel** : BTC Bitstamp hourly 2014→2024, 2 278 jours de RV (2018-05-15→2024-08-08),
SHA-256 `38a4e973955cf9f8527c3096931aa958bfae09580737c909450504b21502c573` ; 5 folds expanding,
seeds {0,1,7,42}, horizons {1,5,10}, cible = moyenne du log-RV futur. PatchTST borné CPU :
`seq_len=64`, patch 16, stride 8, `d_model=32`, 4 heads, 1 couche, 10 epochs — 14 145 / 15 045 /
16 170 paramètres selon l'horizon. Un modèle est ajusté par fold et seed, normalisation et sélection
du meilleur epoch sur le train uniquement. HAR estime son biais signé sur une queue de calibration
antérieure au test (`calibrate_bias=True`) : aucun target du bloc test ne calibre sa propre baseline.
DM porte sur les erreurs recentrées avec `loss_fn="mse"` ; toutes les séries alignées par timestamp
sont persistées hors dépôt pour recalcul post-hoc.

| Horizon | edge PatchTST vs HAR débiaisé | σ cross-seed | dm_p_median recentré | var_ratio PatchTST/HAR | seeds BEATEN | Verdict |
|---|---:|---:|---:|---:|---:|---|
| h=1  | −4,23 %  | 1,32 pt | 0,313  | 1,041 | 0/4 | **INCONCLUSIVE** |
| h=5  | −16,35 % | 2,38 pt | 0,0366 | 1,159 | 3/4 | **NO BEATS** |
| h=10 | −22,86 % | 2,76 pt | 0,0253 | 1,220 | 4/4 | **NO BEATS** |

**Biais signés moyens PatchTST / HAR débiaisé** : h=1 −0,00475 / −0,00388 ; h=5 −0,04321 /
−0,00155 ; h=10 −0,05502 / −0,00242. HAR est effectivement recalé ; l'écart restant vient de la
variance. PatchTST porte une variance supérieure aux trois horizons (`var_ratio > 1`) et la
dégradation croît avec l'horizon. Le résultat h=1 ne sépare pas les modèles (4/4 DM inconclusifs) ;
h=5 et h=10 réfutent l'edge deep-seq, respectivement 3/4 et 4/4 seeds significativement battues.

- **Run** : `python scripts/btc_patchtst.py --device cpu --horizons 1 5 10 --seeds 0 1 7 42 --n-splits 5 --seq-len 64 --patch-len 16 --stride 8 --d-model 32 --n-heads 4 --n-layers 1 --epochs 10 --batch-size 32 --out-json results/btc_patchtst_har_debiased_cpu_20260901.json` — 115,9 s CPU, 12/12 combinaisons, 5 folds chacune.
- **Vérification** : 12 lignes JSON, 1 890 / 1 870 / 1 845 prédictions alignées par seed selon h ; longueurs erreurs/prédictions/timestamps identiques ; `MSE = biais² + variance` recalculé à tolérance numérique sur chaque ligne.
- **Verdict §C** : **0/3 BEATS, 1/3 INCONCLUSIVE, 2/3 NO BEATS**. Mesure de prévision uniquement : aucune stratégie de trading ni claim après coûts.

## M5 HMM regime-switching HAR — entrée §C + revalidation hors biais (2026-09-02) — Epic #1454

Première entrée REGISTRY de M5 : le modèle était documenté (`docs/M5_HMM_REGIME.md`, Cycle 25) et
portait un **BEATS vivant** (`ETH-USD h=1`, +9,6 %, 4/4 seeds) qu'aucun rapport de biais n'avait
audité — le document ne contenait aucune occurrence de `bias`/`biais`/`recentr`/`debias`, et M5
n'apparaissait pas ici. Le harnais ne persistait que des MSE agrégés : le verdict publié était
**invalidable post-hoc sans ré-entraînement**, exactement le constat que #12745 avait levé sur M4/M15.

**Protocole réel** : BTC Bitstamp hourly, 2 278 jours de RV (2018-05-15→2024-08-08) ; ETH Binance
hourly, 1 495 jours (2019-10-21→2023-12-14). HAR à régimes = HMM gaussien K=2 (hmmlearn, Viterbi sur
log-RV) + OLS à 8 coefficients (4 base + 4 termes d'interaction `I(regime=high)`) ; baseline = HAR
classique Corsi 3 paramètres. Walk-forward 5 folds expanding, refit tous les 22 jours, seeds
{0,7,42,99}, horizons {1,5,10} — 24 combinaisons, 331,6 s CPU (ni GPU ni réseau : HMM + OLS).
DM HAC `loss_fn="mse"`. La jambe hors biais recentre les erreurs **des deux côtés**
(`e − mean(e)`) et compare aussi l'edge contre une baseline dé-biaisée. Les jambes brutes publiées en
Cycle 25 sont recalculées à l'identique et **non modifiées**.

| Coin | h | edge brut | edge vs classic dé-biaisée | σ cross-seed | edge/σ | dm_p_median (rec.) | seeds BEATS / BEATEN (rec.) | Verdict hors biais |
|---|---:|---:|---:|---:|---:|---:|:---:|---|
| BTC-USD | 1  |  +7,0 % |  **+1,3 %** |  4,04 pt | **0,3σ** | 1,47e-03 | 3/4 · 0/4 | **INCONCLUSIVE** |
| BTC-USD | 5  | −11,1 % | **−43,5 %** |  9,37 pt | 4,6σ | 6,21e-06 | 0/4 · 4/4 | **NO BEATS** |
| BTC-USD | 10 | −28,3 % | **−99,0 %** | 21,18 pt | 4,7σ | 1,75e-09 | 0/4 · 4/4 | **NO BEATS** |
| ETH-USD | 1  |  +9,6 % |  **+8,7 %** |  2,11 pt | **4,1σ** | 1,14e-05 | 4/4 · 0/4 | **BEATS** |
| ETH-USD | 5  | −17,9 % | **−23,4 %** |  3,85 pt | 6,1σ | 6,16e-04 | 0/4 · 4/4 | **NO BEATS** |
| ETH-USD | 10 | −53,0 % | **−66,2 %** | 14,70 pt | 4,5σ | 4,10e-05 | 0/4 · 4/4 | **NO BEATS** |

**Rapport de biais signé (contrôle §C(7))** — régime / classic, biais² de la baseline en part de son
MSE : BTC −0,1811/−0,2266 (**5,8 %**), −0,2728/−0,3432 (**22,6 %**), −0,3624/−0,4502 (**35,5 %**) ;
ETH −0,0718/−0,0810 (**1,0 %**), −0,1091/−0,1290 (**4,5 %**), −0,1519/−0,1727 (**8,0 %**) — h=1/5/10.
Les deux modèles sous-prévoient le log-RV ; la part de biais de la baseline croît avec l'horizon.

**Lecture — le seul BEATS de M5 survit, et l'échec voisin change de cause.** `ETH h=1` ne perd que
0,9 pt au dé-biaisage (+9,6 → +8,7 %) et satisfait la conjonction §C complète (4/4 seeds sur la jambe
de précision, `dm_p_median` 1,14e-05, **4,1σ ≥ 2σ**) : c'est une vraie réduction de variance, pas la
miscalibration de la baseline. Le contraste avec M15 est net — même instrument, verdict opposé
(`refuted-de-biased` 3/3, #11041). En revanche `BTC h=1` s'effondre de +7,0 % à **+1,3 %** : **~82 %
de son edge apparent était le biais de la HAR BTC**, dont le biais² pèse 5,8 % du MSE. Le verdict brut
disait déjà INCONCLUSIVE mais l'imputait à la graine 7 ; hors biais, l'edge vaut **0,3σ** de la
dispersion cross-seed — l'effet n'existe pas, il n'est pas seulement instable. Enfin, dé-biaiser la
baseline **aggrave** les quatre configs longues (BTC h=10 : −28,3 → −99,0 %) : le biais de la HAR
masquait l'ampleur de la dégradation. La conclusion d'origine « nuisible à h≥5 » est renforcée.

**L'asymétrie BTC/ETH à h=1 appartient à la baseline, pas au modèle.** Même modèle, même instrument :
la HAR BTC porte 5,8 % de biais², la HAR ETH 1,0 % — d'où 82 % de biais dans l'edge BTC contre 9 %
dans l'edge ETH. Toute lecture cross-coin de M5 qui ignore cette colonne compare des baselines de
qualité différente.

**Comparabilité M4/M5 — même objet de baseline.** `hmm_regime_vol.py` et la chaîne
`btc_vol.py → dlinear_vol.py` importent le même `har_model.HARModel` (définition unique). Le biais OOS
BTC mesuré ici est **bit-identique** à `har_bias_oos` de l'artefact #12745 (−0,2265869503892514 /
−0,34317822065868814 / −0,45022101989096786 pour h=1/5/10, 17 chiffres). Ce n'est **pas** une
corroboration indépendante — c'est le même calcul appelé depuis deux harnais — mais cela vérifie le
câblage de l'instrumentation ajoutée ici et rend les edges M4 et M5 directement comparables sur BTC.

**Portée — ce que cette entrée ne couvre PAS** : (1) verdict de **prévision** (MSE log-RV)
uniquement — aucune stratégie de vol-timing dérivée, aucun coût de transaction imputé ; (2) K=2
états seulement (K≥3 non testé) ; (3) le défaut structurel noté en Cycle 25 — la prévision itérative
à h pas utilise un **unique** indicateur de régime pour tous les pas — est inchangé et reste
l'explication la plus plausible de la dégradation aux horizons longs, mais n'est pas isolé
expérimentalement ici ; (4) les séries alignées ne sont pas versionnées (option `--dump-series`,
CSV hors dépôt, 37 040 lignes pour la grille complète).

- **Run** : `python scripts/hmm_regime_vol.py --coins BTC-USD ETH-USD --horizons 1 5 10 --seeds 0 7 42 99 --out results/m5_hmm_regime_debiased/results_full.json --dump-series results/m5_hmm_regime_debiased/series_full.csv` — 331,6 s CPU, 24/24 combinaisons, 5 folds chacune, 30 lignes JSON (24 par seed + 6 agrégats).
- **Vérification** : `MSE = biais² + variance` recalculé par ligne (tolérance 1e-12) ; identité
  `d_brut − d_recentré = biais_a² − biais_b²` vérifiée numériquement (résidu ~1e-17) et scellée en
  test paramétré ; les six verdicts publiés ci-dessous sont rejoués depuis la machine d'états agrégée
  (`_aggregate_debiased_state`), avec contrôles négatifs 3/4 des deux côtés ; 45 tests dans
  `scripts/tests/test_hmm_regime_vol.py`, voisins `test_btc_vol.py` /
  `test_diebold_mariano.py` / `test_har_model.py` / `test_dlinear_debiased_edge.py` verts (57).
- **Verdict §C hors biais** : **1/6 BEATS (ETH h=1, `confirmed`), 1/6 INCONCLUSIVE, 4/6 NO BEATS**.

## M4 DLinear-vol — extension §C ETF (2026-08-23) — Epic #1454

**Verdict §C : NO BEATS.** Première entrée §C **hors BTC**. La question posée était de savoir
si l'edge M4 (BEATS 3/3 sur BTC log-RV, #11036) est spécifique au terrain crypto ou transfère
aux ETF anti-biais. La réponse est **non** : ce qui transfère est la **miscalibration de la
baseline**, pas une capacité prédictive. Une première rédaction de cette entrée concluait
« BEATS 9/9 » sur l'edge brut ; #12684 l'a réfutée et la décomposition ci-dessous, refaite
indépendamment sur les 9 cellules, la confirme.

**Modèle** : DLinear (Zeng et al. AAAI 2023), `seq_len=22 -> horizon`, ~22 params — identique
à l'entrée BTC (#11036). **Univers** : SPY / TLT / GLD daily 2005-01-03 → 2026-08-14
(`datasets/panier/`, 5 438 obs par symbole ; aucun FAANG/Mag7). **Cible** : log-RV quotidien
estimée par **Garman-Klass (1980)** sur OHLC daily (`0.5·ln(H/L)² − (2ln2−1)·ln(C/O)²`).
L'estimateur diffère de la somme horaire du terrain BTC (pas d'intraday ETF sur disque) — la
comparabilité est **interne**, pas cross-terrain. **Baselines** : HAR (Corsi 2009) +
persistence. **DM** : `scripts/dm_test.py`, HAC Newey-West + HLN, `loss_fn="mse"`.
**Protocole** : walk-forward 5-fold expanding, `refit_every=110`, seeds {0,1,7,42},
horizons {1,5,10}. **Compute** : CPU.

### Décomposition biais-variance — la mesure qui tranche

`MSE = biais² + variance`. Le tableau donne les deux edges : celui du MSE total (ce qu'un
DM sur `mse` mesure) et celui de la **variance seule**, c'est-à-dire la précision une fois
les deux prévisionneurs recalés sur leur moyenne.

| Symbole | h | MSE HAR | biais HAR | MSE DL | biais DL | edge brut | **edge hors biais** |
|---|---|---|---|---|---|---|---|
| SPY | 1  | 0,70490 | −0,15614 | 0,67767 | +0,00910 | +3,86 %  | **+0,43 %** |
| SPY | 5  | 0,43526 | −0,23207 | 0,37904 | +0,01425 | +12,92 % | **+0,67 %** |
| SPY | 10 | 0,45129 | −0,30060 | 0,36056 | +0,01683 | +20,10 % | **+0,18 %** |
| TLT | 1  | 0,57879 | −0,19761 | 0,54131 | −0,00425 | +6,47 %  | **−0,29 %** |
| TLT | 5  | 0,27556 | −0,25318 | 0,21095 | −0,00235 | +23,45 % | **+0,24 %** |
| TLT | 10 | 0,27543 | −0,30853 | 0,17967 | −0,00459 | +34,77 % | **+0,33 %** |
| GLD | 1  | 0,72318 | −0,18029 | 0,69440 | +0,02748 | +3,98 %  | **−0,43 %** |
| GLD | 5  | 0,29913 | −0,23270 | 0,24734 | +0,03870 | +17,31 % | **−0,35 %** |
| GLD | 10 | 0,26761 | −0,27958 | 0,19296 | +0,04861 | +27,90 % | **−0,61 %** |

**Moyenne : +16,75 % brut → +0,02 % hors biais. 9 cellules sur 9 sous 1 %, 4 négatives.**
Les variances sont identiques à la 4ᵉ décimale : DLinear n'ajoute **aucune précision**
mesurable. L'edge brut est arithmétiquement le biais² de la baseline — vérification directe,
SPY h=10 : biais² = 0,0904 soit 20,0 % de 0,45129, edge annoncé 20,10 %.

Les DM sont corrects et fortement significatifs (`p` de 1,0e-14 à 1,9e-05 sur ~4 500
prédictions) : ils mesurent fidèlement un écart de MSE **réel**. C'est l'interprétation de cet
écart qui était fausse — un test significatif sur la bonne perte peut porter sur le mauvais
effet.

### Ce que l'entrée établit malgré tout

- **HAR sous-prévoit systématiquement le log-RV**, sur les 3 ETF comme sur BTC, et le biais
  **croît avec l'horizon** (−0,16 à −0,31). C'est un défaut réel de la baseline telle
  qu'implémentée, reproductible sur 4 terrains.
- **DLinear apprend à être non biaisé** (|biais| ≤ 0,049) sans que ce soit un objectif
  explicite. Le modèle est bien calibré ; il ne suit simplement pas mieux la dynamique.
- **La bonne baseline pour la suite est un HAR débiaisé** (correction d'intercept OOS). Toute
  comparaison future de cette famille sur ce terrain doit la prendre comme référence, faute
  de quoi elle re-mesurera le même offset. `dlinear_vol.py` porte déjà `debias` côté modèle
  (l. 203, 242-243, 279-280) et **calcule** `har_bias_oos` (l. 434) sans jamais l'appliquer :
  l'asymétrie est là, elle est corrigeable.
- **Contrepoint M15** : sous la même correction, la décomposition **complète** des 9 cellules
  ETF (SPY/TLT/GLD × h=1/5/10) est **négative 9 fois sur 9** hors biais (jusqu'à −38,6 %),
  y compris la seule qui tenait la conjonction σ+DM (TLT h=5 : +12,3 % brut → −20,2 % hors
  biais). M15 ETF est **NO BEATS définitif**, pas « majoritairement inversé » : la famille
  deep-seq ne bat pas non plus un HAR recalé. Le premier chiffrage (« 3 sur 4 ») portait sur
  un échantillon partiel des cellules ; il est corrigé ici.

### Reproduction

- **Data** : `datasets/panier/{SPY,TLT,GLD}_daily.csv` (2005-2026, 5 438 lignes chacune)
- **Run** : `python -u etf_vol.py --symbols SPY TLT GLD --horizons 1 5 10 --seeds 0 1 7 42 --epochs 100 --refit-every 110 --loss-fn mse --out-json results/m4_dlinear_vol_etf_sc_mse/results.json` (4 328 s)
- **Harnais** : `scripts/etf_vol.py` (réutilise `walk_forward_har`, `walk_forward_dlinear`, `dm_verdict` ; RV GK dans `garman_klass_rv`)
- **Décomposition** : reproductible depuis les checkpoints `bg_logs/etf_vol*.log` (couples
  `HAR MSE`/`bias_OOS` et `DLinear MSE`/`bias` par cellule) — variance = MSE − biais²
- **Suite ouverte** : #12684 (débiaisage de la baseline), #12681 (la ligne de log affiche le
  MSE HAR agrégé quand le verdict porte sur l'aligné)

### M15 LSTM-vol — patch persistance biais + slice 2/2 dé-biaisé symétrique (2026-08-24, issue #12734)

Slice 2/2 du ticket #12734 (slice 1/2 = M4 DLinear-vol, livré via PR #12742). Le ticket note que `m15_lstm_rv.py` ne persistait ni `har_bias_oos` ni les prédictions brutes — le keeper M15 BTC #11041 était donc **invérifiable post-hoc** par la voie symétrique.

**Patch persistance** : `evaluate_one_combo` calcule désormais `har_bias_oos = mean(har_pred - target)` OOS et persiste **les arrays `har_errors`/`lstm_errors`** (même guard `len >= 10 and isfinite`) par combo, pour que `analyze_one_combo` (wrapper `btc_m15.py`) puisse appliquer la décomposition `MSE = biais² + variance` et le DM recentré post-hoc. Rétro-compatible : les anciens champs `sharpe_*`, `mse_*`, `dm_*` sont préservés. Le JSON `results.json` de chaque run M15 porte donc `har_bias_oos` + les erreurs brutes par combo — vérifiable depuis git sans relancer le sweep.

**Wrapper `scripts/btc_m15.py`** : pendant BTC-only de `scripts/btc_vol.py`. Orchestre le run M15 BTC + applique la décomposition `MSE = biais² + variance` et le DM recentré (`loss_fn="mse"` sur erreurs centrees). Helpers `_mse_decomposition` et `_dm_centered_mse` dans le module partage `scripts/bias_metrics.py`, extrait de `btc_vol.py` (issue #14363).

**Section notebook** : section 8 ajoutée à `m15_lstm_rv_sc_validation.ipynb` (méthodologie + commande de run complet + verdict attendu). Markdown-only — la cellule code de lecture du JSON viendra au prochain cycle avec le rerun.

**Run complet** : 3 horizons × 4 seeds = 12 combos, ~50 min/combo (~10h CPU/GPU) — **hors budget cycle worker**. Acceptance #4 du ticket #12734 autorise explicitement ce defer. Commande :

```bash
for h in 1 5 10; do
  for s in 0 1 7 42; do
    python scripts/btc_m15.py --horizon $h --seed $s --refit-every 110 --hidden-size 32
  done
done
```

- **Verdict attendu** : symétrique à M4 (slice 1/2), conjonction §C recentrée `edge ≥ 2σ AND dm_p_median < 0.05`. Lecture : `var_ratio_lstm_over_har_debiased < 1` = LSTM plus précis ; `har_bias_share_of_mse_debiased` < 0.10 = dé-biaisage propre.
- **Statut** : PATCH LIVRÉ, RUN DISPATCHÉ au prochain cycle worker (acceptance #4).

## Ladder #1409 — Final Verdicts (2026-06-12)

Systematic signal-generation ladder, 7 hard disciplines (walk-forward 5-fold expanding,
multi-seed >= 4, anti-FAANG universe, explicit tx costs + 50bps stress, deflated Sharpe,
honest verdict). Full method + results per rung: `docs/L<n>_*.md` + `scripts/results/`.

| Rung | Strategy | Verdict | Key metric | Doc |
|------|----------|---------|------------|-----|
| L1 | TSMOM multi-asset | NO BEATS | net Sharpe -2.26 to -2.56 (costs kill) | `docs/L1_tsmom.md` |
| L2 | Carry + dual momentum | NO BEATS | best CS 252d delta -0.153 | `docs/L2_dual_momentum.md` |
| L3 | Trend long-horizon | NO BEATS | 0/75 signal, median AUC 0.509 | `results/l3_trend_long_horizon/` |
| **L4** | **Decision Transformer (action-based)** | **BEATS** (panel @10bps) | **24/26, median AUC 0.558** ; @50bps INCONCLUSIVE ; holdout temporel 06/08 non reproduit (interne -6.63σ DM p 0.085, frais +19.97σ DM p 0.236) ; **OOT réel 04/09 NO-BEATS** (train gelé 2025-06-30, -5.38σ, DM mse p 0.142, 0/5 seeds) | `docs/L4_decision_transformer.md` |
| L5 | Vol-targeted trend composite | NO BEATS | delta -0.236 vs S4 v2, t=-2.49, DSR 0.074 | `docs/L5_vol_targeted_composite.md` |
| (side) | PatchTST forecast-based (mislabeled "L5" before 2026-06-12) | NO BEATS | 0/26, median AUC 0.501 | `results/l5_patchtst/` |

Conclusion: alpha on this universe comes from learned action policies (L4) — **in cross-section / panel only (@10bps)**; the L4 edge does NOT survive temporal holdout (internal split 06/08: -6.63σ, DM p 0.085) — not trend
overlays or vol conditioning on risk-based allocation. Vol-targeting achieves its 10%
risk target at ~zero Sharpe cost — keep as a *risk* overlay on production candidates
(S3 HMM + S4 v2 Ridge KEEPERS), not as an alpha source.

## Anti-Bias Audit (2026-05-04)

**WARNING: All checkpoints trained on SPY single-asset.** This creates bias toward US equity momentum.
SPY majority class (up days) 2015-2024 = **54.59%**. Most models barely beat this.

These checkpoints are **NOT valid for production** — they serve as baselines for Stage 0.
Future trainings MUST use anti-bias panier (26 symbols, 7 asset classes) per Issue #706.

**Forbidden symbols**: AAPL, MSFT, GOOG, AMZN, NVDA, TSLA, META

## Stage -1: Panier Baselines POST-FIX (2026-05-06)

**Methodology**: Walk-forward 5-fold, advanced features (38 dims), seed=42, train-only normalization.
RF (200 trees, max_depth=8) + XGBoost (200 rounds, max_depth=8) on all 26 panier symbols.

**Result: 18 BEATS, 32 FAILS across 50 experiments.**

| Group | Symbol | RF DirAcc | RF vs Maj | XGB DirAcc | XGB vs Maj | Best Model | Verdict |
|-------|--------|-----------|-----------|------------|------------|------------|---------|
| us_equity_broad | SPY | 0.4972 | -0.0104 | 0.4991 | -0.0085 | None | FAIL |
| us_equity_broad | RSP | 0.5208 | **+0.0075** | 0.5123 | -0.0009 | RF | MIXED |
| us_equity_broad | IWM | 0.5094 | **+0.0047** | 0.5113 | **+0.0066** | XGB | BEATS |
| us_equity_sectors | XLB | 0.5189 | **+0.0085** | 0.5358 | **+0.0255** | XGB | BEATS |
| us_equity_sectors | XLC | 0.4902 | -0.0154 | 0.4958 | -0.0098 | None | FAIL |
| us_equity_sectors | XLF | 0.5113 | -0.0028 | 0.5132 | -0.0009 | None | FAIL |
| us_equity_sectors | XLI | 0.5066 | **+0.0038** | 0.5170 | **+0.0142** | XGB | BEATS |
| us_equity_sectors | XLK | 0.4972 | -0.0321 | 0.5066 | -0.0226 | None | FAIL |
| us_equity_sectors | XLP | 0.5330 | **+0.0047** | 0.5170 | -0.0113 | RF | MIXED |
| us_equity_sectors | XLRE | 0.4816 | -0.0347 | 0.4918 | -0.0245 | None | FAIL |
| us_equity_sectors | XLU | 0.5066 | -0.0057 | 0.4953 | -0.0170 | None | FAIL |
| us_equity_sectors | XLV | 0.5255 | **+0.0085** | 0.5151 | -0.0019 | RF | MIXED |
| us_equity_sectors | XLY | 0.4708 | -0.0632 | 0.5085 | -0.0255 | None | FAIL |
| volatility | VIX | 0.5168 | **+0.0057** | 0.5066 | -0.0045 | RF | MIXED |
| us_bonds | TLT | 0.5274 | -0.0057 | 0.5245 | -0.0085 | None | FAIL |
| us_bonds | IEF | 0.5783 | -0.0311 | 0.5462 | -0.0632 | None | FAIL |
| us_bonds | SHY | 0.8821 | -0.0113 | 0.8877 | -0.0057 | None | FAIL |
| commodities | GLD | 0.5142 | -0.0113 | 0.5038 | -0.0217 | None | FAIL |
| commodities | USO | 0.4802 | -0.0283 | 0.4774 | -0.0311 | None | FAIL |
| commodities | DBA | 0.5151 | -0.0349 | 0.5198 | -0.0302 | None | FAIL |
| international | EFA | 0.5151 | -0.0123 | 0.5198 | -0.0075 | None | FAIL |
| international | EEM | 0.5396 | **+0.0189** | 0.5047 | -0.0160 | RF | MIXED |
| crypto | BTC-USD | 0.5171 | **+0.0171** | 0.5197 | **+0.0197** | XGB | BEATS |
| crypto | ETH-USD | 0.5310 | **+0.0293** | 0.5422 | **+0.0405** | XGB | BEATS |
| crypto | LTC-USD | 0.5203 | **+0.0019** | 0.5273 | **+0.0089** | XGB | BEATS |
| crypto | XRP-USD | 0.5293 | **+0.0267** | 0.5233 | **+0.0207** | RF | BEATS |

Key findings:

- **Crypto dominates**: 7/8 BEATS (all 4 symbols x 2 models, except LTC-USD RF marginal +0.0019).
  Crypto majority class is close to 50%, making prediction viable. ETH-USD XGB +4.05pp = best single edge.
- **XGBoost > RF for crypto**: XGB edges consistently larger (ETH +4.05pp, BTC +1.97pp, LTC +0.89pp).
- **Equity sectors show selective edges**: XLB (+2.55pp XGB), XLI (+1.42pp XGB), but most sectors FAIL.
  XLK (Tech ETF) worst at -3.21pp, reflecting 2015-2024 bull market bias.
- **Bonds are pathological**: SHY 89% majority class (up days) = impossible to beat. TLT/IEF also fail.
- **SPY FAILS**: Confirms single-asset SPY training is dead end (see POST-FIX verdict below).
- **VIX has mild RF edge** (+0.57pp) but XGB fails — volatility regime detection is noisy.

Implication for EPIC #705: **Multi-asset panier baselines confirm the thesis** — ML has genuine predictive
value on crypto (+4.05pp ETH) and selective equity sectors (+2.55pp XLB). SPY/bonds are pathological.
Curriculum should demonstrate ML on crypto/commodities first, then explain why SPY fails.

## POST-FIX Verdict (2026-05-05) — DEFINITIVE

**Methodology**: Deterministic (seed=42), walk-forward, OOS-aware majority baseline (#737),
last-fold checkpoint (#738), RSI Wilder EMA (#736), internal val split from train only (#726/#730).
14 runs across 7 architectures on SPY/BTC/Multi-asset.

| Model | SPY single | BTC single | Multi 4-asset |
| -------- | ---------- | ---------- | ------------- |
| MTGNN | -0.0452 FAILS | -0.0094 FAILS | -0.0116 FAILS |
| LSTM | -0.0186 FAILS | -0.0337 FAILS | n/a |
| Transformer | -0.0497 FAILS | -0.0207 FAILS | n/a |
| PatchTST | -0.1076 FAILS | -0.0030 FAILS | n/a |
| iTransformer | -0.0082 FAILS | -0.0186 FAILS | n/a |
| Mamba | -0.0370 FAILS | -0.0306 FAILS | n/a |
| STGAT | n/a | n/a | -0.0480 FAILS |

**Result: 0 BEATS, 14 FAILS.** No baseline architecture beats the majority predictor under rigorous methodology.

Key findings:

- Pre-fix results (Track A3 below) were **inflated by test-set contamination** — validation early-stopping
  used test_loader directly, creating lookahead bias. PatchTST SPY dropped from -2.10pp to -10.76pp post-fix.
- MTGNN (graph adaptive) previously claimed +0.0005 SPY and +0.0044 multi BEATS — both **non-reproducible**
  after audit fixes (#737 OOS baseline, #738 no cherry-pick, #736 RSI Wilder).
- SPY is pathological (majority 56-58% up days in 2015-2024 bull market). All models learn "predict up"
  and fail when the regime shifts. BTC majority is closer to 50%, but still no edge.
- po-2024 claimed Mamba BTC +3.24pp and PatchTST BTC +1.98pp BEATS — **non-reproducible** on RTX 4090
  with identical hyperparams (d_model=64, batch=16, seed=42). Likely variance from non-determinism or
  thermal throttling on RTX 3070.
- **Implication for EPIC #705**: Current baseline architectures are a dead end on SPY/BTC single-asset.
  Multi-asset panier (Stage 3a, #727) and advanced methods (Stages 5-8: Kronos, Flow Matching,
  FinRL, FinGPT) are the viable path forward.

## Advanced Features (Track A3) — PRE-FIX (INFLATED, superseded by POST-FIX above)

**WARNING**: These results were computed BEFORE contamination fix (#726/#730). Validation early-stopping
used test_loader, inflating direction accuracy. See POST-FIX Verdict above for honest metrics.

Comparison of baseline vs advanced-feature training on SPY 2015-2024.
Majority class baseline: **54.59%** (freq of up days).

| Model | Baseline DirAcc | Advanced DirAcc | vs Majority | Delta | Features |
| ------- | --------------- | --------------- | ----------- | ----- | -------- |
| Transformer (50ep) | 48.72% | **57.95%** | +3.36pp | +9.23pp | 38 (all 13 indicators) |
| Transformer (30ep prod) | 48.72% | **56.43%** | +1.84pp | +7.71pp | 38 (all 13 indicators) |
| LSTM (h=64 prod) | 51.49% | **54.25%** | -0.34pp | +2.76pp | 38 (all 13 indicators) |
| LSTM (h=256) | 51.49% | 50.98% | -3.61pp | -0.51pp | 38 (all 13 indicators) |
| Classification (RF) | 49.66% | **50.86%** | -3.73pp | +1.20pp | 38 (all 13 indicators) |
| DQN | Sharpe 0.89 | Sharpe -0.02 | N/A (in-sample) | -0.91 | 38 (all 13 indicators) |

Key findings (pre-fix):

- Transformer (d=256, h=8, L=6) appeared to beat majority class (+3.36pp) — **this was inflated**.
  POST-FIX reveals -0.0497 FAILS (6.33pp swing).
- LSTM h=64 barely matched majority class (-0.34pp). POST-FIX confirms -0.0186 FAILS.
- RF accuracy (50.86%) was BELOW majority class (-3.73pp). Confirmed no predictive power.
- DQN Sharpe 0.89 was in-sample (no train/test split). Fixed via #729.
- All checkpoints are single-asset (SPY), single-regime (2015-2024 bull market). Not robust.

## Asset Diversity Matters (Cross-Asset Evidence) — PRE-FIX (superseded by POST-FIX)

**Key thesis confirmed (PR #724): Asset selection > model selection.**

**NOTE**: These walk-forward baselines were computed before audit fixes (#737 OOS baseline, #738 last-fold).
The LSTM edges shown below (+3.51pp BTC, +3.68pp TLT) have not been re-validated POST-FIX.
POST-FIX verdict above shows 0 BEATS across all architectures on SPY/BTC deterministic runs.

Cross-asset walk-forward baselines (5-fold, train=500, test=100, gap=10) reveal that
SPY is the *worst* asset for ML training — its 58.7% majority-class frequency (up-day bias
during 2015-2024 bull market) makes it pathological. No model architecture beats this baseline.

| Asset | Best Model | OOS DirAcc | Majority | Edge (pp) | Verdict |
|-------|-----------|------------|----------|-----------|---------|
| BTC-USD | Transformer | 0.5400 | 0.5229 | **+1.71** | Positive edge |
| TLT | Transformer | 0.5533 | 0.5417 | **+1.16** | Positive edge |
| GLD | LSTM | 0.5467 | 0.5200 | **+2.67** | Best single-asset edge |
| EFA | LSTM | 0.5133 | 0.5200 | -0.67 | Near baseline |
| EEM | RF | 0.5200 | 0.5200 | 0.00 | At baseline |
| DBC | LSTM | 0.5067 | 0.5417 | -3.50 | Negative |
| SPY | Transformer | 0.5265 | 0.5873 | **-6.08** | Pathological |

**Implications for curriculum:**
1. Training on SPY alone teaches the wrong lesson — ML appears useless because the asset is too biased.
2. Non-equity assets (BTC, TLT, GLD) show genuine ML edges, validating the approach.
3. Future stages MUST use multi-asset panier (Stage 3a, 19 assets) to demonstrate real ML value.
4. MTGNN (graph neural network) is the only architecture beating baseline even on SPY (+0.05pp),
   suggesting cross-asset graph structure captures signal that single-asset models miss.

**Source**: PR #724 Stage 1 cross-asset walk-forward baselines, ai-01 comparative runs.

## Stage 1: BTC-USD Walk-Forward Baselines (2026-05-05) — PRE-FIX (superseded)

Anti-bias training on BTC-USD 2015-2025 (3653 daily rows, 3594 after feature engineering).
Walk-forward: 5 folds, train=500, test=100, gap=10. BTC majority class (up days) = **55.10%**.

| Model | OOS DirAcc | vs Majority | n_folds | Architecture | Checkpoint |
| ----- | ---------- | ----------- | ------- | ------------ | ---------- |
| LSTM | **54.60%** | **+3.51pp** | 5 | h=64, L=2, ep=30 | 20260505_012529 |
| Transformer | 51.00% | -0.09pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_012554 |
| RF (200 trees) | 49.40% | +0.15pp | 5 | max_depth=8, 19 features | 20260505_012321 |
| DQN | PENDING | PENDING | 3 | h=128, ep=50, w=20 | training |

Key findings:

- LSTM is the only model with meaningful edge (+3.51pp over majority class).
- Transformer at d=64/h=4/L=2 is too small for BTC-USD patterns (previous SPY BEST used d=256/h=8/L=6).
- RF barely matches random — no feature-based signal in BTC daily returns.
- BTC-USD majority class (55.1%) is higher than SPY (54.6%) — crypto has more up days in this period.

## Stage 1: Cross-Asset Walk-Forward Baselines (2026-05-05) — PRE-FIX (superseded)

Anti-bias training on 6 non-FAANG assets (GLD, TLT, EEM, EFA, DBC + BTC-USD).
Walk-forward: 5 folds, train=500, test=100, gap=10. All models use advanced features (38 dims).

| Asset | Model | OOS DirAcc | vs Majority | n_folds | Architecture | Checkpoint |
| ----- | ----- | ---------- | ----------- | ------- | ------------ | ---------- |
| BTC-USD | LSTM | **54.60%** | **+3.51pp** | 5 | h=64, L=2, ep=30 | 20260505_012529 |
| BTC-USD | Transformer | 51.00% | -0.09pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_012554 |
| BTC-USD | RF (200 trees) | 49.40% | +0.15pp | 5 | max_depth=8, 19 features | 20260505_012321 |
| BTC-USD | DQN | 0.00% | -51.14pp | 3 | h=256, ep=100, w=20 | 20260505_021359 |
| GLD | LSTM | **53.80%** | +0.84pp | 5 | h=64, L=2, ep=30 | 20260505_013925 |
| GLD | RF (200 trees) | 53.00% | +1.09pp | 5 | max_depth=8, 38 features | 20260505_010142 |
| GLD | Transformer | 53.80% | +1.19pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_015628 |
| TLT | LSTM | **52.20%** | **+3.68pp** | 5 | h=64, L=2, ep=30 | 20260505_015143 |
| TLT | RF (200 trees) | 48.20% | -5.91pp | 5 | max_depth=8, 38 features | 20260505_010023 |
| TLT | Transformer | 51.20% | +2.68pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_015903 |
| EEM | LSTM | 50.60% | -0.96pp | 5 | h=64, L=2, ep=30 | 20260505_010203 |
| EEM | RF (200 trees) | 51.80% | -0.68pp | 5 | max_depth=8, 38 features | 20260505_010023 |
| EEM | Transformer | 47.20% | -4.11pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_020058 |
| EFA | LSTM | 52.20% | -0.50pp | 5 | h=64, L=2, ep=30 | 20260505_020022 |
| EFA | RF (200 trees) | 50.00% | -2.46pp | 5 | max_depth=8, 38 features | 20260505_015821 |
| EFA | Transformer | 50.40% | -2.55pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_021553 |
| DBC | LSTM | **55.80%** | +0.49pp | 5 | h=64, L=2, ep=30 | 20260505_020144 |
| DBC | RF (200 trees) | 49.60% | +2.40pp | 5 | max_depth=8, 38 features | 20260505_015829 |
| DBC | Transformer | 51.80% | -2.48pp | 5 | d=64, h=4, L=2, ep=30 | 20260505_021816 |

Majority class baselines: BTC-USD=55.10%, GLD=53.04%, TLT=48.09%, EEM=52.44%, EFA=52.46%, DBC=47.20%.

Key findings:

- **LSTM is the best model across 4/6 assets** — consistent edge on BTC (+3.51pp), TLT (+3.68pp), GLD (+0.84pp), DBC (+0.49pp).
- **TLT (bonds) is the most predictable asset** — LSTM +3.68pp, Transformer +2.68pp. Bonds have clearer momentum regimes.
- **Transformer (d=64) underperforms** on equities (EEM -4.11pp) and BTC (-0.09pp), but works on bonds/commodities.
- **RF has no reliable edge** — mixed results across all assets, never the best model.
- **EEM is the hardest asset** — all models struggle, LSTM -0.96pp, Transformer -4.11pp.
- **DBC (commodities) LSTM = best absolute DirAcc** at 55.80%, but majority class is already low (47.20%).
- **DQN completely fails OOS** — 0.00% DirAcc on BTC-USD. All 3 folds have negative OOS reward. The agent overfits training episodes (avg reward 4.7-6.4 in-sample) but produces zero actionable signals out-of-sample. RL approach needs fundamental redesign for this problem.

## Walk-Forward OOS Evaluation (Track B)

Evaluation harness: `scripts/eval_existing_checkpoints.py`
Method: 5-fold walk-forward (3yr train, 1yr test, 5-day gap), per-regime, transaction costs.

| Model | Checkpoint | OOS DirAcc | vs Majority | Regime Avg DirAcc | Gross Sharpe | Net Sharpe | Cost Drag (bps) |
| ----- | ---------- | ---------- | ----------- | ----------------- | ------------ | ---------- | --------------- |
| Transformer | 20260501_134056 (BEST) | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| Transformer | 20260503_222904 (PROD) | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| LSTM | 20260503_221944 (PROD) | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| LSTM | 20260501_133929 | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| RF | 20260501_133837 | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |
| DQN | 20260501_120415 | PENDING | PENDING | PENDING | PENDING | PENDING | PENDING |

**Status**: Evaluation harness ready (27/27 tests pass). OOS metrics to be populated after GPU evaluation run.
SPY majority class baseline = **54.59%**. Values will be populated by `python eval_existing_checkpoints.py --all`.

## Data Sources

| Dataset | Path | Coverage | Status |
| ------- | ---- | -------- | ------ |
| SPY daily | `datasets/yfinance/SPY_2015-01-01_2026-05-01.csv` | 2015-2026 | Used by all checkpoints |
| BTC/USD 1h stitched | `datasets/crypto/BTC_USD_1h_stitched.csv` | 2011-2024 | Available for Stage 1+ |
| Panier anti-bias | `datasets/panier/` (26 symbols) | 2015-2026 | Available for Stage 0+ |
| Forex FXCM/Oanda | `datasets/forex/` (10 pairs) | 2002-2025 | Available for Stage 1+ |

## ARCHIVED — Legacy SPY-single checkpoints (2026-06-12)

The 20 checkpoints below (dqn / lstm / rf / transformer, all `[SPY-ONLY]`) are **ARCHIVED /
OBSOLETE** per #1409 cleanup. POST-FIX verdict above (0 BEATS, 14 FAILS) plus the anti-bias
audit (SPY pathological, majority 54.6-58.7% up days) make them invalid as baselines and
forbidden as production models. They are retained on disk under `checkpoints/` for forensic
reproducibility only — do NOT load them for new work. Valid starting points are the
Curriculum V2 KEEPERS (M12, M15, S3, S4 v2 — see README) and the L4 Decision Transformer.

## dqn [ARCHIVED]

Checkpoints: 5

**WARNING**: All DQN checkpoints below trained WITHOUT train/test split (Issue #703).
Sharpe estimates are in-sample only, NOT reliable out-of-sample metrics.
Marked `[INVALID-NO-SPLIT]` until re-trained with `--test-ratio 0.2`.

### 20260501_120415 [INVALID-NO-SPLIT] [BASELINE] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=2.2865, max_reward=3.0876, mean_reward=1.0177, mean_trades=749.3, min_reward=-1.8051, sharpe_estimate=0.8921
- Architecture: hidden_size=256, n_actions=3, state_size=242
- Config: device=cuda, hidden_size=256, num_episodes=50, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_142319 [INVALID-NO-SPLIT] [ADVANCED-FEATURES] [SPY-ONLY]

- Data hash: `4ec8b44b93f4024f`
- Metrics: best_avg_reward_10=0.3888, max_reward=1.8077, mean_reward=-0.0138, mean_trades=782.5, min_reward=-1.2372, sharpe_estimate=-0.0171
- Architecture: hidden_size=256, n_actions=3, state_size=762
- Config: device=cuda, hidden_size=256, num_episodes=20, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_140955 [INVALID-NO-SPLIT] [SPY-ONLY]

- Data hash: `4ec8b44b93f4024f`
- Metrics: best_avg_reward_10=-0.4572, max_reward=-0.0334, mean_reward=-0.4572, mean_trades=759.3, min_reward=-0.836, sharpe_estimate=-1.6905
- Architecture: hidden_size=128, n_actions=3, state_size=762
- Config: device=cuda, hidden_size=128, num_episodes=10, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_112641 [INVALID-NO-SPLIT] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_avg_reward_10=-0.1559, max_reward=0.9312, mean_reward=-0.5358, mean_trades=739.6, min_reward=-1.5861, sharpe_estimate=-0.8096
- Architecture: hidden_size=32, n_actions=3, state_size=242
- Config: device=cpu, hidden_size=32, num_episodes=20, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111005 [INVALID-NO-SPLIT] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: best_avg_reward_10=-0.0017, max_reward=0.1665, mean_reward=-0.0017, mean_trades=44.1, min_reward=-0.2395, sharpe_estimate=-0.0134
- Architecture: hidden_size=256, n_actions=3, state_size=242
- Config: device=cpu, hidden_size=256, num_episodes=10, symbol=SPY
- Files: metadata.json, model.pt

## lstm [ARCHIVED]

Checkpoints: 5

### 20260503_221944 [OK] [SPY-ONLY] [ADVANCED-FEATURES] [PRODUCTION]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5425, direction_accuracy_significant=0.5506, epochs_trained=50, mae=0.005944, mse=6.2e-05
- Architecture: hidden_size=64, input_size=38, num_layers=2
- Config: device=cuda, epochs=50, hidden_size=64, num_layers=2, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_133929 [OK] [SPY-ONLY] [ADVANCED-FEATURES]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5098, direction_accuracy_significant=0.503, epochs_trained=50, mae=0.005954, mse=6.2e-05
- Architecture: hidden_size=256, input_size=38, num_layers=3
- Config: device=cuda, epochs=50, hidden_size=256, num_layers=3, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_113924 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=0.000144, direction_accuracy=0.4848, direction_accuracy_significant=0.4957, epochs_trained=30, mae=0.008986, mse=0.000147
- Architecture: hidden_size=256, input_size=15, num_layers=3
- Config: device=cuda, epochs=30, hidden_size=256, num_layers=3, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111103 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=0.00015, direction_accuracy=0.5149, direction_accuracy_significant=0.5014, epochs_trained=5, mae=0.009063, mse=0.000153
- Architecture: hidden_size=64, input_size=15, num_layers=1
- Config: device=cpu, epochs=5, hidden_size=64, num_layers=1, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_110937 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: best_val_loss=0.000261, direction_accuracy=0.5, direction_accuracy_significant=0.5139, epochs_trained=2, mae=0.013328, mse=0.000265
- Architecture: hidden_size=128, input_size=15, num_layers=2
- Config: device=cpu, epochs=2, hidden_size=128, num_layers=2, symbol=SPY
- Files: metadata.json, model.pt

## rf [ARCHIVED]

Checkpoints: 5

### 20260501_133837 [OK] [SPY-ONLY] [ADVANCED-FEATURES]

- Data hash: `4ec8b44b93f4024f`
- Metrics: accuracy=0.5086, f1=0.5031, precision=0.5077, recall=0.5086, test_samples=464, train_samples=1852
- Config: model_type=rf, n_estimators=500, max_depth=10, symbol=SPY, advanced=true
- Files: metadata.json, model.joblib

### 20260501_113900 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: accuracy=0.4966, f1=0.4958, precision=0.505, recall=0.4966, test_samples=441, train_samples=1764
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_111041 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: accuracy=0.4966, f1=0.4958, precision=0.505, recall=0.4966, test_samples=441, train_samples=1764
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_111026 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: accuracy=0.3933, f1=0.3951, precision=0.4033, recall=0.3933, test_samples=89, train_samples=352
- Config: symbol=SPY
- Files: metadata.json, model.joblib

### 20260501_110930 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: accuracy=0.3933, f1=0.3951, precision=0.4033, recall=0.3933, test_samples=89, train_samples=352
- Config: symbol=SPY
- Files: metadata.json, model.joblib

## transformer [ARCHIVED]

Checkpoints: 5

### 20260501_134056 [OK] [SPY-ONLY] [ADVANCED-FEATURES] [BEST]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5795, direction_accuracy_significant=0.5804, epochs_trained=50, mae=0.005895, mse=6.1e-05, total_params=3189633
- Architecture: d_model=256, input_size=38, nhead=8, num_layers=6
- Config: device=cuda, d_model=256, epochs=50, nhead=8, num_layers=6, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260503_222904 [OK] [SPY-ONLY] [ADVANCED-FEATURES] [PRODUCTION]

- Data hash: `4ec8b44b93f4024f`
- Metrics: direction_accuracy=0.5643, direction_accuracy_significant=0.5595, epochs_trained=30, mae=0.005932, mse=6.1e-05, total_params=3189633
- Architecture: d_model=256, input_size=38, nhead=8, num_layers=6
- Config: device=cuda, d_model=256, epochs=30, nhead=8, num_layers=6, symbol=SPY, advanced=true
- Files: metadata.json, model.pt

### 20260501_113923 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=7.3e-05, direction_accuracy=0.4872, direction_accuracy_significant=0.5071, epochs_trained=30, mae=0.009084, mse=0.000149
- Architecture: d_model=128, input_size=17, nhead=8, num_layers=4
- Config: d_model=128, device=cuda, epochs=30, nhead=8, num_layers=4, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_111130 [OK] [SPY-ONLY]

- Data hash: `17cb43b404e3ddf1`
- Metrics: best_val_loss=9.9e-05, direction_accuracy=0.4714, direction_accuracy_significant=0.468, epochs_trained=5, mae=0.011033, mse=0.0002
- Architecture: d_model=64, input_size=17, nhead=4, num_layers=2
- Config: d_model=64, device=cpu, epochs=5, nhead=4, num_layers=2, symbol=SPY
- Files: metadata.json, model.pt

### 20260501_110947 [OK] [SPY-ONLY]

- Data hash: `synthetic-dryrun`
- Metrics: best_val_loss=0.000252, direction_accuracy=0.4762, direction_accuracy_significant=0.4722, epochs_trained=2, mae=0.018693, mse=0.000542
- Architecture: d_model=128, input_size=17, nhead=4, num_layers=4
- Config: d_model=128, device=cpu, epochs=2, nhead=4, num_layers=4, symbol=SPY
- Files: metadata.json, model.pt
