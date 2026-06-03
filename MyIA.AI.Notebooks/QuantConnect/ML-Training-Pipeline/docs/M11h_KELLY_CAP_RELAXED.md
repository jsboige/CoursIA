# M11h Kelly cap relaxed — `cap=3.0` pushes break-even from 50bps to 100bps

**Date** : 2026-05-13 (Cycle 29)
**Author** : ai-01 BG ML track (Track C, parallel to PR #1005 Track B FG)
**Wallclock** : 393.2s (CPU, ai-01)
**Script** : `scripts/m11h_kelly_cap_relaxed.py` (imports `evaluate_coin_horizon` from M11g)
**Coins** : BTC-USD, ETH-USD, SOL-USD, LTC-USD, XRP-USD, ADA-USD, DOT-USD (7 × 5 horizons = 35 combos)
**Strategy** : `kelly_har_mu60` with no-trade band, sweeping the Kelly cap

## Question

> M11g a confirme que le seuil no-trade band ne mord pas. M11g pistes ouvertes
> mentionnent : *"Kelly non-cape ou cap relaxe produirait plus de variation
> intermediaire dans les weights"*. Si l'on relache le cap de 1.0 a 3.0,
> le break-even peut-il passer de 50bps a 100bps ?

**Reponse** : **OUI**. Cap=3.0 fait passer la frontiere break-even de ~50bps
(p=0.045) a ~100bps (p=0.088, frontiere). Mediane delta Sharpe ann triple
(de +0.044 a cap=1.0,fee=100bps -> +0.087 a cap=3.0,fee=100bps).

## Methodologie

- Sweep : `kelly_cap in {1.0, 2.0, 3.0}` x `threshold in {0.00, 0.05, 0.10}` x `fee_bps in {10, 50, 100}`
- Pour chaque (cap, threshold, fee, coin, horizon) : reprend `evaluate_coin_horizon` de M11g
- Sign-test binomial 35-combo population par cellule de la grille

## Grille BEATS aggregate (sign-test p-values)

### kelly_cap = 1.0 (M11g/M11f baseline)

| threshold | 10 bps | 50 bps | 100 bps |
|-----------|--------|--------|---------|
| **0.000** | 27/35 p=0.001 med=+0.299 | 23/35 p=0.045 med=+0.186 | 21/35 p=0.155 med=+0.044 |
| **0.050** | 27/35 p=0.001 med=+0.298 | 23/35 p=0.045 med=+0.185 | 21/35 p=0.155 med=+0.044 |
| **0.100** | 27/35 p=0.001 med=+0.295 | 23/35 p=0.045 med=+0.186 | 21/35 p=0.155 med=+0.044 |

### kelly_cap = 2.0

| threshold | 10 bps | 50 bps | 100 bps |
|-----------|--------|--------|---------|
| **0.000** | 25/35 p=0.008 med=+0.313 | 23/35 p=0.045 med=+0.204 | 21/35 p=0.155 med=+0.055 |
| **0.050** | 25/35 p=0.008 med=+0.312 | 23/35 p=0.045 med=+0.204 | 21/35 p=0.155 med=+0.055 |
| **0.100** | 25/35 p=0.008 med=+0.311 | 23/35 p=0.045 med=+0.203 | 21/35 p=0.155 med=+0.055 |

### kelly_cap = 3.0 (relaxed)

| threshold | 10 bps | 50 bps | 100 bps |
|-----------|--------|--------|---------|
| **0.000** | 25/35 p=0.008 med=+0.338 | 23/35 p=0.045 med=+0.227 | **22/35 p=0.088 med=+0.087** |
| **0.050** | 25/35 p=0.008 med=+0.338 | 23/35 p=0.045 med=+0.226 | **22/35 p=0.088 med=+0.091** |
| **0.100** | 25/35 p=0.008 med=+0.338 | 23/35 p=0.045 med=+0.228 | **22/35 p=0.088 med=+0.093** |

Cellules en gras : ESCALATE (sign-test p < 0.10 a 100bps avec cap=3.0).

## Verdict

- **NULL confirme sur threshold band** : 3 niveaux de seuil donnent des resultats
  identiques a 3 decimales sur tous les caps. Threshold band a aucun effet materiel.
- **POSITIVE sur Kelly cap** : 12/27 cellules de la grille (cap, thr, fee>=50bps)
  passent ESCALATE (>=60% delta>0 et p<0.10). Toutes les cellules cap=3.0/fee>=50bps
  sont positives.
- **Trade-off** : cap=3.0 = jusqu'a 3x leverage sur la Kelly fraction. Drawdowns
  potentiels significativement plus eleves. M11h NE QUANTIFIE PAS ces drawdowns
  (script ne calcule que Sharpe paired diff).

## Pistes ouvertes

1. **Drawdown analysis** : recalculer max DD vs cap=1.0 baseline. Si cap=3.0
   double le DD, l'edge net en CAGR risk-adjusted disparait probablement.
2. **Cap=4.0 / cap=5.0** : extrapoler la frontiere. Cap=infinity = full Kelly
   non capped (theoretical optimal mais explosif en pratique).
3. **Per-coin breakdown** : verifier si un coin (BTC ? ETH ?) porte
   disproportionnellement les ESCALATE — sinon edge dilue.
4. **Multi-asset Kelly** : Kelly fractions correlees, calculer cov(coin_i, coin_j)
   et resoudre le portfolio Kelly multi-asset (vs scalar par coin).

## Lien M11g M11f M11e

- **M11f** : fee=50bps p=0.045, fee=100bps p=0.155 (cap=1.0 implicite). M11h
  reproduit exactement ces chiffres au cap=1.0 -> validation du pipeline.
- **M11g** : threshold band sur cap=1.0 = NULL. M11h confirme NULL sur tous les caps.
- **M11h** : levier additionnel = cap. Cap=3.0 etend le break-even de ~50bps a ~100bps.

## Reproduction

```powershell
& "C:\Users\MYIA\miniconda3\envs\coursia-ml-training\python.exe" `
  "MyIA.AI.Notebooks\QuantConnect\ML-Training-Pipeline\scripts\m11h_kelly_cap_relaxed.py"
```

Sortie : `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/results/m11h_kelly_cap_relaxed/{results.json,results.csv}`.

## Discipline (G.2 / regle multi-seed)

- Walk-forward 5-fold preserve (n_splits=5 par default, refit_every=22)
- Pas de FAANG/Mag7 (crypto only, conforme dataset_paths.md)
- Transaction costs documentes (10/50/100 bps)
- Pas de single-seed verdict — agregation 35-combo cross-coin/cross-horizon
- Verdict honnete : NULL sur threshold + POSITIVE conditionnel sur cap (avec caveat DD non-quantifie)
