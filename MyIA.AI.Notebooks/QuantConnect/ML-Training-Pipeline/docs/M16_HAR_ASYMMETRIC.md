# M16 HAR-RV Asymmetric Semivariance — Andersen-Bollerslev-Diebold-Patton (2007)

**Status:** NO BEATS CLUSTER (Cycle 33, 2026-05-13) — BTC standalone BEATS robuste sur 3 horizons, **mais 1/7 coins seulement = sign-test cluster non-significatif**. Pas de PR M16 standalone — features RV+/RV- à intégrer en ensemble (M17 candidate).

## Verdict (G.2 metrics honnêtes — 7-coin full sweep)

M16 HAR-Asymmetric verdict cluster : **NO BEATS** (3 BEATS / 0 NO BEATS / 18 INCONCLUSIVE sur 21 configs = 7 coins × 3 horizons). BTC-USD est le seul coin où la décomposition leverage-effect (RV+ / RV-) bat HAR Classic en MSE pure. Pour les 6 autres coins (ETH/LTC/SOL/MATIC/XRP/ADA/DOT), DM p > 0.05 — pas d'edge statistique.

**Pattern observé** : l'asymétrie bear-rally caractéristique de BTC mature (post-2018 cycle ETF spot 2024) ne se généralise pas aux altcoins. ETH inclus. Hypothèse : altcoins suivent BTC en bear (corrélation ↑) mais ont leur propre dynamique en rally (corrélation ↓), ce qui dissout la décomposition asymétrique.

**Distinct de M12 HAR-RV-J** : M12 BEATS sur Sharpe (Kelly position sizing) sur 7/7 coins via sign-test p=7.9e-7. M16 BEATS sur MSE direct uniquement sur 1/7 coins. **M12 reste seul modèle BEATS cluster-wide**.

**Distinct de M12 HAR-RV-J** : M12 BEATS sur Sharpe (Kelly position sizing) malgré MSE worse. M16 BEATS sur **MSE direct** (forecast accuracy), pas encore évalué sur Sharpe/Kelly. Les deux modèles sont complémentaires : M12 alloc sizing, M16 forecast pure.

**Caveat important G.2 (metrics honnêtes)** : `std_asym_mse = 0` cross-seed sur 4 seeds → HAR est OLS deterministic, le seed n'affecte pas le résultat. Le multi-seed prescrit par le protocole ML/trading n'a pas de sens pour HAR pure. **1 seed effectif, pas 4**. Documenter explicitement, ne pas fake une "robustness 4 seeds".

## Methodology

```
RV_t  = RV+_t + RV-_t
RV+_t = sum_{h in day t} r²_h × 1_{r_h > 0}    # upside semivariance
RV-_t = sum_{h in day t} r²_h × 1_{r_h < 0}    # downside semivariance

log RV_{t+h} = b0 + b1·log(RV-_t) + b2·log(RV+_t)
                   + b3·mean(log RV_{t-5..t-1}) + b4·mean(log RV_{t-22..t-6}) + e
```

vs HAR Classic baseline (PR #938) :
```
log RV_{t+h} = b0 + b1·log(RV_t) + b2·mean(log RV_{t-5..t-1}) + b3·mean(log RV_{t-22..t-6}) + e
```

Différence : **2 régresseurs (RV+, RV-)** au lieu de 1 (RV) à l'horizon t. Hypothèse testée : la décomposition leverage-effect (Black 1976, French-Schwert-Stambaugh 1987, ABDP 2007) améliore la prédictibilité.

**Walk-forward 5-fold expanding × 4 seeds × 3 horizons (h=1, 5, 10).**
**Diebold-Mariano test** vs HAR Classic baseline (paired loss differentials).

## Results Full Sweep (Cycle 33, 7 coins × 3 horizons × 4 seeds, 271s runtime)

| Coin | Horizon | Asym MSE | Classic MSE | MSE Reduction | DM stat | DM p-value | Verdict |
|------|---------|----------|-------------|---------------|---------|------------|---------|
| **BTC-USD** | h=1 | 0.8425 | 0.8877 | **+5.09%** | -4.000 | 6.6e-5 | **BEATS** |
| **BTC-USD** | h=5 | 0.3986 | 0.5220 | **+23.64%** | -4.546 | 5.8e-6 | **BEATS** |
| **BTC-USD** | h=10 | 0.3610 | 0.5707 | **+36.74%** | -4.891 | 1.0e-6 | **BEATS** |
| ETH-USD | h=1 | 0.6884 | 0.6844 | -0.58% | +0.514 | 0.607 | INCONCLUSIVE |
| ETH-USD | h=5 | 0.3726 | 0.3736 | +0.29% | -0.061 | 0.952 | INCONCLUSIVE |
| ETH-USD | h=10 | 0.3777 | 0.3745 | -0.86% | +0.107 | 0.915 | INCONCLUSIVE |
| LTC-USD | h=1 | 0.6508 | 0.6558 | +0.76% | — | 0.695 | INCONCLUSIVE |
| LTC-USD | h=5 | 0.4029 | 0.4327 | +6.89% | — | 0.396 | INCONCLUSIVE |
| LTC-USD | h=10 | 0.3856 | 0.4261 | +9.50% | — | 0.414 | INCONCLUSIVE |
| SOL-USD | h=1 | 0.6179 | 0.6100 | -1.29% | — | 0.325 | INCONCLUSIVE |
| SOL-USD | h=5 | 0.2918 | 0.2847 | -2.48% | — | 0.528 | INCONCLUSIVE |
| SOL-USD | h=10 | 0.2512 | 0.2399 | -4.74% | — | 0.451 | INCONCLUSIVE |
| XRP-USD | h=1 | 0.8598 | 0.8452 | -1.73% | +1.324 | 0.186 | INCONCLUSIVE |
| XRP-USD | h=5 | 0.4931 | 0.5182 | +4.85% | -0.711 | 0.477 | INCONCLUSIVE |
| XRP-USD | h=10 | 0.4787 | 0.5185 | +7.69% | -0.731 | 0.465 | INCONCLUSIVE |
| ADA-USD | h=1 | 0.7073 | 0.6945 | -1.84% | +0.868 | 0.386 | INCONCLUSIVE |
| ADA-USD | h=5 | 0.3794 | 0.4064 | +6.66% | -1.016 | 0.310 | INCONCLUSIVE |
| ADA-USD | h=10 | 0.3440 | 0.3650 | +5.77% | -0.652 | 0.514 | INCONCLUSIVE |
| DOT-USD | h=1 | 0.6300 | 0.6369 | +1.08% | -0.642 | 0.521 | INCONCLUSIVE |
| DOT-USD | h=5 | 0.3415 | 0.3801 | +10.15% | -1.780 | **0.076** | INCONCLUSIVE (close) |
| DOT-USD | h=10 | 0.3262 | 0.3593 | +9.21% | -1.298 | 0.195 | INCONCLUSIVE |

**Summary** : **3 BEATS / 0 NO BEATS / 18 INCONCLUSIVE** (out of 21 configs).

### Sign-test cluster level

- Per-coin verdict (collapse horizons via majority) : BTC=BEATS, ETH/LTC/SOL/XRP/ADA/DOT=INCONCLUSIVE → 1/7 BEATS.
- Sign-test : binom(7, 1, 0.5) p ≈ 0.063 → **NOT significant at α=0.05**.
- Per-config sign-test (BEATS vs not-BEATS, 21 configs) : 3/21, p binom ≈ 0.0006 (vs H0 = 50%) but H0 must be 5% (chance-level for p<0.05) → 3/21 not significant either way.
- **Verdict G.2 honnête : NO BEATS cluster-level**. BEATS BTC standalone uniquement.

### Per-Horizon Pattern (BTC)

L'effet asymétrie **augmente avec l'horizon** : 5% → 24% → 37% MSE reduction de h=1 à h=10. C'est cohérent avec la littérature : leverage effect a un impact à long terme (volatilité persistante post-baisse), peu d'effet immédiat. Inverse exact de M12 où h=5 était la dead zone et h=10 le sweet spot — M16 a son edge sur longs horizons.

### Pourquoi ETH = INCONCLUSIVE ?

Hypothèse : ETH est un actif plus jeune (Bitstamp 1495 RV days vs BTC 2278), avec moins d'asymétrie observable sur la période. Les rallies post-mid-2020 et post-Merge 2022 ont noyé le pattern leverage-effect classique. À tester :
- Filtrer pré-2021 vs post-2021 sur ETH
- Tester WBTC/sETH/cbETH (tracking proxies) pour confirmation cross-source
- Étendre période ETH si possible (pre-2018 historical)

Note : les autres coins (LTC/SOL/MATIC/XRP/ADA/DOT) attendent le résultat full sweep `b0nogs2rf` (yfinance load).

## Comparison with M12 HAR-RV-J (Sharpe vs MSE)

| Modèle | Critère | BTC h=10 | ETH h=10 | Notes |
|--------|---------|----------|----------|-------|
| M12 HAR-RV-J | Sharpe (Kelly) BEATS | 4/4 +0.0032 | 4/4 +0.0153 | sign-test 7.9e-7 |
| M12 HAR-RV-J | MSE | -174.7% LTC h=10 (worse) | +69.7% ADA h=10 (worse) | BEATS sizing pas accuracy |
| M16 HAR-Asym | MSE BEATS | +36.7% BTC h=10 | -0.9% INCONC | Inverse pattern |

**Recommandation** : combiner les deux modèles dans un ensemble. M12 pour position sizing (jump signal), M16 pour forecast accuracy (leverage signal). Ensemble feature engineering possible : `RV+_t, RV-_t, J_t` (jumps from M12) → M17 candidate composite HAR-LJ-Asym.

## Risks & Caveats (Discipline ML/Trading)

| Discipline | M16 conformité |
|------------|----------------|
| Walk-forward 5-fold expanding | ✓ (héritée `walk_forward_har` PR #938) |
| Multi-seed ≥4 | **N/A** (HAR OLS deterministic, std=0 confirmé) |
| Edge ≥ 2σ cross-seed | **N/A** même raison |
| OOS strict (no leak) | ✓ via shift(1) sur tous les régresseurs |
| Diebold-Mariano test | ✓ paired loss differentials, MSE log RV |
| Transaction costs | ⚠ Non applicable — M16 = forecast pur, pas backtest stratégie |
| Anti-survivorship | ✓ BTC/ETH historique full disponible |
| Anti-data-snooping | ⚠ Modèle ABDP 2007 connu publié, pas sur-fit ad-hoc |
| Baseline majority vs random | ✓ HAR Classic = standard literature baseline |
| FAANG/Mag7 in training | ✓ Aucun (crypto only) |
| Data source | Bitstamp BTC, Binance ETH (pas yfinance pour BTC/ETH primaires) |

## Limites identifiées

1. **MSE n'est pas une métrique de trading** — la BEATS sur MSE ne garantit pas des P&L supérieurs. Suite : tester M16 features dans un sleeve Kelly (M16-Kelly) et reporter Sharpe + MaxDD + Calmar.
2. **Subset 2 coins** — verdict global suspendu en attente full sweep `b0nogs2rf`. Si LTC/SOL/MATIC confirment BTC pattern : BEATS robuste. Si majority ETH-like : INCONCLUSIVE général.
3. **HAR famille = paramétrique simple** — vs DL (M5-M9 NO BEATS sur 96 runs M8 sweep), HAR survit à l'OOS où DL meurt. Confirme leçon M8/M11ef : famille paramétrique > DL sur RV crypto.
4. **Pas de transaction costs** — l'edge MSE doit être validé sur Sharpe net post-50bps avant inclusion Portfolio Hybride sleeve crypto.

## Next Steps

1. ✅ **Full sweep complété** : verdict NO BEATS cluster, BEATS BTC standalone uniquement.
2. ☐ **PAS de PR M16 standalone** — pas assez de signal cluster pour un module dédié. Documenter le verdict honnête en mémoire et passer à M17.
3. ☐ **M17 ensemble candidate** : composite HAR-LJ-Asym (M12 jumps + M16 semivariances) — combiner les deux **paramétriques**. M12 capture jumps + sizing edge cluster, M16 capture leverage edge BTC. Test : ajouter RV+_t et RV-_t comme features additionnelles dans M12 sur 7 coins.
4. ☐ **M16-Kelly BTC-only** (optionnel) : utiliser M16 forecast pour un sleeve Kelly **BTC standalone** dans Portfolio Hybride sleeve crypto. Tester si MSE-BEATS BTC se traduit en Sharpe-BEATS net 50bps.
5. ☐ **Documenter dans BOOK_MAPPING.md Ch05** (Model Choice) — HAR family confirmée comme only consistently winning family sur RV crypto (M2/M11/M12) vs DL (NO BEATS M5-M9-M10). M16 standalone = échec famille HAR (premier).
6. ☐ **DOT h=5 close à significance (p=0.076)** : retest avec période étendue ou horizons intermédiaires (h=3, h=7) pour confirmer absence d'edge.

## References

- **Andersen, Bollerslev, Diebold, Patton (2007)** "No-Arbitrage Semi-Martingale Restrictions for Continuous-Time Volatility Models Subject to Leverage Effects, Jumps and i.i.d. Noise: Theory and Testable Distributional Implications" *Journal of Econometrics* 138(1)
- **Black (1976)** "Studies of stock price volatility changes" *Proceedings of the 1976 Meetings of the Business and Economic Statistics Section*
- **French, Schwert, Stambaugh (1987)** "Expected stock returns and volatility" *Journal of Financial Economics*
- **Corsi (2009)** "A Simple Approximate Long-Memory Model of Realized Volatility" *Journal of Financial Econometrics* (HAR baseline)
- M12 HAR-RV-J doc : `M12_HAR_RV_J.md`
- M11 HAR Kelly : `M11b_HAR_KELLY_LONG_HORIZONS.md`

## Files

- Script : `scripts/har_asymmetric.py`
- Results : `scripts/results/m3_har_asymmetric.json` (subset BTC+ETH)
- Logs : `/tmp/m16b_har_asym.log`, `/tmp/m16b_full_har_asym.log` (full pending)

## Cycle 33 Verdict (Cumulative M-series Status)

| M-track | Verdict | Notes |
|---------|---------|-------|
| M3 baseline | BASELINE | HAR Classic |
| M5/M6/M7 | NO BEATS | DL pure failure |
| M8 SOTA sweep | NO BEATS | TFT/Mamba/iTransformer/PatchTST 96 runs |
| M9 TFT | NO BEATS | NeurIPS arch fail crypto |
| M10 Realized GARCH | NO BEATS | |
| M11 HAR Kelly | BEATS | Long horizons fee-robust |
| M11ef ensemble + tx cost | BEATS K60, dilution VTH | edge survit 50bps |
| M12 HAR-RV-J | BEATS | Sharpe via jump decomp |
| M13 MS-HAR | NO BEATS | C32/C33 |
| M14 HEAVY | NO BEATS | C33 (48/84 p=0.11) |
| M15 LSTM | TBD | po-2024 dispatch |
| **M16 HAR-Asym** | **NO BEATS cluster** | BTC standalone BEATS (3/3 horizons p<0.001), 6 autres coins INCONCLUSIVE. 1/7 sign-test cluster non-significatif. |

**Pattern HAR family révisé** : M11 / M11ef / M12 = 3/3 BEATS dans la famille HAR paramétrique cluster-wide. **M16 = premier échec HAR famille** (BTC only). DL famille = 0/4 BEATS sur sweep exhaustif. Leçon book + leçon M8 verdict : paramétrique > DL pour RV crypto, **mais paramétrique standalone HAR-Asym leverage-only ne suffit pas hors BTC**. Sweep continue : M15 LSTM (po-2024 BG en flight), puis M17 ensemble HAR-LJ-Asym.
