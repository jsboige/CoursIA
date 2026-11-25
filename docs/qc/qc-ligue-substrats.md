# Recensement durable — substrats de recherche de la ligue QC

**Périmètre** : `MyIA.AI.Notebooks/QuantConnect/research/` + `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/`

**Issue** : [#26318](https://github.com/jsboige/CoursIA/issues/26318) (sous-grain **D4** de [#24282](https://github.com/jsboige/CoursIA/issues/24282), programme de mesure de la ligue [#19821](https://github.com/jsboige/CoursIA/issues/19821), protocole [#22828](https://github.com/jsboige/CoursIA/issues/22828))

**Dernière re-vérification** : 2026-11-19, contre `origin/main` (lane `myia-po-2023:CoursIA-2`)

---

## Ce que ce document est — et n'est pas

Ce document est le **recensement durable** des substrats de recherche de la ligue QuantConnect : la liste complète des carnets `research_*` du dossier `research/` et du pipeline `ML-Training-Pipeline/`, leur **statut de conservation**, et le **principe de séparation substrat / doctrine** qui les gouverne.

Il **n'ouvre pas de chantier de correction**. Ces carnets appartiennent au programme de mesure de la ligue (#19821, protocole #22828) où le verdict `NO BEATS`, accompagné de sa lecture honnête, **est la méthode**, pas un symptôme de substrat mal choisi — les marchés ne se réécrivent pas comme un terrain pédagogique. Tout ce qui, lu en surface, ressemble ici à un « défaut » est d'abord une **mesure**.

L'instruction **D1–D3** promise par l'issue (séparer l'éventuel residu corrigeable de la doctrine) est un grain `qc` **distinct et ultérieur** ; ce document ne la précède pas, il lui fournit la **carte à jour** sur laquelle elle portera.

---

## Principe substrat / doctrine

Le scan D4 (2026-11-13, lane `myia-po-2024:CoursIA`) sépare **deux parts** dans chaque carnet :

- **La part substrat** — le choix d'univers, de fenêtre, d'horizons, de features. C'est la part *qualifiable* : c'est elle que l'instruction D1–D3 doit, **une fois**, séparer pour en dégager le residu éventuellement corrigeable.
- **La part doctrine** — le verdict lui-même (`NO BEATS`, « B&H 1.1504 », « Edge moyen sur majority : −0.0277 »). C'est la *méthode* de la ligue : un verdict négatif **documenté** est un résultat, pas une erreur.

Exemples représentatifs portés par l'issue :

- `research_l1_tsmom` c.8 — « NO BEATS 0/4 ; B&H 1.1504 » avec « Coupable = la rotation quotidienne » ;
- `m9_tft_vol_research` c.4 — « Edge moyen sur majority : −0.0277 » avec « pourquoi le Transformer échoue ».

**Toute correction qui toucherait le protocole pré-enregistré** (fenêtres, univers, seeds) est **hors du périmètre** de ce recensement — elle relèverait d'un grain `qc` dédié, jamais d'un geste de conservation.

---

## Recensement re-vérifié (2026-11-19)

**43 carnets** sur `origin/main` : **25** dans `research/` + **18** dans `ML-Training-Pipeline/`.

Colonne **Origine** :

- `scan 11-13` — présent dans le recensement one-shot de l'issue (2026-11-13), avec sa qualification CONFIRME / PLAUSIBLE ;
- `+ post-11-13` — ajouté **après** ce scan, donc absent du recensement d'origine.

### `QuantConnect/research/` (25)

| Carnet | Origine |
|---|---|
| `intraday_volume_periodicity` | + post-11-13 |
| `research_btc_ml` | + post-11-13 |
| `research_composite_ff_aw` | scan 11-13 (PLAUSIBLE) |
| `research_composite_mom_regime` | scan 11-13 (PLAUSIBLE) |
| `research_day_of_week` | scan 11-13 (PLAUSIBLE) |
| `research_fifty_two_week_high` | scan 11-13 (CONFIRME) |
| `research_idio_vol_anomaly` | + post-11-13 |
| `research_iv_rank_strike_clusters` | + post-11-13 |
| `research_m11ef_ensemble` | scan 11-13 (CONFIRME) |
| `research_m12_har_rv_j` | scan 11-13 (CONFIRME) |
| `research_m12_har_rv_j_minute` | + post-11-13 |
| `research_m12_hf_btc_local` | + post-11-13 |
| `research_m12_hf_dm_test` | + post-11-13 |
| `research_month_of_year` | scan 11-13 (PLAUSIBLE) |
| `research_quality_lowvol` | scan 11-13 (PLAUSIBLE) |
| `research_risk_parity` | + post-11-13 |
| `research_rl_grpo` | scan 11-13 (PLAUSIBLE) |
| `research_rl_intro` | scan 11-13 (CONFIRME) |
| `research_rl_multi_asset` | scan 11-13 (PLAUSIBLE) |
| `research_rl_ppo` | scan 11-13 (CONFIRME) |
| `research_rl_reward_shaping` | scan 11-13 (PLAUSIBLE) |
| `research_rl_tactical_overlay` | scan 11-13 (PLAUSIBLE) |
| `research_st_reversal` | scan 11-13 (CONFIRME) |
| `research_turn_of_month` | scan 11-13 (CONFIRME) |
| `research_vrp_putwrite` | + post-11-13 |

### `QuantConnect/ML-Training-Pipeline/` (18)

| Carnet | Origine |
|---|---|
| `ML-Research-Template` | + post-11-13 (template, pas un substrat de stratégie) |
| `hmm_alpha_dm_research` | + post-11-13 |
| `hmm_alpha_research` | scan 11-13 (CONFIRME) |
| `m11e_ensemble_research` | scan 11-13 (CONFIRME) |
| `m12_har_rv_j_research` | scan 11-13 (CONFIRME) |
| `m15_lstm_rv_research` | scan 11-13 (CONFIRME) |
| `m15_lstm_rv_sc_validation` | scan 11-13 (CONFIRME) |
| `m3_har_asymmetric_semivariance` | + post-11-13 |
| `m4_dlinear_vol_research` | + post-11-13 |
| `m4_dlinear_vol_sc_validation` | scan 11-13 (CONFIRME) |
| `m5_hmm_regime_research` | scan 11-13 (PLAUSIBLE) |
| `m9_tft_vol_research` | scan 11-13 (CONFIRME) |
| `research_l1_tsmom` | scan 11-13 (CONFIRME) |
| `research_l2_dual_momentum` | scan 11-13 (CONFIRME) |
| `research_l3_trend` | scan 11-13 (CONFIRME) |
| `research_l4_decision_transformer` | scan 11-13 (CONFIRME) |
| `research_what_dl_can_predict` | + post-11-13 |
| `xrp_dt_foldwise_research` | + post-11-13 |

---

## Conservation

**28/28** du recensement d'origine (scan 11-13) sont **présents** sur `origin/main` à la date de cette re-vérification ; **15** carnets ont été ajoutés depuis (14 substrats de stratégie + 1 template `ML-Research-Template`) ; **43** au total. **Aucun carnet du recensement d'origine n'a été perdu.**

Le recensement d'origine de l'issue (2026-11-13) comptait **28** carnets (18 CONFIRME + 10 PLAUSIBLE) ; la dérive mesurée ici est donc de **+15** entre le 13/11 et le 19/11 — cohérent avec un programme de mesure de la ligue **en production** (de nouveaux substrats s'ajoutent au fil des grains `qc`).

---

## Maintien du recensement

Ce document est une **instantanée datée**, pas un invariant : la ligue étant un programme vivant, le décompte dérivera à nouveau. Pour le re-vérifier, la commande de référence est :

```bash
git ls-tree -r --name-only origin/main \
  -- MyIA.AI.Notebooks/QuantConnect/research/ \
     MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/ \
  | grep '\.ipynb$'
```

La colonne « Origine » d'une re-vérification ultérieure se lit contre **cette** instantanée : un carnet `+ post-11-13` ici qui serait absent plus tard serait une **suppression** à signaler ; un carnet nouveau serait un `+ post-<date>`.

---

## Voir aussi

- [#19821](https://github.com/jsboige/CoursIA/issues/19821) — programme de mesure de la ligue QC (le verdict `NO BEATS` est la méthode)
- [#22828](https://github.com/jsboige/CoursIA/issues/22828) — protocole de la ligue
- [qc-strategies-status.md](qc-strategies-status.md) — état des stratégies QC (vue complémentaire, orientée verdicts)
- [quantconnect.md](quantconnect.md) — structure et conventions QuantConnect du dépôt
