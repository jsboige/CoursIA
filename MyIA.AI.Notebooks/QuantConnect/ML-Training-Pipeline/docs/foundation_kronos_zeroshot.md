# Foundation-model zero-shot — Kronos sur le panier anti-biais (spin-out #8607, 2e rung)

> Script associé : [`scripts/eval_kronos_zeroshot.py`](../scripts/eval_kronos_zeroshot.py) (réécrit sur l'API réelle ce cycle).
> Résultats bruts : [`scripts/results/kronos_zeroshot/`](../scripts/results/kronos_zeroshot/) (`results.json` + `verdict.md`).
> 2e rung foundation-model du spin-out #8607 de l'Epic #1409 (parqué après L6 ROBUST NO BEATS). Le 1er rung était Chronos-Bolt ([`docs/foundation_chronos_zeroshot.md`](foundation_chronos_zeroshot.md), c.893 / #8610).

## Verdict : NO BEATS (panier, robuste sur 3 horizons)

Un **foundation-model zero-shot** pré-entraîné sur **K-lines OHLCV** (Kronos-base, AAAI 2026, ~102M params, 12B K-lines multi-actifs, *aucun* entraînement sur l'univers) **ne bat pas majority-class** sur le panier anti-biais en prévision de **direction**, à aucun des 3 horizons demandés par #8607 (h=22/66/132). Sur **9 configurations** (3 symboles × 3 horizons), **9/9** ont un edge strictement négatif, `beats_valid=False` partout, DirAcc sous la baseline majority sur les 9.

## Hypothèse (#8607)

Le 1er rung foundation-model (Chronos-Bolt, c.893) était NO BEATS — mais son harnais a révélé un **artefact méthodologique** (C893-L) : Chronos-Bolt est déterministe, donc `std_edge=0` toutes seeds identiques, et le gate `beats_valid` collapsait en « edge>0=BEATS ». La question de ce 2e rung : un foundation-model **stochastique** (Kronos, échantillonnage autorégressif) donne-t-il un résultat différent — la variance cross-seed étant alors *réelle* et le gate *opérant* ? Biais de fouille après 6 réfutations (L1-L6) → **barre complète** : edge ≥2σ cross-seed, ≥3/4 seeds positifs, bat majority, coûts tx.

## Méthode

- **Modèle** : **Kronos-base** (`NeoQuasar/Kronos-base`, ~102M params, AAAI 2026, transformer pré-entraîné sur 12B K-lines OHLCV) en mode **zero-shot** (figé, *aucun* fine-tuning). Distribué en repo source (pas de wheel PyPI) ; importé via `from model import Kronos, KronosTokenizer, KronosPredictor`.
- **Inférence** : `prediction_length` ∈ {24, 66, 132} (≈ h=22, 66, 132 jours de bourse), contexte `seq_len=96`, échantillonnage autorégressif (`T=1.0, top_p=0.9, sample_count=1`). Device GPU (RTX 3070 8GB, `CUDA_VISIBLE_DEVICES=0`, env `coursia-ml-training`, torch 2.5.1+cu121).
- **Univers** : panier anti-biais (FORBIDDEN FAANG/Mag7) — SPY, TLT, GLD via `data_utils.load_data` (yfinance daily OHLCV, data-source-to-convert AUTORISÉ).
- **Validation** : walk-forward **5 fenêtres**, **5 seeds** (0/1/7/42/99) — le seed contrôle l'échantillonnage AR (`torch.manual_seed`+`np.random.seed` avant chaque `predict`), donc la variance cross-seed est **significative** (contrairement à Chronos). Coût tx **10 bps** par rebalancement, baseline majority-class.
- **Métrique** : `edge_vs_majority = DirAcc − majority_baseline`. Gate `beats_valid` : `seeds≥4 AND mean_edge>0 AND (std<1e-10 OR mean_edge≥2·std)`.

## Le harness était spéculatif — réécrit sur l'API réelle

`eval_kronos_zeroshot.py` appelait `from kronos import KronosPipeline` (API inexistante). Réécrit sur l'API réelle groundée firsthand (`model/__init__.py` + `examples/prediction_example.py`) : `KronosPredictor` + OHLCV DataFrame + `x_timestamp`/`y_timestamp`. **SOTA-OK** (`is_mock=False`). Voir [`verdict.md`](../scripts/results/kronos_zeroshot/verdict.md).

## Résultats — sweep horizon × symbole (walk-forward 5 fenêtres, 5 seeds, 10 bps)

| Horizon | SPY DirAcc | SPY majority | SPY edge | TLT edge | GLD edge |
|---------|-----------|--------------|----------|----------|----------|
| h≈22 (`pred_len=24`) | 0.5113 | 0.5461 | **-0.0348** | **-0.0174** | **-0.0428** |
| h=66 | 0.5058 | 0.5461 | **-0.0403** | **-0.0201** | **-0.0219** |
| h=132 | 0.5014 | 0.5461 | **-0.0448** | **-0.0245** | **-0.0249** |

(TLT majority 0.5130, GLD majority 0.5315.) **9/9 edges négatifs.** `std_edge` 0.0086-0.0502 (strictement positif — Kronos est stochastique).

## Findings clés

1. **Kronos est stochastique → C893-L ne s'applique pas.** Contrairement à Chronos-Bolt (déterministe, `std_edge=0`), Kronos échantillonne autorégressivement → `std_edge > 0` partout (0.0086 à 0.0502). Le gate multi-seed est donc un **vrai test** pour Kronos, pas un artefact dégénéré. Les 2 « BEATS » dégénérés de Chronos (TLT h22, SPY h66) n'ont pas d'équivalent Kronos.

2. **Négatif uniforme (9/9), plus propre que Chronos.** Chronos avait 2 edges positifs dégénérés (artefact harnais). Kronos : 9/9 négatifs, 0 config avec ≥3/5 seeds positifs (max 2/5 sur SPY h22), DirAcc sous majority partout. La variance cross-seed, loin de révéler un signal caché, confirme le **bruit** : aucun edge positif consistant.

3. **Aucune configuration ne bat majority-class de façon robuste.** Barre pleine #8607 (≥2σ cross-seed ET ≥3/4 seeds positifs ET bat majority) : non satisfaite sur les 9 configs. NO BEATS.

4. **Le coût tx achève l'edge résiduel.** Tous les edges (< 0, et même les DirAcc autour de 0.50) sont consommés par les 10 bps par rebalancement. La prévision de direction zero-shot n'a pas la précision pour couvrir le turnover sur cet univers liquide (ETF).

## Implication pour #8607 / #1409

Un **2e** paradigme foundation-model zero-shot (K-lines OHLCV, cette fois) **ne bat pas majority-class** sur le panier — rejoignant Chronos-Bolt (langage des TS). **Deux foundation-models, deux échecs.** Cela **renforce** la conclusion centrale de l'Epic #1409 : l'alpha sur cet univers provient de **politiques d'action apprises** (L4 Decision Transformer), **pas** d'overlays *trend*, de *sizing* régime-conditionnel, **ni de prévision foundation-model zero-shot** — qu'elle vienne du « langage des séries temporelles » (Chronos) ou de K-lines OHLCV multi-actifs (Kronos).

Quatre paradigmes testés désormais (L1-L6 + 2 foundation rungs), un seul BEATS (action-based).

## Comparaison honnête au M15 LSTM (KEEPER Gate V2)

Comme pour Chronos, la comparaison *foundation-zero-shot* vs *M15-fine-tuned* n'est **pas apples-to-apples** : univers disjoints (ETF vs crypto), cibles disjointes (direction vs log-RV), horizons disjoints (h=22-132 vs h=1-10), entraînement disjoint (zero-shot vs fine-tuned). Le verdict « Kronos bat-il le LSTM spécialisé ? » exige un terrain commun — out-of-scope ce cycle.

## Résiduel

- **M15 sur terrain commun** (ETF-direction-long-horizon) : fine-tuner M15 sur le même univers+cible+horizon — out-of-scope, multi-cycle.
- **t-stat cross-fenêtre propre** : le gate actuel utilise std cross-seed (significatif pour Kronos), mais un t-stat cross-fenêtre formaliserait la significativité OOS — non codé ce cycle.
- **Kronos-large** (499M) : non open-source, inaccessible.

## Références

- Kronos : Liu et al., AAAI 2026 — « Kronos : A learned K-line codec tokenizer for financial time-series forecasting » (shiyu-coder/Kronos, NeoQuasar HF mirrors).
- Chronos-Bolt (1er rung) : [`docs/foundation_chronos_zeroshot.md`](foundation_chronos_zeroshot.md).
- M15 LSTM (KEEPER Gate V2) : [`docs/M15_LSTM_RV.md`](M15_LSTM_RV.md).
- L4 Decision Transformer (seul BEATS du ladder) : [`docs/L4_decision_transformer.md`](L4_decision_transformer.md).
- Spin-out : issue #8607. Epic parent parqué : #1409.
