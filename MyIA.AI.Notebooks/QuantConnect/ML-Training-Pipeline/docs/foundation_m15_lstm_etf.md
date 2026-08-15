# LSTM fine-tuned sur ETF direction — terrain commun foundation-models (spin-out #8607, 3e rung)

> Script associé : [`scripts/eval_m15_lstm.py`](../scripts/eval_m15_lstm.py).
> Résultats bruts : [`scripts/results/m15_lstm_etf/`](../scripts/results/m15_lstm_etf/) (`results.json` + `verdict.md`).
> 3e rung du spin-out #8607 de l'Epic #1409 / #1454 (parqué après L6 ROBUST NO BEATS). 1er rung = Chronos-Bolt ([`foundation_chronos_zeroshot.md`](foundation_chronos_zeroshot.md), c.893 / #8610). 2e rung = Kronos ([`foundation_kronos_zeroshot.md`](foundation_kronos_zeroshot.md), c.897 / #8620). Les deux **zero-shot**, tous deux NO BEATS.

## Verdict : NO BEATS (panier, robuste sur 3 horizons) — le plus propre des 3 rungs

Un **LSTM fine-tuned** (Log-LSTM, ~19k params) sur la **direction** des ETF du panier anti-biais **ne bat pas majority-class**, à aucun des 3 horizons (h=22/66/132). Sur **9 configurations** (3 symboles × 3 horizons), **9/9** edge strictement négatif, `beats_valid=False` partout, **0/5 seeds positives sur chaque config**. Le verdict le plus tranché des 3 rungs foundation.

## Hypothèse (#8607)

Les 2 premiers rungs (foundation-models **zero-shot**) étaient NO BEATS. Question de ce 3e rung : un LSTM **fine-tuned** sur l'ETF — qui apprend donc spécifiquement la dynamique de prix de l'univers d'évaluation — extrait-il un edge directionnel que les modèles zero-shot n'ont pas trouvé ? Si oui, l'échec zero-shot serait un défaut de généralisation (pas assez d'entraînement sur l'ETF), pas un plafond fondamental. Si non, le plafond est structurel : la direction des prix ETF n'est pas prévisible à long horizon, figé ou entraîné.

**Réponse : non.** Le fine-tuning n'aide pas. Barre complète #8607 (edge ≥2σ cross-seed ET ≥3/4 seeds positifs ET bat majority) : non satisfaite sur les 9 configs.

## Méthode (terrain commun apples-to-apples avec Chronos / Kronos)

- **Modèle** : Log-LSTM (Hochreiter & Schmidhuber 1997), `input=2` `[log_return, sign]`, `hidden=64`, 1 layer, FC → `pred_len`. **Fine-tuned** (entraîné par fold expanding). Cible = chemin de log-return cumulé (direct multi-step, MSE). DirAcc = day-over-day sign match (**identique** à `evaluate_window`).
- **Univers** : panier anti-biais (FORBIDDEN FAANG/Mag7) — SPY, TLT, GLD via `data_utils.load_data` sur `datasets/panier` (yfinance daily OHLCV).
- **Validation** : walk-forward **5-fold expanding**, **5 seeds** (0/1/7/42/99), coût tx **10 bps**, baseline majority-class.
- **Horizons** : `pred_len` ∈ {24, 66, 132} (~ h=22/66/132 jours de bourse).
- **Métrique** : `edge_vs_majority = DirAcc − majority_baseline`. Gate `beats_valid` identique aux rungs 1-2.
- **Device** : GPU RTX 3070 8GB (`CUDA_VISIBLE_DEVICES=0`, env `coursia-ml-training`, torch 2.5.1+cu121). `is_trained=True`.

## Design — walk-forward self-contained (C898-L en reverse)

M15 est **fine-tuned** (entraîné par fold), structurellement différent du zero-shot window eval de Chronos/Kronos (modèle figé → prédire par fenêtre). Ce harnais possède sa **propre walk-forward** (comme `m15_lstm_rv.walk_forward_lstm`) et réutilise uniquement les helpers **stables** (`load_data`, `compute_majority_baseline`, `compute_direction_accuracy`, gate `beats_valid`) — **pas** `build_evaluation_windows` / `evaluate_window` (le contrat zero-shot qui mute avec #8620). Métriques + protocole IDENTIQUES → comparaison cross-modèle apples-to-apples **et** robustesse au merge #8620 (aucune dépendance de contrat mutable partagée).

## Résultats — sweep horizon × symbole (walk-forward 5 folds, 5 seeds, 10 bps, GPU)

| Horizon | SPY DirAcc | SPY majority | SPY edge | TLT edge | GLD edge |
|---------|-----------|--------------|----------|----------|----------|
| h≈22 (`pred_len=24`) | 0.5032 | 0.5480 | **-0.0448** | **-0.0160** | **-0.0335** |
| h=66 | 0.5022 | 0.5480 | **-0.0458** | **-0.0131** | **-0.0317** |
| h=132 | 0.5025 | 0.5480 | **-0.0455** | **-0.0132** | **-0.0321** |

(TLT majority 0.5127, GLD majority 0.5306.) **9/9 edges négatifs, 0/5 seeds positives sur chaque config.** `std_edge` 0.0003-0.0021 (strictement positif — M15 est stochastique via init+minibatch, C897-L vérifié).

## Findings clés

1. **Le fine-tuning ne sauve pas la prévision de direction.** Conclusion centrale : un LSTM qui **apprend** la dynamique de prix ETF n'obtient pas un edge supérieur aux foundation-models zero-shot. DirAcc ~0.50 partout (sous majority 0.51-0.55). Le plafond n'est **pas** un défaut de généralisation zero-shot — il est **structurel** : la direction des prix ETF liquides à long horizon n'est pas prévisible par les rendements passés seuls.

2. **NO BEATS plus propre que les foundation-models.**
   - **Chronos-Bolt** (zero-shot, déterministe) : 2 edges positifs **dégénérés** (artefact harnais C893-L, `std_edge=0`).
   - **Kronos** (zero-shot, échantillonnage AR) : 0 edge positif, mais jusqu'à 2/5 seeds positives sur SPY h≈22 (variance faux-espoir).
   - **M15 fine-tuned** : 0 edge positif, **0/5 seeds positives sur les 9 configs**, `std_edge` minimal (0.0003-0.0021). Le verdict le plus tranché.

3. **C897-L vérifié : le gate multi-seed est un vrai test pour M15.** `std_edge > 0` partout → gate non-dégénéré (contrairement à Chronos-Bolt C893-L). Mais la stochasticité cross-seed est **plus faible** que Kronos (échantillonnage AR) : le fine-tuning converge vers un optimum quasi-déterministe.

## Comparaison honnête au M15 LSTM d'origine (log-RV crypto, KEEPER Gate V2)

Le M15 LSTM d'origine ([`M15_LSTM_RV.md`](M15_LSTM_RV.md), `m15_lstm_rv.py`) cible la **volatilité** (log-realized variance) sur **crypto**, à **court horizon** (h=1/5/10), fine-tuned — problème **différent** (la volatilité est plus persistante et prévisible que la direction). Ce 3e rung adapte l'architecture M15 à la **direction ETF long-horizon** pour le terrain commun foundation-models. La comparaison direction-vs-volatilité n'est pas apples-to-apples : la volatilité (auto-régressive, clusterée) est un objectif plus tendre que la direction (quasi-martingale).

## Implication pour #8607 / #1409 / #1454

**Quatre paradigmes testés, le même verdict : la prévision de direction prix ne bat pas majority.**
- L1-L5 overlays (trend, sizing régime) : NO BEATS.
- Foundation-model zero-shot langage-TS (Chronos-Bolt) : NO BEATS.
- Foundation-model zero-shot K-lines OHLCV (Kronos) : NO BEATS.
- **LSTM fine-tuned direction (M15, ce rung) : NO BEATS.**

Un seul paradigme BEATS : les **politiques d'action apprises** (L4 Decision Transformer). La conclusion de #1409 se **renforce** : l'alpha sur cet univers ETF liquide provient de **politiques d'action** (quand entrer/sortir, sizing), **pas** de la prévision de direction des prix — qu'elle soit zero-shot, fine-tuned, ou trend-overlay.

## Résiduel

- **t-stat / DM cross-fenêtre Chronos↔Kronos↔M15** : infrastructure existe (`diebold_mariano.py`). Application formelle post-merge #8620 (aligner les results.json).
- **Refit-every-22 intra-fold** : le pilote entraîne une fois par fold (expanding) ; le refit périodique intra-fold (comme `m15_lstm_rv`) = raffinement méthodologique multi-cycle.
- **Features plus riches** : ce rung utilise `[log_return, sign]` seuls (minimal, apples-to-apples avec la fenêtre close des foundation rungs). Ajouter features (vol, momentum) = expérience distincte.

## Références

- LSTM : Hochreiter & Schmidhuber, 1997 — « Long Short-Term Memory ».
- Chronos-Bolt (1er rung) : [`foundation_chronos_zeroshot.md`](foundation_chronos_zeroshot.md).
- Kronos (2e rung) : [`foundation_kronos_zeroshot.md`](foundation_kronos_zeroshot.md).
- M15 LSTM d'origine (log-RV crypto, KEEPER Gate V2) : [`M15_LSTM_RV.md`](M15_LSTM_RV.md).
- L4 Decision Transformer (seul BEATS du ladder) : [`L4_decision_transformer.md`](L4_decision_transformer.md).
- Spin-out : issue #8607. Epic parent parqué : #1409. Capability-core : #1454.
