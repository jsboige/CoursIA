# M15 Log-LSTM fine-tuned sur ETF direction — verdict terrain commun (spin-out #8607, 3e rung)

> Script associé : [`scripts/eval_m15_lstm.py`](../../eval_m15_lstm.py).
> Résultats bruts : [`results.json`](results.json) (45 combos consolidés, `is_trained=True`, `device=cuda`).
> 3e rung du spin-out foundation-model #8607 de l'Epic #1409 / #1454. 1er rung = Chronos-Bolt ([`foundation_chronos_zeroshot.md`](../../../docs/foundation_chronos_zeroshot.md), c.893 / #8610). 2e rung = Kronos ([`foundation_kronos_zeroshot.md`](../../../docs/foundation_kronos_zeroshot.md), c.897 / #8620). Les deux zero-shot, tous deux NO BEATS.

## Verdict : NO BEATS (panier, robuste sur 3 horizons) — le plus propre des 3 rungs

Un LSTM **fine-tuned** (Log-LSTM, ~19k params, direct multi-step) sur la **direction** des ETF du panier anti-biais ne bat pas majority-class, à aucun des 3 horizons (h=22/66/132), en walk-forward 5-fold, 5 seeds, coûts tx 10 bps. Sur les **9 configurations** (3 symboles × 3 horizons), **9/9** ont un edge strictement négatif, `beats_valid=False` partout, **0/5 seeds positives sur chaque config**.

## Question (#8607)

Les 2 premiers rungs (foundation-models **zero-shot**) étaient NO BEATS. La question de ce 3e rung, complémentaire : un LSTM **fine-tuned** sur l'ETF — donc qui apprend spécifiquement la dynamique de prix de l'univers d'évaluation — extrait-il un edge directionnel que les modèles zero-shot n'ont pas trouvé ? Si oui, l'échec zero-shot serait un défaut de généralisation (pas assez d'entraînement sur l'ETF), pas un plafond fondamental. Si non, le plafond est structurel : la direction des prix ETF n'est pas prévisible à long horizon, que le modèle soit figé ou entraîné.

**Réponse : non.** Le fine-tuning n'aide pas. Le verdict est même **plus propre** que les foundation-models zero-shot.

## Méthode (terrain commun apples-to-apples avec Chronos / Kronos)

- **Modèle** : Log-LSTM (Hochreiter & Schmidhuber 1997), `input=2` `[log_return, sign]`, `hidden=64`, 1 layer, FC → `pred_len`. **Fine-tuned** (entraîné par fold, ~19k params).
- **Cible / perte** : chemin de log-return cumulé sur les `pred_len` prochains jours (direct multi-step), MSE. DirAcc = day-over-day sign match du chemin prédit vs rendements réels (**identique** à `evaluate_window`).
- **Univers** : panier anti-biais SPY/TLT/GLD (no FAANG/Mag7), `load_data` sur `datasets/panier` (yfinance daily OHLCV).
- **Validation** : walk-forward **5-fold expanding**, **5 seeds** (0/1/7/42/99), coût tx **10 bps**, baseline majority-class.
- **Horizons** : `pred_len` ∈ {24, 66, 132} (~ h=22/66/132 jours de bourse).
- **Métrique** : `edge_vs_majority = DirAcc − majority_baseline`. Gate `beats_valid` : `seeds≥4 AND mean_edge>0 AND (std<1e-10 OR mean_edge≥2·std)` — **identique** aux rungs 1-2.
- **Device** : GPU RTX 3070 8GB (`CUDA_VISIBLE_DEVICES=0`, env `coursia-ml-training`, torch 2.5.1+cu121). `is_trained=True` (réel, pas workaround).

## Design — walk-forward self-contained (C898-L en reverse)

M15 est **fine-tuned** (entraîné par fold sur la fenêtre expanding), structurellement différent du zero-shot window eval de Chronos/Kronos (charger un modèle figé → prédire par fenêtre). Ce harnais possède donc sa **propre walk-forward** (comme `m15_lstm_rv.walk_forward_lstm`) et réutilise uniquement les helpers **stables** — `load_data`, `compute_majority_baseline`, `compute_direction_accuracy`, le gate `beats_valid` — **pas** `build_evaluation_windows` / `evaluate_window` (le contrat zero-shot qui mute avec le merge #8620). Les métriques externes + le protocole restent IDENTIQUES, donc la comparaison cross-modèle reste apples-to-apples, **et** M15 est robuste au merge #8620 (aucune dépendance de contrat mutable partagée).

## Résultats — sweep horizon × symbole (walk-forward 5 folds, 5 seeds, 10 bps, GPU)

| Symbole | Horizon | DirAcc | Majority | Edge | std_edge | beats/5 | beats_valid |
|---------|---------|--------|----------|------|----------|---------|-------------|
| SPY | h≈22 (`pred_len=24`) | 0.5032 | 0.5480 | **-0.0448** | 0.0021 | 0/5 | False |
| SPY | h=66 | 0.5022 | 0.5480 | **-0.0458** | 0.0012 | 0/5 | False |
| SPY | h=132 | 0.5025 | 0.5480 | **-0.0455** | 0.0003 | 0/5 | False |
| TLT | h≈22 | 0.4968 | 0.5127 | **-0.0160** | 0.0012 | 0/5 | False |
| TLT | h=66 | 0.4997 | 0.5127 | **-0.0131** | 0.0008 | 0/5 | False |
| TLT | h=132 | 0.4996 | 0.5127 | **-0.0132** | 0.0010 | 0/5 | False |
| GLD | h≈22 | 0.4970 | 0.5306 | **-0.0335** | 0.0015 | 0/5 | False |
| GLD | h=66 | 0.4989 | 0.5306 | **-0.0317** | 0.0008 | 0/5 | False |
| GLD | h=132 | 0.4984 | 0.5306 | **-0.0321** | 0.0004 | 0/5 | False |

**9/9 edges négatifs, 0/5 seeds positives sur chaque config**, `beats_valid=False` partout. Runtime 1993s (~33 min) pour 45 combos.

## Findings clés

1. **Le fine-tuning ne sauve pas la prévision de direction.** C'est la conclusion centrale : un LSTM qui **apprend** la dynamique de prix ETF n'obtient pas un edge supérieur aux foundation-models zero-shot. DirAcc ~0.50 partout (sous majority 0.51-0.55). Le plafond n'est donc **pas** un défaut de généralisation zero-shot (manque d'entraînement sur l'ETF) — il est **structurel** : la direction des prix ETF liquides à long horizon n'est pas prévisible par les rendements passés seuls.

2. **NO BEATS plus propre que les foundation-models.** Comparé aux rungs 1-2 :
   - **Chronos-Bolt** (zero-shot, déterministe) : 2 edges positifs **dégénérés** (artefact harnais C893-L, `std_edge=0`).
   - **Kronos** (zero-shot, échantillonnage AR) : 0 edge positif, mais jusqu'à 2/5 seeds positives sur SPY h≈22 (variance qui laisse un faux espoir).
   - **M15 fine-tuned** : 0 edge positif, **0/5 seeds positives sur les 9 configs**, `std_edge` minimal (0.0003-0.0021). Le verdict le plus tranché.

3. **Le coût tx achève l'edge résiduel.** Tous les DirAcc (~0.50) sont sous la baseline majority ; l'edge est déjà négatif avant coûts, et les 10 bps par rebalancement consomment tout espoir résiduel.

4. **C897-L vérifié : le gate multi-seed est un vrai test pour M15.** `std_edge > 0` partout (0.0003-0.0021) — l'entraînement LSTM est stochastique (init poids + ordre minibatch seedés). Le gate n'est **pas** dégénéré (contrairement à Chronos-Bolt `std_edge=0`, C893-L). Mais la stochasticité cross-seed est **plus faible** que Kronos (échantillonnage AR) : le fine-tuning converge vers un optimum quasi-déterministe, donc moins de faux espoir que Kronos.

## Comparaison honnête au M15 LSTM d'origine (log-RV crypto, KEEPER Gate V2)

Le M15 LSTM d'origine (`m15_lstm_rv.py`, c.838) cible la **volatilité** (log-realized variance) sur **crypto**, à **court horizon** (h=1/5/10), avec **fine-tuning** — c'est un problème **différent** (la volatilité est plus persistante et prévisible que la direction). Ce 3e rung adapte l'architecture M15 à la **direction ETF long-horizon** pour le terrain commun foundation-models. La comparaison M15-direction-vs-volatilité n'est pas apples-to-apples : la volatilité (auto-régressive, clusterée) est un objectif plus tendre que la direction (martingale).

## Implication pour #8607 / #1409 / #1454

**Trois paradigmes testés, le même verdict : la prévision de direction prix ne bat pas majority.**
- L1-L5 overlays (trend, sizing régime) : NO BEATS.
- Foundation-model zero-shot langage-TS (Chronos-Bolt) : NO BEATS.
- Foundation-model zero-shot K-lines OHLCV (Kronos) : NO BEATS.
- **LSTM fine-tuned direction (M15, ce rung) : NO BEATS.**

Un seul paradigme BEATS sur cet univers : les **politiques d'action apprises** (L4 Decision Transformer). La conclusion de #1409 se **renforce** : l'alpha sur cet univers ETF liquide provient de **politiques d'action** (quand entrer/sortir, sizing), **pas** de la prévision de direction des prix — qu'elle soit zero-shot, fine-tuned, ou trend-overlay.

## Résiduel (out-of-scope, multi-cycle)

- **t-stat / DM cross-fenêtre Chronos↔Kronos↔M15** : l'infrastructure existe (`diebold_mariano.py`, `dm_test.py`). Application formelle post-merge #8620 (pour aligner les results.json).
- **Refit-every-22 intra-fold** : ce pilote entraîne une fois par fold (expanding) ; le refit périodique intra-fold (comme `m15_lstm_rv`) = raffinement méthodologique multi-cycle.
- **Features plus riches** : ce rung utilise `[log_return, sign]` seuls (minimal, apples-to-apples avec la fenêtre close des foundation rungs). Ajouter features (vol, momentum) = expérience distincte, out-of-scope du terrain commun.

## Références

- LSTM : Hochreiter & Schmidhuber, 1997 — « Long Short-Term Memory ».
- Chronos-Bolt (1er rung) : [`foundation_chronos_zeroshot.md`](../../../docs/foundation_chronos_zeroshot.md).
- Kronos (2e rung) : [`foundation_kronos_zeroshot.md`](../../../docs/foundation_kronos_zeroshot.md).
- M15 LSTM d'origine (log-RV crypto, KEEPER Gate V2) : [`M15_LSTM_RV.md`](../../../docs/M15_LSTM_RV.md).
- L4 Decision Transformer (seul BEATS du ladder) : [`L4_decision_transformer.md`](../../../docs/L4_decision_transformer.md).
- Spin-out : issue #8607. Epic parent : #1409. Capability-core : #1454.
