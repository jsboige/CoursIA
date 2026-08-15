# Cross-rung paired comparison — 3 foundation paradigms are statistically indistinguishable (#8607)

> Script : [`paired_rung_comparison.py`](../../paired_rung_comparison.py).
> Artefacts : [`kronos_vs_m15.json`](kronos_vs_m15.json) · [`chronos_vs_kronos.json`](chronos_vs_kronos.json) · [`chronos_vs_m15.json`](chronos_vs_m15.json) (+ `.md`).

## Question (la suite naturelle de #8607)

`seed_significance.py` (c.902, PR #8626) a répondu **par rung** : « ce modèle est-il significativement sous majority ? » (one-sample t-test sur l'edge par seed). Verdict : Chronos dégénéré (std_edge=0, C893-L), Kronos 6/9 SIG-négatif, M15 9/9 SIG-négatif. Les 3 rungs foundation sont **individuellement** NO BEATS.

Ce module répond à la question **suivante** : **deux rungs sont-ils significativement différents l'un de l'autre ?** Un modèle zero-shot (Kronos, échantillonnage AR) et un modèle fine-tuned (M15 LSTM) échouent tous deux à battre majority — mais le fine-tuning change-t-il l'edge directionnel relativement au zero-shot, ou atterrissent-ils sur le même edge ?

## Verdict — 3 comparaisons par paires, TOUTES non significatives

| Comparaison (A vs B) | n paires appariées | mean diff (B−A) | CI95% | paired t (df) | t p | Wilcoxon p | verdict |
|----------------------|-------------------|-----------------|-------|---------------|-----|-----------|---------|
| **Kronos vs M15** | 45 | −0.00047 | [−0.009, +0.008] | −0.112 (44) | **0.91** | 0.80 | **non sig.** |
| Chronos vs Kronos | 35 | −0.00200 | [−0.015, +0.011] | −0.318 (34) | 0.75 | 0.84 | non sig. |
| Chronos vs M15 | 35 | −0.00018 | [−0.010, +0.009] | −0.039 (34) | 0.97 | 0.60 | non sig. |

Aucune paire n'est significativement différente (alpha=0.05). Les 3 paradigmes foundation — **zero-shot langage-TS** (Chronos-Bolt), **zero-shot OHLCV AR** (Kronos), **fine-tuned LSTM direction** (M15) — produisent des edges directionnels **statistiquement indiscernables** sur le panier ETF (SPY/TLT/GLD), tous autour de −0.02 à −0.03 (sous majority).

## Finding clé — aucun paradigme de prévision n'en surpasse un autre

- **Kronos ↔ M15 (n=45, propre)** : la comparaison centrale. La difference moyenne appariée est −0.00047 (M15 0.05 points de % plus négatif), CI95 chevauche 0 largement, t=−0.112 (p=0.91). Le fine-tuning LSTM **ne change pas** l'edge directionnel relativement au zero-shot Kronos.
- **Picture 3-voies cohérente** : Chronos↔Kronos et Chronos↔M15 tout aussi non significatifs. Quelle que soit la méthode de prévision (langage-TS pré-entraîné, AR OHLCV, ou LSTM fine-tuned sur le log-return), l'edge directionnel atterrit au même endroit (~−0.03, reliably sous majority).
- **Reinforce #1409** : la conclusion capability-core (l'alpha vient de **politiques d'action** L4-DT, pas de prévision de direction prix) est désormais étayée à **deux niveaux statistiques** — (1) chaque rung est SIG-nég vs majority (seed-level, c.902/c.904), (2) aucun rung n'en bat un autre (paired cross-rung, ce cycle). L'absence d'edge directionnel n'est pas un artefact d'un paradigme particulier ; elle est **robuste à travers les paradigmes**.

## Méthode

Test **apparié par (symbole, horizon, seed)** sur les edges par seed **déjà committés** dans les `results.json` de chaque rung (Kronos `seed_results[j].edge_vs_majority`, M15 `combos[i].edge_vs_majority`, Chronos déterministe `edge` par config). Pour chaque observation appariée, `d = edge_B − edge_A`, puis : paired t-test (df=n−1) + Wilcoxon signed-rank + sign (binomial) + IC95% sur la différence moyenne.

- **Kronos ↔ M15** : alignement complet (3 ETF × 3 horizons × 5 seeds = 45). C'est le résultat primaire.
- **Chronos (déterministe, C893-L)** : std_edge=0, 1 edge par config (7 configs, donc 35 paires appariées par seed contre la constante Chronos). Interprété avec prudence (rung déterministe), rapporté pour complétude.

## Scope / résiduel (honnête)

- **Ce n'est PAS le test Diebold-Mariano complet.** DM est apparié **par observation** (erreurs de prévision par fenêtre/par pas de temps, avec correction de variance HAC — Harvey-Leybourne-Newbold). Il nécessite la série DirAcc **par fenêtre**, qui n'est PAS committée (Kronos ne dump que l'agrégat par fold `avg_direction_accuracy` par seed ; M15 dump `fold_results` mais Kronos non). Le vrai DM reste un résiduel **multi-cycle** (re-run dumper les prévisions par fenêtre walk-forward, fenêtres alignées).
- Ce test apparié par (config, seed) est la comparaison cross-rung la plus forte **disponible depuis les edges par seed committés — sans re-run**.

## Références

- Seed-level one-sample (par rung vs majority) : [`kronos_zeroshot/seed_significance_verdict.md`](../kronos_zeroshot/seed_significance_verdict.md) (c.902) · [`m15_lstm_etf/seed_significance_verdict.md`](../m15_lstm_etf/seed_significance_verdict.md) (c.904).
- C893-L : gate cross-seed inopérant pour zero-shot déterministes (Chronos std_edge=0).
- C897-L : Kronos/M15 stochastiques → std_edge>0 → VRAI test (et vraie variance appariée ici).
- Spin-out : #8607. Epic parent : #1409 (capability-core, alpha = politiques d'action L4-DT).
