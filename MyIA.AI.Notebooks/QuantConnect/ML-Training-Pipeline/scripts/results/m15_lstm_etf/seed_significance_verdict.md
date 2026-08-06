# Seed-level significance test — M15 LSTM fine-tuned (3e rung foundation, #8607)

> Script : [`scripts/seed_significance.py`](../../seed_significance.py).
> Résultats : [`m15_lstm_etf/seed_significance.json`](seed_significance.json) (+ `.md`).
> Ferme le résiduel documenté dans PR #8626 (« M15 pending post-merge #8625 »). `results.json` désormais sur `main` (PR #8625 merged), le script l'auto-détecte — **sans re-run**.

## Verdict M15 — 9/9 configs SIGNIFICATIVEMENT négatives, 0 positive, 0 degenerate

| Symbole | Horizon | DirAccs (5 seeds) | mean_edge | std_edge | t_stat | t_p | 95% CI | verdict |
|---------|---------|-------------------|-----------|----------|--------|-----|--------|---------|
| SPY | h≈22 | [0.506, 0.503, 0.506, 0.500, 0.501] | -0.0448 | 0.0024 | -41.7 | 0.000 | [-0.0478, -0.0419] | **SIG-nég** |
| SPY | h=66 | [0.501, 0.504, 0.502, 0.501, 0.503] | -0.0458 | 0.0013 | -79.7 | 0.000 | [-0.0474, -0.0442] | **SIG-nég** |
| SPY | h=132 | [0.502, 0.502, 0.502, 0.503, 0.503] | -0.0455 | 0.0003 | -363.0 | 0.000 | [-0.0458, -0.0451] | **SIG-nég** |
| TLT | h≈22 | [0.498, 0.497, 0.497, 0.497, 0.495] | -0.0160 | 0.0014 | -26.2 | 0.000 | [-0.0177, -0.0143] | **SIG-nég** |
| TLT | h=66 | [0.499, 0.501, 0.500, 0.500, 0.498] | -0.0131 | 0.0009 | -31.3 | 0.000 | [-0.0142, -0.0119] | **SIG-nég** |
| TLT | h=132 | [0.500, 0.499, 0.501, 0.498, 0.500] | -0.0132 | 0.0012 | -25.4 | 0.000 | [-0.0146, -0.0118] | **SIG-nég** |
| GLD | h≈22 | [0.496, 0.497, 0.496, 0.500, 0.497] | -0.0335 | 0.0016 | -45.6 | 0.000 | [-0.0356, -0.0315] | **SIG-nég** |
| GLD | h=66 | [0.498, 0.498, 0.500, 0.500, 0.499] | -0.0317 | 0.0009 | -79.8 | 0.000 | [-0.0328, -0.0306] | **SIG-nég** |
| GLD | h=132 | [0.498, 0.499, 0.498, 0.498, 0.499] | -0.0321 | 0.0004 | -181.3 | 0.000 | [-0.0326, -0.0316] | **SIG-nég** |

**9/9 configs statistiquement significatives (t_p < 0.001), TOUTES négatives, 0 positive.** C'est le verdict le plus tranché des 3 rungs foundation.

## Finding clé — M15 est le verdict le plus tranché (vs Kronos 6/9, Chronos degenerate)

| Rung | configs SIG-nég / total | t_stat range | verdict |
|------|------------------------|--------------|---------|
| Chronos-Bolt | 0/7 (DEGENERATE, std_edge=0) | undefined | gate inopérant (C893-L) |
| Kronos (zero-shot AR) | **6/9** SIG-nég, 0 pos | -3.1 à -4.7 | reliably sous majority |
| **M15 (fine-tuned)** | **9/9** SIG-nég, 0 pos | **-25 à -363** | **massivement sous majority** |

M15 confirme et **renforce** les conclusions c.901 :
- **9/9 vs 6/9** : là où Kronos laissait 3 configs « ns » (bruitées à n=5), M15 est significatif sur **toutes** les configs — le fine-tuning élimine le bruit cross-seed (converge vers un optimum quasi-déterministe, `std_edge` minimal 0.0003-0.0024).
- **t_stats énormes (-25 à -363)** : l'edge n'est pas « marginalement sous majority » — il est **massivement, sans ambiguïté** sous majority. Le LSTM fine-tuned prédit la direction **beaucoup moins bien** que la classe majoritaire, et cet échec est statistiquement certain (IC 95% exclut 0 avec une marge large).
- **0 positive** → aucun signal BEATS caché. NO BEATS confirmé statistiquement sur les 3 rungs.

## Pourquoi le fine-tuning aggrave (interprétation)

Un modèle zero-shot (Kronos) garde une stochasticité d'échantillonnage (AR sampling, `T`/`top_p`) → variance cross-seed modérée → quelques configs « ns ». Un LSTM **fine-tuned** converge vers un optimum déterministe de la fonction de perte MSE sur le chemin de log-return — il apprend donc une solution **répétable** qui, sur ETF liquide, prédit systématiquement sous majority. La stochasticité résiduelle (init poids + ordre minibatch) est trop faible pour introduire du bruit. Autrement dit : le fine-tuning ne sauve pas la prévision de direction, il la rend **encore plus fiablement mauvaise**.

## Méthode

Test one-sample sur l'edge **par seed** `edge_s = DirAcc_s − majority` (n=5 seeds : 0/1/7/42/99) : t-test (df=4) + sign (binomial) + Wilcoxon signed-rank + IC 95%. Le t-test raffine l'heuristique 2-sigma du gate `beats_valid`. M15 est stochastique (init poids + minibatch seedés, C897-L) → `std_edge > 0` → gate (et t-test) **vrai test**, pas dégénéré comme Chronos (C893-L). L'auto-detection du format M15 (clé `combos` + `summary`) est couverte par les tests unitaires (`test_seed_significance.py`).

## Limites (honnêtes)

- **n=5 seeds** : puissance faible inhérente au protocole. Mais ici l'edge est si large et si peu bruité que tous les tests rejettent massivement (t_p < 0.001) — la puissance n'est pas le facteur limitant pour M15.
- **Par seed, pas par fenêtre** : le test opère sur les 5 DirAcc moyens par seed, pas sur les prédictions individuelles. Un test par observation (DM apparié M15↔Kronos sur fenêtres alignées) nécessiterait de dumper les prévisions par fenêtre (re-run, multi-cycle) — résiduel méthodologique.

## Implication pour #8607 / #1409

Le t-stat cross-rung est désormais complet (Kronos 6/9 SIG-nég, Chronos degenerate, **M15 9/9 SIG-nég**). Les **3 paradigmes foundation** (zero-shot langage-TS, zero-shot OHLCV, fine-tuned LSTM direction) sont **statistiquement** confirmés sous majority — pas un artefact d'estimateur ponctuel. La conclusion #1409 (l'alpha vient de **politiques d'action** L4-DT, pas de prévision de direction prix) tient, désormais étayée par statistique formelle sur les 3 rungs stochastiques/déterministes.

## Références

- M15 rung : [`foundation_m15_lstm_etf.md`](../../../docs/foundation_m15_lstm_etf.md) (c.901, #8625).
- Kronos rung : [`kronos_zeroshot/seed_significance_verdict.md`](../kronos_zeroshot/seed_significance_verdict.md) (c.902, #8626).
- Chronos-Bolt rung : [`foundation_chronos_zeroshot.md`](../../../docs/foundation_chronos_zeroshot.md) (c.893, #8610).
- C893-L : gate robustesse cross-seed inopérant pour zero-shot déterministes.
- C897-L : M15 stochastique → gate (et t-test) VRAI test.
- Spin-out : #8607. Epic parent : #1409.
