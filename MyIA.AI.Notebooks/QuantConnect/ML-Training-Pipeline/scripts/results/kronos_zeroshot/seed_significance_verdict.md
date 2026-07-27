# Seed-level significance test — foundation rungs (#8607 residual "t-stat propre")

> Script : [`scripts/seed_significance.py`](../../seed_significance.py).
> Résultats : [`kronos_zeroshot/seed_significance.json`](seed_significance.json) (+ `.md`), [`chronos_bolt/seed_significance.json`](../chronos_bolt/seed_significance.json).
> Résiduel documenté de #8607 (c.897, c.901) : « t-stat cross-seed propre ». Ce script le délivre pour les rungs **stochastiques** (Kronos now, M15 post-merge #8625) à partir des DirAcc **par seed déjà committés** — sans re-run.

## Question

Les rungs foundation reportent « NO BEATS 9/9 » sur la base du `mean_edge` (DirAcc − majority) et d'un gate `beats_valid` qui encode une **heuristique 2-sigma** (`mean_edge >= 2·std_edge`). Question : ce verdict est-il **statistiquement** robuste ? En particulier, l'edge négatif est-il **significativement** négatif (reliably under majority), ou juste un estimateur ponctuel bruité ?

## Méthode — test one-sample sur l'edge par seed

Pour chaque (symbole, horizon), on extrait l'edge **par seed** `edge_s = DirAcc_s − majority` (n=5 seeds : 0/1/7/42/99), puis :

- **t-test one-sample** (edge vs 0), df = n−1 = 4 — la distribution de référence pour petit n (queues plus lourdes que la normale → plus dur de rejeter). Raffine le 2-sigma heuristique.
- **sign test** (binomial, two-sided) — non-paramétrique.
- **Wilcoxon signed-rank** — non-paramétrique.
- **IC 95%** sur le mean_edge.

**Pourquoi un nouveau script, pas `diebold_mariano.py`/`dm_test.py`** : le test DM compare **deux** séries d'erreurs de prévision appariées (pertes par observation). Ce n'est PAS la question ici (« l'edge cross-seed est-il ≠ 0 ? » = test one-sample sur l'edge par seed). Outil distinct, module distinct (C898-L : on ne mute pas le contrat d'un helper importé — ici on ne touche pas aux scripts DM).

## Verdict Kronos — 6/9 configs SIGNIFICATIVEMENT négatives

| Symbole | Horizon | DirAccs (5 seeds) | mean_edge | t_stat | t_p | 95% CI | verdict |
|---------|---------|-------------------|-----------|--------|-----|--------|---------|
| SPY | h≈22 | [0.417, 0.548, 0.530, 0.557, 0.504] | -0.0348 | -1.39 | 0.238 | [-0.105, +0.035] | ns |
| SPY | h=66 | [0.529, 0.498, 0.468, 0.529, 0.505] | -0.0403 | -3.53 | 0.024 | [-0.072, -0.009] | **SIG-nég** |
| SPY | h=132 | [0.470, 0.479, 0.510, 0.516, 0.531] | -0.0448 | -3.90 | 0.018 | [-0.077, -0.013] | **SIG-nég** |
| TLT | h≈22 | [0.504, 0.496, 0.443, 0.530, 0.504] | -0.0174 | -1.22 | 0.291 | [-0.057, +0.022] | ns |
| TLT | h=66 | [0.486, 0.492, 0.495, 0.483, 0.508] | -0.0201 | -4.69 | 0.009 | [-0.032, -0.008] | **SIG-nég** |
| TLT | h=132 | [0.482, 0.485, 0.507, 0.492, 0.476] | -0.0245 | -4.71 | 0.009 | [-0.039, -0.010] | **SIG-nég** |
| GLD | h≈22 | [0.452, 0.461, 0.513, 0.513, 0.504] | -0.0428 | -3.22 | 0.032 | [-0.080, -0.006] | **SIG-nég** |
| GLD | h=66 | [0.492, 0.566, 0.505, 0.480, 0.505] | -0.0219 | -1.48 | 0.214 | [-0.063, +0.019] | ns |
| GLD | h=132 | [0.508, 0.502, 0.515, 0.479, 0.528] | -0.0249 | -3.10 | 0.036 | [-0.047, -0.003] | **SIG-nég** |

**6/9 configs statistiquement significatives (t_p < 0.05), TOUTES négatives, 0 positive.** 3/9 non-distinctes de 0 (SPY h22, TLT h22, GLD h66 — edge négatif mais bruité à n=5).

## Finding clé — le verdict se PRÉCISE : « reliably under majority », pas juste « négatif »

Le verdict du rung (c.897) était « NO BEATS 9/9 (mean_edge négatif) ». Le t-stat **raffine** : Kronos n'est pas seulement « en dessous de majority en moyenne » — sur **6/9 configs** il est **reliably, significativement** en dessous (IC 95% exclut 0). Autrement dit, Kronos ne prédit pas la direction au hasard : il prédit **significativement moins bien** que la classe majoritaire sur 6/9 configs. C'est un résultat plus fort qu'un simple NO BEATS — le modèle est **activement mauvais** (pas juste non-informatif) sur la majorité de la grille.

Aucune config n'est significativement **positive** → pas de signal BEATS caché dans le bruit. NO BEATS confirmé statistiquement.

## Chronos-Bolt — DEGENERATE (C893-L)

Chronos-Bolt est **déterministe** (décodeur non-échantillonné → `std_edge=0`, C893-L) : 1 valeur effective par config, pas de variance cross-seed → **t-test indéfini**. Les 7 configs reportent `DEGENERATE`. C'est la signature même de C893-L : le gate `beats_valid` collapse en « edge>0=BEATS » pour Chronos car std=0, et symétriquement le t-test est inopérant. Le t-stat propre n'a de sens que pour les modèles **stochastiques** (Kronos, M15).

## M15 — pending (post-merge #8625)

M15 LSTM est stochastique (init poids + minibatch seedés, C897-L) avec n=5 seeds par config committés dans `m15_lstm_etf/results.json` (PR #8625, en attente merge). Dès que #8625 merge, `python seed_significance.py results/m15_lstm_etf/results.json` produira la table M15. L'auto-detection de format (Kronos/Chronos/M15) est couverte par les tests unitaires.

## Limites (honnêtes)

- **n=5 seeds = puissance faible**. Le t-test manque la significance sur des edges de l'ordre de 0.02-0.04 quand la variance cross-seed est élevée (SPY h22 std=0.056). C'est inhérent au protocole 5-seeds. Les 3 configs « ns » ne sont pas « BEATS » — leur edge est négatif mais non distinguable de 0 à cette taille d'échantillon.
- **Par seed, pas par fenêtre**. Le test opère sur les 5 DirAcc par seed (moyenne des fenêtres walk-forward), pas sur les prédictions individuelles. Un test par observation (DM apparié Chronos↔Kronos sur fenêtres alignées) nécessiterait de dumper les prévisions par fenêtre (re-run, multi-cycle) — résiduel méthodologique non couvert ici.

## Implication pour #8607 / #1409

Le « t-stat propre » résiduel est délivré pour le rung stochastique (Kronos). Verdict raffiné : **Kronos est significativement sous majority sur 6/9 configs** (pas seulement « négatif en moyenne »). Cela **renforce** NO BEATS : aucun signal BEATS, et le modèle est activement informatif (en mauvais sens) sur la majorité de la grille. La conclusion #1409 (l'alpha vient de politiques d'action, pas de prévision de direction prix) tient, désormais étayée par statistique formelle.

## Références

- Kronos rung : [`foundation_kronos_zeroshot.md`](../../../docs/foundation_kronos_zeroshot.md) (c.897, #8620).
- Chronos-Bolt rung : [`foundation_chronos_zeroshot.md`](../../../docs/foundation_chronos_zeroshot.md) (c.893, #8610).
- M15 LSTM rung : [`foundation_m15_lstm_etf.md`](../../../docs/foundation_m15_lstm_etf.md) (c.901, #8625).
- C893-L : gate robustesse cross-seed inopérant pour zero-shot déterministes.
- C897-L : Kronos stochastique → gate (et t-test) VRAI test.
- Spin-out : #8607. Epic parent : #1409.
