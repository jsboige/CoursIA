# Trivial-baseline counterpoint — persistence lands on the SAME edge as the SOTA foundation rungs (#8607, #1409)

> Script : [`eval_baselines_zeroshot.py`](../../eval_baselines_zeroshot.py).
> Résultats : [`baselines_zeroshot/results.json`](results.json) (9 configs, persistence).
> Tests : [`tests/test_eval_baselines_zeroshot.py`](../../tests/test_eval_baselines_zeroshot.py).

## Question (le contrepoint au spectre #8607)

Les 3 foundation rungs (Chronos-Bolt #8610, Kronos #8620, M15 LSTM #8625) sont tous NO BEATS vs majority sur le panier ETF (SPY/TLT/GLD), et pairwise indiscernables (c.905, PR #8631 : Kronos↔M15 p=0.91). Ce module pose le **contrepoint** :

> La baseline directionnelle la plus triviale qui soit — **persistence** (prédire que la direction de demain = la direction d'aujourd'hui, naive momentum d'une ligne) — fait-elle mieux ou pire que les modèles foundation/fine-tuned qui « apprennent » la série ?

Si oui, la sophistication est inutile. Si une triviale atterrit sur le même edge, **#1409 (alpha = politiques d'action L4-DT, pas prévision de direction) est renforcé par exhaustion du spectre méthodologique** : trivial → classique → foundation → fine-tuned, tous NO BEATS.

## Verdict persistence — edge ≈ -0.029, **indiscernable des 3 foundation rungs**

| Symbole | Horizon | DirAcc persistence | majority | **edge persistence** |
|---------|---------|--------------------|----------|----------------------|
| SPY | 24 | 0.5050 | 0.5480 | **-0.0430** |
| SPY | 66 | 0.5062 | 0.5480 | **-0.0418** |
| SPY | 132 | 0.5059 | 0.5480 | **-0.0421** |
| TLT | 24 | 0.4963 | 0.5127 | **-0.0165** |
| TLT | 66 | 0.4974 | 0.5127 | **-0.0154** |
| TLT | 132 | 0.4984 | 0.5127 | **-0.0144** |
| GLD | 24 | 0.4983 | 0.5306 | **-0.0323** |
| GLD | 66 | 0.5010 | 0.5306 | **-0.0295** |
| GLD | 132 | 0.5008 | 0.5306 | **-0.0298** |

Persistence = déterministe (pas de seed) → 9/9 DEGENERATE au seed-level test (std_edge=0, exactement comme Chronos-Bolt, C893-L).

### Comparaison appariée persistence ↔ foundation (par (symbole, horizon))

| Comparaison | n configs | persistence mean | rung mean | diff (rung - pers) | t | p | verdict |
|-------------|-----------|------------------|-----------|--------------------|----|----|---------|
| **persistence vs Kronos** | 9 | -0.0294 | -0.0302 | -0.0007 | -0.317 | **0.76** | non sig. |
| **persistence vs M15** | 9 | -0.0294 | -0.0306 | -0.0012 | -1.710 | **0.13** | non sig. |
| **persistence vs Chronos** | 7 | -0.0294 | -0.0301 | -0.0007 | -0.068 | **0.95** | non sig. |

(La comparaison appariée est calculée inline ici — `paired_rung_comparison.py` (PR #8631, en attente merge) n'est pas encore sur `main` ; il détectera ce format post-merge.)

## Finding clé — la sophistication n'apporte rien sur ETF direction

- **persistence ≈ Kronos ≈ M15 ≈ Chronos ≈ -0.03** sous majority. Une baseline triviale de **1 ligne** (prédire la dernière direction) atterrit sur le **même edge** que Chronos-Bolt pré-entraîné sur des millions de séries temporelles, Kronos AR, et un LSTM fine-tuned sur le log-return.
- **Le résultat n'était PAS triviallement prévisible** : persistence aurait pu être strictement pire (si les ETF étaient fortement anti-persistents / mean-reverting) ou strictement meilleure (si fortement trend-following). Elle atterrit pile au même endroit que les SOTA — ni mieux ni pire, tous fiablement sous majority.
- **Exhaustion du spectre #1409** : la prévision de direction prix sur ETF liquide est absente **à tous les niveaux de sophistication** — trivial (persistence), zero-shot langage-TS (Chronos), zero-shot OHLCV AR (Kronos), fine-tuned LSTM (M15). Aucun n'extrait d'edge directionnel ; tous sont ~-0.03 sous majority. L'alpha vient de **politiques d'action** (L4-DT), pas de la prévision de direction — désormais étayé par exhaustion méthodologique complète.

## Méthode

`eval_baselines_zeroshot.py` réutilise **uniquement** les helpers stables partagés (C898-L) — `data_utils.load_data` + les formules majority/direction-accuracy identiques aux rungs (eval_m15_lstm / eval_kronos_zeroshot). **Pas de torch, pas de GPU.** Le walk-forward (5 folds expanding, `fold_size = n // (n_splits+1)`, test points `log_returns[i+1:i+horizon]`) est **identique** aux rungs → comparaison apples-to-apples. La seule différence : la prédiction = `log_returns[i-1]` (dernier return observé) au lieu d'une sortie de modèle.

Persistence est déterministe (pas de seed) → std_edge=0 → DEGENERATE au seed-sig (comme Chronos), ce qui est **attendu** — le point est l'estimation ponctuelle de l'edge, comparée aux rungs.

## Note sur random-walk

Le random-walk financier (« la meilleure prévision de demain est aujourd'hui ») se réduit, pour la *direction*, à prédire « pas de changement » — ce qui, sous une DirAcc stricte par signe-match, ne matche que les ~0% de jours exactément plats (DirAcc ~0.001), un artefact dégénéré plutôt qu'un floor significatif. La prévision de direction random-walk est donc **identique à persistence** (prédire la dernière direction observée) ; pas de colonne séparée.

## Références

- Foundation rungs : Chronos-Bolt #8610 (c.893) · Kronos #8620 (c.897) · M15 #8625 (c.901).
- Seed-level one-sample (par rung vs majority) : `seed_significance_verdict.md` (c.902/c.904).
- Paired cross-rung : `cross_rung_paired/verdict.md` (c.905, PR #8631).
- C893-L : gate cross-seed inopérant pour déterministes (persistence + Chronos). C898-L : réutiliser les helpers stables, ne pas muter un importé.
- Spin-out : #8607. Epic parent : #1409 (capability-core, alpha = politiques d'action L4-DT).
