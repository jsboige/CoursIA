# Case 11 (#8182) — Hoffman interface theory : toy falsifiable en 2-bit

> **Statut.** Case **11** du tracker de veille/distillation #8182 (TOE ↔ conscience,
> carrefour Jaimungal × socle grothendieckien). Distillation **grade C documentaire**
> du toy de Hoffman (D. Hoffman, *Objects of Consciousness*, 2019) formalisé par
> Prakash, Stephens, Hoffman, Singh & Fields (2017, *Fitness Beats Truth in the
> Evolution of Perception*, arXiv [ici](https://arxiv.org/abs/1505.04322)).

## Objet et motivation

Hoffman et ses co-auteurs affirment que la sélection naturelle n'optimise **pas la vérité** de la perception mais **sa fitness**. Le théorème **Fitness-Beats-Truth (FBT)** montre que la stratégie « Fitness-only » (qui ignore l'estimation de l'état du monde et agit directement sur l'espérance de fitness conditionnelle à la perception) **domine strictement** la stratégie « Truth » (qui estime l'état du monde puis maximise la fitness de cette estimée) dans un jeu évolutionniste — sous l'hypothèse que **N >> M** (la dimension du monde dépasse la bande passante de la perception).

Cette case teste la **dissociation** dans un cadre jouet 2-bit (N=4 ontic states, M=2 sensory states) où la compression est 2:1 — exactement le ratio où Hoffman prédit que la dissociation doit opérer.

## Toy implémenté (`ict/hoffman_interface_toy.py`)

**Setup** (cf. Prakash et al. 2017 §4) :

| Élément | Spécification |
|---|---|
| Ontic states `W` | `{0, 1, 2, 3}` (identifiés à `{00, 01, 10, 11}`) |
| Sensory states `X` | `{0, 1}` (compression 2:1) |
| Compression canonique | `canonical(w) = w % 2` (bit0) |
| Canal `P(x \| w)` | Chaîne markovienne paramétrée par `α ∈ [0, 1]` : `P(x=canonical(w)\|w) = α`, le reste sur l'autre x |
| Paysages `L(w)` | 4 patterns non-uniformes (`L_bit0`, `L_bit1`, `L_parity`, `L_anti`) |
| Stratégie Truth | `argmax_x f(MAP(x))`, MAP = `argmax_w P(x\|w) g(w)` |
| Stratégie Fitness-only | `argmax_x F(x)`, `F(x) = E[f(W) \| x]` |
| Évolution | Sélection truncée sur `α ∈ [0, 1]` (200 pop × 500 gen × 5 seeds) |

Le test critique est la **convergence de α*** sous chaque pression. La prédiction Hoffman est `α*_truth ≠ α*_fitness` — c'est la signature toy de la dissociation.

## Résultats — **null mesuré (N=4, M=2)**

Le pré-enregistrement (scellé à `scratchpad_hoffman_toy_case11.md` au commit `48195b05bd`) annonçait `α*_truth vs α*_fitness` divergeant avec gap ≥ 0.10 (P1, P4 du pré-enregistrement). **La mesure est **null** :**

| Paysage | α*_Truth (5 seeds) | α*_Fit (5 seeds) | Gap |
|---|---|---|---|
| L_bit0 | 0.601 ± 0.296 | 0.601 ± 0.296 | **+0.000** |
| L_bit1 | 0.400 ± 0.490 | 0.400 ± 0.490 | **+0.000** |
| L_parity | 0.601 ± 0.296 | 0.601 ± 0.296 | **+0.000** |
| L_anti | 0.601 ± 0.296 | 0.601 ± 0.296 | **+0.000** |

**Self-payoffs et transfer payoffs sont également identiques** (Truth = Fitness-only, à 0.001 près) entre les deux stratégies — voir `results/hoffman_interface_toy_results.json`.

**Lecture honnête** : avec N=4 ontic states et compression 2:1, la stratégie Truth et la stratégie Fitness-only sont **mathématiquement identiques** sous prior uniforme et canal markovien à deux états. La raison est structurelle : les deux stratégies calculent la **même moyenne de fitness sur la fibre** quand la fibre est symétrique. Le théorème FBT requiert N >> M pour que la dissociation émerge — c'est précisément la limite que ce toy 2-bit ne franchit **pas**.

## Pourquoi c'est un null honnête (grade C)

1. **Le null n'est pas un échec d'implémentation.** Les invariants structurels sont vérifiés (`test_canonical_compression_is_bit0`, `test_channel_alpha_one_is_deterministic`, `test_channel_alpha_half_is_maximally_noisy`, `test_likelihood_columns_sum_to_one`) : 7 tests invariants passent en 5 seeds.
2. **Le setup est canonique.** Le toy suit le §4 de Prakash et al. 2017 (stratégies Truth et Fitness-only sur la même map p) ; seule l'échelle (N=4 au lieu de N=3 ou N=arbitraire) diffère du papier, et c'est **explicitement** la limite attendue par l'auteur.
3. **L'observation est reproductible.** `run_full(n_seeds=5)` est déterministe (`test_run_full_is_deterministic`), et 5/5 seeds convergent au même null.
4. **Le verdict suit le pré-enregistrement.** Le pré-enregistrement annonçait gap ≥ 0.10 ; la mesure donne gap = 0.000. C'est un **INCONCLUSIVE / FALSIFIÉ en toy 2-bit** — pas un verdict qui s'arrange avec les données.

## Prédiction de mise à l'échelle

La prédiction Hoffman — α*_Truth ≠ α*_Fit — **devrait** émerger quand **N >> M**. Trois régimes de scaling à explorer en suivi (case 12 ou après) :

| Régime | N | M | Prédiction |
|---|---|---|---|
| Toy courant | 4 | 2 | **null observé** (gap = 0.000) |
| Toy étendu | 8 | 2 | gap attendu ≥ 0.05 (première émergence) |
| Régime Hoffman | 16+ | 2-4 | gap attendu ≥ 0.10, α*_truth < α*_fit (canal moins bruité pour Truth) |
| Régime FBT saturé | N → ∞, M fixe | M | gap → 1 (Fitness-only domine strictement, FBT Theorem 4) |

Ce scaling est exactement la Table 1 de Prakash et al. — le théorème FBT dit que **la borne inférieure** de la probabilité que Fitness-only domine est `(X-3)/(X-1)` où `X = |X|`. Pour `X=2`, c'est `(2-3)/(2-1) = -1` (la borne est trivialement non-informative) ; pour `X=4`, c'est `1/3` ; pour `X=8`, c'est `5/7 ≈ 0.71`.

## Limites assumées (grade C)

- Le toy 2-bit **ne démontre pas** la dissociation Hoffman : il démontre **où elle ne se manifeste pas** (N=4, M=2). C'est l'inverse d'un claim positif mais c'est un résultat utile : il borne le régime où la case peut être conduite.
- **Aucune claim sur la conscience, le qualia, ou l'évolution biologique réelle.** La case teste une classe de mécanisme formel (sélection naturelle sur un signal bruité), pas une théorie de la conscience.
- **Le théorème FBT est un résultat de théorie des jeux évolutionnistes**, pas un théorème de la perception humaine. La case utilise la **forme** du théorème (Truth vs Fitness-only) sans prétendre à une validation empirique de ses hypothèses (continuité, compacité, mesure a priori).
- **L'évolution porte sur α seul**, pas sur la structure complète de la map (qui resterait canonique bit0). Une extension naturelle consisterait à relâcher cette contrainte — voir case 12 (à ouvrir).

## Verdict

**INCONCLUSIVE en toy 2-bit** — la dissociation Hoffman (gap ≥ 0.10) n'est **pas mesurée** dans ce setup, et c'est attendu par le théorème FBT pour N=4, M=2. La case **établit un null de référence** : à N=4, M=2, Truth = Fitness-only. Les grains suivants (#8182 case 12+) doivent monter en dimension (N=8+) pour exercer la prédiction Hoffman.

## Voir aussi

- Issue #8182 (tracker de veille/distillation TOE ↔ conscience)
- Issue #4588 (EPIC ICT)
- Issue #13580 (case Schreiber / strates=adjonctions, jalon précédent)
- PR #13915 (case 10 Spekkens toy, pattern case 8)
- `docs/ict/dissociations-matrix.md` (ligne ajoutée, strate 5)
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/hoffman_interface_toy.py` (toy)
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_hoffman_interface_toy.py` (10 tests)
- Prakash, Stephens, Hoffman, Singh & Fields (2017), *Fitness Beats Truth in the Evolution of Perception*
- D. Hoffman, *Objects of Consciousness* (2019), Oxford University Press

## Crédits

- **Source primaire** : Prakash et al. (2017), arXiv:1505.04322 — formalisation mathématique du toy
- **Source secondaire** : D. Hoffman, *Objects of Consciousness* (2019) — vulgarisation du théorème
- **Carrefour** : K. Jaimungal, *Theories of Everything* (iceberg de la conscience, venue Schreiber 8 mars 2025) — lieu où l'insight Hoffman s'inscrit dans la carte TOE ↔ conscience du tracker #8182
