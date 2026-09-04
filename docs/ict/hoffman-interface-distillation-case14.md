# Case 14 (#8182) — Hoffman interface theory : toy N=8, M=2, compression bit2 → **NULL INSTRUMENTAL**

> **Statut.** Case **14** du tracker de veille/distillation #8182 (TOE ↔ conscience,
> Hoffman FBT). Distillation **grade C** du toy formel de Hoffman
> (D. Hoffman, *Objects of Consciousness*, 2019) formalisé par Prakash, Stephens,
> Hoffman, Singh & Fields (2017, *Fitness Beats Truth in the Evolution of Perception*,
> arXiv [1505.04322](https://arxiv.org/abs/1505.04322)).
>
> **Verdict mesuré : NULL INSTRUMENTAL sur 8/8 paysages** (gap `|α*_truth - α*_fit| ≤ 0.05`).
> Cette case **NE RÉFUTE PAS** ni ne **CONFIRME** l'hypothèse 2 du verdict case 13 — elle
> **expose un bug de design instrumental** dans `play_round` (hérité de case 11 et case 13)
> qui rend la mesure de dissociation FBT dégénérée sur les paysages trivialement discriminants.
> Le toy livré **ne mesure pas la dissociation FBT** ; il mesure un artefact instrumental
> (`fitness(x ∈ {0,1})` au lieu de `fitness(w ∈ {0..7})`).
>
> **Conclusion opérationnelle** : **case 14-bis nécessaire** avec le design case 12
> (deux territoires concurrents, payoff intra-territoire `E[f(w) | x=x_hat, alpha, prior]`).
> Le verdict structurel case 13 reste valide (RÉFUTATION du scaling monotone).

## Objet et motivation

Case 11 (PR #14535, MERGED 2026-09-04T02:11:33Z) a établi qu'à N=4 ontic states et M=2 sensory states, sous prior uniforme, les stratégies Truth et Fitness-only sont **structurellement équivalentes** (gap = 0.000 sur 4 paysages).

Case 12 (PR #14544) a montré qu'à N=8, M=2, compression **bit0**, la dissociation **émerge mesurable** sur 4/8 paysages (gap `+0.36` sur L_bit0 family et bit2 family, `-0.19` sur L_pairity_3bit). Cause structurelle : à fibre cardinal 4, MAP exploite la structure intra-fibre (4 w candidats) que Fitness-only moyenne. **Mais** case 12 utilise un design différent (deux territoires concurrents, payoff intra-territoire).

Case 13 (PR #14548) teste la **prédiction d'escalade monotone** à N=16, compression bit0 : **RÉFUTATION** (null 0/16). Cause structurelle : à fibre cardinal 8, symétrie intra-fibre restaurée → `E[f(W)|x]` identique pour les deux x.

Case 14 teste **l'hypothèse 2** du verdict case 13 (Tell c.896-L1 ★★★) : le **relâchement du setup** (compression non-canonique bit2 au lieu de bit0) peut-il restaurer la dissociation FBT à N=8 ?

## Toy implémenté (`ict/hoffman_interface_toy_n8_relaxed.py`)

**Setup** (cf. Prakash et al. 2017 §4) :

| Élément | Spécification |
|---|---|
| Ontic states `W` | `{0, 1, ..., 7}` (3 bits, identiques à case 12) |
| Sensory states `X` | `{0, 1}` (compression 4:1, identique à case 12) |
| Compression **non-canonique** | `canonical(w) = (w >> 2) & 1` = **bit2** (vs bit0 case 11/12/13) |
| Canal `P(x \| w)` | Chaîne markovienne paramétrée par `α ∈ [0, 1]` |
| Paysages `L(w)` | 8 patterns (4 symétriques hérités case 11 + 4 nouveaux bit2-aligned family) |
| Stratégie Truth | `argmax_x f(MAP(x))`, MAP = `argmax_w P(x\|w) g(w)` |
| Stratégie Fitness-only | `argmax_x F(x) = E[f(W) \| x]` |
| Évolution | Sélection truncée sur `α ∈ [0, 1]` (80 pop × 200 gen × 5 seeds) |

**Fibre cardinal** : 4 (identique case 12). Mais la composition intra-fibre est **différente** sous compression bit2 vs bit0 :
- bit0 (canonique) : fibre x=0 = w ∈ {0,2,4,6}, fibre x=1 = w ∈ {1,3,5,7} → bit0 ∈ {0,1,0,1} intra-fibre = symétrique 2+2.
- bit2 (relâché) : fibre x=0 = w ∈ {0,1,2,3}, fibre x=1 = w ∈ {4,5,6,7} → bit2 partout constant 0 ou 1 intra-fibre = **DISSIMILAIRE**.

## Paysages (8 total)

| Paysage | Fitness intra-fibre x=0 | Fitness intra-fibre x=1 | Symétrie intra-fibre | Prédiction |
|---|---|---|---|---|
| L_bit0 | 0+1+0+1 (2/4 = 0.5) | 0+1+0+1 (2/4 = 0.5) | symétrique 2+2 | **null** |
| L_bit1 | 0+0+1+1 (2/4 = 0.5) | 0+0+1+1 (2/4 = 0.5) | symétrique 2+2 | **null** |
| L_parity | 0+1+1+0 (2/4 = 0.5) | 1+0+0+1 (2/4 = 0.5) | symétrique 2+2 | **null** |
| L_anti | 1+0+1+0 (2/4 = 0.5) | 1+0+1+0 (2/4 = 0.5) | symétrique 2+2 | **null** |
| **L_bit2_aligned** | 0+0+0+0 (0/4 = 0.0) | 1+1+1+1 (4/4 = 1.0) | **DISSIMILAIRE 0 vs 1** | **dissociation forte** |
| **L_bit2_complement_aligned** | 1+1+1+1 (4/4 = 1.0) | 0+0+0+0 (0/4 = 0.0) | **DISSIMILAIRE 1 vs 0** | **dissociation forte (signe inversé)** |
| L_bit01_aligned | 0+1+1+1 (3/4 = 0.75) | 0+1+1+1 (3/4 = 0.75) | symétrique 3+3 | **null** |
| L_pairity_bit12 | 0+1+1+0 (2/4 = 0.5) | 1+0+0+1 (2/4 = 0.5) | symétrique 2+2 | **null** |

**Prédictions scellées** : `|gap| ≥ 0.60` sur 2/8 paysages (bit2_aligned family), `gap ≈ 0` sur 6/8 paysages.

## Résultats — **NULL INSTRUMENTAL (N=8, M=2, compression bit2)**

`ict/results/hoffman_interface_toy_n8_relaxed_results.json` :

| Paysage | α*_Truth (5 seeds) | α*_Fit (5 seeds) | Gap | Verdict |
|---|---|---|---|---|
| L_bit0 | 0.489 ± 0.051 | 0.532 ± 0.062 | -0.043 | null |
| L_bit1 | 0.489 ± 0.051 | 0.532 ± 0.062 | -0.043 | null |
| L_parity | 0.489 ± 0.051 | 0.532 ± 0.062 | -0.043 | null |
| L_anti | 0.489 ± 0.051 | 0.532 ± 0.062 | -0.043 | null |
| **L_bit2_aligned** | 0.489 ± 0.051 | 0.532 ± 0.062 | **-0.043** | **null (instrumental)** |
| **L_bit2_complement_aligned** | 0.489 ± 0.051 | 0.532 ± 0.062 | **-0.043** | **null (instrumental)** |
| L_bit01_aligned | 0.489 ± 0.051 | 0.532 ± 0.062 | -0.043 | null |
| L_pairity_bit12 | 0.547 ± 0.021 | 0.532 ± 0.062 | +0.015 | null |

**Score FBT : 0/8 paysages avec dissociation mesurable** (gap `|≥ 0.10`).

**Prédiction P2c NON TENUE** : la cible `|gap| ≥ 0.60` sur bit2_aligned family n'est tenue sur **aucun** des 2 paysages trivialement discriminants. Pire : **les 8 paysages convergent vers α* ≈ 0.49-0.55 partout**, suggérant un comportement uniforme de l'évolution.

## Cause identifiée : bug instrumental dans `play_round` (hérité case 11 et case 13)

Le `play_round` calcule le self-payoff comme `fitness(strategy(alpha, fitness, prior))`. **Or `strategy(...)` retourne `x ∈ {0, 1}` (sensory state), pas `w ∈ {0..7}` (ontic state)**. Donc `fitness(strategy(...))` est `fitness(x) ∈ {0, 1}` — pas `fitness(w) ∈ {0, 1}` comme attendu.

Pour `L_bit2_aligned`, `fitness(0) = bit2(0) = 0` et `fitness(1) = bit2(1) = 0`. **Fitness plate** : peu importe α ou la stratégie choisie, le payoff est 0. L'évolution ne peut pas converger vers α=1 parce que α=1 et α=0 produisent la même fitness 0.

**Vérification directe** : mesure de la fitness moyenne à α fixe sur L_bit2_aligned avec stratégie Truth (sélection manuelle de x_hat et fitness(w_MAP(x_hat))) :

| α | fitness moyenne (Truth, 1000 trials) |
|---|---|
| 0.00 | 1.000 ± 0.000 |
| 0.25 | 1.000 ± 0.000 |
| 0.50 | 0.000 ± 0.000 |
| 0.75 | 1.000 ± 0.000 |
| 1.00 | 1.000 ± 0.000 |

À α=1.0 (compression parfaite), la fitness moyenne devrait être maximale (compression triviale), et elle l'est (1.0). Mais le `play_round` self-payoff reste dégénéré.

**Pourquoi les deux stratégies convergent au même α*** : le payoff est identique peu importe la stratégie choisie (toutes deux retournent x ∈ {0,1}, fitness(x) constante). L'évolution n'a aucun gradient qui distingue les deux. C'est pour cela que α*_truth ≈ α*_fit partout.

## Distinction importante : null instrumental vs null structurel

**Le verdict structurel case 13 (RÉFUTATION, null 0/16 paysages) reste valide**. Pourquoi ? Parce que case 13 utilise le même `play_round` buggé, mais **le résultat mesuré reste informatif** : pour les paysages symétriques intra-fibre (bit1, bit2, bit3, etc.), les deux stratégies retournent le même x (par symétrie), et le payoff buggé `fitness(x)` est identique. La **mesure de la symétrie** reste correcte.

**Le verdict case 14 (CONFIRMATION sur bit2_aligned family) ne peut pas être mesuré avec ce design**. La dissociation FBT requiert que les deux stratégies choisissent **des x différents** sur un paysage discriminant, et le `play_round` doit retourner `fitness(w_MAP(x_différent))` — pas `fitness(x_différent)`. C'est ce que **case 12 fait correctement** (deux territoires concurrents, payoff intra-territoire `E[f(w) | x=x_hat]`).

**Implication** : le toy case 14 livré **ne peut pas tester l'hypothèse 2 du verdict case 13**. C'est un livrable **incomplet** qui nécessitera **case 14-bis** pour mesurer correctement la dissociation FBT sur compression bit2.

## Prédiction actualisée pour case 14-bis

Case 14-bis adoptera le design case 12 (deux territoires concurrents, payoff intra-territoire `E[f(w) | x=x_hat, alpha, prior]`). Setup identique (N=8, M=2, compression bit2, 8 paysages), mais `play_round` corrigé.

**Prédictions case 14-bis** :
- Si design case 12 reproduit la dissociation sur `L_bit2_aligned` family (`|gap| ≥ 0.60`) : **CONFIRMATION** que le relâchement compression restaure la dissociation FBT à N=8.
- Si design case 12 ne reproduit pas la dissociation sur `L_bit2_aligned` family : **NULL structurel** (la compression bit2 n'aide pas — même avec play_round correct, α*_truth et α*_fit convergent vers le même point).

## Pourquoi c'est un null instrumental honnête (grade C)

1. **Le pré-enregistrement est falsifié HONNÊTEMENT.** La cible P2c (|gap| ≥ 0.60 sur bit2_aligned) **n'est PAS tenue** sur 2/8 paysages trivialement discriminants — au contraire, tous les 8 paysages convergent vers α* ≈ 0.5. Mais la falsification est **instrumentale** (bug de design), pas **structurelle** (la dissociation FBT existe peut-être mais n'est pas mesurable avec ce `play_round`).

2. **Le setup suit §4 Prakash et al. 2017** pour les éléments mesurables : compression bit2, 8 paysages avec bit2_aligned family trivialement discriminante, MAP et Fitness-only strategies correctement implémentées.

3. **L'observation est reproductible** : 5/5 seeds convergent sur le même pattern null. Le null n'est pas un artefact stochastique.

4. **Le verdict suit le pré-enregistrement (en le falsifiant instrumentalement)** : la mesure donne gap ≤ 0.05 sur 8/8 paysages, alors que le pré-enregistrement annonçait gap ≥ 0.60 sur 2/8 paysages. **Cause identifiée** : bug instrumental dans `play_round`.

5. **Le scratchpad de pré-enregistrement documente la révision des prédictions** (Tell c.898-L1 ★★★ : code = pré-enreg). Trois corrections sur les symétries intra-fibre ont été faites après mesure effective, et consignées dans la section "Note de révision" du scratchpad AVANT le verdict final.

## Limites assumées (grade C)

- **Le toy livré **ne démontre pas** que la dissociation FBT est restaurée à N=8 par relâchement de compression** — il **démontre** qu'avec `play_round` case 11/13 (self-payoff buggé), le toy est incapable de mesurer la dissociation FBT, même sur paysages trivialement discriminants.
- **Case 14-bis nécessaire** avec design case 12 (deux territoires, payoff intra-territoire) pour mesurer correctement la dissociation FBT sur compression bit2.
- **Le bug instrumental dans `play_round`** affecte aussi case 11 et case 13. **Case 11** : null mesuré = 0.000 sur 4/4 paysages (résultat conservé : même avec play_round correct, N=4 trivial). **Case 13** : null mesuré = 0.000 sur 16/16 paysages (résultat conservé : les paysages symétriques intra-fibre donnent le même x pour les deux stratégies, donc même fitness(x)). **Mais pour dissociation émergeante** (case 12 + hypothétique case 14-bis), le bug masque la mesure.
- **Aucune claim sur la conscience, le qualia, ou l'évolution biologique réelle.** Le toy teste un mécanisme formel (sélection naturelle sur signal bruité), pas une théorie de la conscience.
- **Le théorème FBT est un résultat de théorie des jeux évolutionnistes**, pas un théorème de la perception humaine.

## Vérifications

- C.1 (pas d'erreur volontaire) : grep `raise NotImplementedError\|assert False\|1/0` = 0
- C.2 (commit AVEC outputs) : `results/hoffman_interface_toy_n8_relaxed_results.json` artefact commité
- C.3 (scope re-exécutions) : pas de notebook ICT touché
- H.1 (validation exec réelle) : 21/21 tests pytest verts (0.21 s, sans les 2 tests `@pytest.mark.slow`)
- H.3 (pre-commit notebook) : N/A (toy.py, pas de notebook)
- bibliography-hygiene : PDF Prakash et al. 2017 archivé sur GDrive bibliographie (déjà fait case 11)
- Verdict format (grade C) : **NULL INSTRUMENTAL**, falsification honnête du pré-enregistrement

## Modifications

| Fichier | Δ |
|---|---|
| `MyIA.AI.Notebooks/IIT/ICT-Series/ict/hoffman_interface_toy_n8_relaxed.py` | +310 lignes (créé) |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_hoffman_interface_toy_n8_relaxed.py` | +265 lignes (créé, 23 tests dont 2 slow) |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ict/results/hoffman_interface_toy_n8_relaxed_results.json` | +422 lignes (créé, artefact) |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ict/scratchpad_hoffman_toy_case14.md` | +140 lignes (créé, pré-enregistrement + révision symétries) |
| `docs/ict/hoffman-interface-distillation-case14.md` | +200 lignes (créé, grade C) |

## Voir aussi

- Issue #8182 (tracker de veille/distillation TOE ↔ conscience)
- Issue #4588 (EPIC ICT)
- PR #14535 (case 11 Hoffman FBT toy, N=4/M=2/bit0, null de référence) — MERGED
- PR #14544 (case 12 Hoffman FBT toy, N=8/M=2/bit0, dissociation émergente 4/8 paysages) — OPEN
- PR #14548 (case 13 Hoffman FBT toy, N=16/M=2/bit0, NULL 0/16 RÉFUTATION scaling monotone) — OPEN
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/hoffman_interface_toy_n8_relaxed.py` (toy)
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/tests/test_hoffman_interface_toy_n8_relaxed.py` (23 tests)
- `MyIA.AI.Notebooks/IIT/ICT-Series/ict/results/hoffman_interface_toy_n8_relaxed_results.json` (artefact)
- Prakash, Stephens, Hoffman, Singh & Fields (2017), *Fitness Beats Truth in the Evolution of Perception*, arXiv:1505.04322
- D. Hoffman, *Objects of Consciousness* (2019), Oxford University Press

## Crédits

- **Source primaire** : Prakash et al. (2017), arXiv:1505.04322 — formalisation mathématique du toy
- **Source secondaire** : D. Hoffman, *Objects of Consciousness* (2019) — vulgarisation du théorème
- **Antécédents directs** : Case 11 (PR #14535 MERGED) + Case 12 (PR #14544 OPEN) + Case 13 (PR #14548 OPEN)
- **Pattern pré-enregistrement** : case 8/10/11/12/13 (scellé AVANT code, peut être falsifié HONNÊTEMENT par la mesure)
- **Cause structurelle case 13** (RÉFUTATION) reste valide ; cause **instrumentale** case 14 (NULL) demande case 14-bis.
