# discrepancy_lean — discrépance combinatoire

Lake Lean 4 (Mathlib) de formalisation de la **discrépance combinatoire** :
colorer en `±1` les éléments d'un système d'ensembles de degré `≤ k` en
minimisant la pire somme colorée `‖Ax‖∞`. Suivi : issue
[#12823](https://github.com/jsboige/CoursIA/issues/12823). Paper de
référence : Bansal–Jiang 2025, [arXiv:2508.03961](https://arxiv.org/abs/2508.03961)
— Beck-Fiala et Komlós au-delà de Banaszczyk, par découplage via
indépendance spectrale affine.

**Première formalisation du sujet** ni dans le dépôt ni dans Mathlib
(vérifié 2026-08-24 : `beck.?fiala|banaszczyk|komlos` = 0 hit).

## Désambiguïsation (une ligne)

« Discrepancy » dans [Search-13](../Part3-Advanced/Search-13-LimitedDiscrepancySearch.ipynb)
= *Limited Discrepancy Search* de Harvey & Ginsberg (choix non heuristiques
dans un arbre de recherche) — **aucun rapport** avec les sommes signées
formalisées ici.

## Structure

| Fichier | Contenu |
|---------|---------|
| `Discrepancy/Basic.lean` | définitions (`IsColoring`, `discrepancy`, `degree`, `maxDegree`), 3 lemmes élémentaires, `BeckFialaConjecture` (`O(√k)`), cible `BeckFialaClassic` (`disc ≤ 2k − 1`) |
| `Discrepancy/Komlos.lean` | `KomlosConjecture` (`O(1)`, colonnes unitaires), `BansalJiangLargeDegree` (`k ≥ log² n`), `KomlosBansalJiangWeak` (forme concrète affaiblie) |
| `Discrepancy/Kernel.lean` | brique b1 — double comptage dimensionnel `card_dangerous_lt_card_floating` + direction de noyau `exists_dangerous_kernel_vec` |
| `Discrepancy/Partial.lean` | brique b2 — invariant de coloration partielle `frozen_line_sum_le` (lignes figées ≤ 2k−1) |
| `Discrepancy/Progress.lean` | brique b3 — lemme de progrès `exists_step_hits_boundary` (≥ 1 flottant se fige par phase) |
| `Discrepancy/BeckFiala.lean` | brique b4 — terminaison + assemblage : `theorem beck_fiala_classic` (`disc ≤ 2k − 1`), la « noix » P1 **PROUVÉE** |
| `Discrepancy/ErdosSpencer.lean` | chaîne P2 p1a–p4 — moments de Rademacher, 4ᵉ moment, Paley–Zygmund, familles aléatoires, union bound : `theorem erdos_spencer_lb_explicit` (√k/14) **PROUVÉ** |
| `Discrepancy.lean` | agrégateur racine |
| `Discrepancy/Basic_en.lean`, `Discrepancy/Komlos_en.lean`, `Discrepancy_en.lean` | siblings EN (i18n #4980) : docstrings traduites, signatures/preuves byte-identiques |

État des preuves et découpage en boutes (Beck–Fiala classique `b1..b4` et
Erdős–Spencer `p1a..p4`, toutes **PROUVÉES**) :
[FORMAL_STATUS.md](FORMAL_STATUS.md). La forme optimiste `√k/2`
(`ErdosSpencerLB`) reste une `Prop` ouverte ; le palier P3 (Banaszczyk)
n'est pas engagé (aucun étage correspondant dans Mathlib).

## Conventions

- **0 `sorry`** ; conjectures = `def ... : Prop` nommées, jamais théorèmes
  tronqués.
- Docstrings **FR-first** (i18n #4980).
- Toolchain `leanprover/lean4:v4.32.1`, Mathlib `v4.32.1` (`520045ab`) —
  aligné sur la cohorte fleet (mutualisation #4363).

## Build

```bash
lake exe cache get   # oleans Mathlib
lake build
```

Dépendance cross-lake : `require learning_theory_lean` (chemin relatif
`../../ML/learning_theory_lean`, kernel `PacLearning.Hoeffding` importé
pour P2, jamais dupliqué) — le lake frère fait partie du build.

## Le fil « découplage » (pourquoi ce lake ici)

Le geste technique du papier — *découpler* des évolutions qui conspiraient —
est un motif récurrent du dépôt : reparamétrisation non centrée
[PyMC-12](../../Probas/PyMC/PyMC-12-Modeles-Hierarchiques.ipynb), découplage de
Hoeffding ([`PacLearning/Hoeffding.lean`](../../ML/learning_theory_lean/PacLearning/Hoeffding.lean),
réutilisé en P2 pour Erdős–Spencer), double-Q du RL, Fox-decoupling de
`knot_lean`. Ce lake en est le cinquième volume, porté à la certitude
formelle ; le grounding complet (ICT, « mesures naïves = signaux fantômes »)
vit dans le corps de l'issue #12823.
