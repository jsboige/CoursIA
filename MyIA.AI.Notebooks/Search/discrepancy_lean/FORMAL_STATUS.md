# FORMAL_STATUS — lake `discrepancy_lean`

Registre d'état des preuves (convention des lakes coopératifs du dépôt :
une boute livrée = une ligne mise à jour ici). Source : issue #12823.
Paper de référence : Bansal–Jiang, *Decoupling via Affine Spectral-Independence:
Beck-Fiala and Komlós Bounds Beyond Banaszczyk* (arXiv:2508.03961, 2025).

## Invariants du lake (HARD)

- **0 `sorry`** — anti-régression D. Une boute non finie reste en branche,
  jamais sur main.
- **Conjecture = `def ... : Prop` nommée** — jamais un théorème tronqué.
  Quand une preuve est assemblée, la `Prop` devient un `theorem` (la forme
  d'énoncé reste disponible comme définition).
- **Docstrings FR-first** (convention i18n #4980 ; traduction `_en` sibling
  optionnelle si audience externe).
- **Toolchain/manifest** alignés sur la cohorte fleet v4.32.1 (mathlib
  `520045ab`, mutualisation #4363).

## État des preuves

| ID | Énoncé | Nature | Statut | Livré |
|----|--------|--------|--------|-------|
| P0 | `Discrepancy.Basic` : `IsColoring`, `discrepancy`, `degree`, `maxDegree` + 3 lemmes (`discrepancy_empty`, `discrepancy_singleton_empty`, `degree_le_card`) | fondations | **PROUVÉ** (P0) | ce PR |
| P0 | `BeckFialaConjecture` (`O(√k)`) | conjecture ouverte | **Prop nommée** (P0) | ce PR |
| P0 | `BeckFialaClassic` (`disc ≤ 2k − 1`) | théorème classique — la « noix » | **Prop nommée** (P0) ; cible P1 | ce PR |
| P0 | `KomlosConjecture` (`O(1)`, colonnes unitaires) | conjecture ouverte | **Prop nommée** (P0) | ce PR |
| P0 | `BansalJiangLargeDegree` (BF vrai dès `k ≥ log² n`) | théorème papier 2025 | **Prop nommée** (P0) ; P3 | ce PR |
| P0 | `KomlosBansalJiangWeak` (colonnes unitaires, `C·log² n`) | forme affaiblie concrète du papier | **Prop nommée** (P0) ; P3 | ce PR |
| b1 | Double comptage dimensionnel `card_dangerous_lt_card_floating` (lignes à `>k` flottants ⇒ \|D\| < \|X\|) + direction de noyau `exists_dangerous_kernel_vec` (Q^X → Q^D non injective) | brique P1 | **PROUVÉ** (b1) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| b2 | Invariant de coloration partielle `frozen_line_sum_le` (ligne figée à `\le k` flottants, somme initialement préservée, dérive `< 2` par flottant + arrondi entier ⇒ `\|\sum c\| \le 2k-1`) + briques `sum_sub_eq_sum_inter`, `natAbs_le_of_cast_abs_lt` | brique P1 | **PROUVÉ** (b2) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| b3 | Progrès d'une phase `exists_step_hits_boundary` (pas = min des temps de contact `hitTime`, positif, cube fermé préservé, \u2265 1 flottant atteint `\|\cdot\| = 1`) | brique P1 | **PROUVÉ** (b3) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| b4 | Terminaison + assemblage : invariant complet `BFInv` (flottants intérieurs, figés exactement `±1`, lignes dangereuses de somme nulle, registre d'abandon par ligne) + phase `exists_phase` (décroissance stricte du nombre de flottants) + arrondi final `exists_coloring_of_no_danger` (b2 par ligne) + induction `bf_loop` → `theorem beck_fiala_classic` | brique P1 | **PROUVÉ** (b4) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| P2 | Borne inférieure Erdős–Spencer `√k/2` (méthode probabiliste), en **réutilisant** le kernel `ML/learning_theory_lean/PacLearning/Hoeffding.lean` (import, pas duplication) | bornes inf | **EN COURS** — câblage fait (08-25) : require cross-lake `learning_theory_lean` (path relatif, manifest `dir: ../../ML/learning_theory_lean`), module `Discrepancy.ErdosSpencer` avec l'énoncé cible `ErdosSpencerLB` en `Prop` nommée + import `PacLearning.Hoeffding` (kernel compilé comme dépendance, jamais dupliqué). `lake build SUCCESS` 8672 jobs. Découpage preuve en boutes `p1`–`p4` (anti-concentration / familles aléatoires / union bound / contrôle du degré), voir l'en-tête du module. | boute p1 suivante : anti-concentration via `hoeffding_concentration` |
| p1b-infra | Factorisation sur Finset `sampleExpect_prod_over_finset` (E[∏_{q∈s} g q (S q)] = ∏_{q∈s} E[g q], généralisation 2-coord + kernel), parité des moments du signe `expect_mul_boolSign_pow` (E[a·sign^k] = a si pair, 0 sinon), annulation des moments mixtes `expect_prod_eq_zero_of_mem` | brique P2 | **PROUVÉ** (p1b-infra, 08-25) | prépare le 4ᵉ moment (classification des quadruplets d'indices) |
| p1a | Moments de la somme de Rademacher colorée : `expect_rademacherSum_eq_zero` (`E[Z] = 0`), `expect_rademacherSum_sq` (`E[Z²] = ∑ (c i)²`), corollaire coloration (`E[Z²] = n`) + briques `sampleExpect_coord_mul_coord` (factorisation 2-coordonnées, extension kernel), `prod_two_special`, `fairCoin`/`boolSign` | brique P2 | **PROUVÉ** (p1a, 08-25) | uniformité en `c` établie ; p1b = 4ᵉ moment + Paley–Zygmund |
| P3 | Banaszczyk 1998 / formes fortes du papier 2025 | aspiration | **NON ENGAGÉ** — exige SDP + dualité, indépendance spectrale affine, brownien discret guidé, concentration matricielle : **aucun de cet étage n'existe dans Mathlib** (vérifié 2026-08-24). Documenté, jamais promis. | — |

## Découpage de la noix (P1) — grignotage multi-cycles

Mandat user 2026-08-24 : « grignoter la noix de preuve la plus dure dans la
durée par petits bôuts ». Chaque boute `b1..b4` est un grain **claimable
séparément**, commité **seulement si elle build** (0 sorry intermédiaire) ;
une boute non finie reste en branche. Ordre : `b1` → `b2` → `b3` → `b4`
(les dépendances sont linéaires ; `b4` assemble).

## Note d'honnêteté (G.3)

Le palier P0 ne prouve **aucun** théorème du domaine : il pose les
définitions, trois lemmes-limites immédiats (famille vide, partie vide,
degré ≤ cardinal), et les énoncés exacts de la frontière — y compris la
cible `2k−1` et les deux conjectures ouvertes. C'est le socle sur lequel
grignoter ; la valeur de preuve commence à `b1`.
