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
| p1b-engins | 3 moteurs du 4ᵉ moment : `expect_quad_two_pairs` (quadruplet apparié (i,i,k,k) → constante (a i)²(a k)²), `expect_quad_pair_and_two` (paire + 2 distinctes → 0 par factorisation), `expect_quad_four_distinct` (4 distinctes → 0 via `sampleExpect_prod_over_finset`) + `boolSign_mul_self` | brique P2 | **PROUVÉ** (p1b-engins, 08-25) | assemblage : classification des quadruplets + comptage → E[Z⁴] = 3n²−2n |
| p1b-assemblage-1 | Décomposition du carré `rademacher_sq_split` (Z² = diag `∑ (a i)²` CONSTANTE en S + `crossSum` paires ordonnées distinctes) + annulation `expect_crossSum_eq_zero` (E[crossSum] = 0 par factorisation 2-coordonnées) | brique P2 | **PROUVÉ** (p1b-assemblage-1, 08-26) | fondement de l'expansion Z⁴ = (diag + crossSum)² ; prochaine boute : classification crossSum² (paires appariées 3n²−6n... constantes, reste 0) → E[Z⁴] = 3n²−2n |
| p1b-assemblage-2 (moteurs) | Moteurs de multiplicité : `expect_coord_pow` (E[(c·sign)^m] = c^m si pair, 0 sinon) et `expect_prod_coord_mult` (E[∏_{r∈u} x r^{m r}] = ∏_{r∈u} (a r)^{m r} si m r pair, 0 sinon) — la parité de la multiplicité tue chaque terme | brique P2 | **PROUVÉ** (moteurs, 08-26) | entrée directe pour la classification crossSum² : q ≡ p ou swap(p) ⟺ toutes multiplicités paires |
| p1b-assemblage-3 (classification) | Interface de classification des quadruplets : `expect_quad_paired` (x_i·x_j·x_i·x_j → (a i)²(a j)²), `expect_quad_paired_swap` (forme croisée), `expect_quad_unpaired_zero` ({k,l} ne recollent pas {i,j} → 0, arbre de cas i=k / i=l / j=k / j=l / 4 distincts réduits aux moteurs p1b-engins) | brique P2 | **PROUVÉ** (assemblage-3, 08-26) | E[crossSum²] : chaque (p,q) se réduit à l'une des 3 formes ; prochaine boute : somme interne par p (2 témoins q) → E[C²] = 2((∑a²)²−∑a⁴) |
| p1b-assemblage-4 (somme interne) | `sum_expect_cross_pair` : ∑_q E[F p·F q] = 2(a p.1)²(a p.2)² si p hors diagonale, 0 sinon — les deux seuls contributeurs sont q = p et q = transposé p (scindage or → deux `sum_ite_eq'`), le reste éteint par classification | brique P2 | **PROUVÉ** (assemblage-4, 08-26) | E[C²] = ∑_p (somme interne) ; prochaine boute : somme externe → E[C²] = 2((∑a²)²−∑a⁴) puis E[Z⁴] = 3(∑a²)²−2∑a⁴ |
| p1b-assemblage-5 (E[C²]) | `expect_crossSum_sq` : E[crossSum²] = 2((∑a²)² − ∑a⁴) — assemblage complet : E = ∑_p E[∑_q F p·F q] (sampleExpect_sum) → somme interne (assemblage-4) → ∑_p ite(offdiag, 2c_p, 0) = 2·offdiag ; offdiag = S2² − S4 via scindage ite (ne = total − diag), S2² = ∑_p c_p (sum_mul_sum + sum_prod_type.symm), diag = S4 (sum_ite_eq) | brique P2 | **PROUVÉ** (assemblage-5, 08-26) | prochaine boute : E[Z⁴] = 3(∑a²)² − 2∑a⁴ via Z⁴ = (diag+C)² puis coloration → 3n²−2n |
| p1b-assemblage-6 (**E[Z⁴] complet**) | `sampleExpect_add` (additivité, complément kernel), `expect_rademacher_fourth_moment` : E[Z⁴] = 3(∑a²)² − 2∑a⁴ via Z⁴ = (diag+C)² + additivité + const + smul ×0 + E[C²] (assemblage-5), **corollaire coloration `expect_rademacherSum_fourth_moment_of_isColoring` : E[Z⁴] = 3n² − 2n uniforme en c** | brique P2 | **PROUVÉ** (assemblage-6, 08-26) | LE 4ᵉ MOMENT EST ÉTABLI — prochaine boute p1b-PZ : Paley–Zygmund (E[Z²]²/E[Z⁴] ≥ 1/3 ⇒ ℙ[Z² > n/2] ≥ (1−1/2)²·n²/(3n²−2n)) puis minoration de queue ≥ c > 0 |
| p1b-PZ-1 (Cauchy–Schwarz discret) | Infrastructure Paley–Zygmund : `probEvt` (probabilité = espérance de l'indicatrice, cadre ℝ-weight), `sampleExpect_split_indicator` (E[f] = E[f·1_A] + E[f·1_Ac]), `weighted_cauchy` ((∑wuv)² ≤ (∑wu²)(∑wv²) par discriminant : trinôme t↦∑w(u−tv)² ≥ 0 évalué en t=B/C), `expect_sq_le_mul_prob` ((E[f·1_B])² ≤ E[f²·1_B]·P[B]) | brique P2 | **PROUVÉ** (p1b-PZ-1, 08-26) | assemblage final : E[Z²] = n ≤ √(E[Z⁴]·P) + n/2 → ℙ[Z²≥n/2] ≥ 1/12 |
| p1b-PZ-2 (minoration de queue) | `prob_tail_ge_of_isColoring` (mono via le lemme kernel `PacLearning.sampleExpect_mono`, dédupliqué) : ℙ[Z_S² ≥ n/2] ≥ 1/12 pour toute coloration c — découpage E[Z²] = E[Z²·1_A] + E[Z²·1_Ac] avec E[Z²·1_Ac] ≤ (n/2)·P[Aᶜ] ≤ n/2, Cauchy (E[Z²·1_A])² ≤ E[Z⁴·1_A]·P[A] ≤ 3n²·P[A], mono indicatrice, nlinarith final (n² ≤ 12·n²·P, n² > 0) | brique P2 | **PROUVÉ** (p1b-PZ-2, 08-26) | moments + queue : le versant « une coloration fixe a une grande somme » est complet ; reste p2 familles aléatoires (m tirages), p3 union bound, p4 contrôle degré |
| p2 (familles aléatoires) | `coinDist` (n-échantillon fairCoin comme `Distribution (Fin n → Bool)`), `familyExpect`/`familyProb` (loi produit coinDist^m sur `Fin m → Fin n → Bool`), `familyExpect_prod_blocks` (**indépendance des blocs** : E[∏_k f k (F k)] = ∏_k E[f k] par `Fintype.prod_sum` — Fubini discret), `familyExpect_add`/`_one`, `familyProb_compl`, et le théorème d'application `family_tail_ge` : ℙ[∃ k, Z_{F k}² ≥ n/2] ≥ 1 − (11/12)^m | brique P2 | **PROUVÉ** (p2, 08-26) | p3 union bound sur les 2^n colorations, p4 contrôle de degree (hoeffding_upper_tail) || p1a | Moments de la somme de Rademacher colorée : `expect_rademacherSum_eq_zero` (`E[Z] = 0`), `expect_rademacherSum_sq` (`E[Z²] = ∑ (c i)²`), corollaire coloration (`E[Z²] = n`) + briques `sampleExpect_coord_mul_coord` (factorisation 2-coordonnées, extension kernel), `prod_two_special`, `fairCoin`/`boolSign` | brique P2 | **PROUVÉ** (p1a, 08-25) | uniformité en `c` établie ; p1b = 4ᵉ moment + Paley–Zygmund |
| p3 (union bound) | `colorOf` (encodage booléen → coloration ; `Fin n → ℤ` n'est PAS un Fintype, les colorations sont dénombrées comme IMAGE des `2^n` booléens), `indicator_bUnion_le_sum` (indicatrice d'union ≤ somme d'indicatrices, `Finset.induction_on`), `familyExpect_sum_finset` (linéarité Finset), `familyProb_union_le` (union bound en probabilité via `sampleExpect_mono`), `card_colorings_le` (≤ 2^n par `Finset.card_image_le`), `exists_of_familyProb_pos` (probabilité > 0 ⇒ témoin), et le théorème d'application `exists_family_beats_all_colorings` : pour n ≥ 1 il existe une famille de 12n tirages battant TOUTES les colorations (ℙ[échec] ≤ 2^n·(11/12)^(12n) < 1, numérie par induction `(2·(11/12)^12)^t < 1`) | brique P2 | **PROUVÉ** (p3, 08-26) | le second passage probabiliste (existentiel) est complet ; reste p4 contrôle de degré (`hoeffding_upper_tail`) + assemblage final ErdosSpencerLB |
| p4 (contrôle du degré + assemblage) | `rademacherSum_eq_two_sub` (identité Z = 2·(somme des coords vraies) − somme totale, pont alea signé ↔ sommes d'ensembles), `blockOf`/`drawSet`/`pairFamily` (bloc de t = k/12 points via `Fin.castLEEmb`, tirage → coordonnées vraies, FAMILLE APPARIÉE (drawSet, bloc \\ drawSet)), `blockOf_sum`/`drawSet_sum`/`drawSet_subset`, `drawSet_mem`/`compDraw_mem`, `degree_pairFamily_le` (degré ≤ m par injection vers `Finset.range m` : chaque paire est disjointe donc un point apparaît au plus une fois par tirage), et le THÉORÈME FINAL `erdos_spencer_lb_explicit` : ∀ n k ≥ 1, k ≤ n → ∃ F, maxDegree F ≤ k ∧ ∀ C coloration, Nat.sqrt k ≤ 14 * discrepancy F C — petit k < 12 singletons, gros k = 12 tirages par bloc de k/12 points, triangulaire |Z| ≤ |x| + |x−s| ≤ 2·disc, k ≤ 23t ≤ 184·disc² | brique P2 | **PROUVÉ** (p4, 08-26, axiomes [propext, Classical.choice, Quot.sound]) | **P2 EST ASSEMBLÉ** à constante explicite √k/14 ; la forme optimiste √k/2 (`ErdosSpencerLB`) reste une `Prop` OUVERTE (obstruction structurelle : Paley–Zygmund force m ≥ 12t tirages, degré force m ≤ k — documenté dans le statut du module) |
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
