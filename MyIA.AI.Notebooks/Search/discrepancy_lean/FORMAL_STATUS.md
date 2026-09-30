# FORMAL_STATUS — lake `discrepancy_lean`

Registre d'état des preuves (convention des lakes coopératifs du dépôt :
une boute livrée = une ligne mise à jour ici). Source : issue #12823.
Paper de référence : Bansal–Jiang, *Decoupling via Affine Spectral-Independence:
Beck-Fiala and Komlós Bounds Beyond Banaszczyk* (arXiv:2508.03961, 2025).

**Voie de preuve élémentaire (réaudit 2026-09-25)** : Karingula–Lovett,
*An elementary proof of the Komlós conjecture* (arXiv:2609.20979, v1 17/09/2026,
v2 22/09/2026 ; ECCC TR26-188), constante `36` — ni transformée de Banaszczyk,
ni variation totale directionnelle. Réaudit de la ligne P3 et découpage en
boutes `k1..k5` ci-dessous ; issue de suivi : #17845.

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
| P0 | `BeckFialaConjecture` (`O(√k)`) | **résolution annoncée** — preprint arXiv:2609.11189 (10/09/2026), non revu | **Prop nommée** (P0) | ce PR |
| P0 | `BeckFialaClassic` (`disc ≤ 2k − 1`) | théorème classique — la « noix » | **Prop nommée** (P0) ; cible P1 | ce PR |
| P0 | `KomlosConjecture` (`O(1)`, colonnes unitaires) | **résolution annoncée** — preprint arXiv:2609.11189 (10/09/2026), non revu | **Prop nommée** (P0) | ce PR |
| P0 | `BansalJiangLargeDegree` (BF vrai dès `k ≥ log² n`) | théorème papier 2025 | **Prop nommée** (P0) ; P3 | ce PR |
| P0 | `KomlosBansalJiangWeak` (colonnes unitaires, `C·log² n`) | forme affaiblie concrète du papier | **Prop nommée** (P0) ; P3 | ce PR |
| b1 | Double comptage dimensionnel `card_dangerous_lt_card_floating` (lignes à `>k` flottants ⇒ \|D\| < \|X\|) + direction de noyau `exists_dangerous_kernel_vec` (Q^X → Q^D non injective) | brique P1 | **PROUVÉ** (b1) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| b2 | Invariant de coloration partielle `frozen_line_sum_le` (ligne figée à `\le k` flottants, somme initialement préservée, dérive `< 2` par flottant + arrondi entier ⇒ `\|\sum c\| \le 2k-1`) + briques `sum_sub_eq_sum_inter`, `natAbs_le_of_cast_abs_lt` | brique P1 | **PROUVÉ** (b2) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| b3 | Progrès d'une phase `exists_step_hits_boundary` (pas = min des temps de contact `hitTime`, positif, cube fermé préservé, \u2265 1 flottant atteint `\|\cdot\| = 1`) | brique P1 | **PROUVÉ** (b3) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| b4 | Terminaison + assemblage : invariant complet `BFInv` (flottants intérieurs, figés exactement `±1`, lignes dangereuses de somme nulle, registre d'abandon par ligne) + phase `exists_phase` (décroissance stricte du nombre de flottants) + arrondi final `exists_coloring_of_no_danger` (b2 par ligne) + induction `bf_loop` → `theorem beck_fiala_classic` | brique P1 | **PROUVÉ** (b4) | branche `lean/b1-discrepancy-kernel` (gated P0 #12839) |
| P2 | Borne inférieure Erdős–Spencer `√k/2` (méthode probabiliste), en **réutilisant** le kernel `ML/learning_theory_lean/PacLearning/Hoeffding.lean` (import, pas duplication) | bornes inf | **PROUVÉ à constante explicite `√k/14`** (assemblage p1a–p4, 08-26) : `theorem erdos_spencer_lb_explicit` (∀ n k ≥ 1, k ≤ n → ∃ F, maxDegree F ≤ k ∧ toute coloration a discrepancy ≥ √k/14). Le kernel `PacLearning.Hoeffding` est importé (require cross-lake, jamais dupliqué). La forme optimiste `√k/2` (`ErdosSpencerLB`) reste une `Prop` OUVERTE (obstruction documentée, ligne p4). | boutes p1a–p4 ci-dessous |
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
| p2 (familles aléatoires) | `coinDist` (n-échantillon fairCoin comme `Distribution (Fin n → Bool)`), `familyExpect`/`familyProb` (loi produit coinDist^m sur `Fin m → Fin n → Bool`), `familyExpect_prod_blocks` (**indépendance des blocs** : E[∏_k f k (F k)] = ∏_k E[f k] par `Fintype.prod_sum` — Fubini discret), `familyExpect_add`/`_one`, `familyProb_compl`, et le théorème d'application `family_tail_ge` : ℙ[∃ k, Z_{F k}² ≥ n/2] ≥ 1 − (11/12)^m | brique P2 | **PROUVÉ** (p2, 08-26) | p3 union bound sur les 2^n colorations, p4 contrôle de degree (hoeffding_upper_tail) |
| p1a | Moments de la somme de Rademacher colorée : `expect_rademacherSum_eq_zero` (`E[Z] = 0`), `expect_rademacherSum_sq` (`E[Z²] = ∑ (c i)²`), corollaire coloration (`E[Z²] = n`) + briques `sampleExpect_coord_mul_coord` (factorisation 2-coordonnées, extension kernel), `prod_two_special`, `fairCoin`/`boolSign` | brique P2 | **PROUVÉ** (p1a, 08-25) | uniformité en `c` établie ; p1b = 4ᵉ moment + Paley–Zygmund |
| p3 (union bound) | `colorOf` (encodage booléen → coloration ; `Fin n → ℤ` n'est PAS un Fintype, les colorations sont dénombrées comme IMAGE des `2^n` booléens), `indicator_bUnion_le_sum` (indicatrice d'union ≤ somme d'indicatrices, `Finset.induction_on`), `familyExpect_sum_finset` (linéarité Finset), `familyProb_union_le` (union bound en probabilité via `sampleExpect_mono`), `card_colorings_le` (≤ 2^n par `Finset.card_image_le`), `exists_of_familyProb_pos` (probabilité > 0 ⇒ témoin), et le théorème d'application `exists_family_beats_all_colorings` : pour n ≥ 1 il existe une famille de 12n tirages battant TOUTES les colorations (ℙ[échec] ≤ 2^n·(11/12)^(12n) < 1, numérie par induction `(2·(11/12)^12)^t < 1`) | brique P2 | **PROUVÉ** (p3, 08-26) | le second passage probabiliste (existentiel) est complet ; reste p4 contrôle de degré (`hoeffding_upper_tail`) + assemblage final ErdosSpencerLB |
| p4 (contrôle du degré + assemblage) | `rademacherSum_eq_two_sub` (identité Z = 2·(somme des coords vraies) − somme totale, pont alea signé ↔ sommes d'ensembles), `blockOf`/`drawSet`/`pairFamily` (bloc de t = k/12 points via `Fin.castLEEmb`, tirage → coordonnées vraies, FAMILLE APPARIÉE (drawSet, bloc \\ drawSet)), `blockOf_sum`/`drawSet_sum`/`drawSet_subset`, `drawSet_mem`/`compDraw_mem`, `degree_pairFamily_le` (degré ≤ m par injection vers `Finset.range m` : chaque paire est disjointe donc un point apparaît au plus une fois par tirage), et le THÉORÈME FINAL `erdos_spencer_lb_explicit` : ∀ n k ≥ 1, k ≤ n → ∃ F, maxDegree F ≤ k ∧ ∀ C coloration, Nat.sqrt k ≤ 14 * discrepancy F C — petit k < 12 singletons, gros k = 12 tirages par bloc de k/12 points, triangulaire \|Z\| ≤ \|x\| + \|x−s\| ≤ 2·disc, k ≤ 23t ≤ 184·disc² | brique P2 | **PROUVÉ** (p4, 08-26, axiomes [propext, Classical.choice, Quot.sound]) | **P2 EST ASSEMBLÉ** à constante explicite √k/14 ; la forme optimiste √k/2 (`ErdosSpencerLB`) reste une `Prop` OUVERTE (obstruction structurelle : Paley–Zygmund force m ≥ 12t tirages, degré force m ≤ k — documenté dans le statut du module) |
| P3 | Banaszczyk 1998 / formes fortes des papiers 2025 **et 2026** | aspiration | **NON ENGAGÉ** — exige SDP + dualité, indépendance spectrale affine, brownien discret guidé, concentration matricielle : **aucun de cet étage n'existe dans Mathlib** (vérifié 2026-08-24). **Réaudité 2026-09-13** contre le Mathlib pinné (`520045ab`, v4.32.1) : le contournement proposé par arXiv:2609.11189 ne supprime pas l'obstruction, il la **déplace** — sa route exige la *variation totale directionnelle* d'une densité sur convexe ouvert et la *transformée de Banaszczyk* préservée sous translation, deux notions **absentes du même Mathlib** (`Banaszczyk` : 0 occurrence ; `totalVariation` n'existe que pour les mesures signées ; la théorie BV de Mathlib concerne la dérivabilité a.e. des fonctions de `ℝ`). Ce que ce papier rapproche, ce sont les *socles* : gaussiennes (`Probability/Distributions/Gaussian/*`) et `ConvexBody` (`Analysis/Convex/Body.lean`) sont présents ; le **pont** manque. Documenté, jamais promis. **Réaudité 2026-09-25** : la voie **élémentaire** de Karingula–Lovett (arXiv:2609.20979, constante `36`) **supprime** cet étage au lieu de le déplacer — sa mécanique est discrète (distance de décalage `Δ`, opérateur de scission `T_v`, induction sur `n` et `d`) à une seule exception, l'estimation de la densité-tente, qui se fait par FTC sur segments + Cauchy–Schwarz `L²` et **non** par de la théorie BV. Balayage des prérequis sur le checkout Mathlib local (`v4.32.0`) : famille **`norm_image_sub_le` présente** (dont `Analysis/Calculus/IntervalIntegral/DistLEIntegral.lean`), `totalVariation` toujours cantonné aux mesures vectorielles (`VectorMeasure/Decomposition/*`) — mais le papier n'en a plus besoin. Réserve de portée : ce balayage porte sur un checkout **voisin** (`v4.32.0`), pas sur le pin du lake (`520045ab`) — à re-vérifier avant la première boute `.lean`. Une formalisation Lean 4 tierce de cette preuve existe déjà (mise à jour du 2026-09-25 ci-dessous). | — |
| probe-15944 (réduction, cas régulier) | `komlos_oracle_imp_beck_fiala_regular` (`Komlos.lean` + sibling `_en`) : tout oracle de Komlós **réel** (colonnes unitaires, sommes de lignes `≤ C` en valeur absolue) implique `disc ≤ 2⌈C⌉₊ · Nat.sqrt k` pour toute famille **régulière** (chaque élément dans exactement `k` parties). Scaling uniforme `1/√k` licite car tous degrés égaux ; conversion `ℝ → ℕ` par `√k ≤ Nat.sqrt k + 1`. | brique P3 (pont) | **PROUVÉ** (2026-09-17) | Première brique du pont vers l'oracle du preprint 2026 : avec `C = 3√(2π)` (borne annoncée arXiv:2609.11189, non revue), les familles de degré exactement `t` admettent `disc ≤ 16√t` — **conditionnellement** au preprint. Cas général bloqué par deux obstructions mesurées : degrés hétérogènes (le scaling par colonne `1/√(deg j)` rend la somme colorée pondérée non factorisable — la réduction connue exige la coloration partielle itérée) et l'énoncé `ℚ` de `KomlosConjecture` (scaling irrationnel ; la forme réelle est le pont naturel). |

### Statut épistémique — mise à jour 2026-09-13

Le preprint **arXiv:2609.11189** (*Vector Balancing via Directional Total Variation*, Guo–Fang–Lu, soumis le 10/09/2026) annonce une borne universelle de **`3√(2π) ≈ 7,52`** pour le problème de signature de Komlós, et **`3√(2πt)`** pour Beck–Fiala au degré `t` — soit la dépendance en `√t` prédite par la conjecture. Cela **retire aux deux énoncés leur statut de conjecture ouverte**.

Trois réserves, qui sont la raison pour laquelle la colonne « Statut » ci-dessus continue de dire `Prop nommée` et non « résolue » :

1. le preprint a moins d'une semaine et **n'est pas revu par les pairs** ;
2. la preuve annoncée est **existentielle** (aucune implémentation revendiquée, constante non optimale) ;
3. les énoncés de ce lake ne sont **pas verbatim** ceux du papier — `ℚ` contre `ℝ`, `Nat.sqrt` (plancher entier) contre `√` réelle, borne stricte contre non stricte. Écrire « résolue » laisserait croire que *l'énoncé du lake* est déchargé : il ne l'est pas, aucune preuve formelle n'est engagée ici.

**Attention à la constante** : `3√(2π) = √(18π) ≈ 7,5199`. La forme `√(32π) ≈ 10,0265`, qui circule, **n'est pas** celle du papier — c'est exactement 4/3 de celle-ci.

Fait notable, cité verbatim depuis l'abstract : *« The proof was discovered by the Odin Automatic AI Research Agent. »*

### Statut épistémique — mise à jour 2026-09-25 (voie élémentaire)

**arXiv:2609.20979** — *An elementary proof of the Komlós conjecture*
(S. Karingula, S. Lovett ; v1 17/09, v2 22/09/2026 ; ECCC TR26-188). Théorème 1.2 :
pour `v_1 … v_n ∈ ℝ^d` avec `‖v_i‖₂ ≤ 1`, il existe `ε_i ∈ {−1,1}` tels que
`‖Σ ε_i v_i‖_∞ ≤ 36`. Prix assumé de l'élémentarité : `36` contre
`3√(2π) ≈ 7,52` (papier de #15944), les auteurs déclarant ne pas optimiser.

La preuve se décompose en **six pièces**, aucune n'exigeant un étage absent de
Mathlib :

| # | Pièce | Contenu |
|---|-------|---------|
| 1 | Def 1.3 | distance de décalage `Δ(P,u) = d_TV(P, P+u) = ½ Σ_x \|P(x) − P(x−u)\|` |
| 2 | Def 3.1 | opérateur de **scission** discret `T_v` : `(T_vP)(x,0) = ½max{P(x+v),P(x−v)}`, `(x,1) = ½min{…}` — remplace le réarrangement continu de Guo–Fang–Lu |
| 3 | Claim 3.2 | monotonie `Δ(T_vP, (u,0)) ≤ Δ(P,u)` |
| 4 | Lemme 1.4 | `Δ(P, 6v_i) ≤ 1/3` ⟹ signes tels que `μ(P) + Σ ε_i v_i ∈ conv(supp P)` — induction simultanée sur `n` **et** `d` |
| 5 | Lemme 4.1 | densité-tente `F = f²`, `f = Π_k b(x_k)`, `b(t) = (1/12)max{6−\|t\|,0}` : `∫(f(·+v) − f)² ≤ ‖v‖₂²/12` (FTC sur segments + Cauchy–Schwarz), d'où `TV ≤ ‖v‖₂/√12` |
| 6 | Lemme 1.5 + Thm | discrétisation sur la grille `N⁻¹ℤ^d` (l'arrondi ne fait pas monter la TV) ⟹ `P` fini supporté sur `[−6,6]^d` ; assemblage `Σ ε_i v_i ∈ [−36,36]^d`, constante `36 = 6 × 6` |

**Ce que cela change pour les énoncés nommés du lake** — un changement de
nature, pas de degré :

- `KomlosConjecture` est posé sur **ℚ** : le papier traite les entrées
  rationnelles par sa voie **finie** (Lemme 1.5 + pigeonhole), donc la jambe
  d'approximation réelle **n'est pas nécessaire** pour décharger l'énoncé du
  lake. Témoin plausible `C = 36 : ℚ` (marge à établir à la boute).
- `KomlosBansalJiangWeak` (`C·log² n`) devient un **corollaire gratuit** d'une
  constante explicite (pour `n ≥ 2`, `(log₂ n)² ≥ 1`).
- `komlos_oracle_imp_beck_fiala_regular` (PROUVÉ, probe #15944) devient
  **instanciable inconditionnellement** : Beck–Fiala régulier à
  `2·⌈36⌉·√k = 72√k`.
- Le corollaire Beck–Fiala du papier (constante `36√t`) a la forme exacte de
  `BeckFialaConjecture`, et **impliquerait `BansalJiangLargeDegree`** (dont
  l'hypothèse `k ≥ log² n` devient un cas particulier). **Non acquis** : le
  mécanisme du corollaire pour les **degrés hétérogènes** reste à confronter au
  texte — c'est précisément le point où l'obstruction documentée (itération de
  coloration partielle) doit être réexaminée.

**Corroboration machine** : une formalisation **Lean 4 de cette preuve existe
déjà**, par Dahia (référence [11] du papier ; enregistrée sur Palomar le
18/09/2026), dépôt `github.com/gdahia/Komlos` (Apache-2.0) — modules
`ShiftDistance`, `Split`, `Pullback`, `SignedSums`, `Tent`, `Grid`, `Cube`,
`Transport`, `NearInvariant`, `GridCase`, `Approximation`, `Main`, `BeckFiala`,
et `Solution.lean` exposant `Komlos.exists_sign_forall_abs_sum_apply_le` /
`Hypergraph.discrepancy_incidenceMatrix_le`. Elle annonce `36` et `36·√t`, et
**0 `sorry`** hors les `Challenge.lean` (énoncés-trous). Écart déclaré par ses
auteurs : le passage aux vecteurs réels donne `36 + η` pour tout `η > 0`, pas
`36` exact en une étape. Statut de cette mention : **RAPPORTÉ** (page du dépôt
lue, non recompilée ici) — avant tout pont, vérifier licence, pin Mathlib et
absence de `sorry` **par build**.

**Les trois réserves du 2026-09-13 restent valides** pour les énoncés **du
lake** : v2 non revue par les pairs, argument existentiel, énoncés non verbatim
(`ℚ`/`ℝ`, `Nat.sqrt`/`√`, strict/non strict). Une formalisation tierce est une
corroboration plus forte qu'un preprint ordinaire, **pas** une revue — et
aucune preuve formelle n'est engagée ici. Ne pas écrire « résolue » pour
`KomlosConjecture` tant qu'il n'est pas déchargé.

## Découpage de la noix (P1) — grignotage multi-cycles

Mandat user 2026-08-24 : « grignoter la noix de preuve la plus dure dans la
durée par petits bôuts ». Chaque boute `b1..b4` est un grain **claimable
séparément**, commité **seulement si elle build** (0 sorry intermédiaire) ;
une boute non finie reste en branche. Ordre : `b1` → `b2` → `b3` → `b4`
(les dépendances sont linéaires ; `b4` assemble).

## Voie élémentaire (Karingula–Lovett) — découpage multi-cycles

Mêmes règles que P1 : une boute = un grain **claimable séparément**, commité
**seulement si elle build** (0 `sorry` intermédiaire) ; boute non finie =
branche, jamais `main`. Issue de suivi : #17845.

| Boute | Contenu | Nature | Dépend de |
|-------|---------|--------|-----------|
| **k0** | Registre : ce document + `README.md` — papier enregistré (constante `36`), ligne P3 réauditée, statut épistémique corrigé | docs seules (aucun build Lean requis) | — |
| **k1** | `Δ` + opérateur de scission `T_v` + Claim 3.2 (monotonie) | fini (style p1a–p4) | — |
| **k2** | **Lemme 1.4** — induction simultanée sur `n` et `d` (la noix de cette voie) | fini + induction | k1 |
| **k3** | Lemme 4.1 — densité-tente, FTC sur segments, Cauchy–Schwarz `L²`, `TV ≤ ‖v‖₂/√12` | analyse | `norm_image_sub_le` (re-vérifier au pin) |
| **k4** | Lemme 1.5 — discrétisation sur la grille, cas rationnel | fini | k3 |
| **k5** | Assemblage Thm 1.2 sur `ℚ` (témoin `36`) + corollaires (`KomlosBansalJiangWeak`, Beck–Fiala régulier `72√k`) + notebooks `Search-09c`/`Search-09d` (ligne « course aux bornes » du 22/09/2026) | assemblage | k2, k4 |

**Deux routes, non exclusives** — à trancher au premier cycle d'implémentation :

- **(a) pont vers la formalisation tierce** (`gdahia/Komlos`) : chemin le plus
  court vers « `KomlosConjecture` devient un `theorem` », au prix d'une
  dépendance externe (pin Mathlib du dépôt, licence, écart `36 + η`).
- **(b) re-distillation boute par boute** : la vocation du lake (distillation
  pédagogique multi-cycles, i18n #4980), en utilisant la formalisation tierce
  comme **oracle de confiance** pour débloquer et comparer chaque boute — le
  rôle qui manquait pour la voie Guo–Fang–Lu.

Recommandation : **(b)** comme fond, **(a)** comme oracle ; `k0` est de toute
façon le premier geste et ne risque rien (docs seules).

## Note d'honnêteté (G.3)

Le palier P0 ne prouve **aucun** théorème du domaine : il pose les
définitions, trois lemmes-limites immédiats (famille vide, partie vide,
degré ≤ cardinal), et les énoncés exacts de la frontière — y compris la
cible `2k−1` et les deux conjectures ouvertes. C'est le socle sur lequel
grignoter ; la valeur de preuve commence à `b1`.
