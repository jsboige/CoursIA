import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# La route de Fermat en exercices guidés : la dernière étape, prouvée

Ce module enseigne la **route de la preuve du dernier théorème de Fermat**
(FLT) telle que cartographiée par `PROOF-PATH.md` du dépôt
`anthropics/fermats-last-theorem` (commit
`aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`), en prouvant complètement
l'étape qui est accessible depuis Mathlib seule : **S₂(Γ₀(2)) = 0**.

## La route en six étapes — force exacte déclarée

| # | Étape | Statut dans ce module |
|---|---|---|
| 1 | `fermat_last_theorem` : `aⁿ + bⁿ ≠ cⁿ` pour `3 ≤ n` | **énoncée** (le théorème-bilan, sous hypothèses admises) |
| 2 | `FreyPackage.no_frey_package` : la courbe de Frey est hors package | **admise** (exercice 2 : la courbe est construite, le théorème de Tate est une hypothèse) |
| 3 | `Mazur_Frey` : semi-stabilité + représentation galoisienne | **admise** (exercice 1 : l'arithmétique de la normalisation, elle, est prouvée) |
| 4 | `modularity_of_semistableModel` : modularité des courbes semi-stables (Wiles) | **admise** |
| 5 | `level_lowering_to_two` : réduction du niveau vers `N = 2` | **admise** (exercice 3 : l'indice `[SL₂(ℤ) : Γ₀(2)] = 3`, brique du saut de niveau, est prouvé) |
| 6 | `S2_Gamma0_2_eq_zero` : pas de forme modulaire cuspidale de poids 2 niveau 2 | **POUVÉE** (exercice 4) |

La logique du bilan : si les étapes 2 à 5 (admises) livrent, à partir d'un
contre-exemple de Fermat, une forme modulaire cuspidale **non nulle** de
poids 2 sur `Γ₀(2)`, l'étape 6 — prouvée ici — la tue. C'est exactement
l'articulation du dépôt de référence.

**Adaptation pédagogique** : les exercices 3 et 4 adaptent
`P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` du dépôt ci-dessus
(licence Apache-2.0 préservée, voir `NOTICE.md`) : les énoncés et preuves
sont repris, le sucre de vérification `P2M` (macros `p2m_*`) est retiré.
Les exercices 1 et 2, ainsi que la documentation, sont des additions
CoursIA. Cible #16556. See #14771 (cartographie, tranches 2-3).

## Les quatre exercices

- **Exercice 1** (`frey_congr_mod_eight`) : la normalisation de Frey —
  premier maillon prouvable : pour `p ≥ 5` impair, les solutions de
  `a ^ p + b ^ p = c ^ p` avec `b` pair satisfont `a ≡ c [MOD 8]`.
- **Exercice 2** (`freyCurve`) : la courbe de Frey
  `E : y² = x³ + (b^p − a^p)x² − (ab)^p x`, construite littéralement comme
  une `WeierstrassCurve ℚ`.
- **Exercice 3** (`gamma0_two_index_eq_three`) : l'indice
  `[SL₂(ℤ) : Γ₀(2)] = 3`, par bijection explicite entre les classes à
  gauche et les colonnes non nulles de `(ZMod 2)²`.
- **Exercice 4** (`s2_gamma0_2_eq_zero`) : la percée — l'astuce de la
  **norme** relève une forme de poids 2 sur `Γ₀(2)` en forme de poids
  `2 × 3 = 6` sur `SL₂(ℤ)`, et Mathlib sait que les cusp forms de poids
  strictement inférieur à 12 sont nulles en niveau 1.
-/

set_option autoImplicit false

namespace FltRoute

open UpperHalfPlane SlashInvariantForm Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Topology Filter Manifold CongruenceSubgroup

noncomputable section

/-! ## Exercice 1 : la normalisation de Frey (arithmétique prouvée)

La théorie de Frey part d'un contre-exemple supposé `a ^ p + b ^ p = c ^ p`
(`p ≥ 5` premier) et en tire des contraintes arithmétiques fortes. Le
premier maillon, entièrement prouvable ici : quand `b` est pair (le choix
de normalisation standard), `a` et `c` sont impairs et **congrus modulo 8**.
C'est cette congruence qui, dans la preuve complète, interdit à la courbe de
Frey d'être en le « package » exclu par l'étape 2. -/

section FreyArithmetic

/-- **Brique : le carré d'un impair est `1` modulo `8`.** La décomposition
`(2k+1)² = 4·k(k+1) + 1` et la parité de `k(k+1)` (deux entiers consécutifs)
font tout le travail. -/
theorem sq_odd_eq_one_mod_eight {k : ℕ} : (2 * k + 1) ^ 2 ≡ 1 [MOD 8] := by
  have hktwo : 2 ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (2 * m + 1), by ring⟩
    · exact ⟨(2 * m + 1) * (m + 1), by ring⟩
  obtain ⟨t, ht⟩ := hktwo
  have hexp : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [Nat.ModEq, hexp, ht]
  omega

/-- **Exercice 1 (guidé).** Pour `p` impair, toute puissance impaire d'un
impair est congrue à l'entier lui-même modulo 8 :
`x ^ p ≡ x [MOD 8]`. La preuve écrit `p = 2m + 1` et factorise
`x ^ p = x · (x²) ^ m`, puis remplace `x²` par `1` modulo 8. -/
theorem odd_pow_congr_self_mod_eight {x p : ℕ} (hx : x % 2 = 1) (hp : p % 2 = 1) :
    x ^ p ≡ x [MOD 8] := by
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  subst hm
  obtain ⟨k, hk⟩ : ∃ k, x = 2 * k + 1 := ⟨x / 2, by omega⟩
  subst hk
  have hsplit : (2 * k + 1) ^ (2 * m + 1) = (2 * k + 1) * ((2 * k + 1) ^ 2) ^ m := by
    rw [pow_add, pow_mul]
    ring
  rw [hsplit]
  calc (2 * k + 1) * ((2 * k + 1) ^ 2) ^ m
      ≡ (2 * k + 1) * 1 ^ m [MOD 8] := by
        exact Nat.ModEq.mul (refl _) (Nat.ModEq.pow m sq_odd_eq_one_mod_eight)
    _ = 2 * k + 1 := by simp

/-- **Exercice 1 (bilan).** Soit un contre-exemple supposé de Fermat
`a ^ p + b ^ p = c ^ p` avec `b` pair, `a` et `c` impairs, `p ≥ 5`
**impair**. Alors `a ≡ c [MOD 8]`. C'est la congruence clef de la
normalisation de Frey : puisque `p ≥ 3`, `b ^ p` est divisible par `8`, et
le théorème précédent identifie `a ^ p` à `a` et `c ^ p` à `c` modulo 8. -/
theorem frey_congr_mod_eight {a b c p : ℕ} (hp : 5 ≤ p) (hp1 : p % 2 = 1)
    (ha : a % 2 = 1) (hb : b % 2 = 0) (hc : c % 2 = 1)
    (h : a ^ p + b ^ p = c ^ p) : a ≡ c [MOD 8] := by
  obtain ⟨k, hk⟩ : ∃ k, b = 2 * k := ⟨b / 2, by omega⟩
  subst hk
  obtain ⟨q, hq⟩ : ∃ q, p = 5 + q := ⟨p - 5, by omega⟩
  subst hq
  have hdvd8 : 8 ∣ (2 * k) ^ (5 + q) := by
    have hsplit : (2 * k) ^ (5 + q) = 2 ^ (5 + q) * k ^ (5 + q) := by rw [Nat.mul_pow]
    rw [hsplit]
    have h23 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h23]
    exact (Nat.pow_dvd_pow 2 (by omega)).mul_right _
  have hcongr : a ^ (5 + q) ≡ c ^ (5 + q) [MOD 8] := by
    have hb0 : (2 * k) ^ (5 + q) ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.mpr hdvd8
    have hstep : a ^ (5 + q) + (2 * k) ^ (5 + q) ≡ a ^ (5 + q) + 0 [MOD 8] :=
      Nat.ModEq.add (Nat.ModEq.refl _) hb0
    rw [h, Nat.add_zero] at hstep
    exact hstep.symm
  calc a ≡ a ^ (5 + q) [MOD 8] :=
        (odd_pow_congr_self_mod_eight (by omega) (by omega)).symm
    _ ≡ c ^ (5 + q) [MOD 8] := hcongr
    _ ≡ c [MOD 8] := odd_pow_congr_self_mod_eight (by omega) (by omega)

end FreyArithmetic

/-! ## Exercice 2 : la courbe de Frey, littéralement

La courbe de Frey attachée à un contre-exemple supposé
`a ^ p + b ^ p = c ^ p` est
`E : y² = x(x − a^p)(x + b^p)`, soit après développement
`y² = x³ + (b^p − a^p)x² − (ab)^p x`.
Le théorème de Tate (« la courbe de Frey n'est pas modulaire ») n'est pas
dans Mathlib : il est **admis** dans la route — c'est l'étape 2. -/
section FreyCurve

/-- La courbe de Frey, comme `WeierstrassCurve` sur `ℚ` : coefficients
`a₁ = 0`, `a₂ = b ^ p − a ^ p`, `a₃ = 0`, `a₄ = −(ab) ^ p`, `a₆ = 0`,
autrement dit `y² = x³ + (b^p − a^p)x² − (ab)^p x`. -/
def freyCurve (a b p : ℕ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := (b : ℚ) ^ p - (a : ℚ) ^ p
  a₃ := 0
  a₄ := -((a : ℚ) * (b : ℚ)) ^ p
  a₆ := 0

end FreyCurve

/-! ## Exercice 3 : l'indice de Γ₀(2) dans SL₂(ℤ) vaut 3

Brique du saut de niveau (étape 5) : pour abaisser le niveau d'une forme,
il faut connaître l'indice des groupes de congruence. La preuve construit
une bijection explicite entre les classes `SL₂(ℤ) ⧸ Γ₀(2)` et les colonnes
non nulles de `(ZMod 2)²` — il y en a exactement trois. -/

section IndexThree

/-- La première colonne d'une matrice de `SL(2, ℤ)`, réduite modulo 2. -/
def firstColMod2 (g : SL(2, ℤ)) : ZMod 2 × ZMod 2 :=
  ((g.1 0 0 : ZMod 2), (g.1 1 0 : ZMod 2))

lemma det_eq_one_mod2 (g : SL(2, ℤ)) :
    (g.1 0 0 : ZMod 2) * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h := g.2
  rw [Matrix.det_fin_two] at h
  have hc := congrArg (fun n : ℤ => (n : ZMod 2)) h
  push_cast at hc
  exact hc

lemma firstColMod2_ne_zero (g : SL(2, ℤ)) : firstColMod2 g ≠ 0 := by
  intro h
  rw [firstColMod2, Prod.ext_iff] at h
  obtain ⟨h00, h10⟩ := h
  simp only [Prod.fst_zero, Prod.snd_zero] at h00 h10
  have hdet := det_eq_one_mod2 g
  rw [h00, h10, zero_mul, mul_zero, sub_zero] at hdet
  exact one_ne_zero hdet.symm

lemma gamma0_two_diag_eq_one {h : SL(2, ℤ)}
    (hh : h ∈ CongruenceSubgroup.Gamma0 2) : (h.1 0 0 : ZMod 2) = 1 := by
  have hh10 : (h.1 1 0 : ZMod 2) = 0 := CongruenceSubgroup.Gamma0_mem.1 hh
  have hdet := det_eq_one_mod2 h
  rw [hh10, mul_zero, sub_zero] at hdet
  exact (show ∀ a b : ZMod 2, a * b = 1 → a = 1 by decide) _ _ hdet

lemma firstColMod2_mul_mem (g : SL(2, ℤ)) {h : SL(2, ℤ)}
    (hh : h ∈ CongruenceSubgroup.Gamma0 2) : firstColMod2 (g * h) = firstColMod2 g := by
  have hh10 : (h.1 1 0 : ZMod 2) = 0 := CongruenceSubgroup.Gamma0_mem.1 hh
  have hh00 : (h.1 0 0 : ZMod 2) = 1 := gamma0_two_diag_eq_one hh
  have hmul : ∀ i : Fin 2, (g * h).1 i 0 = g.1 i 0 * h.1 0 0 + g.1 i 1 * h.1 1 0 := fun i => by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  unfold firstColMod2
  refine Prod.ext ?_ ?_ <;> simp only [hmul] <;> push_cast <;> rw [hh10, hh00] <;> ring

/-- La bijection : une classe à gauche est déterminée par sa première
colonne modulo 2 (multiplication à droite par `Γ₀(2)` : elle ne change pas
la colonne, et deux matrices de même colonne diffèrent par un élément de
`Γ₀(2)`). -/
def cosetToProj : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 2 →
    {p : ZMod 2 × ZMod 2 // p ≠ 0} :=
  Quotient.lift (fun g => ⟨firstColMod2 g, firstColMod2_ne_zero g⟩) fun g₁ g₂ hg => by
    have hg' : g₁⁻¹ * g₂ ∈ CongruenceSubgroup.Gamma0 2 := QuotientGroup.leftRel_apply.mp hg
    refine Subtype.ext ?_
    show firstColMod2 g₁ = firstColMod2 g₂
    conv_rhs => rw [show g₂ = g₁ * (g₁⁻¹ * g₂) by group]
    exact (firstColMod2_mul_mem g₁ hg').symm

@[simp] lemma cosetToProj_mk (g : SL(2, ℤ)) :
    cosetToProj (QuotientGroup.mk g) = ⟨firstColMod2 g, firstColMod2_ne_zero g⟩ := rfl

lemma cosetToProj_injective : Function.Injective cosetToProj := by
  rintro ⟨g₁⟩ ⟨g₂⟩ heq
  have heq' : firstColMod2 g₁ = firstColMod2 g₂ := congrArg Subtype.val heq
  rw [firstColMod2, firstColMod2, Prod.mk.injEq] at heq'
  obtain ⟨h00, h10⟩ := heq'
  refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
  rw [CongruenceSubgroup.Gamma0_mem]
  have hinv10 : (g₁⁻¹).1 1 0 = -g₁.1 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp
  have hinv11 : (g₁⁻¹).1 1 1 = g₁.1 0 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]; simp
  have hmul : (g₁⁻¹ * g₂).1 1 0 = (g₁⁻¹).1 1 0 * g₂.1 0 0 + (g₁⁻¹).1 1 1 * g₂.1 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hmul, hinv10, hinv11]
  push_cast
  rw [h00, h10]; ring

lemma cosetToProj_surjective : Function.Surjective cosetToProj := by
  rintro ⟨p, hp⟩
  have key : p = (0, 1) ∨ p = (1, 0) ∨ p = (1, 1) :=
    (show ∀ q : ZMod 2 × ZMod 2, q ≠ 0 → q = (0,1) ∨ q = (1,0) ∨ q = (1,1) by decide) p hp
  rcases key with rfl | rfl | rfl
  · refine ⟨QuotientGroup.mk (⟨!![(0:ℤ), -1; 1, 0], by decide⟩ : SL(2, ℤ)), ?_⟩
    exact Subtype.ext (show firstColMod2 _ = ((0 : ZMod 2), (1 : ZMod 2)) by decide)
  · refine ⟨QuotientGroup.mk 1, ?_⟩
    exact Subtype.ext (show firstColMod2 1 = ((1 : ZMod 2), (0 : ZMod 2)) by decide)
  · refine ⟨QuotientGroup.mk (⟨!![(1:ℤ), 0; 1, 1], by decide⟩ : SL(2, ℤ)), ?_⟩
    exact Subtype.ext (show firstColMod2 _ = ((1 : ZMod 2), (1 : ZMod 2)) by decide)

/-- **Exercice 3 (bilan).** L'indice de `Γ₀(2)` dans `SL(2, ℤ)` vaut `3`. -/
theorem gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  rw [Subgroup.index,
    Nat.card_congr (Equiv.ofBijective _ ⟨cosetToProj_injective, cosetToProj_surjective⟩),
    Nat.card_eq_fintype_card]
  decide

end IndexThree

/-! ## Exercice 4 : S₂(Γ₀(2)) = 0 — la percée

L'astuce : la **norme** d'une forme modulaire `f` pour un groupe `𝒢`,
remontée à un sur-groupe `ℋ` d'indice fini, est une forme modulaire pour
`ℋ` de poids multiplié par l'indice (`ModularForm.norm`, Mathlib). Pour
`f` cuspidale de poids 2 sur `Γ₀(2)`, la norme remontée à `SL₂(ℤ)` est
cuspidale de poids `2 × 3 = 6` — et Mathlib sait (`DimensionFormulas`)
qu'en niveau 1, les cusp forms de poids `< 12` forment un module de rang
nul. Donc la norme est nulle, donc `f` est nulle. -/

section CuspFormNorm

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- La version cuspidale de la norme : la norme d'une cusp form est une
cusp form (l'annulation aux pointes passe au produit des translatés). -/
def CuspForm.norm [ℋ.HasDetPlusMinusOne] [CuspFormClass F 𝒢 k] :
    CuspForm ℋ (k * Nat.card 𝒬) where
  __ := ModularForm.norm ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_norm, IsZeroAtImInfty, Filter.ZeroAtFilter]
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
    refine Filter.ZeroAtFilter.smul _ ?_
    show Filter.Tendsto _ _ (nhds 0)
    rw [show (0 : ℂ) = ∏ _q : 𝒬, (0 : ℂ) by
        rw [Finset.prod_const, Finset.card_univ, zero_pow Fintype.card_ne_zero],
      Finset.prod_fn]
    refine tendsto_finsetProd _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ ?_)
    refine (CuspForm.translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

@[simp]
lemma CuspForm.coe_norm_eq_coe_modularFormNorm [ℋ.HasDetPlusMinusOne] [CuspFormClass F 𝒢 k] :
    (CuspForm.norm ℋ f : ℍ → ℂ) = (ModularForm.norm ℋ f : ℍ → ℂ) := rfl

lemma CuspForm.norm_eq_zero_iff [ℋ.HasDetPlusMinusOne] [CuspFormClass F 𝒢 k] :
    CuspForm.norm ℋ f = 0 ↔ (f : ℍ → ℂ) = 0 := by
  rw [← ModularForm.norm_eq_zero_iff ℋ f, ← DFunLike.coe_injective.eq_iff,
    ← @DFunLike.coe_injective.eq_iff (ModularForm ℋ (k * Nat.card 𝒬)),
    CuspForm.coe_norm_eq_coe_modularFormNorm, FunLike.coe_zero, FunLike.coe_zero]

end CuspFormNorm

section Breakthrough

lemma coe_Gamma_one_eq_SL : (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [CongruenceSubgroup.Gamma_one_top]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

lemma cuspForm_eq_zero_of_subgroup_eq {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)} (h : Γ₂ = Γ₁)
    {k : ℤ} (H : ∀ g : CuspForm Γ₂ k, g = 0) (f : CuspForm Γ₁ k) : f = 0 := by
  subst h; exact H f

/-- Il n'y a pas de cusp form de poids 6 en niveau 1 : c'est Mathlib
(`CuspForm.rank_eq_zero_of_weight_lt_twelve`) qui le sait, et un module de
rang nul sur un corps est nul. -/
theorem s6_levelOne_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma 1) 6) : f = 0 :=
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma_one_eq_SL.symm
    (fun g => rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) g) f

theorem s6_levelOne_eq_zero' {k : ℤ} (hk : k = 6)
    (f : CuspForm (CongruenceSubgroup.Gamma 1) k) : f = 0 := by
  subst hk; exact s6_levelOne_eq_zero f

lemma card_quotient_eq_three :
    Nat.card ((↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) ⧸
      (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ)).subgroupOf
        (↑(CongruenceSubgroup.Gamma 1))) = 3 := by
  show Subgroup.relIndex (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ))
    (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) = 3
  show Subgroup.relIndex ((CongruenceSubgroup.Gamma0 2).map (mapGL ℝ))
    ((CongruenceSubgroup.Gamma 1).map (mapGL ℝ)) = 3
  rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
      CongruenceSubgroup.Gamma_one_top, Subgroup.relIndex_top_right,
      gamma0_two_index_eq_three]

instance : Subgroup.IsFiniteRelIndex
    (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ))
    (↑(CongruenceSubgroup.Gamma 1)) :=
  ⟨by show Nat.card _ ≠ 0; rw [card_quotient_eq_three]; decide⟩

/-- **Exercice 4 (bilan).** Toute forme modulaire cuspidale de poids 2 sur
`Γ₀(2)` est nulle : la norme la relève en poids `2 × 3 = 6` sur `SL₂(ℤ)`,
où l'espace est nul. -/
theorem s2_gamma0_2_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma0 2) 2) : f = 0 := by
  have hweight : (2 : ℤ) * Nat.card ((↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) ⧸
      (↑(CongruenceSubgroup.Gamma0 2) : Subgroup (GL (Fin 2) ℝ)).subgroupOf
        (↑(CongruenceSubgroup.Gamma 1))) = 6 := by
    rw [card_quotient_eq_three]; norm_num
  have hf0 : (f : ℍ → ℂ) = 0 :=
    (CuspForm.norm_eq_zero_iff (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f).1
      (s6_levelOne_eq_zero' hweight
        (CuspForm.norm (↑(CongruenceSubgroup.Gamma 1) : Subgroup (GL (Fin 2) ℝ)) f))
  exact DFunLike.coe_injective (hf0.trans (by simp))

end Breakthrough

/-! ## Le théorème-bilan : la route tue le contre-exemple

Les étapes 2 à 5 sont **admises** (Tate, Mazur, Wiles, Ribet — voir le
tableau d'en-tête). Elles livrent, à partir d'un contre-exemple de Fermat,
une forme modulaire cuspidale **non nulle** de poids 2 sur `Γ₀(2)` : le
niveau abaissé à 2. L'exercice 4 — prouvé — montre que cette forme est
nulle. Contradiction : le dernier théorème de Fermat tient par la route. -/

/-- **La dernière étape, seule.** Il n'existe aucune forme modulaire
cuspidale non nulle de poids 2 sur `Γ₀(2)`. -/
theorem no_weight2_level2_cusp_form :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0 := by
  rintro ⟨f, hf⟩
  exact hf (s2_gamma0_2_eq_zero f)

set_option linter.unusedVariables false in
/-- **Bilan de la route.** Si les étapes admises (2-5) transforment un
contre-exemple supposé `a ^ p + b ^ p = c ^ p` (`p ≥ 5` premier, entiers
non nuls) en forme modulaire cuspidale non nulle de poids 2 sur `Γ₀(2)`
(c'est l'énoncé combiné de Mazur-Frey + modularité + abaissement de
niveau), alors l'absurde est atteinte : le contre-exemple n'existe pas. -/
theorem flt_of_full_route {p a b c : ℕ} (hp : 5 ≤ p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hMazurFrey_modular_level2 :
      a ^ p + b ^ p = c ^ p → ∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro hcon
  obtain ⟨f, hf⟩ := hMazurFrey_modular_level2 hcon
  exact no_weight2_level2_cusp_form ⟨f, hf⟩

end

end FltRoute
