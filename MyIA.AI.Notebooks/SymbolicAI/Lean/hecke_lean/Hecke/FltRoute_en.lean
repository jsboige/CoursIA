import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

/-!
# Fermat's route as guided exercises: the last step, proved

This module teaches the **proof route of Fermat's Last Theorem** (FLT) as
mapped by `PROOF-PATH.md` of the `anthropics/fermats-last-theorem`
repository (commit `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`), by fully
proving the step that is accessible from Mathlib alone: **S₂(Γ₀(2)) = 0**.

## The six-step route — exact strength declared

| # | Step | Status in this module |
|---|---|---|
| 1 | `fermat_last_theorem` : `aⁿ + bⁿ ≠ cⁿ` for `3 ≤ n` | **stated** (the summary theorem, under admitted hypotheses) |
| 2 | `FreyPackage.no_frey_package` : the Frey curve is outside the package | **admitted** (exercise 2: the curve is built, Tate's theorem is a hypothesis) |
| 3 | `Mazur_Frey` : semi-stability + Galois representation | **admitted** (exercise 1: the normalization arithmetic, on the other hand, is proved) |
| 4 | `modularity_of_semistableModel` : modularity of semi-stable curves (Wiles) | **admitted** |
| 5 | `level_lowering_to_two` : lowering the level to `N = 2` | **admitted** (exercise 3: the index `[SL₂(ℤ) : Γ₀(2)] = 3`, a brick of the level jump, is proved) |
| 6 | `S2_Gamma0_2_eq_zero` : no cuspidal modular form of weight 2, level 2 | **PROVED** (exercise 4) |

The logic of the summary: if steps 2 to 5 (admitted) deliver, from a
Fermat counterexample, a **nonzero** cuspidal modular form of weight 2 on
`Γ₀(2)`, then step 6 — proved here — kills it. This is exactly the
articulation of the reference repository.

**Provenance** : this file is the English documentation sibling of
`Hecke/FltRoute.lean`. Exercises 3 and 4 adapt
`P2M/Sol/S_ModularForm_S2_Gamma0_2_eq_zero.lean` from the repository above
(Apache-2.0 license preserved, see `NOTICE.md`): statements and proofs are
reused, the `P2M` verification sugar (`p2m_*` macros) is removed.
Exercises 1 and 2, as well as the documentation, are CoursIA additions.
Statements and proofs are byte-identical to the French file; only
docstrings and comments differ. Target #16556. See #14771 (cartography,
slices 2-3).

## The four exercises

- **Exercise 1** (`frey_congr_mod_eight`): the Frey normalization — first
  provable link: for odd `p ≥ 5`, solutions of `a ^ p + b ^ p = c ^ p`
  with `b` even satisfy `a ≡ c [MOD 8]`.
- **Exercise 2** (`freyCurve`): the Frey curve
  `E : y² = x³ + (b^p − a^p)x² − (ab)^p x`, literally built as a
  `WeierstrassCurve ℚ`.
- **Exercise 3** (`gamma0_two_index_eq_three`): the index
  `[SL₂(ℤ) : Γ₀(2)] = 3`, via an explicit bijection between left cosets
  and the nonzero columns of `(ZMod 2)²`.
- **Exercise 4** (`s2_gamma0_2_eq_zero`): the breakthrough — the **norm**
  trick lifts a weight-2 form on `Γ₀(2)` to a weight `2 × 3 = 6` form on
  `SL₂(ℤ)`, and Mathlib knows that cusp forms of weight strictly below 12
  vanish at level 1.
-/

set_option autoImplicit false

namespace FltRoute_en

open UpperHalfPlane SlashInvariantForm Subgroup Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Topology Filter Manifold CongruenceSubgroup

noncomputable section

/-! ## Exercise 1: the Frey normalization (arithmetic proved)

Frey's theory starts from an assumed counterexample `a ^ p + b ^ p = c ^ p`
(`p ≥ 5` prime) and derives strong arithmetic constraints from it. The
first link, fully provable here: when `b` is even (the standard
normalization choice), `a` and `c` are odd and **congruent modulo 8**.
It is this congruence that, in the full proof, forbids the Frey curve from
being in the "package" excluded by step 2. -/

section FreyArithmetic

/-- **Brick: the square of an odd number is `1` modulo `8`.** The
decomposition `(2k+1)² = 4·k(k+1) + 1` and the parity of `k(k+1)` (two
consecutive integers) do all the work. -/
theorem sq_odd_eq_one_mod_eight {k : ℕ} : (2 * k + 1) ^ 2 ≡ 1 [MOD 8] := by
  have hktwo : 2 ∣ k * (k + 1) := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (2 * m + 1), by ring⟩
    · exact ⟨(2 * m + 1) * (m + 1), by ring⟩
  obtain ⟨t, ht⟩ := hktwo
  have hexp : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [Nat.ModEq, hexp, ht]
  omega

/-- **Exercise 1 (guided).** For odd `p`, every odd power of an odd
number is congruent to the number itself modulo 8:
`x ^ p ≡ x [MOD 8]`. The proof writes `p = 2m + 1` and factors
`x ^ p = x · (x²) ^ m`, then replaces `x²` by `1` modulo 8. -/
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

/-- **Exercise 1 (summary).** Let an assumed Fermat counterexample
`a ^ p + b ^ p = c ^ p` with `b` even, `a` and `c` odd, `p ≥ 5` **odd**.
Then `a ≡ c [MOD 8]`. This is the key congruence of the Frey
normalization: since `p ≥ 3`, `b ^ p` is divisible by `8`, and the
previous theorem identifies `a ^ p` with `a` and `c ^ p` with `c`
modulo 8. -/
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

/-! ## Exercise 2: the Frey curve, literally

The Frey curve attached to an assumed counterexample
`a ^ p + b ^ p = c ^ p` is
`E : y² = x(x − a^p)(x + b^p)`, i.e. after expansion
`y² = x³ + (b^p − a^p)x² − (ab)^p x`.
Tate's theorem ("the Frey curve is not modular") is not in Mathlib: it is
**admitted** in the route — that is step 2. -/
section FreyCurve

/-- The Frey curve, as a `WeierstrassCurve` over `ℚ`: coefficients
`a₁ = 1`, `a₂ = b ^ p − a ^ p`, `a₃ = 0`, `a₄ = −(ab) ^ p`, `a₆ = 0`,
in other words `y² = x³ + (b^p − a^p)x² − (ab)^p x`. -/
def freyCurve (a b p : ℕ) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (b : ℚ) ^ p - (a : ℚ) ^ p
  a₃ := 0
  a₄ := -((a : ℚ) * (b : ℚ)) ^ p
  a₆ := 0

end FreyCurve

/-! ## Exercise 3: the index of Γ₀(2) in SL₂(ℤ) is 3

Brick of the level jump (step 5): to lower the level of a form, one needs
the indices of the congruence groups. The proof builds an explicit
bijection between the cosets `SL₂(ℤ) ⧸ Γ₀(2)` and the nonzero columns of
`(ZMod 2)²` — there are exactly three. -/

section IndexThree

/-- The first column of a matrix of `SL(2, ℤ)`, reduced modulo 2. -/
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

/-- The bijection: a left coset is determined by its first column
modulo 2 (right multiplication by `Γ₀(2)` does not change the column, and
two matrices with the same column differ by an element of `Γ₀(2)`). -/
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

/-- **Exercise 3 (summary).** The index of `Γ₀(2)` in `SL(2, ℤ)` is `3`. -/
theorem gamma0_two_index_eq_three : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  rw [Subgroup.index,
    Nat.card_congr (Equiv.ofBijective _ ⟨cosetToProj_injective, cosetToProj_surjective⟩),
    Nat.card_eq_fintype_card]
  decide

end IndexThree

/-! ## Exercise 4: S₂(Γ₀(2)) = 0 — the breakthrough

The trick: the **norm** of a modular form `f` for a group `𝒢`, lifted to
a super-group `ℋ` of finite index, is a modular form for `ℋ` of weight
multiplied by the index (`ModularForm.norm`, Mathlib). For `f` cuspidal of
weight 2 on `Γ₀(2)`, the norm lifted to `SL₂(ℤ)` is cuspidal of weight
`2 × 3 = 6` — and Mathlib knows (`DimensionFormulas`) that at level 1,
cusp forms of weight `< 12` form a module of zero rank. So the norm is
zero, hence `f` is zero. -/

section CuspFormNorm

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The cuspidal version of the norm: the norm of a cusp form is a cusp
form (vanishing at the cusps passes to the product of translates). -/
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

/-- There is no cusp form of weight 6 at level 1: Mathlib
(`CuspForm.rank_eq_zero_of_weight_lt_twelve`) knows it, and a module of
zero rank over a field is zero. -/
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

/-- **Exercise 4 (summary).** Every cuspidal modular form of weight 2 on
`Γ₀(2)` is zero: the norm lifts it to weight `2 × 3 = 6` on `SL₂(ℤ)`,
where the space is zero. -/
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

/-! ## The summary theorem: the route kills the counterexample

Steps 2 to 5 are **admitted** (Tate, Mazur, Wiles, Ribet — see the header
table). They deliver, from a Fermat counterexample, a **nonzero** cuspidal
modular form of weight 2 on `Γ₀(2)`: the level lowered to 2. Exercise 4 —
proved — shows this form is zero. Contradiction: Fermat's Last Theorem
holds via the route. -/

/-- **The last step, alone.** There exists no nonzero cuspidal modular
form of weight 2 on `Γ₀(2)`. -/
theorem no_weight2_level2_cusp_form :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0 := by
  rintro ⟨f, hf⟩
  exact hf (s2_gamma0_2_eq_zero f)

set_option linter.unusedVariables false in
/-- **Route summary.** If the admitted steps (2-5) turn an assumed Fermat
counterexample `a ^ p + b ^ p = c ^ p` (`p ≥ 5` prime, nonzero integers)
into a nonzero cuspidal modular form of weight 2 on `Γ₀(2)` (this is the
combined statement of Mazur-Frey + modularity + level lowering), then
absurdity is reached: the counterexample does not exist. -/
theorem flt_of_full_route {p a b c : ℕ} (hp : 5 ≤ p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hMazurFrey_modular_level2 :
      a ^ p + b ^ p = c ^ p → ∃ f : CuspForm (CongruenceSubgroup.Gamma0 2) 2, f ≠ 0) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro hcon
  obtain ⟨f, hf⟩ := hMazurFrey_modular_level2 hcon
  exact no_weight2_level2_cusp_form ⟨f, hf⟩

end

end FltRoute_en
