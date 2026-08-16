import SLT.GaussianMeasure
import SLT.HansonWright
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.Exponential

/-!
# Phase 3b — Converse §11: probabilistic bricks of the lower bound

This module formalizes the probabilistic bricks of the converse of the `2 log N`
threshold (Papailiopoulos 2026 paper, §11 — see issue #10984): ML recovery
fails below `2 log N − log log N − s_N`. The three ingredients of §11 are:

1. **Minimal mass of a Gaussian interval** (`gaussian_interval_mass_lower_param`,
   generalized form with arbitrary radius `R`; `gaussian_interval_mass_lower` =
   the `R = 2` case, `gaussian_interval_mass_lower_inv_sqrt` = the paper form
   `1/√ρ₀`): the density `φ` is bounded below by `exp(−R²/2)/√(2π)` on
   `[−R, R]` (`gaussianPDFReal_lower_abs`), hence any interval contained in
   `[−R, R]` carries mass `≥ width · φ(R)`. This is the mechanism behind the
   "Gaussian intervals of width `1/√ρ₀`" of §11.
2. **Complementary union bound** (`one_sub_pow_le_exp_mul`): `(1−p)^n ≤ e^{−np}`
   (direct instance of Mathlib `one_sub_div_pow_le_exp_neg`).
3. **Hanson–Wright concentration** (`hanson_wright_noise`): tails of the
   centered quadratic form of the standard noise `w` (external lake
   `YuanheZ/lean-stat-learning-theory`, `hanson_wright_inequality`), applied to
   the standard Gaussian vector `stdGaussianPi` — the chi-square tail of `‖w‖²`
   from §11.

The assembly (`gaussian_coordinate_escape_bound`): by independence of the
coordinates (`Measure.pi_pi`), the probability that the noise escapes the `n`
coordinate intervals is exactly the product `∏ (1 − mᵢ)`, then
`≤ (1−p)^n ≤ e^{−np}` — the complete skeleton of the impossibility argument
of §11, with no `sorry`.
-/

namespace Mimo_en

open MeasureTheory ProbabilityTheory GaussianMeasure HansonWright Real
open scoped BigOperators NNReal

/-! ## Brick 1 — minimal mass of a Gaussian interval

Generalized form with an arbitrary radius `R` (`gaussianPDFReal_lower_abs`,
`gaussian_interval_mass_lower_param`), the historical `[−2, 2]` versions as
corollaries, and the paper form `1/√ρ₀`
(`gaussian_interval_mass_lower_inv_sqrt`). The `SLT/SmallBallProb` library
was evaluated for this role (issue #11148, Grain 2): its `small_ball_prob`
is a small-ball **upper** bound `P(∑Xᵢ ≤ εN) ≤ (e·ε)^N` (Markov on the
MGF), not a lower anti-concentration bound — it does not cover Brick 1,
hence the parameterized version below rather than a derivation. -/

/-- The standard Gaussian density is bounded below by `exp(−R²/2)/√(2π)` on
`[−R, R]`: the density decreases in `|x|`, so its boundary value on the
domain lower-bounds the whole interior. Generalized form (arbitrary radius)
of `gaussianPDFReal_lower_two`. -/
lemma gaussianPDFReal_lower_abs {R x : ℝ} (hx : |x| ≤ R) :
    Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi) ≤ gaussianPDFReal 0 1 x := by
  have hxR : x ^ 2 ≤ R ^ 2 := by nlinarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have hpi : ((2 * Real.pi * (1 : ℝ≥0)) : ℝ) = 2 * Real.pi := by norm_num
  have h2' : (2 * (1 : ℝ≥0) : ℝ) = 2 := by norm_num
  unfold gaussianPDFReal
  rw [hpi, h2']
  have hexp : Real.exp (-(R ^ 2) / 2) ≤ Real.exp (-(x - 0) ^ 2 / 2) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hxR]
  have hinv : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  calc Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi)
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(R ^ 2) / 2) := div_eq_inv_mul _ _
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x - 0) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hexp hinv.le

/-- The standard Gaussian density is bounded below by `exp(−2)/√(2π)` on `[−2, 2]`. -/
lemma gaussianPDFReal_lower_two (x : ℝ) (hx : |x| ≤ 2) :
    Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤ gaussianPDFReal 0 1 x := by
  have hexp : Real.exp (-(2:ℝ) ^ 2 / 2) = Real.exp (-2) := by
    congr 1
    norm_num
  have h := gaussianPDFReal_lower_abs (R := 2) hx
  rwa [hexp] at h

/-- Any interval contained in `[−R, R]` carries Gaussian mass
`≥ width · φ(R)` where `φ(R) = exp(−R²/2)/√(2π)`: the density is bounded
below by its boundary value (`gaussianPDFReal_lower_abs`), so the integral
is bounded below by `width × lower bound`. Generalized form of
`gaussian_interval_mass_lower`. -/
theorem gaussian_interval_mass_lower_param {a b R : ℝ} (hab : a ≤ b)
    (ha : |a| ≤ R) (hb : |b| ≤ R) :
    (b - a) * Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi) ≤
      (gaussianReal 0 1 (Set.Ioc a b)).toReal := by
  have hk : 0 ≤ Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi) := by positivity
  have hmeasure : gaussianReal 0 1 (Set.Ioc a b) =
      ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      withDensity_apply _ measurableSet_Ioc]
    rfl
  have hsplit : ∀ x ∈ Set.Ioc (a : ℝ) b, |x| ≤ R := by
    intro x hx
    rw [abs_le]
    constructor <;> nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2,
      (abs_le.mp hb).1, (abs_le.mp hb).2, hx.1.le, hx.2]
  have hpoint : ∀ x, (Set.Ioc a b).indicator (fun _ => ENNReal.ofReal
      (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi))) x ≤
      (Set.Ioc a b).indicator (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc a b
    · simp only [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_lower_abs (hsplit x hx))
    · rw [Set.indicator_apply, if_neg hx, Set.indicator_apply, if_neg hx]
  have hmono : (∫⁻ _x in Set.Ioc a b,
        ENNReal.ofReal (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi)) ∂volume) ≤
      ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := by
    rw [← lintegral_indicator measurableSet_Ioc
        (fun _ => ENNReal.ofReal (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi))),
      ← lintegral_indicator measurableSet_Ioc
        (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))]
    exact lintegral_mono hpoint
  have hchain : ENNReal.ofReal ((b - a) *
        (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi))) ≤
      gaussianReal 0 1 (Set.Ioc a b) := by
    rw [hmeasure]
    calc ENNReal.ofReal ((b - a) *
          (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi)))
        = ∫⁻ _x in Set.Ioc a b,
            ENNReal.ofReal (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi)) ∂volume := by
          rw [setLIntegral_const, Real.volume_Ioc,
            ← ENNReal.ofReal_mul (by nlinarith [hab, hk]), mul_comm]
      _ ≤ ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := hmono
  have hnn : 0 ≤ (b - a) * (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi)) := by
    nlinarith [hab, hk]
  have hlhs : (b - a) * Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi) =
      (ENNReal.ofReal ((b - a) *
        (Real.exp (-(R ^ 2) / 2) / Real.sqrt (2 * Real.pi)))).toReal := by
    rw [ENNReal.toReal_ofReal hnn]
    ring
  rw [hlhs]
  exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mpr
    hchain

/-- Any interval contained in `[−2, 2]` carries Gaussian mass
`≥ width · φ(2)` where `φ(2) = exp(−2)/√(2π)` (§11: intervals of width
`1/√ρ₀`). Case `R = 2` of `gaussian_interval_mass_lower_param`. -/
theorem gaussian_interval_mass_lower {a b : ℝ} (hab : a ≤ b)
    (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    (b - a) * Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤
      (gaussianReal 0 1 (Set.Ioc a b)).toReal := by
  have hexp : Real.exp (-(2:ℝ) ^ 2 / 2) = Real.exp (-2) := by
    congr 1
    norm_num
  have h := gaussian_interval_mass_lower_param (R := 2) hab ha hb
  rwa [hexp] at h

/-- **Paper form §11**: any interval of width exactly `1/√ρ₀` centered at
`c` and contained in `[−2, 2]` carries Gaussian mass
`≥ (1/√ρ₀) · φ(2)` — the "Gaussian intervals of width `1/√ρ₀`" of the
converse of Papailiopoulos 2026 (§11), direct instantiation of Brick 1 on
`ε = 1/√ρ₀`. -/
theorem gaussian_interval_mass_lower_inv_sqrt {ρ₀ c : ℝ} (hρ : 0 < ρ₀)
    (hc : |c| + 1 / √ρ₀ / 2 ≤ 2) :
    (1 / √ρ₀) * Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤
      (gaussianReal 0 1 (Set.Ioc (c - 1 / √ρ₀ / 2) (c + 1 / √ρ₀ / 2))).toReal := by
  have he : 0 < 1 / √ρ₀ := by positivity
  have hc' : |c| ≤ 2 - 1 / √ρ₀ / 2 := by nlinarith [hc]
  have hca := abs_le.mp hc'
  have ha : |c - 1 / √ρ₀ / 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hca.1, hca.2, he]
  have hb : |c + 1 / √ρ₀ / 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hca.1, hca.2, he]
  have hab : c - 1 / √ρ₀ / 2 ≤ c + 1 / √ρ₀ / 2 := by nlinarith
  have h := gaussian_interval_mass_lower hab ha hb
  rw [show (c + 1 / √ρ₀ / 2) - (c - 1 / √ρ₀ / 2) = 1 / √ρ₀ from by ring] at h
  exact h

/-! ## Brick 2 — complementary union bound -/

/-- `(1 − p)^n ≤ e^{−n·p}` for `p ≤ 1` (§11: `(1−p)^N ≤ e^{−Np}`).
Direct instance of Mathlib `one_sub_div_pow_le_exp_neg`. -/
theorem one_sub_pow_le_exp_mul {n : ℕ} {p : ℝ} (hn : 0 < n) (hp0 : 0 ≤ p) (hp : p ≤ 1) :
    (1 - p) ^ n ≤ Real.exp (-((n : ℝ) * p)) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ht : (n : ℝ) * p ≤ (n : ℝ) := by nlinarith
  have h := one_sub_div_pow_le_exp_neg (n := n) (t := (n : ℝ) * p) ht
  rwa [mul_div_cancel_left₀ _ (ne_of_gt hnpos)] at h

/-! ## Brick 3 — Hanson–Wright for the standard noise -/

/-- The coordinates of `stdGaussianPi` are sub-Gaussian with parameter `1`
(transport of the `N(0,1)` certificate via the pushforward law
`map_eval_stdGaussianPi`). -/
theorem hasSubgaussianMGF_eval_stdGaussianPi {n : ℕ} (i : Fin n) :
    HasSubgaussianMGF (fun w : Fin n → ℝ => w i) 1 (stdGaussianPi n) := by
  rw [← HasSubgaussianMGF.id_map_iff (continuous_apply i).aemeasurable,
    map_eval_stdGaussianPi]
  exact hasSubgaussianMGF_id_gaussianReal_zero_one

/-- Hanson–Wright for the standard noise vector `w ~ stdGaussianPi n`:
tail of the centered quadratic form `|X ᵀA X − E X ᵀA X|` (§11: chi-square
concentration of `‖w‖²` and of the forms `h_iᵀ w`). Case `K = 1` of the SLT
lake theorem, with sub-Gaussian certificates of the coordinates transported
from `N(0,1)`. -/
theorem hanson_wright_noise {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {C t : ℝ}
    (hC : 0 < C) (hC₁ : 4 * Real.exp 1 ≤ C) (hC₂ : 8 * Real.exp 1 ^ 3 ≤ C)
    (hC₃ : 16 * Real.exp 1 ≤ C ^ 2) (hC₄ : 64 * Real.exp 1 ^ 2 ≤ C)
    (hF : 0 < frobeniusNorm A) (hOp : 0 < operatorNorm A) (ht : 0 ≤ t) :
    (stdGaussianPi n {w | t ≤ |centeredQuadraticForm (stdGaussianPi n) A
        (fun i w => w i) w|}).toReal ≤
      2 * Real.exp (-(1 / (4 * C)) *
        min (t ^ 2 / frobeniusNorm A ^ 2) (t / operatorNorm A)) := by
  have hone : (⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ : ℝ≥0) = 1 := by simp
  have hcert : ∀ i, HasSubgaussianMGF (fun w : Fin n → ℝ => w i)
      ⟨(1 : ℝ) ^ 2, sq_nonneg 1⟩ (stdGaussianPi n) := by
    intro i
    rw [hone]
    exact hasSubgaussianMGF_eval_stdGaussianPi i
  simpa using hanson_wright_inequality (μ := stdGaussianPi n) (K := 1) (C := C)
    (t := t) one_pos hC hC₁ hC₂ hC₃ hC₄ hF hOp iIndepFun_eval_stdGaussianPi hcert ht

/-! ## Assembly — skeleton of the impossibility argument of §11 -/

/-- By independence of the noise coordinates (`Measure.pi_pi`), the
probability that `w` escapes all `n` coordinate intervals
`[c−ε/2, c+ε/2] ⊆ [−2,2]` is exactly the product `∏ᵢ (1 − mᵢ)`, then
`≤ (1−p)^n ≤ e^{−np}` with `p = ε·φ(2)`. Complete skeleton of the §11
converse: each interval carries mass `≥ p` (Brick 1), the escapes are
independent (`Measure.pi_pi`), and the complementary union bound concludes
(Brick 2). -/
theorem gaussian_coordinate_escape_bound {n : ℕ} {c ε : ℝ} (hn : 0 < n)
    (hε : 0 < ε) (hc : |c| + ε / 2 ≤ 2)
    (hp1 : ε * Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤ 1) :
    (stdGaussianPi n
      {w : Fin n → ℝ | ∀ i, w i ∉ Set.Ioc (c - ε / 2) (c + ε / 2)}).toReal ≤
      Real.exp (-((n : ℝ) * (ε * Real.exp (-2) / Real.sqrt (2 * Real.pi)))) := by
  have he : 0 < ε / 2 := by positivity
  have hc' : |c| ≤ 2 - ε / 2 := by nlinarith [hc]
  have hca := abs_le.mp hc'
  have ha : |c - ε / 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hca.1, hca.2, he]
  have hb : |c + ε / 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [hca.1, hca.2, he]
  have hab : c - ε / 2 ≤ c + ε / 2 := by nlinarith
  have hmass := gaussian_interval_mass_lower (a := c - ε / 2) (b := c + ε / 2) hab ha hb
  rw [show (c + ε / 2) - (c - ε / 2) = ε from by ring] at hmass
  have hE : {w : Fin n → ℝ | ∀ i, w i ∉ Set.Ioc (c - ε / 2) (c + ε / 2)} =
      Set.pi (Set.univ : Set (Fin n))
        (fun _ : Fin n => (Set.Ioc (c - ε / 2) (c + ε / 2))ᶜ) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_compl_iff, Set.mem_univ,
      true_implies]
  have hm_le : gaussianReal 0 1 (Set.Ioc (c - ε / 2) (c + ε / 2)) ≤ 1 := by
    have h : gaussianReal 0 1 (Set.Ioc (c - ε / 2) (c + ε / 2)) ≤
        gaussianReal 0 1 (Set.univ) :=
      measure_mono (Set.subset_univ _)
    rwa [measure_univ] at h
  have hfact : ∀ i : Fin n,
      (gaussianReal 0 1 ((Set.Ioc (c - ε / 2) (c + ε / 2))ᶜ)).toReal ≤
        1 - ε * Real.exp (-2) / Real.sqrt (2 * Real.pi) := by
    intro i
    have hcompl : gaussianReal 0 1 ((Set.Ioc (c - ε / 2) (c + ε / 2))ᶜ) =
        1 - gaussianReal 0 1 (Set.Ioc (c - ε / 2) (c + ε / 2)) := by
      have h : gaussianReal 0 1 ((Set.Ioc (c - ε / 2) (c + ε / 2))ᶜ) =
          gaussianReal 0 1 Set.univ - gaussianReal 0 1 (Set.Ioc (c - ε / 2) (c + ε / 2)) :=
        measure_compl measurableSet_Ioc (measure_ne_top _ _)
      rwa [measure_univ] at h
    rw [hcompl, ENNReal.toReal_sub_of_le hm_le ENNReal.one_ne_top]
    have hone : ((1 : ENNReal)).toReal = 1 := by simp
    rw [hone]
    linarith
  have hle : 0 ≤ ε * Real.exp (-2) / Real.sqrt (2 * Real.pi) := by positivity
  calc (stdGaussianPi n
        {w : Fin n → ℝ | ∀ i, w i ∉ Set.Ioc (c - ε / 2) (c + ε / 2)}).toReal
      = (∏ i, gaussianReal 0 1 ((Set.Ioc (c - ε / 2) (c + ε / 2))ᶜ)).toReal := by
        rw [hE]
        simp only [stdGaussianPi, Measure.pi_pi]
    _ = ∏ i, (gaussianReal 0 1 ((Set.Ioc (c - ε / 2) (c + ε / 2))ᶜ)).toReal :=
        ENNReal.toReal_prod _ _
    _ ≤ ∏ i : Fin n, (1 - ε * Real.exp (-2) / Real.sqrt (2 * Real.pi)) :=
        Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hfact i)
    _ = (1 - ε * Real.exp (-2) / Real.sqrt (2 * Real.pi)) ^ n := by simp
    _ ≤ Real.exp (-((n : ℝ) *
        (ε * Real.exp (-2) / Real.sqrt (2 * Real.pi)))) :=
        one_sub_pow_le_exp_mul hn hle hp1

end Mimo_en
