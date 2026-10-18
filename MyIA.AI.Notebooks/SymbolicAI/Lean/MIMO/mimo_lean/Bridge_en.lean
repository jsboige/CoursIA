import Mathlib
import Objective_en
import Converse_en

/-!
# Phase 4 — Bridge: cost identity + a converse fragment wired to the ML objective

This module ties the ML objective (`mimoObj`, Phase 2) to the probabilistic
bricks of the converse (Phase 3b) — the "grains to nibble" work of issue
#11148 (sequel of #10984). The current converse bounds the probability of an
abstract escape event; here, for the first time, a statement of the lake
relates the objective directly to Gaussian noise.

Architecture of the file:

## Grain 1a — cost-difference identity (pure algebra)

1. `cost_diff` — the **generic** form: in any real Hilbert space,
   `‖w + √s•z + √s•v‖² − ‖w + √s•z‖² = s·‖v‖² + 2√s·⟪w,v⟫ + 2s·⟪z,v⟫`.
   This is `norm_add_sq_two` (Phase 2) rearranged: moving from `z` to `z + v`
   costs a quadratic term in `v` and two linear couplings — one to the noise
   `w`, one to the current position `z`;
2. `mimoObj_sub_mimoObj` — **Bridge 1a**: instantiated on the MIMO channel,
   `mimoObj A w s u' − mimoObj A w s u = s·‖A v‖² + 2√s·⟪A v,w⟫ + 2s·⟪A v,A u⟫`
   with `v = u' − u` — the cost-difference identity for **any two
   configurations** `u, u'`;
3. `mimoObj_residual_from_zero` — specialization **start point = truth**
   (`u = 0`, the residual is `w`): `Δ = s·‖A v‖² + 2√s·⟪A v,w⟫` — the term
   coupled to the current position vanishes;
4. `mimo_flip_cost_via_bridge` — **coherence check**: with `v = flipAt i`,
   the Bridge reproduces exactly Lemma 11.1
   (`Δ = 4·(s‖hᵢ‖² + √s·⟪hᵢ,w⟫)`, `hᵢ = A eᵢ`) — Lemma 11.1 becomes a
   corollary of the Bridge, which generalizes it.

## Grain 1b — a concrete converse fragment (wired to the ML)

5. `stdGaussianPi_map_toLp` — **convention bridge**: the SLT-lake product
   Gaussian (`stdGaussianPi`, on `Fin n → ℝ`) pushed by `toLp 2` is Mathlib's
   standard Gaussian on the Euclidean space (`map_pi_eq_stdGaussian`);
6. `map_inner_stdGaussian` — **transport**: for `w` standard Gaussian on the
   Euclidean space, the linear functional `⟪h, w⟫` has law `gaussianReal 0
   ‖h‖²`. This is the technically open piece flagged in #11148, closed here
   through the `IsGaussian` API of Mathlib (every continuous linear form of a
   Gaussian is Gaussian with variance `‖L‖²`);
7. `flip_bat_prob_lower` — **first statement of the type "P(the flip wins) ≥ c"**:
   if `√s·‖hᵢ‖ ≤ 2` (and `s > 0`, `hᵢ ≠ 0` — see docstring), then
   `P(w : the flip i beats x*) ≥ (2 − √s·‖hᵢ‖)·φ(2)` where
   `φ(2) = exp(−2)/√(2π)` — via the transport (`⟪hᵢ,w⟫ ~ N(0,‖hᵢ‖²)`, the
   "beats" event is `⟪hᵢ,w⟫ < −√s·‖hᵢ‖²`) and **Brick 1**
   (`gaussian_interval_mass_lower`, Phase 3b): the interval
   `[−2, −√s·‖hᵢ‖] ⊆ [−2,2]` of width `2 − √s·‖hᵢ‖` carries mass
   `≥ width · φ(2)`.
-/

namespace Mimo_en

open MeasureTheory ProbabilityTheory GaussianMeasure HansonWright Real
open InnerProductSpace
open scoped BigOperators NNReal

section Geometrie

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cost-difference identity (generic form).** For a noise `w`, a current
position `z`, a deviation `v` and an SNR `s ≥ 0`,

    ‖w + √s•z + √s•v‖² − ‖w + √s•z‖² = s·‖v‖² + 2√s·⟪w, v⟫_ℝ + 2s·⟪z, v⟫_ℝ.

Derived from `norm_add_sq_two` (Phase 2): the move `z ↦ z + v` costs a
quadratic term in `v` plus two linear couplings — `2√s·⟪w,v⟫` through the
noise, `2s·⟪z,v⟫` through the current position (the latter vanishes at the
zero residual, cf `mimoObj_residual_from_zero`). -/
theorem cost_diff (w z v : E) {s : ℝ} (hs : 0 ≤ s) :
    ‖w + √s • z + √s • v‖ ^ 2 - ‖w + √s • z‖ ^ 2
      = s * ‖v‖ ^ 2 + 2 * √s * ⟪w, v⟫_ℝ + 2 * s * ⟪z, v⟫_ℝ := by
  have key := norm_add_sq_two (w + √s • z) (√s • v)
  rw [real_inner_smul_right, inner_add_left, real_inner_smul_left,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s),
    mul_pow, Real.sq_sqrt hs] at key
  have hss : √s * √s = s := by rw [← sq]; exact Real.sq_sqrt hs
  rw [key]
  linear_combination (norm := ring_nf) (2 * ⟪z, v⟫_ℝ) * hss

end Geometrie

section Pont

variable {N M : ℕ}

/-- **Bridge 1a — MIMO cost-difference identity.** For all configurations
`u, u'` and `v = u' − u`:

    mimoObj A w s u' − mimoObj A w s u
      = s·‖A v‖² + 2√s·⟪A v, w⟫_ℝ + 2s·⟪A v, A u⟫_ℝ.

The Bridge generalizes Lemma 11.1 (`mimo_flip_cost`, Phase 2), which is only
the special case `u = 0`, `v = flipAt i` (cf `mimo_flip_cost_via_bridge`). -/
theorem mimoObj_sub_mimoObj (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (u u' : Fin N → ℝ) :
    mimoObj A w s u' - mimoObj A w s u
      = s * ‖A (u' - u)‖ ^ 2 + 2 * √s * ⟪A (u' - u), w⟫_ℝ
        + 2 * s * ⟪A (u' - u), A u⟫_ℝ := by
  have hA : A u' = A u + A (u' - u) := by
    rw [← LinearMap.map_add A u (u' - u)]
    congr
    abel
  have hsmul : √s • A u' = √s • A u + √s • A (u' - u) := by
    rw [hA, smul_add]
  have hcd := cost_diff w (A u) (A (u' - u)) hs
  rw [real_inner_comm (A (u' - u)) w, real_inner_comm (A (u' - u)) (A u)] at hcd
  show ‖w + √s • A u'‖ ^ 2 - ‖w + √s • A u‖ ^ 2 = _
  rw [hsmul]
  simpa [add_assoc] using hcd

/-- **Specialization start point = truth.** Starting from `u = 0` (the current
configuration is already `x*`, only the residual `w` remains), the cost of a
deviation `v` is

    mimoObj A w s v − mimoObj A w s 0 = s·‖A v‖² + 2√s·⟪A v, w⟫_ℝ.

The term `2s·⟪A v, A u⟫` disappears: at the origin, only the correlation with
the noise discriminates configurations. -/
theorem mimoObj_residual_from_zero (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (v : Fin N → ℝ) :
    mimoObj A w s v - mimoObj A w s 0
      = s * ‖A v‖ ^ 2 + 2 * √s * ⟪A v, w⟫_ℝ := by
  have h := mimoObj_sub_mimoObj A w hs 0 v
  simpa [LinearMap.map_zero] using h

/-- **Coherence: Lemma 11.1 as a corollary of the Bridge.** With `v = flipAt i`,
the identity above reproduces exactly `mimo_flip_cost` (Phase 2):

    mimoObj A w s (flipAt i) − mimoObj A w s 0
      = 4·(s·‖hᵢ‖² + √s·⟪hᵢ, w⟫_ℝ),   hᵢ = A eᵢ.

The Bridge is therefore a true generalization of Lemma 11.1, not a parallel
statement: the flip is the case `u = 0` of the general identity. -/
theorem mimo_flip_cost_via_bridge (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) {s : ℝ} (hs : 0 ≤ s) (i : Fin N) :
    mimoObj A w s (flipAt i) - mimoObj A w s 0
      = 4 * (s * ‖A (Pi.single i 1)‖ ^ 2
             + √s * ⟪A (Pi.single i 1), w⟫_ℝ) := by
  have h := mimoObj_residual_from_zero A w hs (flipAt i)
  have hA : A (flipAt i) = (2 : ℝ) • A (Pi.single i 1) := by
    rw [flipAt]
    exact LinearMap.map_smul A 2 _
  rw [hA, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left] at h
  ring_nf at h ⊢
  exact h

end Pont

section Converse

variable {N M : ℕ}

/-- **Convention bridge.** The SLT-lake product Gaussian (`stdGaussianPi`,
a measure on `Fin n → ℝ`) pushed by the identification `toLp 2` is exactly
Mathlib's standard Gaussian on the Euclidean space — direct instance of
`map_pi_eq_stdGaussian`. The converse fragment below lives on the Mathlib
side (same convention as Phase 3a, `Lmmse`); this bridge pulls the statement
back to the SLT-lake product convention. -/
lemma stdGaussianPi_map_toLp :
    (stdGaussianPi M).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin M)) :=
  map_pi_eq_stdGaussian

/-- **Transport of the linear functional.** For `w` standard Gaussian on the
Euclidean space (Mathlib `stdGaussian`, image of `stdGaussianPi` under
`toLp 2` — cf `stdGaussianPi_map_toLp`), the linear form `⟪h, w⟫` has law
`gaussianReal 0 ‖h‖²`. This is the technically open piece flagged in #11148,
closed here in one step through the `IsGaussian` API of Mathlib: every
continuous linear form of a Gaussian is Gaussian, with mean `μ[L] = 0`
(`integral_strongDual_stdGaussian`) and variance `Var[L; μ] = ‖L‖²`
(`variance_dual_stdGaussian`); the form `w ↦ ⟪h, w⟫` is `innerSL ℝ h`, with
norm `‖h‖` (`innerSL_apply_norm`). -/
lemma map_inner_stdGaussian (h : EuclideanSpace ℝ (Fin M)) :
    Measure.map (fun w : EuclideanSpace ℝ (Fin M) => ⟪h, w⟫_ℝ)
      (stdGaussian (EuclideanSpace ℝ (Fin M)))
      = gaussianReal 0 ((‖h‖ ^ 2).toNNReal) := by
  have hmap := (isGaussian_stdGaussian (E := EuclideanSpace ℝ (Fin M)) :
    IsGaussian _).map_eq_gaussianReal (L := innerSL ℝ h)
  rw [integral_strongDual_stdGaussian (E := EuclideanSpace ℝ (Fin M))
      (L := innerSL ℝ h),
    variance_dual_stdGaussian (E := EuclideanSpace ℝ (Fin M)) (L := innerSL ℝ h),
    innerSL_apply_norm] at hmap
  simpa [innerSL_apply_apply] using hmap

/-- **Open variant of Brick 1.** Any **open** interval contained in `[−2, 2]`
carries Gaussian mass `≥ width · φ(2)`. Brick 1 of Phase 3b states this for
`Ioc a b`; the converse fragment of the Bridge needs an interval strictly
contained in the event `y < c`, hence an `Ioo a b` (the right endpoint of an
`Ioc` is not in `Iio`). Same proof as `gaussian_interval_mass_lower`, with
`volume_Ioo`. -/
theorem gaussian_interval_mass_lower_open {a b : ℝ} (hab : a ≤ b)
    (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    (b - a) * Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤
      (gaussianReal 0 1 (Set.Ioo a b)).toReal := by
  have hk : 0 ≤ Real.exp (-2) / Real.sqrt (2 * Real.pi) := by positivity
  have hmeasure : gaussianReal 0 1 (Set.Ioo a b) =
      ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := by
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      withDensity_apply _ measurableSet_Ioo]
    rfl
  have hsplit : ∀ x ∈ Set.Ioo (a : ℝ) b, |x| ≤ 2 := by
    intro x hx
    rw [abs_le]
    constructor <;> nlinarith [(abs_le.mp ha).1, (abs_le.mp ha).2,
      (abs_le.mp hb).1, (abs_le.mp hb).2, hx.1.le, hx.2.le]
  have hpoint : ∀ x, (Set.Ioo a b).indicator (fun _ => ENNReal.ofReal
      (Real.exp (-2) / Real.sqrt (2 * Real.pi))) x ≤
      (Set.Ioo a b).indicator (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioo a b
    · simp only [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_lower_two x (hsplit x hx))
    · rw [Set.indicator_apply, if_neg hx, Set.indicator_apply, if_neg hx]
  have hmono : (∫⁻ _x in Set.Ioo a b,
        ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * Real.pi)) ∂volume) ≤
      ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := by
    rw [← lintegral_indicator measurableSet_Ioo
        (fun _ => ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * Real.pi))),
      ← lintegral_indicator measurableSet_Ioo
        (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))]
    exact lintegral_mono hpoint
  have hchain : ENNReal.ofReal ((b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi))) ≤
      gaussianReal 0 1 (Set.Ioo a b) := by
    rw [hmeasure]
    calc ENNReal.ofReal ((b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi)))
        = ∫⁻ _x in Set.Ioo a b,
            ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * Real.pi)) ∂volume := by
          rw [setLIntegral_const, Real.volume_Ioo,
            ← ENNReal.ofReal_mul (by nlinarith [hab, hk]), mul_comm]
      _ ≤ ∫⁻ x in Set.Ioo a b, ENNReal.ofReal (gaussianPDFReal 0 1 x) ∂volume := hmono
  have hnn : 0 ≤ (b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi)) := by
    nlinarith [hab, hk]
  have hlhs : (b - a) * Real.exp (-2) / Real.sqrt (2 * Real.pi) =
      (ENNReal.ofReal ((b - a) * (Real.exp (-2) / Real.sqrt (2 * Real.pi)))).toReal := by
    rw [ENNReal.toReal_ofReal hnn]
    ring
  rw [hlhs]
  exact (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mpr hchain

/-- **First statement of the type "P(the flip wins) ≥ c".** Let `hᵢ = A eᵢ`. If
`√s·‖hᵢ‖ ≤ 2` (with `s > 0` and `‖hᵢ‖ > 0` — two hypotheses absent from the
statement of issue #11148 but necessary: for `s = 0` or `‖hᵢ‖ = 0` the event
has probability `0` while the bound `(2 − √s‖hᵢ‖)·φ(2)` is strictly
positive), then

    P(w : the flip i beats x*) ≥ (2 − √s·‖hᵢ‖)·φ(2)

where `φ(2) = exp(−2)/√(2π)`. Chain: the flip cost
(`mimo_flip_cost_via_bridge`) shows the "beats" event is
`⟪hᵢ, w⟫ < −√s·‖hᵢ‖²`; the transport (`map_inner_stdGaussian`) gives the
law `⟪hᵢ, w⟫ ~ N(0, ‖hᵢ‖²)`; scaling back to `N(0,1)`, the interval
`(−2, −√s·‖hᵢ‖) ⊆ {y < −√s·‖hᵢ‖}` carries mass `≥ (2 − √s·‖hᵢ‖)·φ(2)`
(open variant of Brick 1). -/
theorem flip_bat_prob_lower (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    {s : ℝ} (hs : 0 < s) (i : Fin N) (hσ : 0 < ‖A (Pi.single i 1)‖)
    (hbound : √s * ‖A (Pi.single i 1)‖ ≤ 2) :
    (2 - √s * ‖A (Pi.single i 1)‖) * Real.exp (-2) / Real.sqrt (2 * Real.pi)
      ≤ (stdGaussian (EuclideanSpace ℝ (Fin M))
          {w : EuclideanSpace ℝ (Fin M) | mimoObj A w s (flipAt i) < mimoObj A w s 0}).toReal := by
  set hᵢ : EuclideanSpace ℝ (Fin M) := A (Pi.single i 1) with hhᵢ
  have hsqrt : 0 < √s := by positivity
  have hss : √s * √s = s := by rw [← sq]; exact Real.sq_sqrt hs.le
  have hmono : √s * (-√s * ‖hᵢ‖ ^ 2) = -s * ‖hᵢ‖ ^ 2 := by
    linear_combination (norm := ring_nf) (-(‖hᵢ‖ ^ 2)) * hss
  have hsqrt_nonneg : 0 ≤ √s * ‖hᵢ‖ := mul_nonneg (Real.sqrt_nonneg s) (norm_nonneg _)
  have hev : {w : EuclideanSpace ℝ (Fin M) | mimoObj A w s (flipAt i) < mimoObj A w s 0}
      = {w : EuclideanSpace ℝ (Fin M) | ⟪hᵢ, w⟫_ℝ < -√s * ‖hᵢ‖ ^ 2} := by
    ext w
    simp only [Set.mem_setOf_eq]
    have hfc : mimoObj A w s (flipAt i) - mimoObj A w s 0
        = 4 * (s * ‖hᵢ‖ ^ 2 + √s * ⟪hᵢ, w⟫_ℝ) := by
      simpa [hhᵢ] using mimo_flip_cost_via_bridge A w hs.le i
    constructor <;> intro hw
    · rw [← sub_lt_zero, hfc] at hw
      have hsum : s * ‖hᵢ‖ ^ 2 + √s * ⟪hᵢ, w⟫_ℝ < 0 := by
        nlinarith [hw]
      have hstep : √s * ⟪hᵢ, w⟫_ℝ < -s * ‖hᵢ‖ ^ 2 := by
        linarith
      have hbr : √s * ⟪hᵢ, w⟫_ℝ < √s * (-√s * ‖hᵢ‖ ^ 2) := by
        rw [hmono]; exact hstep
      exact lt_of_mul_lt_mul_left hbr hsqrt.le
    · have hbr : √s * ⟪hᵢ, w⟫_ℝ < √s * (-√s * ‖hᵢ‖ ^ 2) :=
        mul_lt_mul_of_pos_left hw hsqrt
      rw [hmono] at hbr
      have hsum : s * ‖hᵢ‖ ^ 2 + √s * ⟪hᵢ, w⟫_ℝ < 0 := by
        linarith
      rw [← sub_lt_zero, hfc]
      linarith
  have hmap := map_inner_stdGaussian hᵢ
  have hmass : (stdGaussian (EuclideanSpace ℝ (Fin M)))
      {w : EuclideanSpace ℝ (Fin M) | ⟪hᵢ, w⟫_ℝ < -√s * ‖hᵢ‖ ^ 2}
      = (gaussianReal 0 ((‖hᵢ‖ ^ 2).toNNReal)) (Set.Iio (-√s * ‖hᵢ‖ ^ 2)) := by
    rw [← hmap]
    rw [Measure.map_apply (by fun_prop :
        Measurable (fun w : EuclideanSpace ℝ (Fin M) => ⟪hᵢ, w⟫_ℝ)) measurableSet_Iio]
    rfl
  have hscale : Measure.map (fun z : ℝ => ‖hᵢ‖ * z) (gaussianReal 0 1)
      = gaussianReal 0 ((‖hᵢ‖ ^ 2).toNNReal) := by
    rw [gaussianReal_map_const_mul (μ := 0) (v := (1 : ℝ≥0)) ‖hᵢ‖]
    simpa [Real.toNNReal_of_nonneg, sq_nonneg]
  have hmass1 : (gaussianReal 0 ((‖hᵢ‖ ^ 2).toNNReal)) (Set.Iio (-√s * ‖hᵢ‖ ^ 2))
      = (gaussianReal 0 1) (Set.Iio (-√s * ‖hᵢ‖)) := by
    rw [← hscale]
    rw [Measure.map_apply (by fun_prop : Measurable (fun z : ℝ => ‖hᵢ‖ * z))
      measurableSet_Iio]
    congr 1
    ext z
    constructor <;> intro hz
    · have hz' : ‖hᵢ‖ * z < ‖hᵢ‖ * (-√s * ‖hᵢ‖) := by
        simpa [mul_comm, mul_left_comm, mul_assoc, sq] using hz
      exact lt_of_mul_lt_mul_left hz' (norm_nonneg _)
    · have hz' : ‖hᵢ‖ * z < ‖hᵢ‖ * (-√s * ‖hᵢ‖) :=
        mul_lt_mul_of_pos_left hz hσ
      simpa [mul_comm, mul_left_comm, mul_assoc, sq] using hz'
  have hab : -2 ≤ -√s * ‖hᵢ‖ := by nlinarith [hbound]
  have hb' : |-√s * ‖hᵢ‖| ≤ 2 := by
    rw [neg_mul, abs_of_nonpos (neg_nonpos.mpr hsqrt_nonneg)]
    linarith
  have hbrick := gaussian_interval_mass_lower_open (a := -2) (b := -√s * ‖hᵢ‖) hab
    (by norm_num) hb'
  have hsub : Set.Ioo (-2 : ℝ) (-√s * ‖hᵢ‖) ⊆ Set.Iio (-√s * ‖hᵢ‖) := by
    intro y hy
    exact hy.2
  have hmassmono : (gaussianReal 0 1) (Set.Ioo (-2 : ℝ) (-√s * ‖hᵢ‖))
      ≤ (gaussianReal 0 1) (Set.Iio (-√s * ‖hᵢ‖)) := by
    exact measure_mono hsub
  rw [hev, hmass, hmass1]
  calc
    (2 - √s * ‖hᵢ‖) * Real.exp (-2) / Real.sqrt (2 * Real.pi)
        = ((-√s * ‖hᵢ‖) - (-2)) * Real.exp (-2) / Real.sqrt (2 * Real.pi) := by
          ring
    _ ≤ (gaussianReal 0 1 (Set.Ioo (-2) (-√s * ‖hᵢ‖))).toReal := hbrick
    _ ≤ (gaussianReal 0 1 (Set.Iio (-√s * ‖hᵢ‖))).toReal := by
        exact (ENNReal.toReal_le_toReal (measure_ne_top _ _)
          (measure_ne_top _ _)).mpr hmassmono

/-! ## Grain 4 (#11152, step 3) — global failure: coordinate escape bounds ML success

Brick 2 (`gaussian_coordinate_escape_bound`, Phase 3b) bounds the probability
that ALL noise coordinates escape a common interval, by independence of the
product. This grain carries out step 3 of #11152: under a diagonal coverage
hypothesis ("if a noise coordinate lands in the interval, a flip beats
`x*`"), the event "no flip beats `x*`" is included in the product escape,
hence has probability `≤ e^{−M·p}`. This is the bridge from per-coordinate
escape (Brick 2) to global failure: a strict descent away from `x*` must
accept a first flip, which beats — the `log log N` term will be born in the
assembly (grain 5) from counting the codeword lattice. -/

/-- **Global failure (step 3).** Diagonal coverage hypothesis: if a noise
coordinate of `w` lands in `I(c, ε) = (c−ε/2, c+ε/2] ⊆ [−2, 2]`, then a flip
beats `x*`. Then the probability that no flip beats `x*` is
`≤ exp(−M·ε·φ(2))` with `φ(2) = exp(−2)/√(2π)`. Chain: contrapositive of
the coverage ("no flip beats" ⊆ "all coordinates escape"), transport
`stdGaussian = (stdGaussianPi M).map (WithLp.toLp 2)`
(`stdGaussianPi_map_toLp`), then Brick 2. -/
theorem no_flip_beats_prob_le {N M : ℕ} (hM : 0 < M)
    (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M)) {s c ε : ℝ}
    (hε : 0 < ε) (hc : |c| + ε / 2 ≤ 2)
    (hp1 : ε * Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤ 1)
    (hcover : ∀ w : EuclideanSpace ℝ (Fin M),
      (∃ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j ∈ Set.Ioc (c - ε / 2) (c + ε / 2)) →
        ∃ i : Fin N, mimoObj A w s (flipAt i) < mimoObj A w s 0) :
    (stdGaussian (EuclideanSpace ℝ (Fin M))
      {w : EuclideanSpace ℝ (Fin M) |
        ∀ i : Fin N, ¬(mimoObj A w s (flipAt i) < mimoObj A w s 0)}).toReal
      ≤ Real.exp (-((M : ℝ) * (ε * Real.exp (-2) / Real.sqrt (2 * Real.pi)))) := by
  have hsub : {w : EuclideanSpace ℝ (Fin M) |
      ∀ i : Fin N, ¬(mimoObj A w s (flipAt i) < mimoObj A w s 0)} ⊆
      {w : EuclideanSpace ℝ (Fin M) |
        ∀ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)} := by
    intro w hw j hj
    exact ((hcover w ⟨j, hj⟩).elim hw).elim
  have hmeas : MeasurableSet
      {w : EuclideanSpace ℝ (Fin M) |
        ∀ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)} := by
    have hEq : {w : EuclideanSpace ℝ (Fin M) |
        ∀ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)} =
        ⋂ j : Fin M,
            {w : EuclideanSpace ℝ (Fin M) |
              (WithLp.ofLp w : Fin M → ℝ) j ∈ (Set.Ioc (c - ε / 2) (c + ε / 2))ᶜ} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
    rw [hEq]
    refine MeasurableSet.iInter fun j => ?_
    exact measurableSet_Ioc.compl.preimage
      (by fun_prop : Measurable (fun w : EuclideanSpace ℝ (Fin M) =>
        (WithLp.ofLp w : Fin M → ℝ) j))
  have hpre : (WithLp.toLp 2 : (Fin M → ℝ) → EuclideanSpace ℝ (Fin M)) ⁻¹'
      {w : EuclideanSpace ℝ (Fin M) |
        ∀ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)}
      = {v : Fin M → ℝ | ∀ j : Fin M, v j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hmass : (stdGaussian (EuclideanSpace ℝ (Fin M))
        {w : EuclideanSpace ℝ (Fin M) |
          ∀ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)})
      = (stdGaussianPi M
          {v : Fin M → ℝ | ∀ j : Fin M, v j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)}) := by
    rw [← stdGaussianPi_map_toLp,
      Measure.map_apply (by fun_prop :
        Measurable (WithLp.toLp 2 : (Fin M → ℝ) → EuclideanSpace ℝ (Fin M))) hmeas,
      hpre]
  have hesc := gaussian_coordinate_escape_bound (n := M) (c := c) (ε := ε)
    hM hε hc hp1
  calc (stdGaussian (EuclideanSpace ℝ (Fin M))
        {w : EuclideanSpace ℝ (Fin M) |
          ∀ i : Fin N, ¬(mimoObj A w s (flipAt i) < mimoObj A w s 0)}).toReal
      ≤ (stdGaussian (EuclideanSpace ℝ (Fin M))
          {w : EuclideanSpace ℝ (Fin M) |
            ∀ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j
              ∉ Set.Ioc (c - ε / 2) (c + ε / 2)}).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
          (measure_mono hsub)
    _ = (stdGaussianPi M
          {v : Fin M → ℝ | ∀ j : Fin M, v j ∉ Set.Ioc (c - ε / 2) (c + ε / 2)}).toReal :=
        by rw [hmass]
    _ ≤ Real.exp (-((M : ℝ) * (ε * Real.exp (-2) / Real.sqrt (2 * Real.pi)))) := hesc

/-! ## Grain 5 (#11152, step 4) — assembly: the threshold `2 log N − log log N`

Grain 4 bounded the probability that no flip beats `x*` by `exp(−M·ε·φ(2))`.
This grain covers the last distance to the converse statement of Thm 2.1:

1. **The code.** The codewords are `{±1}^N`; the starting point is the
   all-`1` vector, whose deviations are `u ∈ {0, 2}^N` (`u = 1 − x`). A flip
   `flipAt i = 2·eᵢ` is a valid deviation (the codeword `1 − 2·eᵢ` has its
   i-th coordinate at `−1`).
2. **The ML error event.** ML minimizes `‖y − √s·A x‖²` over the code; if
   the channel is `y = √s·A·1 + w` and the start point `x* = 1`, decoding
   **fails** as soon as a competing codeword is strictly closer to `y` than
   `1`, i.e. `∃ u ∈ {0,2}^N, u ≠ 0, mimoObj A w s u < mimoObj A w s 0`.
3. **The reduction.** If a flip beats `x*`, ML fails (`flipAt i` is a valid
   non-zero deviation); hence "no ML error" ⊆ "no flip beats". The grain-4
   bound (on this latter event) lower-bounds the ML failure probability.
4. **The threshold.** Under the diagonal coverage, if `M·ε·φ(2) ≥ 2·log N −
   log log N`, then `P(ML fails) ≥ 1 − exp(−(2·log N − log log N))`. This is
   the assembly form that exhibits the Thm-2.1 term; the `− s_N` refinement
   (lower-order lattice term) and the exact `SNR ↔ ε` link remain the
   documented continuation of §11. -/

/-- **Deviation box of the code `{±1}^N` from the point `1`**: the vectors
`u : Fin N → ℝ` whose every coordinate is `0` (no flip) or `2` (flipped
coordinate at `−1`). `x = 1 − u` ranges exactly over `{±1}^N`. -/
def DeviationBox (N : ℕ) : Set (Fin N → ℝ) :=
  {u : Fin N → ℝ | ∀ i : Fin N, u i = 0 ∨ u i = 2}

/-- **ML decoding error on the code `{±1}^N`** for the starting point `1`: a
competing codeword is strictly closer to `y = √s·A·1 + w` than `1` itself,
i.e. a non-zero deviation `u ∈ {0,2}^N` satisfies
`mimoObj A w s u < mimoObj A w s 0`. -/
def mlError (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M)) (w : EuclideanSpace ℝ (Fin M))
    (s : ℝ) : Prop :=
  ∃ u : Fin N → ℝ, u ∈ DeviationBox N ∧ u ≠ 0 ∧ mimoObj A w s u < mimoObj A w s 0

/-- A flip `flipAt i = 2·eᵢ` is a valid deviation of the code: its coordinate
`i` equals `2`, all others `0`. -/
theorem flipAt_mem_deviationBox (i : Fin N) : flipAt i ∈ DeviationBox N := by
  intro j
  by_cases h : j = i
  · subst h
    right
    simp [flipAt, Pi.single_eq_same]
  · left
    simp [flipAt, Pi.single_eq_of_ne h]

/-- A flip is a non-zero deviation. -/
theorem flipAt_ne_zero (i : Fin N) : flipAt i ≠ 0 := by
  intro h
  have hc := congr_fun h i
  simp [flipAt, Pi.single_eq_same] at hc

/-- **Reduction flip → ML error.** If a flip beats `x*` (`∃ i, mimoObj A w s
(flipAt i) < mimoObj A w s 0`), then the ML decoder on `{±1}^N` fails: the
competing codeword `1 − flipAt i` is strictly closer to `y` than `1`. This is
the bridge that turns the grain-4 bound into a lower bound of the ML error
probability. -/
theorem flip_bat_implies_mlError (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M))
    (w : EuclideanSpace ℝ (Fin M)) (s : ℝ)
    (hw : ∃ i : Fin N, mimoObj A w s (flipAt i) < mimoObj A w s 0) :
    mlError A w s := by
  rcases hw with ⟨i, hi⟩
  exact ⟨flipAt i, flipAt_mem_deviationBox i, flipAt_ne_zero i, hi⟩

/-- **Assembly — ML failure below the threshold.** Under the diagonal coverage
(`hcover`: one noise coordinate in `I(c, ε)` ⟹ a flip beats `x*`), if
`M·ε·φ(2) ≥ 2·log N − log log N`, then the ML error probability is
`≥ 1 − exp(−(2·log N − log log N))`. Grain 4 bounds the event "no flip beats"
by `exp(−M·ε·φ(2))`; the reduction `flip_bat_implies_mlError` combines with
the contrapositive event ("no ML error" ⊆ "no flip beats"); the
sub-additivity of the measure (`P(s) + P(sᶜ) ≥ 1`, valid without
measurability) passes to the ML error event; finally the threshold condition
replaces `M·ε·φ(2)` by the Thm-2.1 term `2·log N − log log N` (monotonicity
of `x ↦ exp(−x)`). The `− s_N` refinement and the `SNR ↔ ε` link remain the
continuation of §11. -/
theorem ml_error_prob_ge_threshold {N M : ℕ} (hM : 0 < M)
    (A : (Fin N → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin M)) {s c ε : ℝ}
    (hε : 0 < ε) (hc : |c| + ε / 2 ≤ 2)
    (hp1 : ε * Real.exp (-2) / Real.sqrt (2 * Real.pi) ≤ 1)
    (hcover : ∀ w : EuclideanSpace ℝ (Fin M),
      (∃ j : Fin M, (WithLp.ofLp w : Fin M → ℝ) j ∈ Set.Ioc (c - ε / 2) (c + ε / 2)) →
        ∃ i : Fin N, mimoObj A w s (flipAt i) < mimoObj A w s 0)
    (hseuil : (M : ℝ) * (ε * Real.exp (-2) / Real.sqrt (2 * Real.pi))
      ≥ 2 * Real.log N - Real.log (Real.log N)) :
    1 - Real.exp (-(2 * Real.log N - Real.log (Real.log N))) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin M)) {w : EuclideanSpace ℝ (Fin M) | mlError A w s}).toReal := by
  set p : ℝ := ε * Real.exp (-2) / Real.sqrt (2 * Real.pi) with hp_def
  set T : ℝ := 2 * Real.log N - Real.log (Real.log N) with hT_def
  let μ : Measure (EuclideanSpace ℝ (Fin M)) := stdGaussian (EuclideanSpace ℝ (Fin M))
  -- 1. Contrapositive of the reduction: "no ML error" ⟹ "no flip beats".
  have hsub : {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s} ⊆
      {w : EuclideanSpace ℝ (Fin M) |
        ∀ i : Fin N, ¬(mimoObj A w s (flipAt i) < mimoObj A w s 0)} := by
    intro w hw i
    by_contra hbi
    exact hw (flip_bat_implies_mlError A w s ⟨i, hbi⟩)
  -- 2. Probability bounds: P(no-flip) ≤ exp(−M·p), then P(¬mlError) ≤ P(no-flip).
  have hno := no_flip_beats_prob_le (N := N) (M := M) hM A (s := s) (c := c) (ε := ε)
    hε hc hp1 hcover
  have hle : (μ {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s}).toReal ≤
      Real.exp (-((M : ℝ) * p)) := by
    have hmonoμ : (μ {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s}).toReal ≤
        (μ {w : EuclideanSpace ℝ (Fin M) |
          ∀ i : Fin N, ¬(mimoObj A w s (flipAt i) < mimoObj A w s 0)}).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr
        (measure_mono hsub)
    have hno' : (μ {w : EuclideanSpace ℝ (Fin M) |
          ∀ i : Fin N, ¬(mimoObj A w s (flipAt i) < mimoObj A w s 0)}).toReal ≤
        Real.exp (-((M : ℝ) * p)) := by
      simpa [μ, hp_def] using hno
    exact le_trans hmonoμ hno'
  -- 3. Sub-additivity: 1 − P(mlError) ≤ P(¬mlError) (no measurability needed).
  have hsubadd : 1 ≤ (μ {w : EuclideanSpace ℝ (Fin M) | mlError A w s}).toReal +
      (μ {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s}).toReal := by
    have h1 : (μ Set.univ).toReal = 1 := by
      rw [measure_univ]
      simp
    have huniv : {w : EuclideanSpace ℝ (Fin M) | mlError A w s} ∪
          {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s} =
        (Set.univ : Set (EuclideanSpace ℝ (Fin M))) := by
      classical
      ext w
      tauto
    have hle' : μ (Set.univ : Set (EuclideanSpace ℝ (Fin M))) ≤
        μ {w : EuclideanSpace ℝ (Fin M) | mlError A w s} +
        μ {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s} := by
      rw [← huniv]
      exact measure_union_le _ _
    have htor : (μ (Set.univ : Set (EuclideanSpace ℝ (Fin M)))).toReal ≤
        (μ {w : EuclideanSpace ℝ (Fin M) | mlError A w s} +
         μ {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s}).toReal :=
      ((ENNReal.toReal_le_toReal (measure_ne_top _ _)
        (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)).mpr hle')
    rw [h1] at htor
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at htor
    exact htor
  have hcomp : 1 - (μ {w : EuclideanSpace ℝ (Fin M) | mlError A w s}).toReal ≤
      (μ {w : EuclideanSpace ℝ (Fin M) | ¬ mlError A w s}).toReal := by
    linarith [hsubadd]
  -- 4. Final chain.
  have hlt : 1 - (μ {w : EuclideanSpace ℝ (Fin M) | mlError A w s}).toReal ≤
      Real.exp (-((M : ℝ) * p)) := le_trans hcomp hle
  have hab : 1 - Real.exp (-((M : ℝ) * p)) ≤
      (μ {w : EuclideanSpace ℝ (Fin M) | mlError A w s}).toReal := by
    linarith [hlt]
  have hmono : Real.exp (-((M : ℝ) * p)) ≤ Real.exp (-T) :=
    Real.exp_le_exp.mpr (by linarith [hseuil])
  calc
    1 - Real.exp (-T) ≤ 1 - Real.exp (-((M : ℝ) * p)) := by linarith [hmono]
    _ ≤ (μ {w : EuclideanSpace ℝ (Fin M) | mlError A w s}).toReal := hab

end Converse

end Mimo_en
