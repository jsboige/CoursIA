import Mathlib
import Perceptron.Perceptron_en
import Perceptron.Convergence_en

/-!
# Saturation of the Novikoff bound — a tight witness (sharpness)

> **Result.** The Novikoff bound `n · γ² ≤ R²` (i.e. `n ≤ (R/γ)²` updates) is
> **optimal** : we exhibit a valid perceptron run, on `ℂ` seen as a real
> 2-dimensional inner product space, which **saturates** the bound —
> `n · γ² = R²` exactly. A universal constant strictly smaller than `1` in front of
> `(R/γ)²` therefore cannot upper-bound the number of mistakes over all separable
> runs.

**Geometric witness.** Two points `x₀ = 1 + I`, `x₁ = 1 − I` (half-lines at ±45°),
both of label `+1`, separated by the unit vector `u = 1` with margin `γ = 1`, each
of norm `‖xₖ‖ = √2` (so `R = √2`). The first update makes `w₁ = x₀ = 1 + I` ; at
the second step, `⟪w₁, x₁⟫ = ⟨1 + I, 1 − I⟩ = 0` (the two half-lines are
orthogonal) : `x₁` lies exactly on the decision boundary of `w₁`, so the update is
a mistake. We then get `n · γ² = 2 · 1 = 2 = (√2)² = R²` : **equality** — the bound
is met, hence sharp.

The space `ℂ` carries the instance `InnerProductSpace ℝ ℂ` ; the real inner product
unfolds as `⟪w, z⟫_ℝ = (z · conj w).re` (`Complex.inner` +
`Complex.starRingEnd_apply`), i.e. `w.re · z.re + w.im · z.im`, and the norms as
`‖z‖² = Complex.normSq z = z.re² + z.im²` (`Complex.normSq_eq_norm_sq`,
`Complex.normSq_apply`).

This module is **entirely sorry-free** : it is a concrete *sharpness* result
(equality attained), distinct from the universal bound theorem
`novikoff_mistake_bound` (inequality) proved in `Convergence.lean`.

English mirror of `Perceptron/Tightness.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling
files in the same lake, both compile; namespace `Perceptron_en` (anti-collision
with the FR `Perceptron` namespace); non-docstring proof code unchanged.
-/

open scoped InnerProductSpace

open Complex

namespace Perceptron_en

/-- Real inner product on `ℂ` unfolded into coordinates : `⟪w, z⟫ = w.re·z.re +
w.im·z.im` (utility lemma for the concrete computations of the witness). -/
theorem complex_inner_re (w z : ℂ) : ⟪w, z⟫_ℝ = w.re * z.re + w.im * z.im := by
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The witness points `xₖ` : `x₀ = 1 + I`, `xₖ = 1 − I` for `k ≥ 1`
(two half-lines at ±45° of the complex plane). -/
def witnessPts : ℕ → ℂ
  | 0 => 1 + I
  | _ + 1 => 1 - I

/-- The witness labels : all `+1`. -/
def witnessLbl : ℕ → ℝ := fun _ => 1

/-- `‖xₖ‖² = 2` for every `k` (the two half-lines have the same norm `√2`). -/
theorem witnessPts_norm_sq (k : ℕ) : ‖witnessPts k‖ ^ 2 = 2 := by
  rcases k with rfl | k
  · rw [show ‖witnessPts 0‖ ^ 2 = Complex.normSq (witnessPts 0) from
          (Complex.normSq_eq_norm_sq _).symm,
        Complex.normSq_apply, witnessPts]
    norm_num [Complex.add_re, Complex.add_im, I_re, I_im]
  · rw [show ‖witnessPts (k + 1)‖ ^ 2 = Complex.normSq (witnessPts (k + 1)) from
          (Complex.normSq_eq_norm_sq _).symm,
        Complex.normSq_apply, witnessPts]
    norm_num [Complex.sub_re, Complex.sub_im, I_re, I_im]

/-- The margin `⟪u, xₖ⟫ = ⟨1, xₖ⟩ = 1` for every `k` (equal to `γ`). -/
theorem witness_margin_inner (k : ℕ) : ⟪(1 : ℂ), witnessPts k⟫_ℝ = 1 := by
  rw [complex_inner_re]
  rcases k with rfl | k
  · rw [witnessPts]
    norm_num [Complex.add_re, Complex.add_im, I_re, I_im]
  · rw [witnessPts]
    norm_num [Complex.sub_re, Complex.sub_im, I_re, I_im]

/-- The "mistake" inner product `⟪1 + I, 1 − I⟫ = 0` (orthogonality of the two
half-lines) — core of the second update. -/
theorem witness_cross_inner : ⟪(1 + I : ℂ), 1 - I⟫_ℝ = 0 := by
  rw [complex_inner_re]
  norm_num [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, I_re, I_im]

/-- After the first update, `w₁ = x₀ = 1 + I`. -/
theorem witness_w1 : perceptronWeights witnessPts witnessLbl 1 = 1 + I := by
  rw [perceptronWeights_succ, perceptronWeights_zero, zero_add]
  show witnessLbl 0 • witnessPts 0 = 1 + I
  rw [show witnessLbl 0 = 1 from rfl, show witnessPts 0 = (1 + I : ℂ) from rfl]
  exact one_smul _ _

theorem witness_lbl : ∀ k < (2 : ℕ), witnessLbl k ^ 2 = 1 := by
  intro k _
  rw [show witnessLbl k = 1 from rfl]
  norm_num

theorem witness_rad : ∀ k < (2 : ℕ), ‖witnessPts k‖ ≤ Real.sqrt 2 := by
  intro k _
  have h := witnessPts_norm_sq k
  have hnn : 0 ≤ ‖witnessPts k‖ := norm_nonneg _
  calc ‖witnessPts k‖
      = Real.sqrt (‖witnessPts k‖ ^ 2) := (Real.sqrt_sq hnn).symm
    _ = Real.sqrt 2 := by rw [h]
    _ ≤ Real.sqrt 2 := le_refl _

theorem witness_margin : ∀ k < (2 : ℕ),
    (1 : ℝ) ≤ witnessLbl k * ⟪(1 : ℂ), witnessPts k⟫_ℝ := by
  intro k _
  rw [show witnessLbl k = 1 from rfl, one_mul]
  linarith [witness_margin_inner k]

theorem witness_mistake : ∀ k < (2 : ℕ),
    witnessLbl k * ⟪perceptronWeights witnessPts witnessLbl k, witnessPts k⟫_ℝ ≤ 0 := by
  intro k _
  have h01 : k = 0 ∨ k = 1 := by omega
  rcases h01 with rfl | rfl
  · rw [perceptronWeights_zero, inner_zero_left, show witnessLbl 0 = 1 from rfl]
    norm_num
  · rw [witness_w1, show witnessLbl 1 = 1 from rfl, one_mul,
        show witnessPts 1 = (1 - I : ℂ) from rfl]
    linarith [witness_cross_inner]

/-- The saturating run : `n = 2` points of `ℂ`, separated by `u = 1` with margin
`γ = 1`, of radius `R = √2`, reaching `n · γ² = R²`. -/
noncomputable def tightnessRun : PerceptronRun ℂ :=
  { n := 2,
    pts := witnessPts,
    lbl := witnessLbl,
    u := 1,
    R := Real.sqrt 2,
    γ := 1,
    hR := Real.sqrt_nonneg _,
    hγ := one_pos,
    hUnit := norm_one,
    hLbl := witness_lbl,
    hRad := witness_rad,
    hMargin := witness_margin,
    hMistake := witness_mistake }

/-- The witness reaches the bound **with equality** : `n · γ² = R²`. -/
theorem tightnessRun_saturates :
    (tightnessRun.n : ℝ) * tightnessRun.γ ^ 2 = tightnessRun.R ^ 2 := by
  have hn : tightnessRun.n = 2 := rfl
  have hγ : tightnessRun.γ = 1 := rfl
  have hR : tightnessRun.R = Real.sqrt 2 := rfl
  rw [hn, hγ, hR]
  rw [show (Real.sqrt 2 : ℝ) ^ 2 = 2 from Real.sq_sqrt (by norm_num)]
  norm_num

/-- **The Novikoff bound is sharp.** There exists a valid run (on `ℂ`) which
reaches it with equality `n · γ² = R²`. Since `novikoff_mistake_bound` gives the
universal inequality `n · γ² ≤ R²` and equality is reached by `tightnessRun`, no
bound of the form `n · γ² ≤ c · R²` with `c < 1` is universally valid : the
constant `1` (in front of `(R/γ)²`) is optimal. -/
theorem novikoff_bound_is_sharp :
    ∃ run : PerceptronRun ℂ, (run.n : ℝ) * run.γ ^ 2 = run.R ^ 2 :=
  ⟨tightnessRun, tightnessRun_saturates⟩

end Perceptron_en
