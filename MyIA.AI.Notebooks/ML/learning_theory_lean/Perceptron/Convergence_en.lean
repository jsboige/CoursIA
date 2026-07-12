import Mathlib
import Perceptron.Perceptron_en

/-!
# Perceptron convergence theorem (Novikoff, 1962) — bound `(R/γ)²`

> **Theorem (Novikoff).** Let a valid perceptron run on data linearly separable by a
> unit vector `u` with margin `γ > 0`, the points being of norm `≤ R`. Then the number
> of updates (mistakes) `n` satisfies `n ≤ (R/γ)²`.

The proof, **elementary geometric and entirely 0-sorry**, rests on two growth
inequalities of the weight vector `wₖ` combined via Cauchy–Schwarz:

- **Lemma A — alignment** (`align_growth`) : `⟪wₖ, u⟫ ≥ k·γ`.
  Each mistake adds `yₖ · xₖ` to `w`, and the margin hypothesis guarantees
  `yₖ · ⟪u, xₖ⟫ ≥ γ`, so the alignment onto the separator grows by at least `γ`.
- **Lemma B — norm** (`norm_bound`) : `‖wₖ‖² ≤ k·R²`.
  Each mistake adds at most `R²` to `‖w‖²` (via the expansion
  `‖a + b‖² = ‖a‖² + 2⟪a,b⟫ + ‖b‖²`), the cross term being `≤ 0` because the update
  is a mistake (`yₖ · ⟪wₖ, xₖ⟫ ≤ 0`).
- **Conclusion** : Cauchy–Schwarz `⟪wₙ, u⟫ ≤ ‖wₙ‖·‖u‖ = ‖wₙ‖` (with `‖u‖ = 1`)
  yields `n·γ ≤ ‖wₙ‖`, hence `(n·γ)² ≤ ‖wₙ‖² ≤ n·R²`, i.e. `n·γ² ≤ R²`.

Reference : A. B. J. Novikoff, *On convergence proofs for perceptrons*, Symposium
on the Mathematical Theory of Automata (1962).

English mirror of `Perceptron/Convergence.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling
files in the same lake, both compile; namespace `Perceptron_en` (anti-collision
with the FR `Perceptron` namespace); non-docstring proof code unchanged.
-/

open scoped InnerProductSpace

namespace Perceptron_en

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

open PerceptronRun

/-- **Lemma A — alignment growth** : after `k ≤ n` updates,
`⟪wₖ, u⟫ ≥ k·γ` (each mistake aligns `w` onto `u` by at least the margin `γ`). -/
theorem PerceptronRun.align_growth (run : PerceptronRun V) :
    ∀ k ≤ run.n,
      (k : ℝ) * run.γ ≤ ⟪perceptronWeights run.pts run.lbl k, run.u⟫_ℝ := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [perceptronWeights_zero, inner_zero_left, Nat.cast_zero]
    linarith
  | succ k ih =>
    intro hk
    have hkn : k < run.n := Nat.lt_of_succ_le hk
    have hstep : run.γ ≤ run.lbl k * ⟪run.u, run.pts k⟫_ℝ := run.hMargin k hkn
    have hih : (k : ℝ) * run.γ ≤ ⟪perceptronWeights run.pts run.lbl k, run.u⟫_ℝ :=
      ih (Nat.le_of_succ_le hk)
    rw [perceptronWeights_succ run.pts run.lbl k, inner_add_left,
        real_inner_smul_left, real_inner_comm run.u (run.pts k), Nat.cast_add_one]
    linarith

/-- **Lemma B — norm growth** : after `k ≤ n` updates,
`‖wₖ‖² ≤ k·R²` (each mistake adds at most `R²` to `‖w‖²`). -/
theorem PerceptronRun.norm_bound (run : PerceptronRun V) :
    ∀ k ≤ run.n,
      ‖perceptronWeights run.pts run.lbl k‖ ^ 2 ≤ (k : ℝ) * run.R ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [perceptronWeights_zero, norm_zero]
    -- But `0 ≤ ↑0 * run.R²` : product of non-negatives (`↑0 ≥ 0`, `run.R² ≥ 0`).
    nlinarith [sq_nonneg run.R]
  | succ k ih =>
    intro hk
    have hkn : k < run.n := Nat.lt_of_succ_le hk
    have hih : ‖perceptronWeights run.pts run.lbl k‖ ^ 2 ≤ (k : ℝ) * run.R ^ 2 :=
      ih (Nat.le_of_succ_le hk)
    -- Decomposition of the squared norm of a sum.
    have hCross : ⟪perceptronWeights run.pts run.lbl k, run.lbl k • run.pts k⟫_ℝ ≤ 0 := by
      rw [real_inner_smul_right]
      exact run.hMistake k hkn
    have hLbl2 : run.lbl k ^ 2 = 1 := run.hLbl k hkn
    have hRad : ‖run.pts k‖ ≤ run.R := run.hRad k hkn
    have hRad2 : ‖run.pts k‖ ^ 2 ≤ run.R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) run.hR).mpr hRad
    have hSc2 : ‖run.lbl k • run.pts k‖ ^ 2 ≤ run.R ^ 2 := by
      have hexp : ‖run.lbl k • run.pts k‖ ^ 2 = run.lbl k ^ 2 * ‖run.pts k‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [hexp, hLbl2, one_mul]
      exact hRad2
    rw [perceptronWeights_succ run.pts run.lbl k, norm_add_sq_eq]
    -- Linarith does not see `↑(k+1)·R²` as `↑k·R² + R²` (product of atoms):
    -- we provide the expanded equality as a hypothesis.
    have hRHS : (k + 1 : ℝ) * run.R ^ 2 = (k : ℝ) * run.R ^ 2 + run.R ^ 2 := by ring
    simp only [Nat.cast_add_one]
    linarith

/-- **Perceptron convergence theorem (Novikoff, 1962)** : the number of updates `n`
of a valid run on data of radius `R` separated with margin `γ` satisfies the bound
`n · γ² ≤ R²`, i.e. `n ≤ (R/γ)²`. -/
theorem PerceptronRun.novikoff_mistake_bound (run : PerceptronRun V) :
    (run.n : ℝ) * run.γ ^ 2 ≤ run.R ^ 2 := by
  -- Lemma A at `k = n`.
  have hAlign : (run.n : ℝ) * run.γ ≤
      ⟪perceptronWeights run.pts run.lbl run.n, run.u⟫_ℝ :=
    run.align_growth run.n (Nat.le_refl run.n)
  -- Lemma B at `k = n`.
  have hNorm : ‖perceptronWeights run.pts run.lbl run.n‖ ^ 2 ≤ (run.n : ℝ) * run.R ^ 2 :=
    run.norm_bound run.n (Nat.le_refl run.n)
  -- Cauchy–Schwarz : ⟪wₙ, u⟫ ≤ ‖wₙ‖·‖u‖ = ‖wₙ‖.
  have hCS : ⟪perceptronWeights run.pts run.lbl run.n, run.u⟫_ℝ ≤
      ‖perceptronWeights run.pts run.lbl run.n‖ := by
    have hle := real_inner_le_norm (perceptronWeights run.pts run.lbl run.n) run.u
    rw [run.hUnit] at hle
    linarith
  -- n·γ ≤ ‖wₙ‖, then (n·γ)² ≤ ‖wₙ‖² ≤ n·R².
  have hNG : (run.n : ℝ) * run.γ ≤ ‖perceptronWeights run.pts run.lbl run.n‖ :=
    le_trans hAlign hCS
  have hNG2 : ((run.n : ℝ) * run.γ) ^ 2 ≤ ‖perceptronWeights run.pts run.lbl run.n‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) (le_of_lt run.hγ)) (norm_nonneg _)).mpr hNG
  have hKey : ((run.n : ℝ) * run.γ) ^ 2 ≤ (run.n : ℝ) * run.R ^ 2 :=
    le_trans hNG2 hNorm
  -- Conclusion : (n·γ)² ≤ n·R²  ⟹  n·γ² ≤ R²  (case n = 0 trivial ; n ≥ 1 simplify by n).
  rcases Nat.eq_zero_or_pos run.n with hz | hpos
  · -- n = 0 : 0·γ² ≤ R² trivial.
    rw [hz, Nat.cast_zero, zero_mul]
    exact sq_nonneg run.R
  · -- n > 0 : simplify by n (strictly positive).
    have hnpos : (0 : ℝ) < run.n := Nat.cast_pos.mpr hpos
    have hkey' : (run.n : ℝ) * ((run.n : ℝ) * run.γ ^ 2) ≤ (run.n : ℝ) * run.R ^ 2 := by
      have hexp : ((run.n : ℝ) * run.γ) ^ 2 = (run.n : ℝ) ^ 2 * run.γ ^ 2 := by
        rw [mul_pow]
      rw [hexp, pow_two, mul_assoc] at hKey
      exact hKey
    exact (mul_le_mul_iff_of_pos_left hnpos).mp hkey'

end Perceptron_en
