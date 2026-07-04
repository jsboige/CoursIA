import Mathlib

/-!
  Minimax.ZeroSum — finite zero-sum games: matrix, mixed strategies, payoff (EN sibling)
  =======================================================================================

  English mirror of `Minimax/ZeroSum.lean` (FR-first canonical).
  Convention i18n Lean ratifiée par ai-01 (2026-07-04, #4980 comment-4881909354) :
  fichiers `.lean` distincts FR + EN siblings dans le même lake, les deux compilent.
  Drift-CI detectable : contenu non-docstring byte-identique entre siblings.

  Note méthodologique : traduction manuelle du FR canonique (pas de source
  EN historique pré-Option A à recover, fichier FR-first depuis origin
  commit `821e9de1a` du `821e9de` original, jsboige 2026-06-24).

  A two-player finite zero-sum game: the row player picks a row `i`, the
  column player picks a column `j`, and the row player gets the payoff
  `A i j` (the column player gets `-A i j`). In **mixed strategy**, each
  player draws from a probability distribution; the expected payoff of
  the row player is the **bilinear payoff** `xᵀ A y = Σᵢⱼ xᵢ Aᵢⱼ yⱼ`,
  where `x` and `y` are points of the probability simplex
  (`stdSimplex`).

  This module lays down the definitions and proves the **bilinearity** of
  the payoff (key to applying Sion): `payoff` is affine in each variable
  separately, hence both continuous and quasi-convex/quasi-concave —
  exactly the assumptions of `Sion.exists_isSaddlePointOn'` (see
  `Minimax.lean`).

  Cross reference: the `GameTheory` series (Nash already exists via
  `lean_game_defs/Nash.lean`, of which this lake is the zero-sum
  specialization). See issue #4054.
-/

namespace MinimaxLean_en

open Finset

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The payoff matrix of a zero-sum game (rows = row player, columns =
    column player). `A i j` = row player's gain when `i` plays row `i`
    and `j` plays column `j`. -/
abbrev PayoffMatrix (m n : Type*) := Matrix m n ℝ

/-- The **expected bilinear payoff**: `payoff A x y = Σᵢⱼ xᵢ · Aᵢⱼ · yⱼ`
    (sum over `m × n`). This is the row player's expected gain under the
    mixed strategies `x` (rows) and `y` (columns). The representation as
    **a single sum over the product** makes bilinearity immediate
    (`sum_add_distrib` / `sum_mul` in one step). -/
def payoff (A : PayoffMatrix m n) (x : m → ℝ) (y : n → ℝ) : ℝ :=
  ∑ ij : m × n, x ij.1 * A ij.1 ij.2 * y ij.2

/-- **Additivity in `x`**: the payoff is additive in the row player's
    strategy (first half of linearity). -/
lemma payoff_add_in_x (A : PayoffMatrix m n) (x x' : m → ℝ) (y : n → ℝ) :
    payoff A (x + x') y = payoff A x y + payoff A x' y := by
  simp only [payoff, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- **Homogeneity in `x`**: the payoff is homogeneous in the row
    player's strategy (second half of linearity). -/
lemma payoff_smul_in_x (A : PayoffMatrix m n) (c : ℝ) (x : m → ℝ) (y : n → ℝ) :
    payoff A (c • x) y = c * payoff A x y := by
  simp only [payoff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1 with ij
  ring

/-- **Additivity in `y`**: the payoff is additive in the column player's
    strategy (first half of linearity in `y`). -/
lemma payoff_add_in_y (A : PayoffMatrix m n) (x : m → ℝ) (y y' : n → ℝ) :
    payoff A x (y + y') = payoff A x y + payoff A x y' := by
  simp only [payoff, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- **Homogeneity in `y`**: the payoff is homogeneous in the column
    player's strategy (second half of linearity in `y`). -/
lemma payoff_smul_in_y (A : PayoffMatrix m n) (c : ℝ) (x : m → ℝ) (y : n → ℝ) :
    payoff A x (c • y) = c * payoff A x y := by
  simp only [payoff, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1 with ij
  ring

/-- The payoff is **continuous** (jointly) since it is a finite sum of
    continuous monomials. This is the key fact that yields, by
    restriction, the upper and lower semicontinuity required by Sion. -/
lemma continuous_payoff (A : PayoffMatrix m n) :
    Continuous (fun p : (m → ℝ) × (n → ℝ) => payoff A p.1 p.2) := by
  unfold payoff
  apply continuous_finsetSum
  intro ij _
  fun_prop

/-- The payoff `payoff A · y` is **continuous** in the row player's
    strategy (special case of `continuous_payoff`, by restriction
    `y` = constant). -/
lemma continuous_payoff_in_x (A : PayoffMatrix m n) (y : n → ℝ) :
    Continuous (fun x : m → ℝ => payoff A x y) := by
  unfold payoff
  fun_prop

/-- The payoff `payoff A x ·` is **continuous** in the column player's
    strategy (special case of `continuous_payoff`, by restriction
    `x` = constant). -/
lemma continuous_payoff_in_y (A : PayoffMatrix m n) (x : m → ℝ) :
    Continuous (fun y : n → ℝ => payoff A x y) := by
  unfold payoff
  fun_prop

end MinimaxLean_en
