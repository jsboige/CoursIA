import Mathlib

/-!
# GradientFlow.Plain — gradient vanishing in a "plain" stack

English mirror of `GradientFlow/Plain.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`GradientFlow_en` (anti-collision with the FR `GradientFlow` namespace);
non-docstring proof code unchanged.

Submodule of `GradientFlow` (digestion #13106, formalization form — cf CHSH
pilot #14858): a stack of `n` blocks **without shortcut** (the plain
architecture of the notebook `4.2-ConvNet-Profonde-Residuelles`) is the
composition `f_{n-1} ∘ … ∘ f_0`. If every block contracts the derivative
(`|f'_k| ≤ c`), the chain rule and an induction on depth give

    |(f_{n-1} ∘ … ∘ f_0)'| ≤ c ^ n,

and for a strict contraction `c < 1` the bound `c ^ n` tends to `0`: **the
gradient dies exponentially fast with depth**. This is exactly the phenomenon
measured in the notebook (§3): factor ≈ 0.4 per block, hence
`0.4 ^ 20 ≈ 1e-8` after 20 blocks. The numeric anchor
`two_fifths_pow_twenty_lt` locks this course value (`0.4 ^ 20 < 1e-7`).

All proofs are **0-sorry** and elementary (chain rule via `HasDerivAt.comp`,
then product monotonicity): the content of the module is the theorem, not the
tactics.
-/

namespace GradientFlow_en

variable (fs : ℕ → ℝ → ℝ) (c : ℝ)

/-- "Plain" stack of depth `n`: composition of blocks `0, …, n-1`, block `k`
being the function `fs k`. `plainStack fs 0 = id` and
`plainStack fs (n + 1) = fs n ∘ plainStack fs n`. -/
def plainStack (fs : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => fs n ∘ plainStack fs n

/-- **Central lemma**: by induction on depth, the plain stack derives to a
product of block derivatives, with absolute value bounded by `c ^ n` as soon as
every block derives and contracts (`|f'_k| ≤ c`). The derivative value is
carried by `HasDerivAt` so the recursion stays syntactic. -/
theorem plainStack_deriv_bound (hc : 0 ≤ c)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) :
    ∀ n, ∃ d : ℝ, HasDerivAt (plainStack fs n) d x ∧ |d| ≤ c ^ n := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa [plainStack] using hasDerivAt_id x
    · simp
  | succ n ih =>
    obtain ⟨dA, hA, hB⟩ := ih
    have hfd := (hf n (plainStack fs n x)).1
    have hcomp := HasDerivAt.comp x hfd.hasDerivAt hA
    show ∃ d : ℝ, HasDerivAt (fs n ∘ plainStack fs n) d x ∧ |d| ≤ c ^ (n + 1)
    refine ⟨deriv (fs n) (plainStack fs n x) * dA, hcomp, ?_⟩
    have hFs : |deriv (fs n) (plainStack fs n x)| ≤ c := (hf n _).2
    rw [abs_mul, pow_succ, ← mul_comm c (c ^ n)]
    exact (mul_le_mul_of_nonneg_right hFs (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hB hc)

/-- **Gradient vanishing (plain stack)**: if every block contracts the
derivative (`|f'_k| ≤ c`), the derivative of the `n`-block stack is bounded by
`c ^ n`. For `c < 1`, `plainStack_gradient_vanishes` draws the exponential
death. -/
theorem abs_deriv_plainStack_le (hc : 0 ≤ c)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) (n : ℕ) :
    |deriv (plainStack fs n) x| ≤ c ^ n := by
  obtain ⟨d, hA, hB⟩ := plainStack_deriv_bound fs c hc hf x n
  rw [hA.deriv]
  exact hB

/-- **Exponential vanishing**: for a strict contraction `c < 1`, the bound
`c ^ n` tends to `0` — depth kills the gradient geometrically, which the
4.2-ConvNet notebook measures at `c ≈ 0.4` (straight line on a semilog scale). -/
theorem plainStack_gradient_vanishes (hc : 0 ≤ c) (h1 : c < 1) :
    Filter.Tendsto (fun n => c ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rwa [abs_of_nonneg hc])

/-- **Numeric anchor of the course** (notebook
`4.2-ConvNet-Profonde-Residuelles`, §3): at a factor of `0.4` per block, 20
blocks let through less than one ten-millionth of the gradient —
`0.4 ^ 20 ≈ 1.1e-8 < 1e-7`. -/
theorem two_fifths_pow_twenty_lt : (2 / 5 : ℝ) ^ 20 < 1 / 10 ^ 7 := by norm_num

end GradientFlow_en
