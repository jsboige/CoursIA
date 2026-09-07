import Mathlib

/-!
# GradientFlow.Residual — gradient survival in a residual stack

English mirror of `GradientFlow/Residual.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`GradientFlow_en`; non-docstring proof code unchanged.

Submodule of `GradientFlow` (digestion #13106, formalization form): every
block of the stack is now a **residual block** `h ↦ h + f h` — the identity
shortcut of He, Zhang, Ren & Sun (*Deep Residual Learning for Image
Recognition*, arXiv:1512.03385, 2015). If every branch contracts the derivative
(`|f'_k| ≤ c` with `c ≤ 1`), the `+1` of the shortcut changes the game: each
block's derivative is `1 + f'_k`, of modulus at least `1 - c > 0`, and the
induction on depth gives

    (1 - c) ^ n ≤ |(g_{n-1} ∘ … ∘ g_0)'|,

the gradient **survives** geometrically instead of dying. At equal branch
contraction `c = 0.4`, the gap with the plain stack is three orders of
magnitude at depth 20: `0.6 ^ 20 ≈ 3.7e-5` versus `0.4 ^ 20 ≈ 1.1e-8` —
numeric anchors `three_fifths_pow_twenty_gt` and
`GradientFlow.two_fifths_pow_twenty_lt`.

The lower bound rests on the reverse triangle inequality derived from
`abs_add_le` (`1 - |t| ≤ |1 + t|`). All proofs are **0-sorry**.
-/

namespace GradientFlow_en

variable (fs : ℕ → ℝ → ℝ) (c : ℝ)

/-- Residual block (identity shortcut, He et al. 2016): `h ↦ h + f h`. Its
derivative at a point is `1 + f'`, of modulus at least `1 - |f'|`. -/
def residualBlock (f : ℝ → ℝ) : ℝ → ℝ := fun h => h + f h

/-- **Reverse triangle inequality (residual-block form)**: the `+1` of the
shortcut guarantees `1 - |t| ≤ |1 + t|` — a residual block's derivative cannot
drop below `1 - c` when the branch contracts at `|f'| ≤ c`. -/
theorem one_sub_le_abs_add (t : ℝ) : 1 - |t| ≤ |1 + t| := by
  have h : (1 : ℝ) ≤ |1 + t| + |t| := by
    simpa using abs_add_le (1 + t) (-t)
  linarith

/-- Residual stack of depth `n`: composition of residual blocks built on
`fs 0, …, fs (n-1)`. `residualStack fs 0 = id` and
`residualStack fs (n + 1) = residualBlock (fs n) ∘ residualStack fs n`. -/
def residualStack (fs : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => id
  | n + 1 => residualBlock (fs n) ∘ residualStack fs n

/-- **Central lemma**: by induction on depth, the residual stack derives to a
product whose modulus is **bounded below** by `(1 - c) ^ n` as soon as every
branch derives and contracts (`|f'_k| ≤ c`, `c ≤ 1`). -/
theorem residualStack_deriv_bound (hc1 : c ≤ 1)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) :
    ∀ n, ∃ d : ℝ, HasDerivAt (residualStack fs n) d x ∧ (1 - c) ^ n ≤ |d| := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa [residualStack] using hasDerivAt_id x
    · simp
  | succ n ih =>
    obtain ⟨dA, hA, hB⟩ := ih
    have hfd := (hf n (residualStack fs n x)).1
    have hBlock : HasDerivAt (residualBlock (fs n))
        (1 + deriv (fs n) (residualStack fs n x)) (residualStack fs n x) :=
      (hasDerivAt_id _).add hfd.hasDerivAt
    have hcomp := HasDerivAt.comp x hBlock hA
    show ∃ d : ℝ, HasDerivAt (residualBlock (fs n) ∘ residualStack fs n) d x ∧
      (1 - c) ^ (n + 1) ≤ |d|
    refine ⟨(1 + deriv (fs n) (residualStack fs n x)) * dA, hcomp, ?_⟩
    have hFs : |deriv (fs n) (residualStack fs n x)| ≤ c := (hf n _).2
    have hLow : 1 - c ≤ |1 + deriv (fs n) (residualStack fs n x)| :=
      (sub_le_sub_left hFs 1).trans (one_sub_le_abs_add _)
    have hc0 : 0 ≤ 1 - c := sub_nonneg.mpr hc1
    rw [abs_mul, pow_succ, ← mul_comm (1 - c) ((1 - c) ^ n)]
    calc (1 - c) * (1 - c) ^ n
        ≤ |1 + deriv (fs n) (residualStack fs n x)| * (1 - c) ^ n :=
          mul_le_mul_of_nonneg_right hLow (pow_nonneg hc0 n)
      _ ≤ |1 + deriv (fs n) (residualStack fs n x)| * |dA| :=
          mul_le_mul_of_nonneg_left hB (abs_nonneg _)

/-- **Gradient survival (residual stack)**: if every branch contracts the
derivative (`|f'_k| ≤ c`, `c ≤ 1`), the derivative of the `n`-block stack is
**bounded below** by `(1 - c) ^ n` — the identity shortcut prevents the plain
stack's exponential vanishing (`abs_deriv_plainStack_le`). -/
theorem abs_deriv_residualStack_ge (hc1 : c ≤ 1)
    (hf : ∀ k x, DifferentiableAt ℝ (fs k) x ∧ |deriv (fs k) x| ≤ c) (x : ℝ) (n : ℕ) :
    (1 - c) ^ n ≤ |deriv (residualStack fs n) x| := by
  obtain ⟨d, hA, hB⟩ := residualStack_deriv_bound fs c hc1 hf x n
  rw [hA.deriv]
  exact hB

/-- **Twin numeric anchor** (notebook `4.2-ConvNet-Profonde-Residuelles`, §6):
at equal branch contraction `c = 0.4`, the residual stack lets through at
least `0.6 ^ 20 ≈ 3.7e-5` — three orders of magnitude above the plain stack
(`0.4 ^ 20 ≈ 1.1e-8`, see `GradientFlow.two_fifths_pow_twenty_lt`). -/
theorem three_fifths_pow_twenty_gt : 3 / 10 ^ 5 < (3 / 5 : ℝ) ^ 20 := by norm_num

end GradientFlow_en
