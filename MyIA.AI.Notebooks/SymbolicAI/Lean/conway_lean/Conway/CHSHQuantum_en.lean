/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## CHSH inequality: Tsirelson's quantum bound

This module is the third slice of the quantum pilot from Epic #13106. The
first two bounded the **classical** frontier (`Conway.CHSH`) and then its
**randomized** envelope (`Conway.CHSHRandomized`). This one takes the
algebraic step: in a real ordered star-algebra, the CHSH score of a quadruple
of self-adjoint involutive observables commuting in cross pairs is bounded by
`2√2`, no longer by `2`.

That second bound is not reproved here. It is **imported together with its
kernel proof** from Mathlib (`Mathlib.Algebra.Star.CHSH.tsirelson_inequality`,
Kim Morrison), which establishes it by sum-of-squares decomposition.
Reproving the SOS argument would be heavy formalization work with no
pedagogical payoff: what this module contributes is the **hypothesis map** —
stating exactly what the theorem requires, in which usual form it is phrased,
and where the boundary runs between what is proved here, what is imported, and
what remains open.

### Status of the statements (digestion grid #13106)

| Statement | Status |
|---|---|
| Deterministic classical frontier (`\|score\| = 2`) | **proved locally** — `Conway.CHSH` |
| Randomized classical frontier (`\|expectedScore\| ≤ 2`) | **proved locally** — `Conway.CHSHRandomized` |
| Quantum bound `2√2` under ordered star-algebra hypotheses | **imported**, Mathlib kernel proof |
| Scalar rewriting `√2 ^ 3 = 2 * √2` and gap `2 < 2√2` | **proved here** |
| Saturation of `2√2` by a quantum state | **not established** in this slice |
| Matrix / Pauli construction | **not established** in this slice |
| Full probabilistic interpretation of a quantum state | **not established** in this slice |
| Two-sided bound in operator norm | **not established** in this slice |

The absence of these last four points is **declared**, not papered over: the
bound established here is a *one-sided* upper bound `≤ 2√2`, and this module
contains no witness exhibiting equality. That is precisely the limit the next
slice must lift if it is to prove that `2√2` is **attained**.

### Dependencies and axioms

The axiomatization of `tsirelson_bound` exhibits only the standard Mathlib
axioms (`propext`, `Classical.choice`, `Quot.sound`): the module introduces
**no `sorry`**, neither directly nor transitively through
`tsirelson_inequality`. The boolean `Classical.choice` is non-constructive but
legitimate here — Mathlib uses it in its own proof, and whitelisting it by
explicit name is the repository's accepted practice.

### Discovery path and final reconstruction

The path followed by this slice is: (1) check the exact signature of the
Mathlib theorem at pin v4.32.1; (2) establish the scalar rewriting and the
numeric gap separately; (3) assemble the generic bridge under the exact
hypotheses; (4) only then expose the usual form `2√2`. A
`simpa using tsirelson_inequality` without a hypothesis map would have produced
a toy wrapper: it would have named no hypothesis, exposed no `2√2`, and made no
classical/quantum gap inspectable. The final reconstruction is therefore kept
separate from the discovery path, and both are readable here.

### Sources

- J. F. Clauser, M. A. Horne, A. Shimony, R. A. Holt,
  "Proposed Experiment to Test Local Hidden-Variable Theories",
  Physical Review Letters 23 (1969), 880-884.
- B. S. Tsirelson, "Quantum generalizations of Bell's inequality",
  Letters in Mathematical Physics 4 (1980), 93-100.

### Connections within the series

- `Lean-13-Kochen-Specker.ipynb`: another obstruction to classical agreement,
  but combinatorial in nature (vector colorability) rather than analytic like
  Tsirelson's bound.
- `Lean-16f-Conway-Free-Will-Theorem.ipynb`: the Conway-Kochen free will
  theorem, which exploits the same frontier between classical and quantum
  correlations.
- `Lean-13b-CHSH-Tsirelson-Native.ipynb`: the native notebook **planned** for this
  slice (Epic #13106), which will execute the statements of this module under the
  `lean4-wsl` kernel. It is not delivered yet: this reference is prospective, not
  an existing file.
-/

import Conway.CHSH_en
import Conway.CHSHRandomized_en
import Mathlib.Algebra.Star.CHSH

namespace Conway_en
namespace CHSHQuantum_en

/-- The noncommutative CHSH operator of a quadruple `(A₀, A₁, B₀, B₁)`:
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`.

This pedagogical name does not duplicate Mathlib's `IsCHSHTuple` structure,
which remains the entry point for the hypotheses; it merely gives a readable
name to the expression that both bounds dominate. -/
def chshOperator {R : Type*} [Ring R] (A₀ A₁ B₀ B₁ : R) : R :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

/-- Scalar rewriting: `√2 ^ 3 = 2 * √2`.

Mathlib states the bound with the scalar `√2 ^ 3`; the usual form in physics
is `2√2`. This equality is the bridge between the two writings, and it is what
makes the bound readable without rewriting Mathlib's proof. -/
theorem sqrt_two_cubed : (√2 : ℝ) ^ 3 = 2 * √2 := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc (√2 : ℝ) ^ 3 = (√2 : ℝ) ^ 2 * √2 := by ring
    _ = 2 * √2 := by rw [h2]

/-- Strict numeric gap between the classical bound `2` and the quantum bound
`2√2`.

This is the only separation witness this slice can exhibit without fabricating
an absent matrix construction: the classical bound `2` is **strictly** below
`2√2`, so the interval `(2, 2√2]` is non-empty. What the module does not prove
is that a quantum system **attains** the upper end of that interval. -/
theorem classical_quantum_gap : (2 : ℝ) < 2 * √2 := by
  have h : (1 : ℝ) < √2 := Real.one_lt_sqrt_two
  linarith

/-- Deterministic classical frontier, transported into `ℝ`.

`Conway.CHSH.classical_bound` is stated over `ℤ`; comparing it with the
quantum bound `2√2`, which lives in `ℝ`, requires transporting it. This is the
form used by the comparative table
`deterministic classical / randomized classical / quantum`. -/
theorem classical_deterministic_bound_real (a₀ a₁ b₀ b₁ : CHSH_en.Outcome) :
    ((|CHSH_en.score a₀ a₁ b₀ b₁| : ℤ) : ℝ) ≤ 2 := by
  exact_mod_cast CHSH_en.classical_bound a₀ a₁ b₀ b₁

/-- Randomized classical frontier, transported into `ℝ`.

Same transport as above, from `Conway.CHSHRandomized.randomized_bound` which
lives in `ℚ`. -/
theorem classical_randomized_bound_real (μ : CHSHRandomized_en.Strategy)
    (h_nonneg : ∀ p, 0 ≤ μ p)
    (h_total : (∑ p : CHSHRandomized_en.Profile, μ p) = 1) :
    ((|CHSHRandomized_en.expectedScore μ| : ℚ) : ℝ) ≤ 2 := by
  exact_mod_cast CHSHRandomized_en.randomized_bound μ h_nonneg h_total

/-- **Tsirelson's bound**, in its usual form.

For every real ordered star-algebra `R` and every quadruple
`(A₀, A₁, B₀, B₁)` forming an `IsCHSHTuple`, the CHSH score is bounded by
`2√2 • 1`.

The hypotheses restate those of
`Mathlib.Algebra.Star.CHSH.tsirelson_inequality`: `[Ring R] [PartialOrder R]
[StarRing R] [StarOrderedRing R] [Algebra ℝ R] [IsOrderedModule ℝ R]
[StarModule ℝ R]`. The direction "no hypothesis removed" is pinned by
elaboration: strengthening the upstream signature would make the `have` below
fail. The direction "no hypothesis added" is guarded by no instrument — an
upstream weakening would leave this theorem compiling with a now-superfluous
hypothesis, and the list above would become false in silence. That is why it is
stated as a restatement, not as a guaranteed equality.
The proof applies the Mathlib theorem, then transports the scalar rewriting
established in this module. -/
theorem tsirelson_bound {R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOperator A₀ A₁ B₀ B₁ ≤ (2 * √2) • (1 : R) := by
  have h := tsirelson_inequality A₀ A₁ B₀ B₁ T
  rw [sqrt_two_cubed] at h
  simpa only [chshOperator] using h

end CHSHQuantum_en
end Conway_en
