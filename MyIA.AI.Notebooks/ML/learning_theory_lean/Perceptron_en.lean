import Mathlib
import Perceptron.Data
import Perceptron.Perceptron
import Perceptron.Convergence
import Perceptron.Tightness

/-!
# learning_theory_lean — perceptron convergence (Novikoff's theorem)

Lean 4 lake (Mathlib) at the root of the **ML** series, formalizing the
**perceptron convergence theorem** (Novikoff, 1962): for linearly separable data
with margin `γ > 0` and radius `R`, the perceptron makes at most `(R/γ)²` updates
before finding a correct classifier.

This is the **first Lean theorem of the ML series** (no prior ML Lean lake). The
proof is **elementary geometric and entirely 0-sorry**:
- `Perceptron/Data.lean` — real inner product space, expansion
  `‖a + b‖² = ‖a‖² + 2⟪a,b⟫ + ‖b‖²`, labels `±1`.
- `Perceptron/Perceptron.lean` — weight sequence `perceptronWeights`, structure
  `PerceptronRun` (separable data + mistake trace).
- `Perceptron/Convergence.lean` — Lemma A `⟨wₖ,u⟩ ≥ kγ`, Lemma B `‖wₖ‖² ≤ kR²`,
  Cauchy–Schwarz ⟹ **`novikoff_mistake_bound`**: `n·γ² ≤ R²`.
- `Perceptron/Tightness.lean` — **saturation of the bound**: a concrete witness on
  `ℂ` (`n=2`, `γ=1`, `R=√2`) reaching equality `n·γ² = R²`
  (`novikoff_bound_is_sharp`) ⟹ the `(R/γ)²` bound is optimal.

Reference: A. B. J. Novikoff, *On convergence proofs for perceptrons*, Symposium
on the Mathematical Theory of Automata, Polytechnic Institute of Brooklyn (1962).
See issue #4051 (Lean roadmap #4038).
-/

namespace Perceptron_en

/-- Status: module entirely 0-sorry. `novikoff_mistake_bound` (the `(R/γ)²` bound)
is proved by growth of the alignment + growth of the norm + Cauchy–Schwarz. -/
abbrev Status : Prop := True

end Perceptron_en

/-!
English mirror of `Perceptron.lean` (FR-first canonical), EPIC #4980 (i18n Lean).
Convention ratified 2026-07-04 (issue #4980): distinct FR + EN sibling files in the
same lake; namespace `Perceptron_en` (anti-collision with the FR `Perceptron`
namespace); non-docstring proof code unchanged.
-/
