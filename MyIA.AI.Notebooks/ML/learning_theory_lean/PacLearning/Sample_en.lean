import Mathlib
import PacLearning.Data_en

/-!
# PacLearning.Sample — product distribution over the sample space

Submodule of `PacLearning`: we equip the space of **samples**
`Fin n → X` (sequences of `n` instances drawn i.i.d. from `D`) with a **product
distribution** `D^m`, the discrete counterpart of the tensor product of measures.
This is the probabilistic framework required by the sample-complexity bound
`pac_finite_class_bound` (iteration 2+): concentration of the empirical error
is proved on independent draws `S ∼ D^m`.

We stay in the **pedagogical ℝ-weight style** (no `ℝ≥0∞` / `Measure`):
the weight of a sample `S` is the product of the weights of its components,

    sampleWeight D S = ∏ i : Fin n, D.weight (S i),

and the **normalization** `∑ S, sampleWeight D S = 1` (lemma `sampleWeight_sum_one`)
ensures that `D^m` is indeed a distribution. The proof is the discrete Fubini
identity `(∑ x, w x)^n = ∑ S, ∏ i, w (S i)`, available in Mathlib as
`sum_pow'` (multinomial expansion: product of sums over a finite type).

This deliverable is **brick 1/3** of iter-2: the sample model + its product
distribution. Hoeffding-for-Bernoulli concentration (brick 2/3) and the final
bound `pac_finite_class_bound` (brick 3/3) follow.

English mirror of `PacLearning/Sample.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`PacLearning_en` (anti-collision with the FR `PacLearning` namespace); cross-module
`_en` imports `_en` (pattern decision_theory_lean/Gittins_en, Perceptron_en #5683);
non-docstring proof code unchanged.
-/

namespace PacLearning_en

open Finset

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Weight of a sample** `S : Fin n → X` under the product distribution `D^m`:
product of the weights of its components. This is the discrete counterpart of
the density of the tensor product `D ⊗ … ⊗ D`. -/
def sampleWeight {n : ℕ} (S : Fin n → X) : ℝ :=
  ∏ i : Fin n, D.weight (S i)

variable {D}

/-- The weight of a sample is non-negative: product of non-negative weights
(`D.nonneg`). Empty-sample case `n = 0`: empty product = `1 ≥ 0`. -/
theorem sampleWeight_nonneg {n : ℕ} (S : Fin n → X) : 0 ≤ sampleWeight D S := by
  dsimp only [sampleWeight]
  apply prod_nonneg
  intro i _
  exact D.nonneg (S i)

/-- The total mass of the size-`n` samples is `1`: `D^m` is a distribution.
Discrete Fubini identity `(∑ x, D.weight x)^n = ∑ S, ∏ i, D.weight (S i)`
(Mathlib lemma `sum_pow'`), then `D.sum_one`. -/
theorem sampleWeight_sum_one (n : ℕ) : ∑ S : Fin n → X, sampleWeight D S = 1 := by
  dsimp only [sampleWeight]
  -- Discrete Fubini: (∑ x, w x)^n = ∑ S, ∏ i, w (S i).
  have hfubini : (∑ x, D.weight x) ^ n = ∑ S : Fin n → X, ∏ i, D.weight (S i) := by
    have h := sum_pow' (univ : Finset X) D.weight n
    simpa using h
  rw [← hfubini, D.sum_one, one_pow]

end PacLearning_en
