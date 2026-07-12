import Mathlib
import PacLearning.Data_en

/-!
# PacLearning.ERM — the ERM (Empirical Risk Minimization) argument, agnostic brick 6/6 step b

Submodule of `PacLearning`: the deterministic argument at the heart of **agnostic
generalization**. Given a sample `S`, an ERM hypothesis `ĥ` (which minimizes the
empirical error on `S`) and a reference hypothesis `h* ∈ Hs`, the true error of `ĥ`
is controlled by that of `h*` within `2ε`, **provided uniform concentration holds**
on the class `Hs`:

    trueError D f ĥ ≤ trueError D f h* + 2·ε.

This is a **purely arithmetic** result (4 elementary inequalities chained) — it uses
no probabilistic structure. The role of probability is played by the hypothesis
`hconc : ∀ h ∈ Hs, |empError f h S − trueError D f h| ≤ ε`, which is exactly the
event "uniform concentration holds" — whose violation probability `uniform_concentration`
(UniformConcentration.lean, brick 6a) bounds by `2·|Hs|·exp(−2nε²)`.

Specializing `h*` to the argmin of `trueError` over `Hs` (the best hypothesis in the
class) yields the agnostic generalization bound: the ERM does no worse than `2ε`
beyond the class optimum. Combined with `uniform_concentration`, this gives the
**agnostic** PAC sample complexity `m ≥ (1/ε²)(ln|H|+ln(1/δ))` — to be compared with
the realizable `m ≥ (1/ε)(ln|H|+ln(1/δ))` (delivered in `pac_finite_class_bound`,
PR #4580), where the `1/ε` factor (vs `1/ε²`) reflects geometric concentration
`(1−μ)^n ≤ e^{−εn}` rather than Hoeffding's quadratic concentration.

Inequality chain (the essence of ERM):
1. **Concentration of `ĥ`**: `|empError(ĥ) − trueError(ĥ)| ≤ ε` ⟹ `trueError(ĥ) ≤ empError(ĥ) + ε`.
2. **ERM**: `empError(ĥ) ≤ empError(h*)` (since `ĥ` minimizes `empError` over `Hs`, and `h* ∈ Hs`).
3. **Concentration of `h*`**: `|empError(h*) − trueError(h*)| ≤ ε` ⟹ `empError(h*) ≤ trueError(h*) + ε`.
4. **Combination**: `trueError(ĥ) ≤ empError(ĥ) + ε ≤ empError(h*) + ε ≤ trueError(h*) + 2ε`.

We stay in the **pedagogical ℝ-weight style**: no `ℝ≥0∞`/`Measure`/`iIndepFun` machinery.

English mirror of `PacLearning/ERM.lean` (FR-first canonical), EPIC #4980
(i18n Lean). Convention ratified 2026-07-04 (issue #4980): namespace
`PacLearning_en` (anti-collision with the FR `PacLearning` namespace); cross-module
`_en` imports `_en` (pattern Perceptron_en #5683 / Gittins_en); non-docstring
proof code unchanged.
-/

namespace PacLearning_en

open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **ERM error bound** (agnostic brick 6/6, step b): on the event where uniform
concentration holds over `Hs` (`∀ h ∈ Hs, |empError − trueError| ≤ ε`), an ERM
hypothesis `ĥ` (minimizing the empirical error over `S`) has a true error controlled
by that of any reference hypothesis `h* ∈ Hs`, within `2ε`.

    trueError D f ĥ ≤ trueError D f h* + 2·ε.

Proof (arithmetic, 4 chained inequalities, closed by `linarith`):
1. `|empError(ĥ) − trueError(ĥ)| ≤ ε` ⟹ `trueError(ĥ) ≤ empError(ĥ) + ε` (concentration of `ĥ`).
2. `empError(ĥ) ≤ empError(h*)` (ERM: `ĥ` minimizes `empError`, and `h* ∈ Hs`).
3. `|empError(h*) − trueError(h*)| ≤ ε` ⟹ `empError(h*) ≤ trueError(h*) + ε` (concentration of `h*`).
4. `trueError(ĥ) ≤ empError(ĥ) + ε ≤ empError(h*) + ε ≤ trueError(h*) + 2ε`.

The bounds are extracted from `|a − b| ≤ ε` via `abs_le : |x| ≤ u ↔ -u ≤ x ∧ x ≤ u`.
`linarith` then chains the 4 inequalities without help.

**Agnostic specialization**: taking `h* = argmin_{h∈Hs} trueError D f h` (the best
hypothesis in the class), the bound says the ERM does no worse than `2ε` beyond the
class optimum — the agnostic generalization bound. Combined with `uniform_concentration`
(which bounds the probability that the `hconc` hypothesis fails), this gives the
agnostic PAC sample complexity `m ≥ (1/ε²)(ln|H|+ln(1/δ))`. -/
theorem erm_error_bound (f : Hypothesis X) (Hs : Finset (Hypothesis X)) {n : ℕ} (hn : 0 < n)
    (S : Fin n → X) {ε : ℝ} (hε : 0 < ε)
    (ĥ hOpt : Hypothesis X) (hĥ_mem : ĥ ∈ Hs) (hOpt_mem : hOpt ∈ Hs)
    (hconc : ∀ h ∈ Hs, |empError f h S - trueError D f h| ≤ ε)
    (hĥ_erm : ∀ h ∈ Hs, empError f ĥ S ≤ empError f h S) :
    trueError D f ĥ ≤ trueError D f hOpt + 2 * ε := by
  -- Pointwise concentration of `ĥ` and `hOpt` (instances of the uniform hypothesis `hconc`).
  have hĥ := hconc ĥ hĥ_mem
  have hhOpt := hconc hOpt hOpt_mem
  -- Unfold the absolute values: `|a − b| ≤ ε ⟺ -ε ≤ a−b ∧ a−b ≤ ε`.
  rw [abs_le] at hĥ hhOpt
  -- ERM applied to `hOpt ∈ Hs`: `empError(ĥ) ≤ empError(hOpt)`.
  have heĥ : empError f ĥ S ≤ empError f hOpt S := hĥ_erm hOpt hOpt_mem
  -- Chain of the 4 inequalities (essence of ERM), closed by `linarith`:
  --   trueError(ĥ) ≤ empError(ĥ) + ε ≤ empError(hOpt) + ε ≤ trueError(hOpt) + 2ε.
  linarith [hĥ.1, hhOpt.2, heĥ]

end PacLearning_en
