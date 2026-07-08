import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en
import PacLearning.SampleExpect_en
import PacLearning.UnionBound_en
import PacLearning.MGF_en
import PacLearning.BernoulliMGF_en
import PacLearning.Hoeffding_en

/-!
# PacLearning_en.UniformConcentration — uniform concentration over a finite class
## (iter-2 brick 6/6-agnostic, step a)

EN mirror of `UniformConcentration.lean` (EPIC #4980 i18n). Submodule of `PacLearning_en`:
the **uniform concentration** of the empirical error over a **finite hypothesis class**
`Hs`. This is the key ingredient of the **agnostic** case of the PAC theorem (the
realisable case, `m ≥ (1/ε)(ln|H|+ln(1/δ))`, is delivered in `UnionBound_en.lean` /
`pac_finite_class_bound`, PR #4580).

We prove:

    ℙ_{S∼D^n} [ ∃ h ∈ Hs, |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · |Hs| · exp(−2·n·ε²).

This is the **finite doubling** of the pointwise flagship `hoeffding_concentration` (brick
5/5, `Hoeffding_en.lean`): each `h ∈ Hs` contributes individually `2·exp(−2nε²)` (Hoeffding),
and the union bound `sampleProb_union_bound` (`UnionBound_en.lean`) sums these contributions
over the finite class. The ERM argument (brick 6b, next cycle: `ĥ = argmin empError` ⟹
`trueError ĥ ≤ trueError h* + 2ε`) will bridge the gap to the final agnostic sample-complexity
bound `m ≥ (1/ε²)(ln|H|+ln(1/δ))`.

We stay in the **pedagogical ℝ-weight** style: no `ℝ≥0∞`/`Measure`/`iIndepFun` machinery.

Namespace `PacLearning_en` to avoid collision with the FR canonical. Proof code unchanged;
only docstrings/comments translated FR→EN.
-/

namespace PacLearning_en

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)
variable {D}

/-- **Uniform concentration over a finite hypothesis class** (brick 6/6-agnostic, step a):
for a target concept `f`, a finite class `Hs` of hypotheses, `n ≥ 1` i.i.d. draws and
`ε > 0`, the probability that **there exists** a hypothesis `h ∈ Hs` whose empirical error
deviates from its true error by at least `ε` is bounded by `2 · |Hs| · exp(−2·n·ε²)`.

    ℙ_{S∼D^n} [ ∃ h ∈ Hs, |empError f h S − trueError D f h| ≥ ε ] ≤ 2 · |Hs| · exp(−2·n·ε²).

This is the **finite doubling** of the pointwise flagship (brick 5/5,
`hoeffding_concentration`): each `h ∈ Hs` contributes `2·exp(−2nε²)` (pointwise Hoeffding),
and the union bound `sampleProb_union_bound` (UnionBound_en.lean) sums these contributions
over the finite class.

Proof: `sampleProb_union_bound Hs _` (Boole's inequality) bounds `ℙ[∃]` by
`∑_{h∈Hs} ℙ[|empError−trueError| ≥ ε]`, each term is bounded by `hoeffding_concentration f h`
(`2·exp(−2nε²)`), and then the constant sum factorises into `|Hs| · 2·exp(−2nε²)`
(`Finset.sum_const`).

This is the exact ingredient which, combined with the ERM argument (brick 6b), yields the
**agnostic** PAC sample-complexity bound `m ≥ (1/ε²)(ln|H|+ln(1/δ))` (compare to the
realisable `m ≥ (1/ε)(ln|H|+ln(1/δ))`, where the `1/ε` reflects the geometric concentration
`(1−μ)^n ≤ e^{−εn}` rather than the quadratic Hoeffding concentration). -/
theorem uniform_concentration (f : Hypothesis X) (Hs : Finset (Hypothesis X)) {n : ℕ} (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) ≤
      ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2))) := by
  -- (1) Union bound (Boole's inequality) over the finite class:
  --     ℙ[∃ h ∈ Hs, |empError−trueError| ≥ ε] ≤ ∑_{h∈Hs} ℙ[|empError−trueError| ≥ ε].
  have hunion :
      sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) ≤
        ∑ h ∈ Hs, sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) :=
    sampleProb_union_bound Hs (fun h (S : Fin n → X) ↦ ε ≤ |empError f h S - trueError D f h|)
  -- (2) Each term ≤ 2·exp(−2nε²) (pointwise Hoeffding concentration, brick 5/5).
  have hhoef : ∀ h ∈ Hs,
      sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) ≤
        (2 * Real.exp (-(2 * ↑n * ε ^ 2)) : ℝ) :=
    fun h _ ↦ hoeffding_concentration f h hn hε
  -- (3) Assembly: bound the sum term by term, then factor out the constant.
  calc sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|)
      ≤ ∑ h ∈ Hs, sampleProb D (fun S : Fin n → X ↦ ε ≤ |empError f h S - trueError D f h|) :=
        hunion
    _ ≤ ∑ h ∈ Hs, (2 * Real.exp (-(2 * ↑n * ε ^ 2)) : ℝ) := by
          exact Finset.sum_le_sum hhoef
    _ = ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2))) := by
          -- `Finset.sum_const` gives `card • c`; `ring` (via `ring_nf`) normalises the `nsmul`
          -- into multiplication and closes the goal (`push_cast` is unnecessary, `ring` suffices).
          rw [Finset.sum_const]
          ring

end PacLearning_en
