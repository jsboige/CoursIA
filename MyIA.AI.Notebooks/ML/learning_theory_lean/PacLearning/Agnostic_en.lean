import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en
import PacLearning.SampleExpect_en
import PacLearning.UnionBound_en
import PacLearning.MGF_en
import PacLearning.BernoulliMGF_en
import PacLearning.Hoeffding_en
import PacLearning.UniformConcentration_en
import PacLearning.ERM_en

/-!
# PacLearning_en.Agnostic — agnostic PAC generalisation bound (flagship iter-2)
## assembly uniform_concentration + erm_error_bound

EN mirror of `Agnostic.lean` (EPIC #4980 i18n). Submodule of `PacLearning_en`: the
**agnostic flagship** of iteration 2 — the PAC generalisation bound for a finite hypothesis
class `Hs` in the **agnostic** regime (the target hypothesis `f` is not necessarily in `Hs`).
We prove that, for an ERM `ĥ` (selected as a function of the sample `S`) and any reference
hypothesis `hOpt ∈ Hs`,

    ℙ_{S∼D^n} [ trueError D f (ĥ S) ≤ trueError D f hOpt + 2·ε ] ≥ 1 − 2·|Hs|·exp(−2·n·ε²).

This is the **agnostic generalisation bound**: with probability ≥ 1−δ over the sample, the
true error of the ERM does not exceed that of the best hypothesis in the class by more than
`2ε`. By specialising `hOpt` to `argmin_{h∈Hs} trueError D f h` (the best of the class), this
yields the standard generalisation theorem. Inverting `1−δ = 1−2|Hs|exp(−2nε²)`, one obtains
the **agnostic** PAC sample complexity `m ≥ (1/ε²)(ln|H|+ln(1/δ))` — compare to the realisable
`m ≥ (1/ε)(ln|H|+ln(1/δ))` (`pac_finite_class_bound`, PR #4580), where the `1/ε` factor (vs
`1/ε²`) reflects the geometric concentration `(1−μ)^n ≤ e^{−εn}` rather than the quadratic
Hoeffding concentration.

**Assembly** (both ingredients are delivered on main):
1. `uniform_concentration` (UniformConcentration_en.lean, brick 6a) bounds the probability
   of the "bad" event (there exists a poorly-concentrated hypothesis):
   `ℙ[∃ h ∈ Hs, ε ≤ |empError − trueError|] ≤ 2·|Hs|·exp(−2nε²)`.
2. `erm_error_bound` (ERM_en.lean, brick 6b) is the deterministic argument: on the "good"
   event (`∀ h ∈ Hs, |empError − trueError| ≤ ε`), the ERM generalises:
   `trueError(ĥ) ≤ trueError(hOpt) + 2ε`.
3. This module connects the two: by contrapositive of `erm_error_bound`, the event
   `trueError(ĥ) > trueError(hOpt) + 2ε` implies `∃ h ∈ Hs, ε < |empError − trueError|`
   (uniform concentration failed), which is contained in the event bounded by
   `uniform_concentration`. Hence `ℙ[trueError(ĥ) > ...] ≤ 2|Hs|exp(...)`, and by passing to
   the complement `ℙ[trueError(ĥ) ≤ ...] ≥ 1 − 2|Hs|exp(...)`.

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

/-- **Monotonicity of `sampleProb` under event inclusion**: if `P S ⟹ Q S` for every sample
`S`, then `ℙ[P] ≤ ℙ[Q]` (the indicator `𝟙_P ≤ 𝟙_Q` pointwise, then monotonicity of the
weighted sum). Used by `pac_agnostic_generalization` to lift the inclusion
`{bad conclusion} ⊆ {bad uniform concentration}` to a probability inequality. -/
theorem sampleProb_mono {n : ℕ} (P Q : (Fin n → X) → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ S, P S → Q S) : sampleProb D P ≤ sampleProb D Q := by
  -- Indicator `𝟙_P ≤ 𝟙_Q` pointwise (the only `if`, isolated outside the sums).
  have hind : ∀ S : Fin n → X,
      (if P S then (1 : ℝ) else 0) ≤ (if Q S then (1 : ℝ) else 0) := by
    intro S
    by_cases hP : P S
    · -- `P S` ⟹ `Q S` (by `h`) ⟹ `𝟙_P = 1 = 𝟙_Q`.
      have hQ : Q S := h S hP
      simp [hP, hQ]
    · -- `¬ P S` ⟹ `𝟙_P = 0 ≤ 𝟙_Q` (indicator `≤ 1`).
      by_cases hQ : Q S <;> simp [hP, hQ]
  -- Assembly: multiply the indicator inequality by the weight `≥ 0` (pointwise),
  -- then monotonicity of the weighted sum.
  dsimp only [sampleProb]
  exact sum_le_sum (fun S _ ↦ mul_le_mul_of_nonneg_left (hind S) (sampleWeight_nonneg (D := D) S))

/-- **Agnostic flagship — PAC generalisation bound** (iter-2 capstone): for `n ≥ 1` i.i.d.
draws and `ε > 0`, an ERM `ĥ` (selected as a function of the sample `S`, minimising the
empirical error over `Hs`) has true error controlled by that of any reference hypothesis
`hOpt ∈ Hs`, to within `2ε`, **with high probability** over the sample:

    ℙ_{S∼D^n} [ trueError D f (ĥ S) ≤ trueError D f hOpt + 2·ε ] ≥ 1 − 2·|Hs|·exp(−2·n·ε²).

**Specialisation**: taking `hOpt = argmin_{h∈Hs} trueError D f h` (the best hypothesis of the
class), the bound says that the ERM is no more than `2ε` worse than the optimum of the class,
with probability ≥ 1−δ — the standard agnostic generalisation theorem. Inverting
`δ = 2·|Hs|·exp(−2·n·ε²)`, one obtains the **agnostic** PAC sample complexity
`m ≥ (1/ε²)(ln|H|+ln(1/δ))`.

**Modelling the ERM**: `ĥ : (Fin n → X) → Hypothesis X` is a selection function (given each
sample `S`, it returns an ERM hypothesis on `S`), with the two natural hypotheses `hĥ_mem`
(the ERM is in the class) and `hĥ_erm` (it minimises the empirical error). We need not
construct the argmin (existence via `Finset` is delegated) — we reason about any ERM
selection.

Proof (assembly of `uniform_concentration` + `erm_error_bound`):
1. **Contrapositive of the ERM**: on the "bad conclusion" event `trueError(ĥ S) >
   trueError(hOpt) + 2ε`, uniform concentration must have failed, i.e.
   `∃ h ∈ Hs, ε ≤ |empError − trueError|` (otherwise `erm_error_bound` would give the
   conclusion). This is the inclusion `{bad conclusion} ⊆ {bad concentration}`.
2. **Monotonicity** (`sampleProb_mono`): `ℙ[bad conclusion] ≤ ℙ[bad concentration]`.
3. **Uniform concentration** (`uniform_concentration`): `ℙ[bad concentration] ≤ 2|Hs|exp(...)`.
4. **Complement** (`sampleProb_compl`): `ℙ[good conclusion] = 1 − ℙ[bad conclusion] ≥ 1 − 2|Hs|exp(...)`. -/
theorem pac_agnostic_generalization (f : Hypothesis X) (Hs : Finset (Hypothesis X)) {n : ℕ}
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (ĥ : (Fin n → X) → Hypothesis X) (hOpt : Hypothesis X) (hOpt_mem : hOpt ∈ Hs)
    (hĥ_mem : ∀ S, ĥ S ∈ Hs)
    (hĥ_erm : ∀ S, ∀ h ∈ Hs, empError f (ĥ S) S ≤ empError f h S) :
    1 - ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2))) ≤
      sampleProb D (fun S : Fin n → X ↦ trueError D f (ĥ S) ≤ trueError D f hOpt + 2 * ε) := by
  -- (1) Contrapositive of the ERM: "bad conclusion" ⟹ "bad concentration".
  --   If `trueError(ĥ) > trueError(hOpt)+2ε`, then uniform concentration has failed
  --   (otherwise `erm_error_bound` would be contradicted). Hence `∃ h ∈ Hs, ε ≤ |empError−trueError|`.
  have hcontra : ∀ S : Fin n → X,
      (trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) →
        ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h| := by
    intro S hbad
    -- By contradiction: assume uniform concentration holds over all of `Hs`.
    by_contra hno
    -- `hno : ¬(∃ h ∈ Hs, ε ≤ |...|)`. We deduce `∀ h ∈ Hs, |...| ≤ ε` (concentration).
    have hconc : ∀ h ∈ Hs, |empError f h S - trueError D f h| ≤ ε := by
      intro h hHs
      -- `¬(ε ≤ |...|)` ⟺ `|...| < ε` (via `not_le`) ⟹ `|...| ≤ ε`.
      have : ¬(ε ≤ |empError f h S - trueError D f h|) := by
        intro hh; exact hno ⟨h, hHs, hh⟩
      linarith [not_le.mp this]
    -- `erm_error_bound` (brick 6b): on the good event, `trueError(ĥ) ≤ trueError(hOpt)+2ε`.
    have herb := erm_error_bound f Hs hn S hε (ĥ S) hOpt (hĥ_mem S) hOpt_mem hconc (hĥ_erm S)
    -- Contradiction with `hbad : trueError(hOpt)+2ε < trueError(ĥ)`.
    linarith
  -- (2) Monotonicity: `ℙ[bad conclusion] ≤ ℙ[bad concentration]`.
  --   We give the type to the `have` because `D` (implicit section variable of `sampleProb_mono`)
  --   appears only in the conclusion, not in the `P`/`Q` args — hence not synthesisable
  --   from the predicates alone; the provided type allows `D` to unify.
  have hmono :
      sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) ≤
        sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) :=
    sampleProb_mono _ _ hcontra
  -- `C = 2|Hs|exp(...)` the bound.
  set C : ℝ := ↑Hs.card * (2 * Real.exp (-(2 * ↑n * ε ^ 2)))
  -- (3) Uniform concentration (brick 6a): `ℙ[bad concentration] ≤ C`.
  --   `uniform_concentration` has `D` implicit (section var) and the predicate `∃ h ∈ Hs, ...`
  --   is frozen in its statement — so we pass ONLY `f Hs hn hε`. Explicit type on the `have`
  --   to unify `D` (not synthesisable from the `f Hs hn hε` args alone).
  have hunif :
      sampleProb D (fun S : Fin n → X ↦ ∃ h ∈ Hs, ε ≤ |empError f h S - trueError D f h|) ≤ C :=
    uniform_concentration f Hs hn hε
  -- (4) Complement: `ℙ[¬(bad conclusion)] = 1 − ℙ[bad conclusion]` (`sampleProb_compl`).
  --   The good conclusion `trueError(ĥ S) ≤ ...` is exactly `¬(bad conclusion)`.
  have hcompl :
      sampleProb D (fun S : Fin n → X ↦ ¬(trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S))) =
        1 - sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) :=
    sampleProb_compl _
  -- Assembly: `ℙ[bad conclusion] ≤ ℙ[bad concentration] ≤ C`, hence
  -- `ℙ[good conclusion] = 1 − ℙ[bad conclusion] ≥ 1 − C`.
  have hbad_le_C :
      sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) ≤ C :=
    le_trans hmono hunif
  -- `ℙ[good] = 1 − ℙ[bad] ≥ 1 − C` (final arithmetic):
  --   `¬bad ↔ good` pointwise (`not_le`), hence `sampleProb_congr` transports the probabilities.
  calc 1 - C
      ≤ 1 - sampleProb D (fun S : Fin n → X ↦ trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S)) := by
            linarith [hbad_le_C]
    _ = sampleProb D (fun S : Fin n → X ↦ ¬(trueError D f (hOpt) + 2 * ε < trueError D f (ĥ S))) :=
          hcompl.symm
    _ = sampleProb D (fun S : Fin n → X ↦ trueError D f (ĥ S) ≤ trueError D f hOpt + 2 * ε) :=
          sampleProb_congr _ _ (fun S ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩)

end PacLearning_en
