import Mathlib
import PacLearning.Data_en
import PacLearning.Sample_en
import PacLearning.SampleExpect_en

/-!
# PacLearning.UnionBound — sample probability + union bound (Boole's inequality)

Submodule of `PacLearning`: the **combinatorial half** of the flagship
`pac_finite_class_bound`. We define the **probability of an event** over the
sample space `Fin n → X` (under the product distribution `D^m`) and prove the
**union bound** (Boole's inequality) over a finite class of hypotheses.

    sampleProb D (Q : (Fin n → X) → Prop) := ∑ S, sampleWeight D S · 𝟙{Q S}

The union bound states that the probability of a union of events is **bounded
above** by the sum of the probabilities:

    ℙ_S [ ∃ h ∈ H, Q h S ] ≤ ∑_{h ∈ H} ℙ_S [ Q h S ].

This is the combinatorial ingredient of Valiant's bound: to bound the probability
that **at least one** hypothesis of `H` deviates from its true error, we sum the
deviation probabilities (each bounded by Hoeffding, brick 2c/3-concentration,
still OPEN). The flagship `pac_finite_class_bound` (brick 3/3) combines the
`union_bound` below with a generic Hoeffding concentration.

We stay in the **pedagogical ℝ-weight style** (no `ℝ≥0∞` / `Measure`): the
indicator `𝟙{Q S}` is `if Q S then (1 : ℝ) else 0`, and the probability is a
weighted sum (the expectation of the indicator, `sampleExpect D (𝟙 ∘ Q)`).
-/

namespace PacLearning_en

open Finset
open scoped Classical

variable {X : Type*} [Fintype X]
variable (D : Distribution X)

/-- **Probability of an event** over the sample space `Fin n → X` under `D^m`:
weighted sum of the indicator `𝟙{Q S}`. This is the empirical expectation of the
indicator of `Q` (cf `sampleExpect`). The domain `Fin n → X` of `Q` pins `n`. -/
noncomputable def sampleProb {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] : ℝ :=
  ∑ S : Fin n → X, sampleWeight D S * (if Q S then (1 : ℝ) else 0)

variable {D}

/-- Link with `sampleExpect`: the probability of `Q` is the empirical expectation
of the indicator `𝟙{Q}`. Bridge between probability (measure) and expectation
(linear). -/
theorem sampleProb_eq_sampleExpect {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] :
    sampleProb D Q = sampleExpect D (fun S ↦ if Q S then (1 : ℝ) else 0) := by
  rfl

/-- The probability is non-negative (sum of weights `≥ 0` times `0` or `1`). -/
theorem sampleProb_nonneg {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] :
    0 ≤ sampleProb D Q := by
  dsimp only [sampleProb]
  apply sum_nonneg
  intro S _
  exact mul_nonneg (sampleWeight_nonneg (D := D) S) (by
    by_cases h : Q S <;> simp [h])

/-- The probability is at most `1` (total mass of samples `= 1` by
`sampleWeight_sum_one`, and each indicator is `≤ 1`). -/
theorem sampleProb_le_one {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q] :
    sampleProb D Q ≤ 1 := by
  dsimp only [sampleProb]
  have h_le : ∀ S, sampleWeight D S * (if Q S then (1 : ℝ) else 0) ≤ sampleWeight D S := by
    intro S
    by_cases h : Q S
    · simp [h]
    · simp [h]; exact sampleWeight_nonneg (D := D) S
  calc ∑ S : Fin n → X, sampleWeight D S * (if Q S then (1 : ℝ) else 0)
      ≤ ∑ S : Fin n → X, sampleWeight D S := sum_le_sum (fun S _ ↦ h_le S)
    _ = 1 := sampleWeight_sum_one n

/-- **Probability of the complement**: `ℙ[¬Q] = 1 − ℙ[Q]` (the indicator of the
complement is `1 − 𝟙{Q}`, and `E[1] = 1` by `sampleExpect_const`). -/
theorem sampleProb_compl {n : ℕ} (Q : (Fin n → X) → Prop) [DecidablePred Q]
    [DecidablePred (fun S ↦ ¬ Q S)] :
    sampleProb D (fun S ↦ ¬ Q S) = 1 - sampleProb D Q := by
  -- Indicator of the complement = `1 − indicator` pointwise.
  have hind : ∀ S : Fin n → X,
      sampleWeight D S * (if ¬ Q S then (1 : ℝ) else 0) =
        sampleWeight D S * 1 - sampleWeight D S * (if Q S then (1 : ℝ) else 0) := by
    intro S
    by_cases h : Q S <;> simp [h]
  dsimp only [sampleProb]
  rw [Finset.sum_congr rfl (fun S _ ↦ hind S), Finset.sum_sub_distrib,
      ← Finset.sum_mul, sampleWeight_sum_one, one_mul]

/-- **Linearity over a Finset-indexed sum**: the empirical expectation of a sum
indexed by a `Finset` is the sum of the expectations (like `sampleExpect_sum` but
over `s : Finset ι` rather than over all of `ι`). No `Decidable` instance involved
(`F : ι → ℝ`, we do not manipulate indicators). -/
theorem sampleExpect_finset_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (s : Finset ι) (F : ι → ((Fin n → X) → ℝ)) :
    sampleExpect D (fun S ↦ ∑ i ∈ s, F i S) = ∑ i ∈ s, sampleExpect D (F i) := by
  dsimp only [sampleExpect]
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- **Union bound (Boole's inequality)** over a `Finset`-indexed family: the
probability that a sample `S` satisfies `P i S` for **at least one** `i ∈ s` is
bounded above by the sum of the probabilities `ℙ[P i]`.

Proof: pointwise, the indicator `𝟙{∃ i ∈ s, P i S}` is `≤ ∑_i 𝟙{P i S}` (if a
witness `i₀` exists, it contributes `1` to the sum, and the other terms are
`≥ 0`; otherwise the indicator is `0`). We then go through `sampleExpect`:
`ℙ[∃] = E[𝟙_{∃}] ≤ E[∑ 𝟙_{P i}]` (monotonicity) `= ∑ E[𝟙_{P i}]` (Finset
linearity) `= ∑ ℙ[P i]`. Monotonicity isolates the only indicator (`if`) in a
`have`, outside the sum calc — avoiding `Decidable` instance friction inside the
weighted sums. -/
theorem sampleProb_union_bound {n : ℕ} {ι : Type*} [Fintype ι] (s : Finset ι) [DecidableEq ι]
    (P : ι → ((Fin n → X) → Prop)) :
    sampleProb D (fun S ↦ ∃ i ∈ s, P i S) ≤ ∑ i ∈ s, sampleProb D (P i) := by
  -- `open scoped Classical` (namespace header) provides `Decidable` for every
  -- predicate: decidability is a computational detail, not a mathematical one
  -- (the probability of an event does not depend on deciding the predicate). This
  -- is the standard Mathlib idiom for probabilistic results.
  -- Indicator(∃) ≤ ∑ indicators(P i), pointwise (the only `if` of the proof).
  have hind_le : ∀ S : Fin n → X,
      (if ∃ i ∈ s, P i S then (1 : ℝ) else 0) ≤ ∑ i ∈ s, (if P i S then 1 else 0) := by
    intro S
    by_cases h : ∃ i ∈ s, P i S
    · -- A witness `i₀` exists: it contributes `1` to the sum, the others `≥ 0`.
      obtain ⟨i₀, hi₀, hPi₀⟩ := h
      -- All indicators are `≥ 0`.
      have hge : ∀ i ∈ s, 0 ≤ (if P i S then (1 : ℝ) else 0) := fun i _ ↦ by
        by_cases hpi : P i S <;> simp [hpi]
      calc (if ∃ i ∈ s, P i S then (1 : ℝ) else 0)
          = 1 := if_pos ⟨i₀, hi₀, hPi₀⟩
        _ = (if P i₀ S then 1 else 0) := (if_pos hPi₀).symm
        _ ≤ ∑ i ∈ s, (if P i S then 1 else 0) := Finset.single_le_sum hge hi₀
    · -- No witness: indicator(∃) = `0 ≤` sum (of terms `≥ 0`).
      simp only [if_neg h]
      exact sum_nonneg (fun i _ ↦ by by_cases hpi : P i S <;> simp [hpi])
  -- Assembly via `sampleExpect` (monotonicity + Finset linearity), with no `if`
  -- inside the weighted sums.
  calc sampleProb D (fun S ↦ ∃ i ∈ s, P i S)
      = sampleExpect D (fun S ↦ (if ∃ i ∈ s, P i S then (1 : ℝ) else 0)) :=
          sampleProb_eq_sampleExpect _
    _ ≤ sampleExpect D (fun S ↦ ∑ i ∈ s, (if P i S then (1 : ℝ) else 0)) :=
        sampleExpect_mono hind_le
    _ = ∑ i ∈ s, sampleExpect D (fun S ↦ (if P i S then (1 : ℝ) else 0)) :=
        sampleExpect_finset_sum s _
    _ = ∑ i ∈ s, sampleProb D (P i) := by
          exact Finset.sum_congr rfl (fun i _ ↦ (sampleProb_eq_sampleExpect (P i)).symm)

end PacLearning_en
