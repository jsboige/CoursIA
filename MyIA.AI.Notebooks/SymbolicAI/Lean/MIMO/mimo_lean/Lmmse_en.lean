import Mathlib

/-!
# LMMSE error — Phase 3: Lemma 5.1 (trace identity), with Mathlib

This module proves **Lemma 5.1** of the MIMO detection paper
(Papailiopoulos, 2026 — issue #10984): the mean squared error of the
LMMSE estimator is the trace of the error matrix

    E‖b − x*‖² = tr(B_ρ),   B_ρ = (I_N + s·HᵀH)⁻¹,   s = ρ/N.

File architecture:

1. `integral_norm_sq_eq_trace` — the **gaussian trace formula**: for a
   centered gaussian with covariance `B` (positive semidefinite), the
   expected squared norm is `tr B`. This is the core of the lemma;
2. `B_ρ` — the channel LMMSE error matrix: `(I + s·HᴴH)⁻¹`;
3. `B_ρ_posSemidef` — `B_ρ` is positive semidefinite (for `s ≥ 0`),
   the condition under which the associated gaussian exists;
4. `lmmse_error_eq_trace` — **Lemma 5.1**: any error field whose law is
   the centered gaussian with covariance `B_ρ` has mean energy
   `E‖e‖² = tr B_ρ`.
-/

namespace Mimo_en

open Matrix MeasureTheory ProbabilityTheory

section Trace

/-- Gaussian trace formula: for a centered gaussian with covariance `B`,
the expected squared norm equals `tr B`. Each coordinate contributes its
variance `B i i` (the mean being zero). -/
theorem integral_norm_sq_eq_trace {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) :
    ∫ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 ∂(multivariateGaussian 0 B)
      = B.trace := by
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := fun x => by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]; simp
  have hint : ∀ i : Fin n,
      ∫ x : EuclideanSpace ℝ (Fin n), (x i) ^ 2 ∂(multivariateGaussian 0 B) = B i i := by
    intro i
    have hmp := measurePreserving_eval_multivariateGaussian (μ := 0) hB (i := i)
    have hinteg : Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2)
        (multivariateGaussian 0 B) := by
      have h2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 (B i i).toNNReal) :=
        IsGaussian.memLp_two_id
      have h5 := h2.comp_measurePreserving hmp
      simpa [Function.comp_def, id_eq] using h5.integrable_sq
    have hE0 : (multivariateGaussian 0 B)[fun x : EuclideanSpace ℝ (Fin n) => x i] = 0 := by
      have h6 : (multivariateGaussian 0 B)[fun x : EuclideanSpace ℝ (Fin n) => x i]
          = ∫ y : ℝ, y ∂(Measure.map (fun x : EuclideanSpace ℝ (Fin n) => x i)
              (multivariateGaussian 0 B)) := by
        symm
        exact integral_map (by fun_prop) (by fun_prop)
      rw [h6, hmp.map_eq, integral_id_gaussianReal]
      simp
    have hvar := variance_eq_integral (μ := multivariateGaussian 0 B)
      (X := fun x : EuclideanSpace ℝ (Fin n) => x i) (by fun_prop)
    rw [hE0] at hvar
    simp only [sub_zero] at hvar
    rw [← hvar, variance_eval_multivariateGaussian (μ := 0) hB i]
  have hinteg' : ∀ i : Fin n, Integrable (fun x : EuclideanSpace ℝ (Fin n) => (x i) ^ 2)
      (multivariateGaussian 0 B) := by
    intro i
    have hmp := measurePreserving_eval_multivariateGaussian (μ := 0) hB (i := i)
    have h2 : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 (B i i).toNNReal) :=
      IsGaussian.memLp_two_id
    have h5 := h2.comp_measurePreserving hmp
    simpa [Function.comp_def, id_eq] using h5.integrable_sq
  simp only [hnorm]
  rw [integral_finsetSum (hf := fun i _ => hinteg' i)]
  simp only [hint]
  rfl

end Trace

section LMMSE

variable {N : ℕ}

/-- The channel LMMSE error matrix: `B_ρ = (I + s·HᴴH)⁻¹`
(paper: `B_ρ = (I_N + (ρ/N)·HᵀH)⁻¹` with `s = ρ/N`). -/
noncomputable def B_ρ (H : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  ((1 : Matrix (Fin N) (Fin N) ℝ) + s • (Hᴴ * H))⁻¹

/-- The error matrix `B_ρ` is positive semidefinite whenever `s ≥ 0`:
`HᴴH` is always PSD, so is `I + s·HᴴH`, and the inverse of a PSD matrix
is PSD. -/
theorem B_ρ_posSemidef (H : Matrix (Fin N) (Fin N) ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (B_ρ H s).PosSemidef := by
  have hH : (Hᴴ * H).PosSemidef := posSemidef_conjTranspose_mul_self H
  have hadd : ((1 : Matrix (Fin N) (Fin N) ℝ) + s • (Hᴴ * H)).PosSemidef :=
    Matrix.PosSemidef.one.add (hH.smul hs)
  exact Matrix.PosSemidef.inv hadd

/-- **Lemma 5.1 (Papailiopoulos 2026) — LMMSE error.** If the estimation
error field `e = b − x*` follows the centered gaussian law with covariance
`B_ρ = (I + s·HᴴH)⁻¹` — the LMMSE error matrix of the channel at per-antenna
SNR `s = ρ/N` — then its mean squared error is exactly the trace:

    E‖b − x*‖² = tr(B_ρ).

The proof combines the gaussian trace formula
(`integral_norm_sq_eq_trace`) with the transport of the law of `e`. -/
theorem lmmse_error_eq_trace {Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    {s : ℝ} (hs : 0 ≤ s) (e : Ω → EuclideanSpace ℝ (Fin N))
    (he : AEMeasurable e μ)
    (hdist : Measure.map e μ = multivariateGaussian 0 (B_ρ H s)) :
    μ[fun ω => ‖e ω‖ ^ 2] = (B_ρ H s).trace := by
  rw [← integral_map he (by fun_prop : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin N) => ‖y‖ ^ 2) (Measure.map e μ)), hdist]
  exact integral_norm_sq_eq_trace (B_ρ_posSemidef H hs)

end LMMSE

end Mimo_en
