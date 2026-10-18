import Mathlib

/-!
# Erreur LMMSE — Phase 3 : Lemme 5.1 (identité trace), avec Mathlib

Ce module prouve le **Lemme 5.1** du papier de détection MIMO
(Papailiopoulos, 2026 — issue #10984) : l'erreur quadratique moyenne de
l'estimateur LMMSE est la trace de la matrice d'erreur

    E‖b − x*‖² = tr(B_ρ),   B_ρ = (I_N + s·HᵀH)⁻¹,   s = ρ/N.

Architecture du fichier :

1. `integral_norm_sq_eq_trace` — la **formule de la trace gaussienne** :
   pour une gaussienne centrée de covariance `B` (semi-définie positive),
   l'espérance de la norme au carré est `tr B`. C'est le cœur du lemme ;
2. `B_ρ` — la matrice d'erreur LMMSE du canal : `(I + s·HᴴH)⁻¹` ;
3. `B_ρ_posSemidef` — `B_ρ` est bien semi-définie positive (`s ≥ 0`),
   condition sous laquelle la gaussienne associée existe ;
4. `lmmse_error_eq_trace` — **Lemme 5.1** : tout champ d'erreur dont la loi
   est la gaussienne centrée de covariance `B_ρ` a une énergie moyenne
   `E‖e‖² = tr B_ρ`.
-/

namespace Mimo

open Matrix MeasureTheory ProbabilityTheory

section Trace

/-- Formule de la trace gaussienne : pour une gaussienne centrée de
covariance `B`, l'espérance de la norme au carré vaut `tr B`. Chaque
coordonnée contribue sa variance `B i i` (la moyenne étant nulle). -/
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

/-- La matrice d'erreur LMMSE du canal : `B_ρ = (I + s·HᴴH)⁻¹`
(papier : `B_ρ = (I_N + (ρ/N)·HᵀH)⁻¹` avec `s = ρ/N`). -/
noncomputable def B_ρ (H : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  ((1 : Matrix (Fin N) (Fin N) ℝ) + s • (Hᴴ * H))⁻¹

/-- La matrice d'erreur `B_ρ` est semi-définie positive dès que `s ≥ 0` :
`HᴴH` est toujours PSD, `I + s·HᴴH` aussi, et l'inverse d'une PSD est PSD. -/
theorem B_ρ_posSemidef (H : Matrix (Fin N) (Fin N) ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (B_ρ H s).PosSemidef := by
  have hH : (Hᴴ * H).PosSemidef := posSemidef_conjTranspose_mul_self H
  have hadd : ((1 : Matrix (Fin N) (Fin N) ℝ) + s • (Hᴴ * H)).PosSemidef :=
    Matrix.PosSemidef.one.add (hH.smul hs)
  exact Matrix.PosSemidef.inv hadd

/-- **Lemme 5.1 (Papailiopoulos 2026) — erreur LMMSE.** Si le champ d'erreur
d'estimation `e = b − x*` suit la loi gaussienne centrée de covariance
`B_ρ = (I + s·HᴴH)⁻¹` — la matrice d'erreur LMMSE du canal à SNR par antenne
`s = ρ/N` — alors son erreur quadratique moyenne est exactement la trace :

    E‖b − x*‖² = tr(B_ρ).

La preuve combine la formule de la trace gaussienne
(`integral_norm_sq_eq_trace`) avec le transport de la loi de `e`. -/
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

end Mimo
