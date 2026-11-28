/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/

import Discrepancy.Komlos.Approximation_en
import Discrepancy.Komlos.Discrepancy_en
/-! # From grids to real matrices

Adapted from Gabriel Dahia, `Komlos/Main.lean` at `d802857`
(blob `e2700e76aa87e93f1dc231d896cd38cd4fe0dade`), Apache-2.0;
the bound is generalized to an arbitrary constant C and its grid hypothesis
is explicit. The license text is in `LICENSE-Apache-2.0.txt` at the lake root.

A hypothetical uniform bound on all grids with a common denominator transfers
to real matrices without loss in the constant. This result does not itself
provide the grid bound: the Komlós proof remains open at this stage.
-/

namespace Discrepancy.Komlos_en

open Finset Matrix

/-- A uniform bound for grid matrices with the same Euclidean column norm
transfers to real matrices without loss in the constant. -/
theorem discrepancy_le_of_grid_bound {d n : ℕ} {C : ℝ}
    (hgrid : ∀ (N : ℕ), 0 < N → ∀ (g : Fin n → Fin d → ℤ),
      (∀ j, ∑ i, ((g j i : ℝ) / N) ^ 2 ≤ 1) →
      discrepancy (Matrix.of fun (i : Fin d) (j : Fin n) ↦ (g j i : ℝ) / N) ≤ C)
    (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : ∀ j, ∑ i, A i j ^ 2 ≤ 1) : discrepancy A ≤ C := by
  refine le_of_forall_pos_le_add ?_
  intro η hη
  obtain ⟨N, g, hN, happ1, happ2⟩ :=
    exists_grid_approx (fun j i => A i j) (by positivity : 0 < η / (n + 1))
  set B := Matrix.of fun (i : Fin d) (j : Fin n) ↦ (g j i : ℝ) / N
  have hnorm (j) : ∑ i, ((g j i : ℝ) / N) ^ 2 ≤ 1 := by
    refine (sum_le_sum ?_).trans (hA j)
    intro i _
    exact sq_le_sq.2 (happ1 j i)
  obtain ⟨ε, hε, hB⟩ := discrepancy_le_iff.1 (hgrid N hN g hnorm)
  refine discrepancy_le_iff.2 ⟨ε, hε, ?_⟩
  rw [← add_sub_cancel B A]
  refine (colouringDiscrepancy_add_le _ _ _).trans (add_le_add hB ?_)
  refine (colouringDiscrepancy_le_of_abs_le hε
    (c := η / (n + 1)) (by positivity) ?_).trans ?_
  · intro i j
    simpa [B] using happ2 j i
  · rw [Fintype.card_fin, mul_div_assoc', div_le_iff₀ (by positivity)]
    linarith

/-- Bridge consumer: a grid bound yields a real colouring. -/
theorem exists_colouring_of_grid_bound {d n : ℕ} {C : ℝ}
    (hgrid : ∀ (N : ℕ), 0 < N → ∀ (g : Fin n → Fin d → ℤ),
      (∀ j, ∑ i, ((g j i : ℝ) / N) ^ 2 ≤ 1) →
      discrepancy (Matrix.of fun (i : Fin d) (j : Fin n) ↦ (g j i : ℝ) / N) ≤ C)
    (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : ∀ j, ∑ i, A i j ^ 2 ≤ 1) :
    ∃ χ, IsColouring χ ∧ colouringDiscrepancy A χ ≤ C := by
  exact discrepancy_le_iff.mp (discrepancy_le_of_grid_bound hgrid A hA)

end Discrepancy.Komlos_en
