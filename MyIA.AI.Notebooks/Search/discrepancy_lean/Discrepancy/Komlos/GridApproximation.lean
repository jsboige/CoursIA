/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/

import Discrepancy.Komlos.Approximation
import Discrepancy.Komlos.Discrepancy
/-! # De la grille aux matrices réelles

Adapté de Gabriel Dahia, `Komlos/Main.lean` à `d802857`
(blob `e2700e76aa87e93f1dc231d896cd38cd4fe0dade`), Apache-2.0 ;
la borne est généralisée à une constante C arbitraire et son hypothèse
sur grille est explicite. Le texte de licence est dans `LICENSE-Apache-2.0.txt`
à la racine du lac.

Une borne uniforme hypothétique sur toutes les grilles à dénominateur commun
se transporte aux matrices réelles sans perte sur la constante. Ce résultat
ne fournit pas lui-même la borne de grille : la preuve de Komlós reste ouverte
à ce stade du lac.
-/

namespace Discrepancy.Komlos

open Finset Matrix

/-- Une borne uniforme sur les matrices de grille, avec la même norme euclidienne
des colonnes, passe aux matrices réelles sans perte sur la constante. -/
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

/-- Consommateur du pont : une borne de grille fournit une coloration réelle. -/
theorem exists_colouring_of_grid_bound {d n : ℕ} {C : ℝ}
    (hgrid : ∀ (N : ℕ), 0 < N → ∀ (g : Fin n → Fin d → ℤ),
      (∀ j, ∑ i, ((g j i : ℝ) / N) ^ 2 ≤ 1) →
      discrepancy (Matrix.of fun (i : Fin d) (j : Fin n) ↦ (g j i : ℝ) / N) ≤ C)
    (A : Matrix (Fin d) (Fin n) ℝ)
    (hA : ∀ j, ∑ i, A i j ^ 2 ≤ 1) :
    ∃ χ, IsColouring χ ∧ colouringDiscrepancy A χ ≤ C := by
  exact discrepancy_le_iff.mp (discrepancy_le_of_grid_bound hgrid A hA)

end Discrepancy.Komlos
