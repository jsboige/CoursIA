import Mathlib
import Perceptron.Perceptron

/-!
# Théorème de convergence du Perceptron (Novikoff, 1962) — borne `(R/γ)²`

> **Théorème (Novikoff).** Soit une exécution valide du perceptron sur des données
> linéairement séparables par un vecteur unitaire `u` avec marge `γ > 0`, les points
> étant de norme `≤ R`. Alors le nombre de mises à jour (erreurs) `n` vérifie
> `n ≤ (R/γ)²`.

La preuve, **géométrique élémentaire et entièrement 0-sorry**, repose sur deux
inégalités de croissance du vecteur de poids `wₖ` combinées par Cauchy–Schwarz :

- **Lemme A — alignement** (`align_growth`) : `⟪wₖ, u⟫ ≥ k·γ`.
  Chaque erreur ajoute `yₖ · xₖ` à `w`, et l'hypothèse de marge garantit
  `yₖ · ⟪u, xₖ⟫ ≥ γ`, donc l'alignement sur le séparateur croît d'au moins `γ`.
- **Lemme B — norme** (`norm_bound`) : `‖wₖ‖² ≤ k·R²`.
  Chaque erreur ajoute au plus `R²` à `‖w‖²` (via le développement
  `‖a + b‖² = ‖a‖² + 2⟪a,b⟫ + ‖b‖²`), le terme croisé étant `≤ 0` car la mise à
  jour est une erreur (`yₖ · ⟪wₖ, xₖ⟫ ≤ 0`).
- **Conclusion** : Cauchy–Schwarz `⟪wₙ, u⟫ ≤ ‖wₙ‖·‖u‖ = ‖wₙ‖` (avec `‖u‖ = 1`)
  donne `n·γ ≤ ‖wₙ‖`, donc `(n·γ)² ≤ ‖wₙ‖² ≤ n·R²`, i.e. `n·γ² ≤ R²`.

Référence : A. B. J. Novikoff, *On convergence proofs for perceptrons*, Symposium
on the Mathematical Theory of Automata (1962).
-/

open scoped InnerProductSpace

namespace Perceptron

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

open PerceptronRun

/-- **Lemme A — croissance de l'alignement** : après `k ≤ n` mises à jour,
`⟪wₖ, u⟫ ≥ k·γ` (chaque erreur aligne `w` d'au moins la marge `γ` sur `u`). -/
theorem PerceptronRun.align_growth (run : PerceptronRun V) :
    ∀ k ≤ run.n,
      (k : ℝ) * run.γ ≤ ⟪perceptronWeights run.pts run.lbl k, run.u⟫_ℝ := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [perceptronWeights_zero, inner_zero_left, Nat.cast_zero]
    linarith
  | succ k ih =>
    intro hk
    have hkn : k < run.n := Nat.lt_of_succ_le hk
    have hstep : run.γ ≤ run.lbl k * ⟪run.u, run.pts k⟫_ℝ := run.hMargin k hkn
    have hih : (k : ℝ) * run.γ ≤ ⟪perceptronWeights run.pts run.lbl k, run.u⟫_ℝ :=
      ih (Nat.le_of_succ_le hk)
    rw [perceptronWeights_succ run.pts run.lbl k, inner_add_left,
        real_inner_smul_left, real_inner_comm run.u (run.pts k), Nat.cast_add_one]
    linarith

/-- **Lemme B — croissance de la norme** : après `k ≤ n` mises à jour,
`‖wₖ‖² ≤ k·R²` (chaque erreur ajoute au plus `R²` à `‖w‖²`). -/
theorem PerceptronRun.norm_bound (run : PerceptronRun V) :
    ∀ k ≤ run.n,
      ‖perceptronWeights run.pts run.lbl k‖ ^ 2 ≤ (k : ℝ) * run.R ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [perceptronWeights_zero, norm_zero]
    -- But `0 ≤ ↑0 * run.R²` : produit de non-négatifs (`↑0 ≥ 0`, `run.R² ≥ 0`).
    nlinarith [sq_nonneg run.R]
  | succ k ih =>
    intro hk
    have hkn : k < run.n := Nat.lt_of_succ_le hk
    have hih : ‖perceptronWeights run.pts run.lbl k‖ ^ 2 ≤ (k : ℝ) * run.R ^ 2 :=
      ih (Nat.le_of_succ_le hk)
    -- Décomposition du carré de la norme d'une somme.
    have hCross : ⟪perceptronWeights run.pts run.lbl k, run.lbl k • run.pts k⟫_ℝ ≤ 0 := by
      rw [real_inner_smul_right]
      exact run.hMistake k hkn
    have hLbl2 : run.lbl k ^ 2 = 1 := run.hLbl k hkn
    have hRad : ‖run.pts k‖ ≤ run.R := run.hRad k hkn
    have hRad2 : ‖run.pts k‖ ^ 2 ≤ run.R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) run.hR).mpr hRad
    have hSc2 : ‖run.lbl k • run.pts k‖ ^ 2 ≤ run.R ^ 2 := by
      have hexp : ‖run.lbl k • run.pts k‖ ^ 2 = run.lbl k ^ 2 * ‖run.pts k‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [hexp, hLbl2, one_mul]
      exact hRad2
    rw [perceptronWeights_succ run.pts run.lbl k, norm_add_sq_eq]
    -- Linarith ne voit pas `↑(k+1)·R²` comme `↑k·R² + R²` (produit d'atomes) :
    -- on lui fournit l'égalité expansée comme hypothèse.
    have hRHS : (k + 1 : ℝ) * run.R ^ 2 = (k : ℝ) * run.R ^ 2 + run.R ^ 2 := by ring
    simp only [Nat.cast_add_one]
    linarith

/-- **Théorème de convergence du Perceptron (Novikoff, 1962)** : le nombre de
mises à jour `n` d'une exécution valide sur des données de rayon `R` séparées avec
marge `γ` vérifie la borne `n · γ² ≤ R²`, i.e. `n ≤ (R/γ)²`. -/
theorem PerceptronRun.novikoff_mistake_bound (run : PerceptronRun V) :
    (run.n : ℝ) * run.γ ^ 2 ≤ run.R ^ 2 := by
  -- Lemme A en `k = n`.
  have hAlign : (run.n : ℝ) * run.γ ≤
      ⟪perceptronWeights run.pts run.lbl run.n, run.u⟫_ℝ :=
    run.align_growth run.n (Nat.le_refl run.n)
  -- Lemme B en `k = n`.
  have hNorm : ‖perceptronWeights run.pts run.lbl run.n‖ ^ 2 ≤ (run.n : ℝ) * run.R ^ 2 :=
    run.norm_bound run.n (Nat.le_refl run.n)
  -- Cauchy–Schwarz : ⟪wₙ, u⟫ ≤ ‖wₙ‖·‖u‖ = ‖wₙ‖.
  have hCS : ⟪perceptronWeights run.pts run.lbl run.n, run.u⟫_ℝ ≤
      ‖perceptronWeights run.pts run.lbl run.n‖ := by
    have hle := real_inner_le_norm (perceptronWeights run.pts run.lbl run.n) run.u
    rw [run.hUnit] at hle
    linarith
  -- n·γ ≤ ‖wₙ‖, puis (n·γ)² ≤ ‖wₙ‖² ≤ n·R².
  have hNG : (run.n : ℝ) * run.γ ≤ ‖perceptronWeights run.pts run.lbl run.n‖ :=
    le_trans hAlign hCS
  have hNG2 : ((run.n : ℝ) * run.γ) ^ 2 ≤ ‖perceptronWeights run.pts run.lbl run.n‖ ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) (le_of_lt run.hγ)) (norm_nonneg _)).mpr hNG
  have hKey : ((run.n : ℝ) * run.γ) ^ 2 ≤ (run.n : ℝ) * run.R ^ 2 :=
    le_trans hNG2 hNorm
  -- Conclusion : (n·γ)² ≤ n·R²  ⟹  n·γ² ≤ R²  (cas n = 0 trivial ; n ≥ 1 on simplifie par n).
  rcases Nat.eq_zero_or_pos run.n with hz | hpos
  · -- n = 0 : 0·γ² ≤ R² trivial.
    rw [hz, Nat.cast_zero, zero_mul]
    exact sq_nonneg run.R
  · -- n > 0 : on simplifie par n (strictement positif).
    have hnpos : (0 : ℝ) < run.n := Nat.cast_pos.mpr hpos
    have hkey' : (run.n : ℝ) * ((run.n : ℝ) * run.γ ^ 2) ≤ (run.n : ℝ) * run.R ^ 2 := by
      have hexp : ((run.n : ℝ) * run.γ) ^ 2 = (run.n : ℝ) ^ 2 * run.γ ^ 2 := by
        rw [mul_pow]
      rw [hexp, pow_two, mul_assoc] at hKey
      exact hKey
    exact (mul_le_mul_iff_of_pos_left hnpos).mp hkey'

end Perceptron
