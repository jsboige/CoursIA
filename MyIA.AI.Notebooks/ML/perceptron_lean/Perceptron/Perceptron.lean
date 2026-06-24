import Mathlib
import Perceptron.Data

/-!
# Le perceptron et son exécution — vecteur de poids et cadres valides

La règle de mise à jour du perceptron : sur une erreur de classification de
`(xₖ, yₖ)`, le vecteur de poids évolue par
```
w_{k+1} = wₖ + yₖ · xₖ        (w₀ = 0)
```
La suite `perceptronWeights` code cette évolution. Une **exécution valide**
(`PerceptronRun`) enregistre qu'on se place sur `n` mises à jour consécutives,
chacune étant une **erreur** (`yₖ · ⟨wₖ, xₖ⟩ ≤ 0`), sur des données de rayon `R`
séparées par un vecteur unitaire `u` avec marge `γ`.

Ces deux invariants (erreur + marge) sont exactement ce qui fait fonctionner la
preuve de Novikoff : l'erreur plafonne la croissance de `‖w‖`, la marge garantit
celle de `⟨w, u⟩`.
-/

open scoped InnerProductSpace

namespace Perceptron

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- La suite des vecteurs de poids du perceptron après `k` mises à jour :
`w₀ = 0`, `w_{k+1} = wₖ + yₖ · xₖ`. -/
def perceptronWeights (pts : ℕ → V) (lbl : ℕ → ℝ) : ℕ → V
  | 0 => 0
  | k + 1 => perceptronWeights pts lbl k + lbl k • pts k

@[simp]
theorem perceptronWeights_zero (pts : ℕ → V) (lbl : ℕ → ℝ) :
    perceptronWeights pts lbl 0 = 0 :=
  rfl

theorem perceptronWeights_succ (pts : ℕ → V) (lbl : ℕ → ℝ) (k : ℕ) :
    perceptronWeights pts lbl (k + 1) =
      perceptronWeights pts lbl k + lbl k • pts k :=
  rfl

/-- Une **exécution valide du perceptron** sur des données linéairement séparables :
`n` mises à jour consécutives, chacune étant une erreur, sur des points de rayon
`R` séparés par le vecteur unitaire `u` avec marge `γ`. -/
structure PerceptronRun (V : Type*) [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- Nombre de mises à jour (erreurs) considérées. -/
  n : ℕ
  /-- Les points `xₖ` (pertinents pour `k < n`). -/
  pts : ℕ → V
  /-- Les étiquettes `yₖ` (de carré `1`, soit `±1`). -/
  lbl : ℕ → ℝ
  /-- Séparateur unitaire de marge `γ`. -/
  u : V
  /-- Rayon des données (`R ≥ 0`, `‖xₖ‖ ≤ R`). -/
  R : ℝ
  /-- Marge de séparation (`γ > 0`). -/
  γ : ℝ
  /-- Le rayon est non négatif. -/
  hR : 0 ≤ R
  /-- La marge est strictement positive. -/
  hγ : 0 < γ
  /-- Le séparateur est unitaire. -/
  hUnit : ‖u‖ = 1
  /-- Chaque étiquette est `±1`. -/
  hLbl : ∀ k < n, lbl k ^ 2 = 1
  /-- Chaque point est de norme `≤ R`. -/
  hRad : ∀ k < n, ‖pts k‖ ≤ R
  /-- **Marge** : `γ ≤ yₖ · ⟨u, xₖ⟩` (le séparateur classe correctement avec marge). -/
  hMargin : ∀ k < n, γ ≤ lbl k * ⟪u, pts k⟫_ℝ
  /-- **Erreur** : `yₖ · ⟨wₖ, xₖ⟩ ≤ 0` (la k-ième mise à jour est bien une erreur). -/
  hMistake : ∀ k < n, lbl k * ⟪perceptronWeights pts lbl k, pts k⟫_ℝ ≤ 0

namespace PerceptronRun

/-- Le vecteur de poids avant la `k`-ième mise à jour. -/
abbrev w (run : PerceptronRun V) (k : ℕ) : V :=
  perceptronWeights run.pts run.lbl k

end PerceptronRun

end Perceptron
