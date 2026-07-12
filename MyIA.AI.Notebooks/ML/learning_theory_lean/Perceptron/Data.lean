import Mathlib

/-!
# Données du perceptron — espace préhilbertien réel, points, étiquettes

Le théorème de Novikoff (1962) se démontre dans un **espace préhilbertien réel
abstrait** `V` (la borne `(R/γ)²` est indépendante de la dimension). Ce fichier
rassemble les faits géométriques élémentaires sur la norme et le produit scalaire
nécessaires à la preuve, en particulier le développement
`‖a + b‖² = ‖a‖² + 2·⟪a, b⟫ + ‖b‖²` qui est le cœur du Lemme B (croissance de la
norme du vecteur de poids).

Les données elles-mêmes (suite de points `xₖ`, étiquettes `yₖ ∈ {±1}`, séparateur
unitaire `u` de marge `γ`, rayon `R`) sont modélisées dans `Perceptron.lean` par la
structure `PerceptronRun`.
-/

open scoped InnerProductSpace

namespace Perceptron

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `‖x‖² = ⟪x, x⟫_ℝ` — le carré de la norme coïncide avec l'auto-produit scalaire. -/
theorem norm_sq_eq_inner_self (x : V) : ‖x‖ ^ 2 = ⟪x, x⟫_ℝ :=
  (real_inner_self_eq_norm_sq x).symm

/-- Développement du carré de la norme d'une somme :
`‖a + b‖² = ‖a‖² + 2·⟪a, b⟫ + ‖b‖²`. Identité centrale du Lemme B de Novikoff. -/
theorem norm_add_sq_eq (a b : V) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := by
  rw [norm_sq_eq_inner_self (a + b), real_inner_add_add_self,
      ← norm_sq_eq_inner_self a, ← norm_sq_eq_inner_self b]

/-- Une **étiquette** est un scalaire réel de carré `1` (autrement dit `±1`). -/
abbrev IsLabel (y : ℝ) : Prop :=
  y ^ 2 = 1

/-- Un point étiqueté : un vecteur `x ∈ V` et son étiquette `y ∈ {±1}`. -/
structure LabeledPoint where
  /-- Le vecteur (point de l'espace). -/
  x : V
  /-- L'étiquette (`±1`). -/
  y : ℝ

end Perceptron
