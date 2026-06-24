import Mathlib
import Perceptron.Data
import Perceptron.Perceptron
import Perceptron.Convergence

/-!
# perceptron_lean — convergence du Perceptron (théorème de Novikoff)

Lake Lean 4 (Mathlib) à la racine de la série **ML**, formalisant le **théorème de
convergence du Perceptron** (Novikoff, 1962) : pour des données linéairement
séparables de marge `γ > 0` et de rayon `R`, le perceptron effectue au plus
`(R/γ)²` mises à jour avant de trouver un classifieur correct.

C'est le **premier théorème Lean de la série ML** (aucun lake Lean en ML auparavant).
La preuve est **géométrique élémentaire et entièrement 0-sorry** :
- `Perceptron/Data.lean` — espace préhilbertien réel, développement
  `‖a + b‖² = ‖a‖² + 2⟪a,b⟫ + ‖b‖²`, étiquettes `±1`.
- `Perceptron/Perceptron.lean` — suite des poids `perceptronWeights`, structure
  `PerceptronRun` (données séparables + trace d'erreurs).
- `Perceptron/Convergence.lean` — Lemme A `⟨wₖ,u⟩ ≥ kγ`, Lemme B `‖wₖ‖² ≤ kR²`,
  Cauchy–Schwarz ⟹ **`novikoff_mistake_bound`** : `n·γ² ≤ R²`.

Référence : A. B. J. Novikoff, *On convergence proofs for perceptrons*, Symposium
on the Mathematical Theory of Automata, Polytechnic Institute of Brooklyn (1962).
Voir l'issue #4051 (roadmap Lean #4038).
-/

namespace Perceptron

/-- Statut : module entièrement 0-sorry. `novikoff_mistake_bound` (borne `(R/γ)²`)
est prouvé par croissance de l'alignement + croissance de la norme + Cauchy–Schwarz. -/
abbrev Status : Prop := True

end Perceptron
