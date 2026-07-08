import Mathlib

/-!
# Astar.Graph — graphes pondérés, chemins, coût d'un chemin

Modèle abstrait pour la preuve d'optimalité de A* (issue #4048). Un graphe orienté
pondéré à arêtes non-négatives (`NNReal` ≡ ℝ≥0), des chemins vus comme des listes de
sommets, et le coût d'un chemin comme somme des poids des arcs consécutifs.
-/

namespace Astar

/- Sommets abstraits : `V` est le type des sommets, paramètre du modèle. -/
variable {V : Type*}

/-- Graphe orienté pondéré : `edge a b` est le coût non-négatif de l'arc `a → b`.
    La valeur `0` signifie « pas d'arc » (ou boucle triviale). L'hypothèse de
    non-négativité (`NNReal`) est exactement l'hypothèse requise pour l'optimalité
    de A*. -/
structure WeightedGraph (V : Type*) where
  /-- Poids (non-négatif) de chaque arc orienté. -/
  edge : V → V → NNReal

variable (G : WeightedGraph V)

/-- Un chemin est une liste de sommets consécutifs. -/
abbrev Path (V : Type*) := List V

/-- Coût d'un chemin = somme des poids des arcs consécutifs.

    `pathCost [] = 0`, `pathCost [v] = 0` (un sommet seul n'a pas d'arc),
    `pathCost [v₀, v₁, v₂, ...] = edge v₀ v₁ + edge v₁ v₂ + ...`. -/
def pathCost : Path V → NNReal
  | [] => 0
  | [_] => 0
  | v₀ :: v₁ :: rest => G.edge v₀ v₁ + pathCost (v₁ :: rest)

@[simp]
theorem pathCost_nil : pathCost G ([] : Path V) = 0 := rfl

@[simp]
theorem pathCost_singleton (v : V) : pathCost G [v] = 0 := rfl

@[simp]
theorem pathCost_cons_cons (v₀ v₁ : V) (rest : Path V) :
    pathCost G (v₀ :: v₁ :: rest) = G.edge v₀ v₁ + pathCost G (v₁ :: rest) := rfl

/-- Un chemin `p` va de `start` à `goal` : il est non-vide, son premier sommet est
    `start` et son dernier sommet est `goal`. -/
def PathFrom (start goal : V) (p : Path V) : Prop :=
  p ≠ [] ∧ p.head? = some start ∧ p.getLast? = some goal

end Astar
