import Mathlib
import Astar.Graph

/-!
# Astar.Heuristic — admissibilité et consistance

Définitions centrales de A*. Soit `hStar : V → NNReal` le « vrai coût optimal
restant » (le coût minimal pour atteindre le but depuis chaque sommet). Une
heuristique `h : V → NNReal` est :

- **admissible** si `h n ≤ hStar n` pour tout sommet `n` : elle ne surestime
  jamais le coût optimal restant ;
- **consistante** (ou monotone) si `h n ≤ edge n n' + h n'` pour tout arc
  `n → n'` : c'est la « relaxation » de l'équation de Bellman (programmation
  dynamique). La consistance implique l'admissibilité (voir `Optimality.lean`).

`hStar` reste ici abstrait ; sa propriété caractéristique de borne inférieure
sur le coût des chemins menant au but est énoncée dans `Optimality.lean`
(`IsTrueRemainingCost`). Pour un graphe fini, `hStar` se construit comme le minimum
des coûts des chemins simples menant au but (minimum atteint, car les chemins
simples sont en nombre fini).
-/

namespace Astar

variable {V : Type*} (G : WeightedGraph V)

/-- Heuristique **admissible** : ne surestime jamais `hStar` (le vrai coût optimal
    restant). Hypothèse clé pour l'optimalité de A*. -/
def Admissible (h hStar : V → NNReal) : Prop :=
  ∀ n : V, h n ≤ hStar n

/-- Heuristique **consistante** (monotone) : relaxation de l'équation de Bellman le
    long de chaque arc. La consistance implique l'admissibilité
    (`consistent_implies_admissible`), et garantit en outre que la fonction `f = g + h`
    est croissante le long des chemins, donc qu'A* ne ré-expande jamais un nœud. -/
def Consistent (h : V → NNReal) : Prop :=
  ∀ n n' : V, h n ≤ G.edge n n' + h n'

end Astar
