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

/-! ## Propriétés de base des prédicats `Admissible` / `Consistent`

Lemmas compagnons fondateurs (companion lemmas, issue #4048) : propriétés élémentaires
des deux prédicats centraux. On établit notamment la **connexion à Dijkstra** : avec
l'heuristique nulle `h ≡ 0`, A* se réduit à l'algorithme de Dijkstra (recherche à coût
uniforme) — fait standard des manuels (Russell & Norvig, §3.5). Tous prouvés 0 `sorry`. -/

/-- **Monotonie de l'admissibilité.** Une heuristique majorée partout par une
    heuristique admissible est elle-même admissible. Combinateur réutilisable : pour
    « raboter » une heuristique trop optimiste en restant admissible. -/
theorem admissible_mono (h₁ h₂ hStar : V → NNReal) (hle : ∀ n, h₁ n ≤ h₂ n)
    (hadm : Admissible h₂ hStar) : Admissible h₁ hStar :=
  fun n => le_trans (hle n) (hadm n)

/-- **Fermeture par le minimum.** Le minimum ponctuel de deux heuristiques admissibles
    est admissible. C'est la base théorique de la combinaison d'heuristiques : prendre
    `min` de plusieurs heuristiques admissibles préserve l'admissibilité (et l'optimalité
    de A* qui en découle). -/
theorem admissible_min (h₁ h₂ hStar : V → NNReal) (hA : Admissible h₁ hStar)
    (_hB : Admissible h₂ hStar) : Admissible (fun n => min (h₁ n) (h₂ n)) hStar :=
  fun n => le_trans (min_le_left (h₁ n) (h₂ n)) (hA n)

/-- **L'heuristique parfaite est admissible.** Le « vrai coût optimal restant » `hStar`
    est lui-même admissible (borne supérieure de l'ensemble des heuristiques admissibles,
    au sens où toute admissible le minore). -/
theorem hStar_admissible (hStar : V → NNReal) : Admissible hStar hStar :=
  fun _ => le_rfl

/-- **Connexion à Dijkstra (admissibilité).** L'heuristique nulle `h ≡ 0` est
    admissible (`0 ≤ hStar` partout, trivial en `NNReal` ≡ ℝ≥0). A* avec heuristique
    nulle se réduit à la recherche à coût uniforme (Dijkstra). -/
theorem zero_admissible (hStar : V → NNReal) : Admissible (fun _ => (0 : NNReal)) hStar :=
  fun _ => zero_le

/-- **Connexion à Dijkstra (consistance).** L'heuristique nulle `h ≡ 0` est consistante
    (`0 ≤ edge + 0` partout, trivial en `NNReal`). Le compagnon de `zero_admissible`. -/
theorem zero_consistent : Consistent G (fun _ => (0 : NNReal)) :=
  fun _ _ => zero_le

end Astar
