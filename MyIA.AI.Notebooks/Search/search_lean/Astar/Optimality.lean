import Mathlib
import Astar.Graph
import Astar.Heuristic

/-!
# Astar.Optimality — borne en `f` (lemme abstrait : borne de suffixe)

Brique de la série (issue #4048, registre #3801 — prong B « problème non-trivial »).
On prouve la **borne en `f`** : sous une heuristique admissible, pour tout nœud
`p.get i` d'un chemin `p` allant au but, `h(p.get i)` ne dépasse jamais le coût du
suffixe restant `pathCost (p.drop i)`. C'est le cœur mathématique de l'argument
d'optimalité de A* (Hart, Nilsson & Raphael, 1968) — mais **seulement ce cœur**,
sous forme abstraite.

Le lake ne modélise **pas** l'algorithme A* (ni file de priorité, ni ensemble fermé,
ni chemin retourné) : il n'y a donc **aucun théorème d'optimalité d'A*** ici. La
garantie « heuristique admissible ⇒ A* renvoie un chemin de coût optimal » — **fausse**
pour la variante Graph-Search sans ré-ouverture (cf #14824) — n'est pas prouvée.

`hStar` est un « vrai coût optimal restant » : propriété de borne inférieure
`IsTrueRemainingCost` (la forme abstraite, cf #4048).
-/

namespace Astar

variable {V : Type*} (G : WeightedGraph V)

/-! ## Le « vrai coût optimal restant » `hStar` -/

/-- `hStar` est une **borne inférieure** sur le coût de tout chemin allant de son
    premier sommet au but. C'est la propriété caractéristique du vrai coût optimal
    restant : pour un graphe fini, `hStar n = min { pathCost p | p va de n au but }`,
    minimum atteint (chemins simples en nombre fini) et qui minore donc tout chemin
    réalisé. On garde ici la forme abstraite (hypothèse), plus propre pédagogiquement
    (cf #4048). -/
def IsTrueRemainingCost (hStar : V → NNReal) (goal : V) : Prop :=
  ∀ (start : V) (p : Path V), PathFrom start goal p → hStar start ≤ pathCost G p

/-! ## Lemme auxiliaire : un suffixe d'un chemin allant au but va encore au but -/

/-- Si `p` va de `start` à `goal`, alors pour tout indice `i`, le suffixe
    `p.drop i` va de `p.get i` à `goal`. -/
lemma suffix_pathFrom (p : Path V) (i : Fin p.length) (start goal : V)
    (hp : PathFrom start goal p) : PathFrom (p.get i) goal (p.drop i.val) := by
  obtain ⟨hnil, hhead, hlast⟩ := hp
  have hi : i.val < p.length := i.isLt
  refine ⟨?_, ?_, ?_⟩
  · -- (p.drop i.val) ≠ []
    rw [Ne, List.drop_eq_nil_iff]
    omega
  · -- head? (p.drop i.val) = some (p.get i)
    rw [List.head?_drop, List.getElem?_eq_getElem hi]
    rfl
  · -- getLast? (p.drop i.val) = some goal
    have hne : ¬(p.length ≤ i.val) := by omega
    rw [List.getLast?_drop, if_neg hne]
    exact hlast

/-! ## Théorème phare : borne en `f` (borne de suffixe) -/

/-- **Borne en `f` au départ.** Heuristique admissible + `hStar` borne inférieure ⇒
    `h(start) ≤ pathCost(p)` pour tout chemin `p` allant au but depuis `start`.
    C'est la borne en `f` (`f = g + h`) au point de départ. -/
theorem admissible_head_bound (h hStar : V → NNReal) (hAdm : Admissible h hStar)
    (goal start : V) (p : Path V) (hStar_lb : IsTrueRemainingCost G hStar goal)
    (hp : PathFrom start goal p) : h start ≤ pathCost G p :=
  le_trans (hAdm start) (hStar_lb start p hp)

/-- **Borne en `f` sur un suffixe (heuristique admissible).** Pour tout nœud
    `p.get i` d'un chemin `p` allant au but, `h(p.get i) ≤ pathCost(p.drop i)` :
    la valeur de l'heuristique admissible ne dépasse jamais le coût du suffixe
    restant. C'est la borne en `f` (`f = g + h`) en chaque nœud — le cœur abstrait
    de l'argument d'optimalité de A* (Hart, Nilsson & Raphael, 1968).

    **Portée — ce que ce théorème ne dit pas.** Il borne l'heuristique par le coût
    du suffixe ; il ne prouve **pas** qu'A* renvoie un chemin de coût optimal. Le
    lake ne modélise ni file de priorité, ni ensemble fermé, ni chemin retourné :
    la garantie « heuristique admissible ⇒ A* optimal » (fausse pour la variante
    Graph-Search sans ré-ouverture, cf #14824) n'est pas un théorème de ce lake. -/
theorem admissible_le_suffix_cost (h hStar : V → NNReal) (hAdm : Admissible h hStar)
    (goal start : V) (p : Path V) (hStar_lb : IsTrueRemainingCost G hStar goal)
    (hp : PathFrom start goal p) (i : Fin p.length) :
    h (p.get i) ≤ pathCost G (p.drop i.val) := by
  apply le_trans (hAdm (p.get i))
  exact hStar_lb (p.get i) (p.drop i.val) (suffix_pathFrom p i start goal hp)

end Astar
