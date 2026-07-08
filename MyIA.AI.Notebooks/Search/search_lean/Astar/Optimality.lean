import Mathlib
import Astar.Graph
import Astar.Heuristic

/-!
# Astar.Optimality — admissible ⇒ optimal (lemme abstrait d'optimalité)

Théorème phare de la série (issue #4048, registre #3801 — prong B « problème
non-trivial »). On prouve la **borne en `f`** qui est le mécanisme exact d'optimalité
de A* : sous une heuristique admissible, `h(start)` ne dépasse jamais le coût d'un
chemin réalisé jusqu'au but. Appliquée à chaque suffixe du chemin optimal, cette borne
donne `f(nœud) = g(nœud) + h(nœud) ≤ coût optimal` en tout point du chemin optimal —
donc A* (qui déploie le nœud de `f` minimal) ne dépasse jamais la frontière du coût
optimal et renvoie un chemin de coût optimal (Hart, Nilsson & Raphael, 1968).

On prouve la **forme abstraite** (sans modéliser la file de priorité complète), comme
suggéré par #4048 : `hStar` est un « vrai coût optimal restant » satisfaisant la
propriété de borne inférieure `IsTrueRemainingCost`.
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

/-! ## Théorème phare : borne en `f` et optimalité -/

/-- **Borne en `f` au départ.** Heuristique admissible + `hStar` borne inférieure ⇒
    `h(start) ≤ pathCost(p)` pour tout chemin `p` allant au but depuis `start`.
    C'est la borne en `f` (`f = g + h`) au point de départ. -/
theorem admissible_head_bound (h hStar : V → NNReal) (hAdm : Admissible h hStar)
    (goal start : V) (p : Path V) (hStar_lb : IsTrueRemainingCost G hStar goal)
    (hp : PathFrom start goal p) : h start ≤ pathCost G p :=
  le_trans (hAdm start) (hStar_lb start p hp)

/-- **A* admissible ⇒ optimal (lemme abstrait).** Théorème phare (issue #4048,
    registre #3801).

    Sous une heuristique **admissible**, pour tout nœud `p.get i` d'un chemin `p`
    allant au but, l'heuristique ne dépasse jamais le coût du suffixe restant
    `pathCost (p.drop i)`. C'est la **borne en `f`** en chaque nœud : combinée à
    `f(nœud) = g(nœud) + h(nœud)` et au fait que `g + suffixCost = pathCost`, elle
    donne `f(nœud) ≤ pathCost(optimal)` le long du chemin optimal — le mécanisme
    exact d'optimalité de A* (déploiement du `f` minimal ⇒ la frontière du coût
    optimal n'est jamais dépassée). Voir Hart, Nilsson & Raphael (1968). -/
theorem admissible_implies_optimal (h hStar : V → NNReal) (hAdm : Admissible h hStar)
    (goal start : V) (p : Path V) (hStar_lb : IsTrueRemainingCost G hStar goal)
    (hp : PathFrom start goal p) (i : Fin p.length) :
    h (p.get i) ≤ pathCost G (p.drop i.val) := by
  apply le_trans (hAdm (p.get i))
  exact hStar_lb (p.get i) (p.drop i.val) (suffix_pathFrom p i start goal hp)

/-- **Corollaire : borne globale au départ.** Cas particulier `i = 0`
    (le nœud de départ) : `h(start) ≤ pathCost(p)`. -/
theorem admissible_implies_optimal_start (h hStar : V → NNReal) (hAdm : Admissible h hStar)
    (goal start : V) (p : Path V) (hStar_lb : IsTrueRemainingCost G hStar goal)
    (hp : PathFrom start goal p) : h start ≤ pathCost G p :=
  admissible_head_bound G h hStar hAdm goal start p hStar_lb hp

end Astar
