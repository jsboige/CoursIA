import Mathlib
import Astar.Graph
import Astar.Heuristic
import Astar.Optimality

/-!
# Astar.Consistency — consistance ⟹ admissibilité (téléscopage)

Issue #4048, théorème cible `consistent_implies_admissible`. La **consistance**
(monotonie par arc : `h n ≤ edge n n' + h n'`) est une condition **locale** ;
l'**admissibilité** (`h n ≤ hStar n`) est une condition **globale**. Le pont entre les
deux est un **téléscopage** : le long des arcs d'un chemin `start = v₀ → v₁ → … → vₖ =
goal`, la consistance se compose en

```
h(start) ≤ edge(v₀,v₁) + h(v₁)
         ≤ edge(v₀,v₁) + edge(v₁,v₂) + h(v₂)
         ≤ …
         ≤ pathCost(p) + h(goal).
```

Sous l'hypothèse naturelle `h(goal) = 0` (l'heuristique est nulle au but), il vient
**`h(start) ≤ pathCost(p)` pour tout chemin `p` allant au but** — c'est exactement la
borne globale que l'admissibilité fournit aussi (cf `admissible_head_bound` dans
`Optimality.lean`). C'est le contenu substantiel de « la consistance implique
l'admissibilité » : la condition locale, par téléscopage, atteint gratuitement la
borne globale.

**Note de cadrage (honnête).** Dans ce modèle abstrait, `hStar` n'est qu'une *borne
inférieure* sur les coûts de chemins (`IsTrueRemainingCost`), pas nécessairement le
coût optimal réalisé. La consistance donne `h(start) ≤ pathCost(p)` pour **tout**
chemin réalisé `p` ; en déduire `h(start) ≤ hStar(start)` nécessiterait que `hStar`
soit le *minimum atteint* (graphe fini, chemins simples en nombre fini). Cette
« réalisabilité de `hStar` » est délibérément laissée abstraite ici (cf #4048 : on
prouve la **forme abstraite**). Le résultat `consistent_implies_path_bound` ci-dessous
est donc le **théorème substantiel pleinement prouvé** ; il entraîne l'admissibilité au
sens « ne surestime jamais un coût de chemin réalisé », qui est le mécanisme exact
d'optimalité de A*. Voir Hart, Nilsson & Raphael (1968).
-/

namespace Astar

variable {V : Type*} (G : WeightedGraph V)

/-- **Consistance ⟹ borne sur le chemin (téléscopage).** Théorème cible #4048
    (`consistent_implies_admissible`). Une heuristique **consistante** nulle au but
    (`h goal = 0`) ne dépasse jamais le coût d'un chemin réalisé vers le but : pour
    tout chemin `p` de `start` à `goal`, `h(start) ≤ pathCost(p)`.

    La consistance est locale (par arc) ; par téléscopage le long des arcs du chemin,
    elle atteint la même borne globale que l'admissibilité (`h ≤ hStar ≤ pathCost`).
    C'est le mécanisme exact qui rend A* optimal sous heuristique consistante : la
    fonction `f = g + h` est alors croissante le long des chemins, donc aucun nœud
    n'est jamais ré-expansé (cf Hart, Nilsson & Raphael 1968). -/
theorem consistent_implies_path_bound (h : V → NNReal) (goal : V)
    (hCons : Consistent G h) (hGoal : h goal = 0)
    (start : V) (p : Path V) (hp : PathFrom start goal p) :
    h start ≤ pathCost G p := by
  obtain ⟨hnel, hhead, hlast⟩ := hp
  -- Lemme auxiliaire : pour toute liste `q` finissant au `goal`, `h(q.head) ≤ pathCost q`.
  -- (On garde `start` abstrait via sa position de tête, pour pouvoir récurer sur la queue.)
  have key : ∀ (q : Path V), q.getLast? = some goal →
      ∀ s : V, q.head? = some s → h s ≤ pathCost G q := by
    intro q
    induction q with
    | nil => simp
    | cons hd tl ih =>
      intro hqgoal s hs
      -- `hs : (hd :: tl).head? = some s`  ⟹  `hd = s`. (`subst` élimine `s`, garde `hd`.)
      have hhd : hd = s := by simp_all
      subst hhd
      cases tl with
      | nil =>
        -- `q = [hd]`, `getLast? = some goal` ⟹ `hd = goal`, puis `pathCost = 0`.
        have hhdg : hd = goal := by simp_all
        simp only [pathCost_singleton]
        rw [hhdg, hGoal]
      | cons w rest' =>
        -- `q = hd :: w :: rest'`. Le dernier sommet est porté par la queue.
        have hqgoal' : (w :: rest').getLast? = some goal := by simp_all
        -- Récurrence sur la queue `(w :: rest')` : `h w ≤ pathCost(w :: rest')`.
        have hihw : h w ≤ pathCost G (w :: rest') := ih hqgoal' w (by simp)
        -- Consistance à l'arc `(hd, w)` : `h hd ≤ edge(hd,w) + h w`.
        have hcons := hCons hd w
        -- `pathCost(hd :: w :: rest') = edge(hd,w) + pathCost(w :: rest')`.
        simp only [pathCost_cons_cons]
        linarith
  exact key p hlast start hhead

/-- **Consistance ⟹ admissibilité au sens du chemin.** Corollaire immédiat du
    téléscopage : sous une heuristique consistante nulle au but, l'heuristique au
    départ ne dépasse jamais le coût d'un chemin menant au but — exactement la borne
    que fournit l'admissibilité (`admissible_head_bound`), atteinte ici sans hypothèse
    sur `hStar`. -/
theorem consistent_implies_admissible_bound (h : V → NNReal) (goal : V)
    (hCons : Consistent G h) (hGoal : h goal = 0)
    (start : V) (p : Path V) (hp : PathFrom start goal p) :
    h start ≤ pathCost G p :=
  consistent_implies_path_bound G h goal hCons hGoal start p hp

end Astar
