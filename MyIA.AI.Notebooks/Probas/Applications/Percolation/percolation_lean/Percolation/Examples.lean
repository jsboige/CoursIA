import Percolation.Components
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Noyau fini de la percolation — un exemple calculable (tranche 3, acceptation 3)

Instance concrète du noyau composantes/frontière sur le **triangle** `C₃`
(`SimpleGraph.cycleGraph 3`). Dans `cycleGraph 3` toute paire de sommets est
adjacente (soustraction modulaire), donc `C₃` est le graphe complet sur `Fin 3` :
son ensemble d'arêtes a pour cardinal 3, et la configuration `full3` (toutes les
arêtes ouvertes) rend le graphe entier connexe.

Ce module ancre les lemmes abstraits de `Percolation/Components.lean` sur un
petit graphe fini — l'« exemple calculable » de l'issue #14871, acceptation 3 —
et est vérifiable par `lake build`.

- `component_C3_full` : dans la configuration complète, la composante ouverte de
  `0` est l'ensemble des sommets.
- `not_openEdgeClosed_C3_singleton` : le singleton `{0}` n'est **pas** ω-fermé.
- `exists_boundary_edge_C3` : l'arête ouverte `0—1` traverse de `{0}` à son
  complémentaire — un témoin de frontière concret.
-/

set_option linter.unusedSectionVars false

namespace Percolation

open Finset

/-- **Triangle** `C₃` — le 3-cycle, un graphe simple fini concret. Dans
`SimpleGraph.cycleGraph 3` toute paire de sommets est adjacente, donc `C₃` est
le graphe complet sur `Fin 3`. -/
abbrev C3 : SimpleGraph (Fin 3) := SimpleGraph.cycleGraph 3

/-- **Configuration complète** sur `C₃` : toutes les arêtes sont ouvertes. -/
abbrev full3 : Finset (Edge C3) := Finset.univ

/-- `C₃` a exactement trois arêtes (ouvrables). -/
theorem card_edge_C3 : Fintype.card (Edge C3) = 3 := by
  decide

/-- Dans `C₃` les sommets `0` et `1` sont adjacents. -/
theorem adj_C3_0_1 : (SimpleGraph.cycleGraph 3).Adj (0 : Fin 3) 1 := by
  decide

/-- Dans `C₃` les sommets `0` et `2` sont adjacents. -/
theorem adj_C3_0_2 : (SimpleGraph.cycleGraph 3).Adj (0 : Fin 3) 2 := by
  decide

/-- Dans la configuration complète `full3`, la composante ouverte de `0` est
l'ensemble des sommets : tout sommet est atteignable depuis `0` par un chemin
d'arêtes ouvertes. -/
theorem component_C3_full :
    Component C3 full3 (0 : Fin 3) = Set.univ := by
  ext u
  constructor
  · intro _; trivial
  · intro _; unfold Component
    fin_cases u
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        (show openAdj C3 full3 (0 : Fin 3) 1 from by
          use adj_C3_0_1; simp [full3])
    · exact Relation.ReflTransGen.single
        (show openAdj C3 full3 (0 : Fin 3) 2 from by
          use adj_C3_0_2; simp [full3])

/-- Le singleton `{0}` n'est **pas** ω-fermé dans `full3` : l'arête ouverte
`0—1` en sort. Un ensemble ω-fermé dans la configuration complète doit être bien
plus grand qu'un sommet unique. -/
theorem not_openEdgeClosed_C3_singleton :
    ¬ openEdgeClosed C3 full3 ({0} : Set (Fin 3)) := by
  intro h
  have h1 : (1 : Fin 3) ∈ ({0} : Set (Fin 3)) :=
    h (by simp) (show openAdj C3 full3 (0 : Fin 3) 1 from by
      use adj_C3_0_1; simp [full3])
  simp at h1

/-- L'**arête frontière** de `{0}` dans `full3` : l'arête ouverte `0—1` traverse
de `{0}` à son complémentaire. C'est le témoin concret que le complémentaire de
`{0}` a une frontière non vide — la face frontière du pont du noyau. -/
theorem exists_boundary_edge_C3 :
    ∃ u v : Fin 3, u ∈ ({0} : Set (Fin 3)) ∧ v ∉ ({0} : Set (Fin 3)) ∧ openAdj C3 full3 u v := by
  refine ⟨(0 : Fin 3), (1 : Fin 3), ?_, ?_, ?_⟩
  · simp
  · simp
  · show openAdj C3 full3 (0 : Fin 3) 1
    use adj_C3_0_1; simp [full3]

end Percolation
