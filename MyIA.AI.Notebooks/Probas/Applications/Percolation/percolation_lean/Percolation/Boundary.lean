import Percolation.Components
import Percolation.Examples
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Noyau fini de la percolation — frontière isopérimétrique (tranche 4)

Suite du noyau fini (voir `Percolation/Components.lean`). Ce module complète la
trilogie composantes / connexité / frontière par le versant **isopérimétrique
fini** : quantifier et caractériser la **frontière** d'un ensemble `A` dans une
configuration `ω` d'arêtes ouvertes.

- `openEdgeCrosses` : une arête ouverte **traversante** de `A` vers son
  complémentaire — un élément de la frontière de `A`.
- `not_closed_iff_exists_crossing` : frontière vide ⟺ ensemble fermé (dual de
  `openEdgeClosed_iff_no_cross` de la tranche 3).
- `closed_eq_empty_or_univ_of_connected` : **le lemme isopérimétrique** — dans une
  configuration où tout sommet est relié à tout autre (graphe ω-connexe), les seuls
  ensembles ω-fermés sont `∅` et l'univers. Tout ensemble propre non vide a donc une
  frontière non vide.
- Les **bornes C₃/C₄** : sur le triangle et le carré en configuration complète, les
  seuls ensembles fermés sont triviaux.

Convention i18n EPIC #4980 : docstrings en français ici ; le miroir anglais vit
dans `Percolation/Boundary_en.lean` (byte-identique hors docstrings/commentaires).
-/

set_option linter.unusedSectionVars false

namespace Percolation

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

/-- **Arête ouverte traversante** : une arête ouverte relie un élément de `A` à son
complémentaire — un élément de la frontière de `A` dans la configuration `ω`. -/
def openEdgeCrosses (ω : Finset (Edge G)) (A : Set V) (u v : V) : Prop :=
  u ∈ A ∧ v ∉ A ∧ openAdj G ω u v

/-- **Frontière vide ⟺ fermé** : `A` est ω-fermé si et seulement si aucune arête
ouverte ne traverse sa frontière (aucun élément de `A` n'est adjacent ouvertement
à son complémentaire). C'est le dual de `openEdgeClosed_iff_no_cross`. -/
theorem not_closed_iff_exists_crossing {ω : Finset (Edge G)} (A : Set V) :
    ¬ openEdgeClosed G ω A ↔ ∃ u v : V, openEdgeCrosses G ω A u v := by
  rw [openEdgeClosed_iff_no_cross]
  constructor
  · intro h
    apply by_contra
    intro hnone
    apply h
    intro u v hu hvnot hAdj
    exact hnone ⟨u, v, hu, hvnot, hAdj⟩
  · intro h hclosed
    rcases h with ⟨u, v, hu, hvnot, hAdj⟩
    exact (hclosed (u := u) (v := v) hu hvnot) hAdj

/-- **Isopérimètre — le lemme frontière** : dans une configuration `ω` où tout
sommet est relié à tout autre (graphe ω-connexe), les seuls ensembles ω-fermés
sont `∅` et l'univers. Tout ensemble propre non vide a donc une frontière non
vide. La preuve est le pont composante↔frontière : un fermé non vide contient la
composante (ouvrant connexe) de chacun de ses éléments, laquelle, par
ω-connexité, est l'univers tout entier. -/
theorem closed_eq_empty_or_univ_of_connected {ω : Finset (Edge G)} (A : Set V)
    (hconn : ∀ u v : V, ConnectedIn G ω u v) :
    openEdgeClosed G ω A ↔ A = Set.univ ∨ A = ∅ := by
  constructor
  · intro hclosed
    by_cases hA : A = ∅
    · exact Or.inr hA
    · left
      apply Set.eq_univ_iff_forall.mpr
      intro v
      rcases Set.nonempty_iff_ne_empty.mpr hA with ⟨u, hu⟩
      exact openEdgeClosed.mem_of_connected (G := G) hclosed hu (hconn u v)
  · intro htriv
    rcases htriv with hAuniv | hAempty
    · intro u v hu hAdj
      rw [hAuniv]
      simp
    · intro u v hu hAdj
      exfalso
      rw [hAempty] at hu
      simp at hu

/-- Dans la configuration complète `full3`, toute arête de `C₃` est ouverte. -/
theorem openAdj_C3 {a b : Fin 3} (h : C3.Adj a b) : openAdj C3 full3 a b := by
  use h
  simp [full3]

/-- **`C₃` est ω-connexe en configuration complète** : tout sommet est relié à
tout autre (dans le graphe complet, un seul pas suffit). C'est l'hypothèse de
`closed_eq_empty_or_univ_of_connected`. -/
theorem C3_full_connected : ∀ a b : Fin 3, ConnectedIn C3 full3 a b := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (0 : Fin 3) 1))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (0 : Fin 3) 2))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (1 : Fin 3) 0))
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (1 : Fin 3) 2))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (2 : Fin 3) 0))
  · exact Relation.ReflTransGen.single (openAdj_C3 (by decide : C3.Adj (2 : Fin 3) 1))
  · exact Relation.ReflTransGen.refl

/-- **Borne `C₃`** : sur le triangle en configuration complète, les seuls ensembles
fermés sont `∅` et l'univers. Aucun singulet ni paire propre n'est fermé. -/
theorem C3_closed_iff (A : Set (Fin 3)) :
    openEdgeClosed C3 full3 A ↔ A = Set.univ ∨ A = ∅ :=
  closed_eq_empty_or_univ_of_connected C3 (A := A) (ω := full3) C3_full_connected

/-- Dans la configuration complète `full4`, toute arête de `C₄` est ouverte. -/
theorem openAdj_C4 {a b : Fin 4} (h : C4.Adj a b) : openAdj C4 full4 a b := by
  use h
  simp [full4]

/-- **`C₄` est ω-connexe en configuration complète** : tout sommet est relié à
tout autre, en **composant** `Relation.ReflTransGen.trans` pour les paires non
adjacentes (`0—2` via `0—1—2`, `1—3` via `1—0—3`). -/
theorem C4_full_connected : ∀ a b : Fin 4, ConnectedIn C4 full4 a b := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 1))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 1)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 2)))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 3))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 0))
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 2))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 0)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 3)))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (2 : Fin 4) 1)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (1 : Fin 4) 0)))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (2 : Fin 4) 1))
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (2 : Fin 4) 3))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (3 : Fin 4) 0))
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (3 : Fin 4) 0)))
      (Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (0 : Fin 4) 1)))
  · exact Relation.ReflTransGen.single (openAdj_C4 (by decide : C4.Adj (3 : Fin 4) 2))
  · exact Relation.ReflTransGen.refl

/-- **Borne `C₄`** : sur le carré en configuration complète, les seuls ensembles
fermés sont `∅` et l'univers. Aucun singleton ni paire propre n'est fermé, même
sans arête directe entre extrémités opposées. -/
theorem C4_closed_iff (A : Set (Fin 4)) :
    openEdgeClosed C4 full4 A ↔ A = Set.univ ∨ A = ∅ :=
  closed_eq_empty_or_univ_of_connected C4 (A := A) (ω := full4) C4_full_connected

end Percolation
