import Mathlib.Logic.Relation
import Percolation.Connectivity

/-! # Noyau fini de la percolation — composantes et frontière (tranche 3)

Suite du noyau fini (voir `Percolation/Connectivity.lean`). Ce module relie trois
notions : la **composante connexe ouverte** d'un sommet, la propriété d'être
**fermé le long des arêtes ouvertes** (aucune arête ouverte n'en sort), et la
**frontière** (le complémentaire). Le pont central est le lemme
connexion↔composante↔frontière : un ensemble est ω-fermé si et seulement s'il
est une union de composantes connexes (il contient la composante de chacun de
ses éléments), si et seulement si aucune arête ouverte ne le relie à son
complémentaire (frontière vide).

Sur un graphe simple fini `G` et une configuration `ω` d'arêtes ouvertes, la
composante `Component ω v` est l'ensemble des sommets reliés à `v` par un chemin
d'arêtes ouvertes (la fermeture réflexive-transitive de l'adjacence ouverte).

Convention i18n EPIC #4980 : docstrings en français ici ; le miroir anglais vit
dans `Percolation/Components_en.lean` (byte-identique hors docstrings/commentaires).
-/

set_option linter.unusedSectionVars false

namespace Percolation

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

/-- **Composante connexe ouverte** d'un sommet `v` : l'ensemble des sommets `w`
reliés à `v` dans la configuration `ω` (chemin d'arêtes ouvertes). -/
def Component (ω : Finset (Edge G)) (v : V) : Set V :=
  {w : V | ConnectedIn G ω v w}

/-- **Fermé le long des arêtes ouvertes** : `A` est ω-fermé si aucune arête
ouverte n'en sort — tout `u ∈ A` adjoint ouvertement à `v` implique `v ∈ A`. -/
def openEdgeClosed (ω : Finset (Edge G)) (A : Set V) : Prop :=
  ∀ ⦃u v : V⦄, u ∈ A → openAdj G ω u v → v ∈ A

/-- **Un sommet appartient à sa propre composante** (réflexivité). -/
theorem component_self {ω : Finset (Edge G)} (v : V) : v ∈ Component G ω v := by
  unfold Component
  exact Relation.ReflTransGen.refl

/-- **La composante est ω-fermée** : aucune arête ouverte n'en sort. C'est la
première face du lien composante↔frontière. -/
theorem component_closed {ω : Finset (Edge G)} (v : V) : openEdgeClosed G ω (Component G ω v) := by
  intro u w hu huw
  unfold Component at hu ⊢
  exact Relation.ReflTransGen.trans hu (Relation.ReflTransGen.single huw)

/-- **Pont connexité↔composante** : `w ∈ Component v` si et seulement si `v` et
`w` sont reliés. Définitionnel (la composante EST l'ensemble des reliés). -/
theorem component_iff_connected {ω : Finset (Edge G)} (v w : V) :
    w ∈ Component G ω v ↔ ConnectedIn G ω v w := by
  rfl

/-- **Contiguïté implique appartenance à la composante** : une arête ouverte en
partant de `u` place son extrémité dans la composante de `u`. -/
theorem mem_component_of_adj {ω : Finset (Edge G)} {u v : V} (hAdj : openAdj G ω u v) :
    v ∈ Component G ω u := by
  unfold Component
  exact Relation.ReflTransGen.single hAdj

/-- **Un ensemble fermé contient la composante de chacun de ses éléments** : si
`A` est ω-fermé et contient `u`, il contient tous les sommets reliés à `u`
(récurrence le long du chemin d'arêtes ouvertes). -/
theorem openEdgeClosed.mem_of_connected {ω : Finset (Edge G)} {A : Set V}
    (h : openEdgeClosed G ω A) {u w : V} (hu : u ∈ A) (hconn : ConnectedIn G ω u w) : w ∈ A := by
  induction hconn with
  | refl => exact hu
  | tail hconn2 hstep ih => exact h ih hstep

/-- **Fermé ⟺ frontière vide** : `A` est ω-fermé si et seulement si aucune
arête ouverte ne relie `A` à son complémentaire. C'est la face « frontière »
(deuxième face du lien). -/
theorem openEdgeClosed_iff_no_cross {ω : Finset (Edge G)} (A : Set V) :
    openEdgeClosed G ω A ↔ ∀ ⦃u v : V⦄, u ∈ A → v ∉ A → ¬ openAdj G ω u v := by
  constructor
  · intro h u v hu hvnot hAdj
    exact hvnot (h hu hAdj)
  · intro h u v hu hAdj
    by_contra hvnot
    exact (h hu hvnot) hAdj

/-- **Lemme connexion↔composante↔frontière** : `A` est ω-fermé si et seulement
s'il est une union de composantes connexes (contient la composante de chacun de
ses éléments). C'est le pont du noyau : la frontière vide (aucune arête ouverte
ne sort de `A`) équivaut à « `A` est une réunion de composantes ». -/
theorem openEdgeClosed_iff_contains_components {ω : Finset (Edge G)} (A : Set V) :
    openEdgeClosed G ω A ↔ ∀ ⦃u : V⦄, u ∈ A → Component G ω u ⊆ A := by
  constructor
  · intro h u hu w hw
    exact openEdgeClosed.mem_of_connected (G := G) h hu (by simpa [Component] using hw)
  · intro h u v hu hAdj
    exact h hu (mem_component_of_adj (G := G) hAdj)

end Percolation
