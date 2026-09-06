import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Relation

/-! # Noyau fini de la percolation — connexité (tranche 2)

Suite du noyau fini (voir `Percolation/Basic.lean`). Ce module établit que
l'événement « deux sommets sont reliés » est un événement **croissant**
(monotone pour l'inclusion des arêtes ouvertes) : plus d'arêtes ouvertes ne
peut que le conserver. C'est précisément la propriété qui rend les événements
de connexité éligibles à l'inégalité de **Harris–Kleitman** (FKG fini) prouvée
au jalon 1.

Sur un graphe simple fini `G` et un ensemble `ω` d'arêtes **ouvertes** (une
configuration), deux sommets `u` et `v` sont *reliés* s'il existe un chemin
d'arêtes ouvertes les joignant — la fermeture réflexive-transitive de la
relation « `u` et `v` sont adjacents par une arête ouverte ».

Convention i18n EPIC #4980 : docstrings en français ici, le miroir anglais vit
dans `Percolation/Connectivity_en.lean` (byte-identiques hors docstrings/comments).
-/

-- Les lemmes de monotonie `openAdj_mono`/`connected_mono` raisonnent sur
-- l'inclusion de `Finset (Edge G)` sans avoir besoin des instances de finitude
-- (utiles aux événements `connectedEvent`) : on désactive l'avertissement.
set_option linter.unusedSectionVars false

namespace Percolation

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Le type des arêtes d'un graphe simple fini `G` : une paire non ordonnée
`{u, v}` (`Sym2 V`) qui appartient à l'ensemble d'arêtes `G.edgeSet`. -/
abbrev Edge (G : SimpleGraph V) := {e : Sym2 V // e ∈ G.edgeSet}

variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

/-- **Adjacence ouverte** : dans la configuration `ω` (ensemble d'arêtes
ouvertes), `u` et `v` sont adjacents s'ils le sont dans `G` et si l'arête
`s(u, v)` est ouverte (appartient à `ω`). -/
abbrev openAdj (ω : Finset (Edge G)) (u v : V) : Prop :=
  ∃ (huv : G.Adj u v), (⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩ : Edge G) ∈ ω

/-- **Connexité par arêtes ouvertes** : `u` et `v` sont reliés dans la
configuration `ω` s'il existe un chemin d'arêtes ouvertes les joignant
(fermeture réflexive-transitive de `openAdj`). -/
abbrev ConnectedIn (ω : Finset (Edge G)) (u v : V) : Prop :=
  Relation.ReflTransGen (openAdj G ω) u v

/-- **Monotonie de l'adjacence ouverte** : si `ω₁ ⊆ ω₂` (plus d'arêtes
ouvertes), alors toute adjacence ouverte dans `ω₁` l'est dans `ω₂`. -/
lemma openAdj_mono {ω₁ ω₂ : Finset (Edge G)} (h : ω₁ ⊆ ω₂) :
    openAdj G ω₁ ≤ openAdj G ω₂ := by
  intro u v huv
  rcases huv with ⟨huv_adj, hmem⟩
  exact ⟨huv_adj, h hmem⟩

/-- **Monotonie de la connexité** : si `ω₁ ⊆ ω₂`, alors tout couple relié dans
`ω₁` reste relié dans `ω₂`. L'événement de connexité est donc **croissant**. -/
lemma connected_mono {ω₁ ω₂ : Finset (Edge G)} (h : ω₁ ⊆ ω₂) :
    ConnectedIn G ω₁ ≤ ConnectedIn G ω₂ := by
  intro u v h_conn
  exact Relation.ReflTransGen.mono (openAdj_mono G h) u v h_conn

/-- **Événement de connexité** : la famille des configurations `ω` dans
lesquelles `u` et `v` sont reliés, vue comme un `Finset` de configurations. -/
noncomputable def connectedEvent (u v : V) : Finset (Finset (Edge G)) :=
  Finset.univ.filter (fun ω : Finset (Edge G) => ConnectedIn G ω u v)

/-- **L'événement de connexité est croissant** : c'est un `IsUpperSet` pour
l'ordre d'inclusion des configurations — plus d'arêtes ouvertes conserve la
connexité. -/
theorem connectedEvent_isUpperSet {u v : V} :
    IsUpperSet (connectedEvent G u v : Set (Finset (Edge G))) := by
  intro ω₁ ω₂ hsub hm
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    connected_mono G hsub u v (Finset.mem_filter.mp hm).2⟩

/-- **Harris–Kleitman (FKG fini) pour la connexité** : deux événements croissants
de connexité corrèlent positivement sous la mesure uniforme du cube booléen des
arêtes. C'est le pont du jalon 1 vers la percolation : la connexité étant un
événement croissant, elle est éligible à l'inégalité d'association. -/
theorem harris_kleitman_connected {u v x y : V} :
    #(connectedEvent G u v) * #(connectedEvent G x y) ≤
      2 ^ Fintype.card (Edge G) * #((connectedEvent G u v) ∩ (connectedEvent G x y)) :=
  (connectedEvent_isUpperSet G (u := u) (v := v)).le_card_inter_finset
    (connectedEvent_isUpperSet G (u := x) (v := y))

end Percolation
