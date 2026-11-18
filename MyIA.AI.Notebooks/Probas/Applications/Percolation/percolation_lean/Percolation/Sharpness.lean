import Percolation.Basic
import Percolation.Boundary
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Noyau fini de la percolation — sharpness fini par comptage (tranche 5)

Dernier étage du socle fini : une **inégalité de sharpness finie**, forme
paramétrique uniforme (`p = 1/2`) dont l'inégalité de décroissance
exponentielle de l'article de référence sur la percolation surcritique
(Diskin–Easo–Radhakrishnan–Sudakov–Tassion, arXiv:2603.03257, §3.0) est la
limite. Le socle reste uniforme (le cas Bernoulli-`p` général est hors périmètre
du socle, cf `Percolation/Basic.lean`) : l'énoncé ci-dessous vit sur la mesure
de comptage de `Finset (Edge G)`.

L'argument est un **comptage de renouvellement** en trois temps :

1. **Frontière pleine** `graphBoundary G A` : les arêtes de `G` (ouvertes ou
   fermées) qui quittent `A` — l'objet ω-indépendant dont `boundary` (tranche 4)
   est la trace sur `ω`.
2. **Confinement ⇒ arêtes forcées fermées** : si `A` est ω-fermé, toutes les
   arêtes de la frontière pleine sont fermées — l'événement de confinement vit
   dans le sous-cube où `|δA|` coordonnées sont fixées, donc a au plus
   `2^(N − |δA|)` configurations.
3. **Union sur les petits candidats** : la composante ouverte de `v` est elle-même
   ω-fermée, donc l'événement « composante de cardinal ≤ k » est couvert par
   l'union des confinements aux candidats `A ∋ v` de cardinal ≤ k — chaque
   candidat payant son facteur `2^(N − |δA|)`.

Le résultat est le théorème `card_smallClusterEvent_le` : la « probabilité »
(mesure de comptage normalisée par `2^N`) que la composante de `v` reste de
cardinal ≤ k est au plus `Σ_{A ∋ v, |A| ≤ k} 2^(−|δA|)` — la forme finie de
l'inégalité de l'article : un profil isopérimétrique qui croît avec `|A|`
suffit à écraser exponentiellement les petites composantes.

Le module ajoute le chaînon manquant de la trilogie Harris–Kleitman du socle :
la forme **mixte** `harris_kleitman_upper_lower` (un événement croissant et un
décroissant sont anti-corrélés), instanciée sur connexité × confinement.

Convention i18n EPIC #4980 : docstrings en français ici ; le miroir anglais vit
dans `Percolation/Sharpness_en.lean` (byte-identique hors docstrings/commentaires).
-/

set_option linter.unusedSectionVars false

namespace Percolation

open Finset
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)]

-- ============================================================
-- Événements de confinement (décroissants)
-- ============================================================

/-- **Événement de fermeture** : les configurations `ω` dans lesquelles `A` est
ω-fermé — aucune arête ouverte n'en sort. C'est un événement **décroissant** :
retirer des arêtes ouvertes ne peut pas ouvrir une sortie. -/
noncomputable def closedEvent (A : Finset V) : Finset (Finset (Edge G)) :=
  Finset.univ.filter (fun ω => openEdgeClosed G ω (↑A : Set V))

/-- **L'événement de fermeture est décroissant** : si `A` est fermé dans une
configuration, il le reste dans toute sous-configuration. -/
theorem closedEvent_isLowerSet (A : Finset V) :
    IsLowerSet (closedEvent G A : Set (Finset (Edge G))) := by
  intro ω₁ ω₂ hsub hmem
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro u v hu hadj
  exact ((Finset.mem_filter.mp hmem).2) hu (openAdj_mono G hsub u v hadj)

/-- **Événement « petite composante »** : les configurations `ω` dans
lesquelles la composante ouverte de `v` a au plus `k` sommets. Événement
**décroissant** : ajouter des arêtes ouvertes ne peut que grossir la composante. -/
noncomputable def smallClusterEvent (v : V) (k : ℕ) : Finset (Finset (Edge G)) :=
  Finset.univ.filter (fun ω => (Component G ω v).toFinset.card ≤ k)

/-- **L'événement « petite composante » est décroissant** : la composante ne
peut que grossir quand on ouvre des arêtes (`connected_mono`). -/
theorem smallClusterEvent_isLowerSet (v : V) (k : ℕ) :
    IsLowerSet (smallClusterEvent G v k : Set (Finset (Edge G))) := by
  intro ω₁ ω₂ hsub hmem
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hmono : (Component G ω₂ v).toFinset ⊆ (Component G ω₁ v).toFinset := by
    refine Set.toFinset_subset_toFinset.mpr ?_
    intro w hw
    exact connected_mono G hsub v w hw
  exact le_trans (Finset.card_le_card hmono) ((Finset.mem_filter.mp hmem).2)

-- ============================================================
-- Harris–Kleitman mixte : croissant × décroissant = anti-corrélés
-- ============================================================

/-- **Inégalité de Harris–Kleitman uniforme, forme mixte** : un événement
**croissant** `𝒜` et un événement **décroissant** `ℬ` sont **anti-corrélés** —
dans la mesure uniforme (`p = 1/2`), la probabilité de l'intersection est au
plus le produit des probabilités. C'est le chaînon que le socle
(`harris_kleitman_upper_upper`, `harris_kleitman_lower_lower`) laissait ouvert ;
la preuve dualise la forme « deux décroissants » en passant au complémentaire
de l'événement croissant. -/
theorem harris_kleitman_upper_lower {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 ℬ : Finset (Finset α))
    (h𝒜 : IsUpperSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) :
    #(𝒜 ∩ ℬ) * 2 ^ Fintype.card α ≤ #𝒜 * #ℬ := by
  classical
  have huniv : (Finset.univ : Finset (Finset α)).card = 2 ^ Fintype.card α := by
    rw [Finset.card_univ, Fintype.card_finset]
  -- Le complémentaire d'un événement croissant est décroissant.
  have hA' : IsLowerSet ((Finset.univ \ 𝒜 : Finset (Finset α)) : Set (Finset α)) := by
    intro ω₁ ω₂ hsub hmem
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun h => (Finset.mem_sdiff.mp hmem).2 (h𝒜 hsub h)⟩
  -- Harris–Kleitman « deux décroissants » sur (complémentaire de 𝒜, ℬ).
  have hk := harris_kleitman_lower_lower (Finset.univ \ 𝒜 : Finset (Finset α)) ℬ hA' hℬ
  have hcardA : #(Finset.univ \ 𝒜) = 2 ^ Fintype.card α - #𝒜 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ 𝒜), huniv]
  have hint : ((Finset.univ \ 𝒜 : Finset (Finset α)) ∩ ℬ) = ℬ \ (𝒜 ∩ ℬ) := by
    ext ω; simp [Finset.mem_sdiff]; tauto
  rw [hint, Finset.card_sdiff_of_subset (inter_subset_right), hcardA] at hk
  -- hk : (2^n − #𝒜) · #ℬ ≤ 2^n · (#ℬ − #(𝒜 ∩ ℬ)) ; arithmétique tronquée ℕ.
  have hN₂ : #(𝒜 ∩ ℬ) ≤ #ℬ := card_le_card (inter_subset_right)
  have e1 : (2 ^ Fintype.card α - #𝒜) * #ℬ
      = 2 ^ Fintype.card α * #ℬ - #𝒜 * #ℬ := Nat.sub_mul _ _ _
  have e2 : 2 ^ Fintype.card α * (#ℬ - #(𝒜 ∩ ℬ))
      = 2 ^ Fintype.card α * #ℬ - 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) := Nat.mul_sub _ _ _
  rw [e1, e2] at hk
  have final : 2 ^ Fintype.card α * #(𝒜 ∩ ℬ) ≤ #𝒜 * #ℬ :=
    (Nat.sub_le_sub_iff_left (Nat.mul_le_mul_left _ hN₂)).mp hk
  exact Nat.mul_comm _ _ ▸ final

/-- **Anti-corrélation connexité × confinement** : l'événement « `u` et `v`
sont reliés » (croissant, `connectedEvent_isUpperSet`) et l'événement « `A` est
fermé » (décroissant) sont anti-corrélés — forme uniforme finie de l'intuition
surcritique : être confiné défavorise les grandes connexions. -/
theorem card_inter_connected_closed_le (u v : V) (A : Finset V) :
    #((connectedEvent G u v) ∩ (closedEvent G A)) * 2 ^ Fintype.card (Edge G) ≤
      #(connectedEvent G u v) * #(closedEvent G A) :=
  harris_kleitman_upper_lower _ _ (connectedEvent_isUpperSet G)
    (closedEvent_isLowerSet G A)

-- ============================================================
-- Frontière pleine et comptage du confinement
-- ============================================================
variable (G : SimpleGraph V) [Fintype (Edge G)] [DecidableEq (Edge G)] [DecidableRel G.Adj]

/-- **Frontière pleine `δA`** : toutes les arêtes de `G` (ouvertes ou non) qui
quittent `A` — l'objet ω-indépendant du comptage. La frontière ouverte `boundary`
de la tranche 4 en est la trace sur une configuration (`boundary_eq_inter`). -/
def graphBoundary (A : Finset V) : Finset (Edge G) :=
  Finset.univ.filter (fun e : Edge G =>
    ∃ (u : V) (v : V) (huv : G.Adj u v),
      u ∈ A ∧ v ∉ A ∧ e = ⟨s(u, v), (show s(u, v) ∈ G.edgeSet from huv)⟩)

/-- **La frontière ouverte est la trace de la frontière pleine** : `∂A` (tranche 4)
est l'intersection de la configuration `ω` avec la frontière pleine. -/
theorem boundary_eq_inter_graphBoundary (ω : Finset (Edge G)) (A : Finset V) :
    boundary G ω A = ω ∩ graphBoundary G A := by
  ext e
  simp [boundary, graphBoundary, Finset.mem_filter, Finset.mem_inter]

/-- **Confinement ⇒ frontière pleine fermée** : si `A` est ω-fermé, aucune arête
de la frontière pleine n'est ouverte — `|δA|` coordonnées sont **forcées
fermées**, c'est le levier du comptage. -/
theorem disjoint_graphBoundary_of_openEdgeClosed {ω : Finset (Edge G)} {A : Finset V}
    (h : openEdgeClosed G ω (↑A : Set V)) : Disjoint ω (graphBoundary G A) :=
  Finset.disjoint_left.mpr fun _e heω hebd =>
    let ⟨_, _, _, huv, hu, hv, heq⟩ := Finset.mem_filter.mp hebd
    hv (h hu ⟨huv, heq ▸ heω⟩)

/-- **Comptage du confinement** : les configurations où `A` est ω-fermé sont au
plus `2^(N − |δA|)` — l'événement vit dans le sous-cube où les `|δA|` arêtes de
la frontière pleine sont fixées fermées (`N` = nombre total d'arêtes). -/
theorem card_closedEvent_le (A : Finset V) :
    (closedEvent G A).card ≤
      2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) := by
  have hsub : (closedEvent G A) ≤ (Finset.univ \ graphBoundary G A).powerset := by
    intro ω hω
    refine Finset.mem_powerset.mpr (Finset.subset_sdiff.mpr
      ⟨Finset.subset_univ _, disjoint_graphBoundary_of_openEdgeClosed G
        ((Finset.mem_filter.mp hω).2)⟩)
  calc (closedEvent G A).card
      ≤ ((Finset.univ \ graphBoundary G A).powerset).card := Finset.card_le_card hsub
    _ = 2 ^ (Finset.univ \ graphBoundary G A).card := Finset.card_powerset _
    _ = 2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]

/-- **Candidats au confinement de `v`** : les parties finies contenant `v`, de
cardinal au plus `k` — les témoins possibles de « la composante de `v` vit dans
`A` ». -/
def confineCandidates (v : V) (k : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun A => v ∈ A ∧ A.card ≤ k)

/-- **Couverture de l'événement « petite composante »** : si la composante de
`v` a au plus `k` sommets, elle est elle-même un candidat — `ω`-fermée
(`component_closed`), contenant `v` (`component_self`), de cardinal ≤ k. -/
theorem smallClusterEvent_subset_biUnion (v : V) (k : ℕ) :
    (smallClusterEvent G v k) ≤ (confineCandidates v k).biUnion (closedEvent G) := by
  intro ω hω
  rw [Finset.mem_biUnion]
  refine ⟨(Component G ω v).toFinset, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Set.mem_toFinset.mpr (component_self G v), (Finset.mem_filter.mp hω).2⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Set.coe_toFinset]
    exact component_closed (ω := ω) G v

/-- **Inégalité de sharpness finie** (uniforme, `p = 1/2`) : les configurations
où la composante ouverte de `v` reste de cardinal ≤ k sont au plus

`Σ_{A ∋ v, |A| ≤ k} 2^(N − |δA|)`,

soit, après normalisation par `2^N` (la mesure uniforme), la forme finie de
l'inégalité de décroissance de l'article surcritique (arXiv:2603.03257, §3.0) :
`P(|C(v)| ≤ k) ≤ Σ_{A ∋ v, |A| ≤ k} 2^(−|δA|)`. Tout profil isopérimétrique
bornant `|δA|` par dessous écrase donc exponentiellement les petites
composantes — c'est le contenu paramétrique fini que la limite surcritique de
l'article généralise. -/
theorem card_smallClusterEvent_le (v : V) (k : ℕ) :
    (smallClusterEvent G v k).card ≤ ∑ A ∈ confineCandidates v k,
      2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) := by
  calc (smallClusterEvent G v k).card
      ≤ ((confineCandidates v k).biUnion (closedEvent G)).card :=
        Finset.card_le_card (smallClusterEvent_subset_biUnion G v k)
    _ ≤ ∑ A ∈ confineCandidates v k, (closedEvent G A).card := Finset.card_biUnion_le
    _ ≤ ∑ A ∈ confineCandidates v k,
          2 ^ ((Finset.univ : Finset (Edge G)).card - (graphBoundary G A).card) :=
        Finset.sum_le_sum fun A _ => card_closedEvent_le G A

-- ============================================================
-- Témoins C₃ / C₄ : le comptage évalué sur le triangle et le carré
-- ============================================================

/-- **Frontière pleine du singleton `{0}` dans `C₃`** : les deux arêtes
`0—1` et `0—2` quittent `{0}`. -/
theorem graphBoundary_C3_singleton :
    #(graphBoundary C3 ({0} : Finset (Fin 3))) = 2 := by decide

/-- **Frontière pleine du singleton `{0}` dans `C₄`** : les deux arêtes `0—1`
et `0—3` quittent `{0}` (le carré n'a pas d'arête `0—2`). -/
theorem graphBoundary_C4_singleton :
    #(graphBoundary C4 ({0} : Finset (Fin 4))) = 2 := by decide

/-- **Un seul candidat au confinement `k = 1` sur `C₃`** : la partie `{0}`
elle-même (le candidat ne dépend que du type des sommets, pas de `G`). -/
theorem confineCandidates_C3_one :
    (confineCandidates (0 : Fin 3) 1).card = 1 := by decide

/-- **Un seul candidat au confinement `k = 1` sur `C₄`** : la partie `{0}`
elle-même. -/
theorem confineCandidates_C4_one :
    (confineCandidates (0 : Fin 4) 1).card = 1 := by decide

/-- **La somme de sharpness sur `C₃` (`k = 1`) vaut exactement `2 = 2^(3−2)`** :
un seul candidat `{0}`, de frontière pleine `2`, pour `N = 3` arêtes. -/
theorem sharpness_sum_C3_one :
    ∑ A ∈ confineCandidates (0 : Fin 3) 1,
      2 ^ ((Finset.univ : Finset (Edge C3)).card - #(graphBoundary C3 A)) = 2 := by
  decide

/-- **La somme de sharpness sur `C₄` (`k = 1`) vaut exactement `4 = 2^(4−2)`** :
un seul candidat `{0}`, de frontière pleine `2`, pour `N = 4` arêtes. -/
theorem sharpness_sum_C4_one :
    ∑ A ∈ confineCandidates (0 : Fin 4) 1,
      2 ^ ((Finset.univ : Finset (Edge C4)).card - #(graphBoundary C4 A)) = 4 := by
  decide

/-- **Sharpness fini sur `C₃`** : au plus `2` configurations sur `2^3 = 8`
gardent la composante de `0` confinée à un seul sommet — une proportion
`≤ 2^(−2) = 1/4`. La borne est exacte (les deux configurations ferment les
deux arêtes en `0`). -/
theorem sharpness_C3_one : (smallClusterEvent C3 (0 : Fin 3) 1).card ≤ 2 := by
  have h := card_smallClusterEvent_le C3 (0 : Fin 3) 1
  rw [sharpness_sum_C3_one] at h
  exact h

/-- **Sharpness fini sur `C₄`** : au plus `4` configurations sur `2^4 = 16`
gardent la composante de `0` confinée à un seul sommet — une proportion
`≤ 2^(−2) = 1/4`. -/
theorem sharpness_C4_one : (smallClusterEvent C4 (0 : Fin 4) 1).card ≤ 4 := by
  have h := card_smallClusterEvent_le C4 (0 : Fin 4) 1
  rw [sharpness_sum_C4_one] at h
  exact h

end Percolation
