/-
Grothendieck hommage — Partie 68 : la topologie de Grothendieck d'un espace
topologique.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Le cas fondateur de toute la théorie : les faisceaux sur un espace topologique
`T` sont les faisceaux sur le site `Opens T` — la catégorie des ouverts de `T`,
munie de la topologie des recouvrements ouverts. Toutes les Parties précédentes
travaillaient sur une catégorie `C` arbitraire ou sur des schémas ; celle-ci
rebranche la formalisation sur le point d'entrée historique (Mac Lane –
Moerdijk, chap. II).

Sur l'objet `X` (un ouvert de `T`), un crible `S` couvre lorsque tout point de
`X` appartient au domaine d'une flèche de `S` — la transcription exacte de
« la famille des domaines recouvre `X` ». Deux constructions sont données,
et leur coïncidence est le résultat central :

  - `opensTopology` : la topologie définie à la main (les trois axiomes de
    topologie de Grothendieck prouvés un à un sur les cribles d'ouverts) ;
  - `opensPretopology` : la prétopologie des recouvrements ouverts (les
    précribles dont les domaines recouvrent), avec ses trois axiomes de
    stabilité ;
  - `opensPretopology_toGrothendieck` : la topologie engendrée par la
    prétopologie est exactement la topologie définie à la main ;
  - `toPretopology_opensTopology` : réciproquement, la prétopologie des
    recouvrements ouverts est la plus grande prétopologie qui engendre cette
    topologie ;
  - `coversTop_isOpenCover_iff` : une famille d'ouverts `U : ι → Opens T` est
    couvrante au sens du site si et seulement si c'est un `IsOpenCover` au sens
    de la topologie usuelle de `T` — le pont entre les deux mondes.

Références :
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §1 (« Grothendieck topologies »).
  - Mathlib, `CategoryTheory.Sites.Spaces` (point de départ de la présente
    formalisation, dont ce module est l'équivalent own).

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`Spaces_en.lean`. Les énoncés, preuves et noms Lean restent identiques ; seules
les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Topology.Sets.OpenCover

namespace Grothendieck

open CategoryTheory TopologicalSpace CategoryTheory.Limits

universe u

section Contenu

variable (T : Type u) [TopologicalSpace T]

/-- La topologie de Grothendieck d'un espace topologique, définie à la main :
un crible `S` sur l'ouvert `X` couvre lorsque tout point de `X` appartient au
domaine d'une flèche de `S`. Les trois axiomes (le crible maximal couvre,
stabilité par image réciproque, transitivité) sont prouvés directement sur
cette description, sans passer par une prétopologie génératrice — c'est ce qui
donne au prédicat d'appartendance ses bonnes propriétés définitionnelles. -/
def opensTopology : GrothendieckTopology (Opens T) where
  sieves X := {S | ∀ x ∈ X, ∃ (U : Opens T) (f : U ⟶ X), S f ∧ x ∈ U}
  top_mem' _ _ hx := ⟨_, 𝟙 _, trivial, hx⟩
  pullback_stable' X Y S f hf y hy := by
    rcases hf y (f.le hy) with ⟨U, g, hg, hU⟩
    refine ⟨U ⊓ Y, homOfLE inf_le_right, ?_, hU, hy⟩
    apply S.downward_closed hg (homOfLE inf_le_left)
  transitive' X S hS R hR x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩
    exact ⟨_, g ≫ f, hg, hV⟩

/-- Caractérisation de l'appartenance : `S` couvre l'ouvert `X` pour la
topologie `opensTopology` si et seulement si tout point de `X` appartient au
domaine d'une flèche de `S`. -/
theorem mem_opensTopology_iff {X : Opens T} {S : Sieve X} :
    S ∈ opensTopology T X ↔ ∀ x ∈ X, ∃ (U : Opens T) (f : U ⟶ X), S f ∧ x ∈ U :=
  .rfl

/-- La prétopologie des recouvrements ouverts : un précrible `R` sur l'ouvert
`X` couvre lorsque tout point de `X` appartient au domaine d'une flèche de
`R`. Les axiomes de prétopologie (les isomorphismes couvrent, stabilité par
image réciproque, transitivité) sont prouvés à la main : pour les pullbacks,
le domaine-témoin est l'intersection `U ⊓ Y`, ouvert image réciproque de `U`
le long de `f : Y ⟶ X`. -/
def opensPretopology : Pretopology (Opens T) where
  coverings X := {R | ∀ x ∈ X, ∃ (U : Opens T) (f : U ⟶ X), R f ∧ x ∈ U}
  has_isos _ _ f _ _ hx := ⟨_, _, Presieve.singleton_self _, (inv f).le hx⟩
  pullbacks X Y f S hS x hx := by
    rcases hS _ (f.le hx) with ⟨U, g, hg, hU⟩
    refine ⟨_, _, Presieve.pullbackArrows.mk _ _ hg, ?_⟩
    have : U ⊓ Y ≤ pullback g f :=
      leOfHom (pullback.lift (homOfLE inf_le_left) (homOfLE inf_le_right) rfl)
    apply this ⟨hU, hx⟩
  transitive X S Ti hS hTi x hx := by
    rcases hS x hx with ⟨U, f, hf, hU⟩
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩

/-- Caractérisation de l'appartenance : `R` couvre l'ouvert `X` pour la
prétopologie `opensPretopology` si et seulement si tout point de `X`
appartient au domaine d'une flèche de `R`. -/
theorem mem_opensPretopology_iff {X : Opens T} {R : Presieve X} :
    R ∈ opensPretopology T X ↔ ∀ x ∈ X, ∃ (U : Opens T) (f : U ⟶ X), R f ∧ x ∈ U :=
  .rfl

/-- La prétopologie des recouvrements ouverts est la plus grande prétopologie
qui engendre la topologie `opensTopology`. Le sens direct déplie le crible
engendré par un précrible couvrant ; le sens retour utilise que tout précrible
est inclus dans le crible qu'il engendre. -/
@[simp]
theorem toPretopology_opensTopology :
    (opensTopology T).toPretopology = opensPretopology T := by
  apply le_antisymm
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, ⟨V, g₁, g₂, hg₂, _⟩, hU⟩
    exact ⟨V, g₂, hg₂, g₁.le hU⟩
  · intro X R hR x hx
    rcases hR x hx with ⟨U, f, hf, hU⟩
    exact ⟨U, f, Sieve.le_generate R U _ hf, hU⟩

/-- **Résultat central** : la topologie de Grothendieck engendrée par la
prétopologie des recouvrements ouverts est exactement la topologie définie à
la main `opensTopology`. Le site `(Opens T, opensTopology T)` se lit donc
indifféremment en termes de cribles ou de recouvrements ouverts. -/
@[simp]
theorem opensPretopology_toGrothendieck :
    (opensPretopology T).toGrothendieck = opensTopology T := by
  rw [← toPretopology_opensTopology]
  exact (Pretopology.gi (Opens T)).l_u_eq _

/-- Le pont vers la topologie usuelle : une famille d'ouverts `U : ι → Opens T`
couvre l'objet terminal du site si et seulement si c'est un recouvrement ouvert
au sens de `IsOpenCover`. La notion catégorique de recouvrement (les domaines
recouvrent `⊤`) coïncide avec la notion ensembliste (la réunion des `U i`
est égale à `univ`). -/
theorem coversTop_isOpenCover_iff {ι : Type*} (U : ι → Opens T) :
    (opensTopology T).CoversTop U ↔ IsOpenCover U := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ ⊤ isTerminalTop]
  dsimp only [opensTopology]
  simp only [IsOpenCover, eq_top_iff, SetLike.le_def, exists_and_right, Opens.mem_top,
    Opens.mem_iSup, forall_const]
  refine ⟨fun h x ↦ ?_, fun hU x hx ↦ ?_⟩
  · obtain ⟨V, ⟨u, ⟨i, ⟨hi⟩⟩⟩, hx⟩ := h x trivial
    exact ⟨i, leOfHom hi hx⟩
  · obtain ⟨i, hi⟩ := hU (x := x)
    exact ⟨U i, ⟨homOfLE le_top, ⟨i, ⟨𝟙 _⟩⟩⟩, hi⟩

end Contenu

end Grothendieck
