/-
Grothendieck hommage — Partie 73 : points du site des ouverts et tiges.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

Un point d'un site au sens de SGA 4 (IV 6.3) est un foncteur fibre : un
foncteur vers `Type` dont la catégorie des éléments est cofiltrée et qui
rencontre tous les cribles couvrants. La Partie 15 (`SitePoints`) avait
établi la théorie abstraite ; la Partie 72 (`Stalks`) le calcul concret des
tiges sur le site des ouverts. Cette partie soude les deux : à tout point
`x : T` on associe un point du site `(Opens T, opensTopology T)` — la fibre
en `U` est l'ensemble (au plus unimodal) des éléments de `U` égaux à `x` —
et l'on montre que **le foncteur fibre de ce point est exactement la tige
en `x`** :

  `stalkFiberIso : (opensPoint T x).presheafFiber.obj F ≅ F.stalk x`

C'est le TODO explicite de Mathlib (`Topology/Sheaves/Points.lean` :
« Redefine the stalks functors in Stalks.lean using
`GrothendieckTopology.Point.presheafFiber` ») — l'iso est ici établi côté
lake. La preuve est un double passage à la colimite : les germes forment un
cône sur le diagramme des éléments de la fibre (via `germ_res`), les
`toPresheafFiber` forment un cône sur le diagramme des voisinages (via
`toPresheafFiber_w`), et les deux universalités se répondent via les deux
lemmes d'extension (`stalk_hom_ext`, `presheafFiber_hom_ext`). L'iso est
naturel en le préfaisceau.

Références :
  - SGA 4, IV 6.3 (points d'un site, foncteurs fibres).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3, exercice (les points de l'espace redonnent les tiges).
  - Mathlib, `Mathlib.Topology.Sheaves.Points` (le point canonique
    `Opens.pointGrothendieckTopology`, dont la construction de
    `opensPoint` est la transcription sur le site own).
  - Partie 15 (`Grothendieck.SitePoints`) : foncteurs fibres abstraits.
  - Partie 70 (`Grothendieck.SpacesMathlib`) : l'égalité des topologies.
  - Partie 72 (`Grothendieck.Stalks`) : germes et tiges concrets.

Convention i18n (EPIC #4980 ratifiée 2026-07-04) : ce module est jumelé avec
`StalkPoints_en.lean`. Les énoncés, preuves et noms Lean restent identiques ;
seules les docstrings et les commentaires diffèrent.

Epic #1646, Phase 2 (#2159). Aucun `sorry` introduit.
-/

import Grothendieck.Spaces
import Grothendieck.SpacesMathlib
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Stalks

universe u

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

section Contenu

variable (T : Type u) [TopologicalSpace T] (x : T)

/-- **Le point du site des ouverts associé à `x`** : la fibre d'un ouvert
`U` est l'ensemble des éléments de `U` égaux à `x` (un type au plus
singleton, habité exactement lorsque `x ∈ U`). La catégorie des éléments —
les voisinages ouverts de `x` et leurs inclusions — est cofiltrée ; tout
crible couvrant d'un ouvert contenant `x` contient un voisinage de `x`
(`mem_opensTopology_iff`). C'est la transcription sur le site own du point
canonique `Opens.pointGrothendieckTopology` de Mathlib, l'égalité des
topologies (Partie 70) garantissant qu'il s'agit du même point. -/
def opensPoint : GrothendieckTopology.Point (opensTopology T) where
  fiber.obj U := ULift.{u} (PLift (x ∈ U))
  fiber.map f := ↾fun h ↦ ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
          ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hU⟩⟩
    rw [mem_opensTopology_iff] at hR
    obtain ⟨V, f, hf, hV⟩ := hR x hU
    exact ⟨_, _, hf, ⟨⟨hV⟩⟩, rfl⟩

/-- Tout élément de la fibre de `U` provient d'une appartenance `x ∈ U`
(réciproque tautologique de la construction). -/
theorem mem_of_fiber {U : Opens T} (p : (opensPoint T x).fiber.obj U) : x ∈ U :=
  p.down.down

/-- L'élément de la fibre codant une appartenance `x ∈ U`. -/
def fiberElem {U : Opens T} (hx : x ∈ U) : (opensPoint T x).fiber.obj U :=
  ⟨⟨hx⟩⟩

variable (F : TopCat.Presheaf (Type u) (TopCat.of T))

/-- Le cône des germes sur le diagramme des éléments de la fibre : un
élément `(U, p)` vit au-dessus d'un ouvert `U` qui contient `x`, et le germe
s'y restreint (`germ_res`). -/
noncomputable def fiberToStalkCocone :
    Cocone ((CategoryOfElements.π (opensPoint T x).fiber).op ⋙ F) where
  pt := TopCat.Presheaf.stalk (X := TopCat.of T) F x
  ι.app e := TopCat.Presheaf.germ (X := TopCat.of T) F e.unop.1 x e.unop.2.down.down
  ι.naturality _ j' f := by
    obtain ⟨V, ⟨⟨hV⟩⟩⟩ := j'
    exact TopCat.Presheaf.germ_res (X := TopCat.of T) F f.unop.1 x hV

/-- **De la fibre vers la tige** : descente universelle du cône des germes,
morphisme de la fibre colimite vers la tige. -/
noncomputable def fiberToStalk :
    (opensPoint T x).presheafFiber.obj F ⟶ TopCat.Presheaf.stalk (X := TopCat.of T) F x :=
  colimit.desc _ (fiberToStalkCocone T x F)

/-- Le cône des `toPresheafFiber` sur le diagramme des voisinages : chaque
voisinage `U ∋ x` fournit une section au-dessus de `U`, donc un élément de
la fibre colimite (`toPresheafFiber_w`). -/
noncomputable def stalkToFiberCocone :
    Cocone ((OpenNhds.inclusion (X := TopCat.of T) x).op ⋙ F) where
  pt := (opensPoint T x).presheafFiber.obj F
  ι.app j := (opensPoint T x).toPresheafFiber j.unop.1 ⟨⟨j.unop.2⟩⟩ F
  ι.naturality _ j' f := by
    obtain ⟨V, hV⟩ := j'
    exact (opensPoint T x).toPresheafFiber_w f.unop ⟨⟨hV⟩⟩ F

/-- **De la tige vers la fibre** : descente universelle du cône des
`toPresheafFiber`, morphisme de la tige vers la fibre. -/
noncomputable def stalkToFiber :
    TopCat.Presheaf.stalk (X := TopCat.of T) F x ⟶ (opensPoint T x).presheafFiber.obj F :=
  colimit.desc _ (stalkToFiberCocone T x F)

/-- Le morphisme `fiberToStalk` envoie le `toPresheafFiber` d'une section
au-dessus de `U` sur son germe : les deux côtés sont des composantes de
colimite (`colimit.ι_desc`). -/
theorem toPresheafFiber_fiberToStalk (U : Opens T) (p : (opensPoint T x).fiber.obj U) :
    (opensPoint T x).toPresheafFiber U p F ≫ fiberToStalk T x F =
      TopCat.Presheaf.germ (X := TopCat.of T) F U x p.down.down :=
  colimit.ι_desc _ _

/-- Le morphisme `stalkToFiber` envoie chaque germe sur le `toPresheafFiber`
de la section : les deux côtés sont des composantes de colimite
(`colimit.ι_desc`). -/
theorem germ_stalkToFiber (U : Opens T) (hx : x ∈ U) :
    TopCat.Presheaf.germ (X := TopCat.of T) F U x hx ≫ stalkToFiber T x F =
      (opensPoint T x).toPresheafFiber U ⟨⟨hx⟩⟩ F :=
  colimit.ι_desc _ _

section

set_option backward.isDefEq.respectTransparency false

/-- La section tige → fibre → tige est l'identité : deux morphismes sortant
de la tige coïncident dès qu'ils coïncident après tout germe
(`stalk_hom_ext`), et le triangle se ferme par les deux caractérisations
ci-dessus. -/
@[simp]
theorem stalkToFiber_comp_fiberToStalk :
    stalkToFiber T x F ≫ fiberToStalk T x F = 𝟙 _ := by
  apply TopCat.Presheaf.stalk_hom_ext (X := TopCat.of T)
  intro U hx
  rw [← Category.assoc, germ_stalkToFiber, toPresheafFiber_fiberToStalk,
    Category.comp_id]

/-- La section fibre → tige → fibre est l'identité : deux morphismes sortant
de la fibre colimite coïncident dès qu'ils coïncident après tout
`toPresheafFiber` (`presheafFiber_hom_ext`), et le triangle se ferme de
façon symétrique. -/
@[simp]
theorem fiberToStalk_comp_stalkToFiber :
    fiberToStalk T x F ≫ stalkToFiber T x F = 𝟙 _ := by
  apply (opensPoint T x).presheafFiber_hom_ext
  intro U p
  obtain ⟨⟨h⟩⟩ := p
  rw [← Category.assoc, toPresheafFiber_fiberToStalk, germ_stalkToFiber,
    Category.comp_id]

end

/-- **La tige est le foncteur fibre du point associé** : iso canonique entre
la fibre de tout préfaisceau `F` au point du site `opensPoint T x` et la tige
topologique de `F` en `x`. Cet iso est le TODO explicite de
`Mathlib.Topology.Sheaves.Points` ; il soude la théorie abstraite de la
Partie 15 au calcul concret de la Partie 72. -/
noncomputable def stalkFiberIso :
    (opensPoint T x).presheafFiber.obj F ≅ TopCat.Presheaf.stalk (X := TopCat.of T) F x where
  hom := fiberToStalk T x F
  inv := stalkToFiber T x F
  hom_inv_id := fiberToStalk_comp_stalkToFiber T x F
  inv_hom_id := stalkToFiber_comp_fiberToStalk T x F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- L'iso `stalkFiberIso` est naturel en le préfaisceau : il entrelace
`presheafFiber.map` et `stalkFunctor.map`. -/
theorem stalkFiberIso_naturality {G : TopCat.Presheaf (Type u) (TopCat.of T)} (f : F ⟶ G) :
    (opensPoint T x).presheafFiber.map f ≫ fiberToStalk T x G =
      fiberToStalk T x F ≫
        (TopCat.Presheaf.stalkFunctor (Type u) (X := TopCat.of T) x).map f := by
  apply (opensPoint T x).presheafFiber_hom_ext
  intro U p
  rw [← Category.assoc, (opensPoint T x).toPresheafFiber_naturality f U p, Category.assoc]
  rw [toPresheafFiber_fiberToStalk T x G U p]
  rw [← Category.assoc, toPresheafFiber_fiberToStalk T x F U p]
  exact (@TopCat.Presheaf.stalkFunctor_map_germ (Type u) _ _ (X := TopCat.of T)
    F G U x p.down.down f).symm

end Contenu

end Grothendieck
