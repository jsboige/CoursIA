/-
Grothendieck tribute — Part 73: points of the site of opens and stalks.

Alexandre Grothendieck (1928-2014).

Extension Phase 2 (#2159, Epic #1646).

A point of a site in the sense of SGA 4 (IV 6.3) is a fiber functor: a
functor to `Type` whose category of elements is cofiltered and which meets
every covering sieve. Part 15 (`SitePoints`) established the abstract
theory; Part 72 (`Stalks`) the concrete computation of stalks on the site
of opens. This part solders the two together: to every point `x : T` we
attach a point of the site `(Opens T, opensTopology T)` — the fiber at `U`
is the (at most singleton) set of elements of `U` equal to `x` — and we
show that **the fiber functor of this point is exactly the stalk at `x`**:

  `stalkFiberIso : (opensPoint T x).presheafFiber.obj F ≅ F.stalk x`

This is Mathlib's explicit TODO (`Topology/Sheaves/Points.lean`: "Redefine
the stalks functors in Stalks.lean using
`GrothendieckTopology.Point.presheafFiber`") — the iso is established here
on the lake side. The proof is a double passage to colimits: germs form a
cone on the diagram of elements of the fiber (via `germ_res`), the
`toPresheafFiber` maps form a cone on the diagram of neighborhoods (via
`toPresheafFiber_w`), and the two universal properties answer each other
through the two extension lemmas (`stalk_hom_ext`,
`presheafFiber_hom_ext`). The iso is natural in the presheaf.

References:
  - SGA 4, IV 6.3 (points of a site, fiber functors).
  - S. Mac Lane, I. Moerdijk, *Sheaves in Geometry and Logic* [MM92],
    Chap. II §3, exercise (points of the space recover the stalks).
  - Mathlib, `Mathlib.Topology.Sheaves.Points` (the canonical point
    `Opens.pointGrothendieckTopology`, whose construction `opensPoint`
    transcribes on the own site).
  - Part 15 (`Grothendieck.SitePoints`): abstract fiber functors.
  - Part 70 (`Grothendieck.SpacesMathlib`): the equality of topologies.
  - Part 72 (`Grothendieck.Stalks`): concrete germs and stalks.

i18n convention (EPIC #4980 ratified 2026-07-04): this module is twinned
with `StalkPoints.lean`. Statements, proofs and Lean names remain
identical; only docstrings and comments differ.

Epic #1646, Phase 2 (#2159). No `sorry` introduced.
-/

import Grothendieck.Spaces
import Grothendieck.SpacesMathlib
import Mathlib.Topology.Sheaves.Points
import Mathlib.Topology.Sheaves.Stalks

universe u

namespace Grothendieck.StalkPoints_en

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

section Contenu

variable (T : Type u) [TopologicalSpace T] (x : T)

/-- **The point of the site of opens attached to `x`**: the fiber of an
open `U` is the set of elements of `U` equal to `x` (an at most singleton
type, inhabited exactly when `x ∈ U`). The category of elements — the open
neighborhoods of `x` and their inclusions — is cofiltered; every covering
sieve of an open containing `x` contains a neighborhood of `x`
(`mem_opensTopology_iff`). This is the transcription on the own site of
Mathlib's canonical point `Opens.pointGrothendieckTopology`, the equality
of topologies (Part 70) guaranteeing it is the same point. -/
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

/-- Every element of the fiber of `U` arises from a membership `x ∈ U`
(tautological converse of the construction). -/
theorem mem_of_fiber {U : Opens T} (p : (opensPoint T x).fiber.obj U) : x ∈ U :=
  p.down.down

/-- The element of the fiber encoding a membership `x ∈ U`. -/
def fiberElem {U : Opens T} (hx : x ∈ U) : (opensPoint T x).fiber.obj U :=
  ⟨⟨hx⟩⟩

variable (F : TopCat.Presheaf (Type u) (TopCat.of T))

/-- The cone of germs on the diagram of elements of the fiber: an element
`(U, p)` lives over an open `U` which contains `x`, and the germ restricts
along the inclusion (`germ_res`). -/
noncomputable def fiberToStalkCocone :
    Cocone ((CategoryOfElements.π (opensPoint T x).fiber).op ⋙ F) where
  pt := TopCat.Presheaf.stalk (X := TopCat.of T) F x
  ι.app e := TopCat.Presheaf.germ (X := TopCat.of T) F e.unop.1 x e.unop.2.down.down
  ι.naturality _ j' f := by
    obtain ⟨V, ⟨⟨hV⟩⟩⟩ := j'
    exact TopCat.Presheaf.germ_res (X := TopCat.of T) F f.unop.1 x hV

/-- **From the fiber to the stalk**: universal descent of the cone of
germs, a morphism from the fiber colimit to the stalk. -/
noncomputable def fiberToStalk :
    (opensPoint T x).presheafFiber.obj F ⟶ TopCat.Presheaf.stalk (X := TopCat.of T) F x :=
  colimit.desc _ (fiberToStalkCocone T x F)

/-- The cone of `toPresheafFiber` maps on the diagram of neighborhoods:
every neighborhood `U ∋ x` provides a section over `U`, hence an element of
the fiber colimit (`toPresheafFiber_w`). -/
noncomputable def stalkToFiberCocone :
    Cocone ((OpenNhds.inclusion (X := TopCat.of T) x).op ⋙ F) where
  pt := (opensPoint T x).presheafFiber.obj F
  ι.app j := (opensPoint T x).toPresheafFiber j.unop.1 ⟨⟨j.unop.2⟩⟩ F
  ι.naturality _ j' f := by
    obtain ⟨V, hV⟩ := j'
    exact (opensPoint T x).toPresheafFiber_w f.unop ⟨⟨hV⟩⟩ F

/-- **From the stalk to the fiber**: universal descent of the cone of
`toPresheafFiber` maps, a morphism from the stalk to the fiber. -/
noncomputable def stalkToFiber :
    TopCat.Presheaf.stalk (X := TopCat.of T) F x ⟶ (opensPoint T x).presheafFiber.obj F :=
  colimit.desc _ (stalkToFiberCocone T x F)

/-- The morphism `fiberToStalk` sends the `toPresheafFiber` of a section
over `U` to its germ: both sides are colimit components
(`colimit.ι_desc`). -/
theorem toPresheafFiber_fiberToStalk (U : Opens T) (p : (opensPoint T x).fiber.obj U) :
    (opensPoint T x).toPresheafFiber U p F ≫ fiberToStalk T x F =
      TopCat.Presheaf.germ (X := TopCat.of T) F U x p.down.down :=
  colimit.ι_desc _ _

/-- The morphism `stalkToFiber` sends every germ to the `toPresheafFiber`
of the section: both sides are colimit components (`colimit.ι_desc`). -/
theorem germ_stalkToFiber (U : Opens T) (hx : x ∈ U) :
    TopCat.Presheaf.germ (X := TopCat.of T) F U x hx ≫ stalkToFiber T x F =
      (opensPoint T x).toPresheafFiber U ⟨⟨hx⟩⟩ F :=
  colimit.ι_desc _ _

section

set_option backward.isDefEq.respectTransparency false

/-- The round trip stalk → fiber → stalk is the identity: two morphisms
out of the stalk coincide as soon as they coincide after every germ
(`stalk_hom_ext`), and the triangle closes via the two characterizations
above. -/
@[simp]
theorem stalkToFiber_comp_fiberToStalk :
    stalkToFiber T x F ≫ fiberToStalk T x F = 𝟙 _ := by
  apply TopCat.Presheaf.stalk_hom_ext (X := TopCat.of T)
  intro U hx
  rw [← Category.assoc, germ_stalkToFiber, toPresheafFiber_fiberToStalk,
    Category.comp_id]

/-- The round trip fiber → stalk → fiber is the identity: two morphisms
out of the fiber colimit coincide as soon as they coincide after every
`toPresheafFiber` (`presheafFiber_hom_ext`), and the triangle closes
symmetrically. -/
@[simp]
theorem fiberToStalk_comp_stalkToFiber :
    fiberToStalk T x F ≫ stalkToFiber T x F = 𝟙 _ := by
  apply (opensPoint T x).presheafFiber_hom_ext
  intro U p
  obtain ⟨⟨h⟩⟩ := p
  rw [← Category.assoc, toPresheafFiber_fiberToStalk, germ_stalkToFiber,
    Category.comp_id]

end

/-- **The stalk is the fiber functor of the attached point**: canonical iso
between the fiber of any presheaf `F` at the site point `opensPoint T x`
and the topological stalk of `F` at `x`. This iso is the explicit TODO of
`Mathlib.Topology.Sheaves.Points`; it solders the abstract theory of Part
15 to the concrete computation of Part 72. -/
noncomputable def stalkFiberIso :
    (opensPoint T x).presheafFiber.obj F ≅ TopCat.Presheaf.stalk (X := TopCat.of T) F x where
  hom := fiberToStalk T x F
  inv := stalkToFiber T x F
  hom_inv_id := fiberToStalk_comp_stalkToFiber T x F
  inv_hom_id := stalkToFiber_comp_fiberToStalk T x F

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The iso `stalkFiberIso` is natural in the presheaf: it intertwines
`presheafFiber.map` and `stalkFunctor.map`. -/
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

end Grothendieck.StalkPoints_en
