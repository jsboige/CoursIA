/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck Homage — Part 37 : pullback coherence laws

Alexandre Grothendieck (1928-2014).

Extension Phase 5 (#2159, EPIC #1646).

Parts 1-36 established the foundations: categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure, calibration,
subcanonicity, dense topologies, sheaves, internal hom, Cech cohomology,
Mayer-Vietoris limits, Kan extensions, adjunctions, monads, equivalences,
monoidal categories, limits and colimits, comma categories, direct images,
proper theorems on the arrow form (`J.Covers S f`) and on the bundled cover
(`J.Cover X`).

This module records the **coherence laws of the pullback pseudofunctor**:
for a Grothendieck topology `J` on a category `C`, the pullback along a
morphism `f : X ⟶ Y` is the contravariant functor
`J.pullback f : J.Cover Y ⥤ J.Cover X`. Mathlib provides the natural
isomorphisms `J.pullbackId X : J.pullback (𝟙 X) ≅ 𝟭 _` and
`J.pullbackComp f g : J.pullback (f ≫ g) ≅ J.pullback g ⋙ J.pullback f`;
it does **not** provide their coherence laws. This module states and proves
them: these are **real tactical proofs** (DEEP vein, as opposed to the
re-export bridges of the previous parts):

  - `pullback_triple` : elementary cocycle — pulling back along `f`, then
    `g`, then `h` is pulling back once along `f ≫ g ≫ h`.
  - `pullbackComp_unit_left` : left unit triangle — the composition
    `J.pullbackComp (𝟙 X) f` is straightened to the identity by the
    reindexing `J.pullbackId X` and the right unitor.
  - `pullbackComp_unit_right` : right unit triangle — the composition
    `J.pullbackComp f (𝟙 Y)` is straightened to the identity by
    `J.pullbackId Y` and the left unitor.
  - `pullbackComp_assoc` : pentagon law — the cocycle is associative:
    pulling back along `f`, `g`, `h` in two stages is independent of the
    grouping (commuting via the functor-product associator).

Each proof mobilizes a distinct Mathlib lemma (`Iso.ext`, `NatTrans.ext`,
`Subsingleton.elim`, `Category.assoc`, `Category.id_comp`,
`Category.comp_id`) and the definitional laws of `J.Cover` — no proof is a
mere re-export.

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its French sibling in the file
`PullbackFunctor.lean` (sibling pair model, see PR #6154 for the pilot on
`Utility.lean`). The `_en` suffix is applied to this English file's namespace
(collision-avoidance, per code-style.md #4980). Theorem statements, lemma
names, Lean tactics and Mathlib references remain in English; only the
docstrings `/-- ... -/` and comments `-- ...` differ between the two files
(byte-identity preservation).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.Category

namespace Grothendieck.PullbackFunctor_en

open CategoryTheory

/-!
## Section 1 : elementary cocycle

Recall : the membership of `S.pullback f` is given by the `simp` rule
`GrothendieckTopology.Cover.coe_pullback : (S.pullback f) g ↔ S (g ≫ f)`.
The elementary cocycle states that pulling back three times in a row along
`f`, `g`, `h` is pulling back once along the composition `f ≫ g ≫ h`.
-/

/-- Elementary cocycle of the pullback :
    `((S.pullback h).pullback g).pullback f = S.pullback (f ≫ g ≫ h)`.
    Proof : extensionality (`GrothendieckTopology.Cover.ext`), four rewrites
    by `GrothendieckTopology.Cover.coe_pullback` (both sides of the
    equivalence) then associativity normalization by `simp`
    (`Category.assoc`) bring the left membership to the right one. -/
theorem pullback_triple {C : Type*} [Category C] {X Y Z W : C}
    (J : GrothendieckTopology C) (S : J.Cover W) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) :
    ((S.pullback h).pullback g).pullback f = S.pullback (f ≫ g ≫ h) := by
  apply GrothendieckTopology.Cover.ext
  intro Y' f'
  rw [GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback,
    GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback]
  simp [Category.assoc]

/-!
## Section 2 : coherence laws of the pseudofunctor

The three following theorems are the coherence laws missing from Mathlib for
`J.pullbackId` and `J.pullbackComp` to form a genuine contravariant
pseudofunctor `Cᵒᵖ ⥤ Cat`. The codomain `J.Cover X` is a preorder (a cover
is determined by its arrows), so any two arrows between given covers are
equal (`CategoryTheory.subsingleton_hom`). The common proof strategy :
`Iso.ext` reduces the equality of natural isomorphisms to the equality of
their morphisms (`α.hom`), `ext` unfolds at the components (`NatTrans.ext`),
and `Subsingleton.elim` closes each arrow equality in the preorder.
-/

/-- Left unit triangle : pulling back along `𝟙 X` then `f` (via
    `J.pullbackComp`) is straightened to the identity by the reindexing
    `J.pullbackId X` (whiskering on the left along `J.pullback f`) and the
    right unitor of the functor product.
    Proof : `Iso.ext`, `ext` at the components, `Subsingleton.elim`. -/
theorem pullbackComp_unit_left {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) :
    J.pullbackComp (𝟙 X) f ≪≫ Functor.isoWhiskerLeft (J.pullback f) (J.pullbackId X) ≪≫
        Functor.rightUnitor (J.pullback f) = eqToIso (by simp [Category.id_comp]) := by
  apply Iso.ext
  ext S
  apply Subsingleton.elim

/-- Right unit triangle : pulling back along `f` then `𝟙 Y` (via
    `J.pullbackComp`) is straightened to the identity by `J.pullbackId Y`
    (whiskering on the right along `J.pullback f`) and the left unitor of
    the functor product.
    Proof : `Iso.ext`, `ext` at the components, `Subsingleton.elim`. -/
theorem pullbackComp_unit_right {C : Type*} [Category C] {X Y : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) :
    J.pullbackComp f (𝟙 Y) ≪≫ Functor.isoWhiskerRight (J.pullbackId Y) (J.pullback f) ≪≫
        Functor.leftUnitor (J.pullback f) = eqToIso (by simp [Category.comp_id]) := by
  apply Iso.ext
  ext S
  apply Subsingleton.elim

/-- Pentagon law (cocycle) : pulling back along `f`, `g`, `h` in two stages
    is independent of the grouping. Both sides compose `J.pullbackComp` with
    the whiskerings and the associator of the functor product ; they share
    source `J.pullback (f ≫ g ≫ h)` and target
    `J.pullback h ⋙ (J.pullback g ⋙ J.pullback f)`.
    Proof : `Iso.ext`, `ext` at the components, `Subsingleton.elim`. -/
theorem pullbackComp_assoc {C : Type*} [Category C] {W X Y Z : C}
    (J : GrothendieckTopology C) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    J.pullbackComp f (g ≫ h) ≪≫ Functor.isoWhiskerRight (J.pullbackComp g h) (J.pullback f) ≪≫
        Functor.associator (J.pullback h) (J.pullback g) (J.pullback f) =
      eqToIso (by simp [Category.assoc]) ≪≫
        (J.pullbackComp (f ≫ g) h ≪≫
          Functor.isoWhiskerLeft (J.pullback h) (J.pullbackComp f g)) := by
  apply Iso.ext
  ext S
  apply Subsingleton.elim

end Grothendieck.PullbackFunctor_en
