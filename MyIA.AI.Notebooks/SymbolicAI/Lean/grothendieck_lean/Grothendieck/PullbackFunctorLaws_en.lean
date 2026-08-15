/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Grothendieck Homage — Part 38 : pullback functor laws

Alexandre Grothendieck (1928-2014).

Phase 5 extension (#2159, EPIC #1646).

Parts 1-37 established the fundamentals : categories, sieves, topologies,
lattice laws, pullback identities, sheaf bases, covering closure,
calibration, subcanonicity, dense topologies, sheaves, internal hom, Cech
cohomology, Mayer-Vietoris limit, Kan extensions, adjunctions, monads,
equivalences, monoidal categories, limits and colimits, comma couples,
direct images, proper theorems on the arrow form (`J.Covers S f`), on the
bundled cover (`J.Cover X`) and the pullback pseudofunctor coherence laws
(Part 37).

Part 37 proved the **coherence laws** of the natural isomorphisms
`J.pullbackId X` and `J.pullbackComp f g` provided by Mathlib. This part goes
further : it states and proves the **functor laws themselves** — the functor
equalities that Mathlib does **not** provide (it only registers the
definitions `pullbackId`/`pullbackComp` at iso level) :

  - `pullback_functor_id` : pulling back along the identity is the identity
    functor — `J.pullback (𝟙 X) = 𝟭 (J.Cover X)`.
  - `pullback_functor_comp` : contravariance — pulling back along the
    composition `f ≫ g` is the composition of the pullbacks —
    `J.pullback (f ≫ g) = J.pullback g ⋙ J.pullback f`.
  - `pullback_functor_comp_assoc` : associativity of the contravariance (two
    groupings of the functor product).
  - `covers_pullback_comp` : the translation of the contravariance to the
    arrow form — `J.Covers S (f ≫ g)` is equivalent to
    `J.Covers (S.pullback g) f`.

Each proof is a **real tactic proof** (DEEP vein) : `Functor.ext` reduces the
functor equality to objects and arrows ; on objects,
`GrothendieckTopology.Cover.ext` + the Mathlib pullback laws
(`Sieve.pullback_id`, `Sieve.pullback_comp`) ; on arrows, `Subsingleton.elim`
(the codomain `J.Cover X` is a preorder).

EPIC #1646, Phase 5 (#2159). All `sorry`s eliminated at creation.

### i18n convention (EPIC #4980 ratified by user 2026-07-04)

This module is paired with its French twin in the sibling file
`PullbackFunctorLaws.lean` (sibling pair model, see PR #6154 for the pilot
on `Utility.lean`). The `_en` suffix is applied to this English file's
namespace (anti-collision, per code-style.md #4980). Theorem statements,
lemma names, Lean tactics and Mathlib references remain in English ; only the
docstrings `/-- ... -/` and comments `-- ...` differ between the two files
(byte-identity preservation).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.Category

namespace Grothendieck.PullbackFunctorLaws_en

open CategoryTheory

/-!
## Section 1 : functor laws

Mathlib defines the contravariant functor `J.pullback f : J.Cover Y ⥤ J.Cover X`
for an arrow `f : X ⟶ Y` (`@[simps obj]` : `(J.pullback f).obj S = S.pullback f`),
and the natural isomorphisms `J.pullbackId X` / `J.pullbackComp f g`. It does
**not** provide the corresponding functor laws. This module states and proves
them — functor equalities, stronger than the isomorphisms. Common strategy :
`Functor.ext` splits into the object component (Mathlib pullback laws) and the
arrow component (`Subsingleton.elim`, the preorder `J.Cover X` has
subsingleton hom sets).
-/

/-- Pulling back along the identity is the identity functor :
    `J.pullback (𝟙 X) = 𝟭 (J.Cover X)`.
    Proof : `Functor.ext` ; on objects, `Cover.ext` + `Sieve.pullback_id`
    (`(f ≫ 𝟙 X)` reduces to `f`) ; on arrows, `Subsingleton.elim`. -/
theorem pullback_functor_id {C : Type*} [Category C] (X : C)
    (J : GrothendieckTopology C) :
    J.pullback (𝟙 X) = 𝟭 (J.Cover X) := by
  apply CategoryTheory.Functor.ext
  · intro S T g
    apply Subsingleton.elim
  · intro S
    change S.pullback (𝟙 X) = S
    apply GrothendieckTopology.Cover.ext
    intro Y f
    rw [GrothendieckTopology.Cover.coe_pullback]
    simp [Category.comp_id]

/-- Contravariance of the pullback : `J.pullback (f ≫ g) = J.pullback g ⋙ J.pullback f`.
    Proof : `Functor.ext` ; on objects, `Cover.ext` + three `coe_pullback`
    rewrites bring the left membership to the right one via `simp`
    associativity ; on arrows, `Subsingleton.elim`. -/
theorem pullback_functor_comp {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) (g : Y ⟶ Z) :
    J.pullback (f ≫ g) = J.pullback g ⋙ J.pullback f := by
  apply CategoryTheory.Functor.ext
  · intro S T g'
    apply Subsingleton.elim
  · intro S
    change S.pullback (f ≫ g) = (S.pullback g).pullback f
    apply GrothendieckTopology.Cover.ext
    intro Y f'
    rw [GrothendieckTopology.Cover.coe_pullback, GrothendieckTopology.Cover.coe_pullback,
      GrothendieckTopology.Cover.coe_pullback]
    simp [Category.assoc]

/-- Associativity of the contravariance : pulling back along `f ≫ g ≫ h`
    is, whichever the grouping, pulling back along `h`, then `g`, then `f`.
    Proof : two rewrites of `pullback_functor_comp` then `rfl` (the
    associativity of the functor product is definitional). -/
theorem pullback_functor_comp_assoc {C : Type*} [Category C] {W X Y Z : C}
    (J : GrothendieckTopology C) (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    J.pullback (f ≫ g ≫ h) = J.pullback h ⋙ (J.pullback g ⋙ J.pullback f) := by
  rw [pullback_functor_comp J f (g ≫ h)]
  rw [pullback_functor_comp J g h]
  rfl

/-!
## Section 2 : arrow form (J.Covers)

The arrow form `J.Covers S f` is defined by `S.pullback f ∈ J Y` (Mathlib,
`GrothendieckTopology.Covers` ; `covers_iff` is `Iff.rfl`). The following
theorem translates the contravariance of the previous section into this form.
-/

/-- Translation of `pullback_functor_comp` to the arrow form : covering `S`
    along `f ≫ g` is equivalent to covering `S.pullback g` along `f`.
    Proof : `rw [covers_iff]` on both sides then `Sieve.pullback_comp` (both
    members are `∈ J X`). -/
theorem covers_pullback_comp {C : Type*} [Category C] {X Y Z : C}
    (J : GrothendieckTopology C) (f : X ⟶ Y) (g : Y ⟶ Z) (S : J.Cover Z) :
    J.Covers (S : Sieve Z) (f ≫ g) ↔ J.Covers (S.pullback g : Sieve Y) f := by
  rw [GrothendieckTopology.covers_iff, GrothendieckTopology.covers_iff]
  rw [Sieve.pullback_comp]
  simp

end Grothendieck.PullbackFunctorLaws_en
