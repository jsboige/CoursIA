/-
Grothendieck Part 25 — Adjunctions (English mirror of Adjunction.lean)

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Alongside the Yoneda lemma, adjoint functors are the most universal
categorical tool of Grothendieck-style algebraic geometry. Grothendieck uses
them everywhere: the Spec ⊣ Γ adjunction (geometry ↔ algebra), the
sheafification ⊣ inclusion adjunction (presheaves ↔ sheaves), the fiber ⊣
skyscraper-sheaf adjunction (points ↔ sheaves), and the adjoint derived
functors of cohomology.

An adjunction L ⊣ R between two categories is a natural equivalence
`Hom_D(L X, Y) ≃ Hom_C(X, R Y)`. It balances two dual viewpoints:
"resolve on the left" (L builds free objects) and "forget on the right"
(R returns to the base category). Every universal construction (limits,
colimits, free objects) is expressible as an adjunction.

Mathlib 4 formalises all of this infrastructure in
`Mathlib.CategoryTheory.Adjunction`:
  - `CategoryTheory.Adjunction : C ⥤ D → Type*` — the L ⊣ R structure
  - `CategoryTheory.Adjunction.homEquiv` — the natural Hom equivalence
  - `CategoryTheory.Adjunction.unit` / `counit` — the natural transformations
  - `CategoryTheory.Adjunction.left_triangle` / `right_triangle` — triangle identities
  - `CategoryTheory.IsLeftAdjoint` — the property of having a right adjoint
  - `CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit` — full faithfulness via the unit

This module re-exposes these facts as an organised pedagogical tour.

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English mirror of `Adjunction.lean`. Theorem statements,
lemma names, Lean tactics and Mathlib references stay in English. Only the
**docstrings `/-- ... -/`** and **comments `-- ...`** differ between the two
files. Anti-§D byte-identity guaranteed.
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

universe v₁ v₂ u₁ u₂

namespace Grothendieck.Adjunction_en

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-!
## 1. The adjunction structure

An adjunction `L ⊣ R` between a functor `L : C ⥤ D` (left adjoint) and
`R : D ⥤ C` (right adjoint) is the natural equivalence in both variables:
`Hom_D(L X, Y) ≃ Hom_C(X, R Y)`.
-/

-- The L ⊣ R adjunction structure between two functors.
#check @CategoryTheory.Adjunction

-- The natural Hom equivalence Hom_D(L X, Y) ≃ Hom_C(X, R Y).
#check @CategoryTheory.Adjunction.homEquiv

-- The notation `L ⊣ R` denotes `Adjunction L R` (L left adjoint to R).
#check @CategoryTheory.Adjunction

/-!
## 2. The unit and counit, triangle identities

Every adjunction `L ⊣ R` determines the unit `η : 𝟭 C ⟶ R ⋙ L` and the
counit `ε : L ⋙ R ⟶ 𝟭 D`, satisfying the triangle identities. Components at
an object are obtained via `h.unit.app X` and `h.counit.app Y` (natural
transformation application).
-/

-- The unit η : 𝟭 C ⟶ R ⋙ L of the adjunction.
#check @CategoryTheory.Adjunction.unit

-- The counit ε : L ⋙ R ⟶ 𝟭 D of the adjunction.
#check @CategoryTheory.Adjunction.counit

-- First triangle identity (counit after L of the unit = identity).
#check @CategoryTheory.Adjunction.left_triangle

-- Second triangle identity (unit after R of the counit = identity).
#check @CategoryTheory.Adjunction.right_triangle

/-!
## 3. Existence of an adjoint

A functor with a right adjoint is a "left adjoint"
(`CategoryTheory.Functor.IsLeftAdjoint`). This is a Prop-class recording the
existence of an `R` with `L ⊣ R`.
-/

-- The property of a functor being a left adjoint (having an R with L ⊣ R).
#check @CategoryTheory.Functor.IsLeftAdjoint

/-!
## 4. Preservation of limits and colimits

Practical theorem: a right adjoint preserves limits, a left adjoint preserves
colimits.
-/

-- A right adjoint preserves limits.
#check @CategoryTheory.Adjunction.rightAdjoint_preservesLimits

-- A left adjoint preserves colimits.
#check @CategoryTheory.Adjunction.leftAdjoint_preservesColimits

/-!
## 5. Full faithfulness of an adjoint

The unit is a natural isomorphism iff the left adjoint is fully faithful;
symmetrically for the counit and the right adjoint.
-/

-- The left adjoint is fully faithful if the unit is an isomorphism.
#check @CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit

-- The right adjoint is fully faithful if the counit is an isomorphism.
#check @CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit

/-!
## 6. Bridge theorems

Reformulations in the project namespace, bridging the Mathlib facts.
-/

/-- Bridge: the hom-equivalence of an adjunction L ⊣ R, viewed as a family
    natural in X and Y. This is the datum that makes an adjunction a natural
    bijection, not just a pointwise one. -/
def homEquiv_family {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    (X : C) → (Y : D) → (L.obj X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  fun X Y ↦ h.homEquiv X Y

/-- Bridge: a left adjoint preserves colimits. The structural fact most used in
    algebraic geometry to transport colimits along "free" functors
    (sheafification, tensoring, inverse image). -/
theorem leftAdjoint_preserves_colimits {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    PreservesColimitsOfSize L :=
  h.leftAdjoint_preservesColimits

/-- Bridge: a right adjoint preserves limits. -/
theorem rightAdjoint_preserves_limits {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    PreservesLimitsOfSize R :=
  h.rightAdjoint_preservesLimits

/-- Bridge: in an adjunction L ⊣ R, if the unit is a natural isomorphism then
    the left adjoint L is fully faithful (full reflection criterion). -/
noncomputable def fully_faithful_of_unit_iso {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    [IsIso h.unit] : L.FullyFaithful :=
  h.fullyFaithfulLOfIsIsoUnit

/-- Bridge: in an adjunction L ⊣ R, if the counit is a natural isomorphism
    then the right adjoint R is fully faithful. -/
noncomputable def fully_faithful_of_counit_iso {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    [IsIso h.counit] : R.FullyFaithful :=
  h.fullyFaithfulROfIsIsoCounit

end Grothendieck.Adjunction_en
