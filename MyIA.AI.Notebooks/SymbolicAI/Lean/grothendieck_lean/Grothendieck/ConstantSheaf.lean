/-
Grothendieck Part 18 — The constant sheaf

Part 17 (SheafHom.lean) introduced the internal hom of sheaves, the first step
toward Cartesian closed structure on Sheaf J (Type _).

This module introduces the **constant sheaf functor** `constantSheaf J D`,
defined as the sheafification of the constant presheaf. It is left adjoint
to evaluation at a terminal object (constantSheafAdj), establishing a
fundamental adjunction in Grothendieck topos theory.

Key constructions bridged from Mathlib (`CategoryTheory.Sites.ConstantSheaf`):

  - `constantPresheafAdj` : constant presheaf ⊣ evaluation at terminal object
  - `constantSheaf J D` : the constant sheaf functor D ⥤ Sheaf J D
  - `constantSheafAdj` : constantSheaf ⊣ sheafSections at terminal object
  - `Sheaf.IsConstant` : predicate for sheaves in the essential image
  - `Sheaf.isConstant_iff_isIso_counit_app` : constancy ↔ counit is iso
  - `Sheaf.isConstant_iff_of_equivalence` : constancy invariant under equivalence
  - `Sheaf.isConstant_iff_forget` : constancy through forgetful functors

This is a key ingredient for understanding the "locally constant" nature of
sheaves and for connecting sheaf theory to cohomology (SGA 4 II, IV).

Epic #1646, See #2159. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.ConstantSheaf

universe v v' u u'

namespace Grothendieck.ConstantSheaf

open CategoryTheory Category Opposite Limits Functor Sheaf Adjunction

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type u'} [Category.{v'} D]

/-! ## 1. The constant presheaf adjunction

The constant presheaf functor `Functor.const Cᵒᵖ` sends an object X : D to the
constant presheaf at X. When C has a terminal object T, this functor is left
adjoint to evaluation at T (i.e., taking global sections).

This adjunction lifts to sheaves via sheafification.
-/

-- The constant presheaf functor is left adjoint to evaluation at a terminal object.
-- constantPresheafAdj : Functor.const Cᵒᵖ ⊣ (evaluation Cᵒᵖ D).obj (op T)
#check @constantPresheafAdj

/-! ## 2. The constant sheaf functor

The constant sheaf functor `constantSheaf J D` is defined as the composition
of the constant presheaf functor with sheafification:

  constantSheaf J D = Functor.const Cᵒᵖ ⋙ presheafToSheaf J D

It sends an object X : D to the sheafification of the constant presheaf at X.
This requires `HasWeakSheafify J D` (existence of sheafification).
-/

-- The constant sheaf functor: sheafification of the constant presheaf.
#check @constantSheaf

/-- Bridge construction: the constant sheaf at an object X : D, defined as the
    sheafification of the constant presheaf at X. -/
noncomputable def constantSheafObj (X : D) [HasWeakSheafify J D] :
    Sheaf J D :=
  (constantSheaf J D).obj X

/-! ## 3. The constant sheaf adjunction

When C has a terminal object T, the constant sheaf functor is left adjoint
to the "global sections" functor `sheafSections J D`.obj (op T):

  constantSheaf J D ⊣ (sheafSections J D).obj (op T)

This means: morphisms from the constant sheaf at X to a sheaf F correspond
naturally to morphisms X ⟶ F.obj.obj (op T) in D.
-/

-- The constant sheaf adjunction: constantSheaf ⊣ evaluation at terminal object.
#check @constantSheafAdj

/-- Bridge theorem: given a terminal object T, the constant sheaf functor is
    left adjoint to evaluation of sheaf sections at T. This is the fundamental
    adjunction underlying constant sheaf theory. -/
noncomputable def constantSheafAdjBridge {T : C} (hT : IsTerminal T)
    [HasWeakSheafify J D] :
    constantSheaf J D ⊣ (sheafSections J D).obj (op T) :=
  constantSheafAdj J D hT

/-! ## 4. The IsConstant predicate

A sheaf F is "constant" if it lies in the essential image of the constant
sheaf functor: there exists X : D such that F ≅ constantSheaf J D.obj X.

This is a property, not structure — constancy is a proposition.
-/

-- A sheaf is constant if it is in the essential image of constantSheaf.
#check @Sheaf.IsConstant

-- If F is constant, it lies in the essential image of constantSheaf.
#check @Sheaf.mem_essImage_of_isConstant

-- Isomorphisms preserve constancy.
#check @Sheaf.isConstant_congr

-- An iso with a constant sheaf witnesses constancy.
#check @Sheaf.isConstant_of_iso

/-! ## 5. Characterization via the counit

When the constant sheaf functor is fully faithful, a sheaf F is constant
if and only if the counit of the constant sheaf adjunction applied to F
is an isomorphism. This gives a practical criterion for constancy.
-/

-- When constantSheaf is fully faithful, constancy ↔ counit is iso.
#check @Sheaf.isConstant_iff_isIso_counit_app

/-- Bridge theorem: when the constant sheaf functor is fully faithful and
    C has a terminal object T, a sheaf is constant iff the counit of the
    adjunction applied to it is an isomorphism. -/
theorem isConstant_iff_counit_iso [HasWeakSheafify J D]
    [(constantSheaf J D).Faithful] [(constantSheaf J D).Full]
    (F : Sheaf J D) {T : C} (hT : IsTerminal T) :
    Sheaf.IsConstant J F ↔
      IsIso ((constantSheafAdj J D hT).counit.app F) :=
  CategoryTheory.Sheaf.isConstant_iff_isIso_counit_app J F hT

/-! ## 6. Invariance under equivalence

The property of being constant is invariant under equivalences of sheaf
categories induced by dense subsites. If G : C ⥤ C' is a dense subsite
morphism, then a sheaf on (C', K) is constant iff its pullback to (C, J)
is constant.
-/

-- Constancy is invariant under equivalence of sheaf categories.
#check @Sheaf.isConstant_iff_of_equivalence

/-! ## 7. Constancy through forgetful functors

Given a "forgetful" functor U : D ⥤ B, the property of being constant
is detected by postcomposing with U (when U preserves sheafification and
sheafCompose reflects isomorphisms).
-/

-- Constancy detected through forgetful functors.
#check @Sheaf.isConstant_iff_forget

/-! ## 8. Commutation with sheafCompose

The constant sheaf functor commutes with `sheafCompose J U` up to
isomorphism, provided that U preserves sheafification.
-/

-- constantSheaf commutes with sheafCompose up to iso.
#check @constantCommuteCompose

/-! ## 9. Bridge theorems: essential image and roundtrips

The essential image characterization gives roundtrip properties connecting
the IsConstant predicate to explicit witnesses.
-/

/-- Construction bridge: from an isomorphism with a constant sheaf, obtain
    a witness that the sheaf is constant. Uses `Sheaf.isConstant_of_iso`. -/
theorem isConstant_of_iso_bridge [HasWeakSheafify J D]
    {F : Sheaf J D} {X : D}
    (i : F ≅ (constantSheaf J D).obj X) :
    Sheaf.IsConstant J F := by
  exact CategoryTheory.Sheaf.isConstant_of_iso J i

/-- Construction bridge: constancy is preserved by isomorphism.
    Uses `Sheaf.isConstant_congr`. -/
theorem isConstant_congr_bridge [HasWeakSheafify J D]
    {F G : Sheaf J D} (i : F ≅ G) [Sheaf.IsConstant J F] :
    Sheaf.IsConstant J G := by
  exact CategoryTheory.Sheaf.isConstant_congr J i

end Grothendieck.ConstantSheaf
