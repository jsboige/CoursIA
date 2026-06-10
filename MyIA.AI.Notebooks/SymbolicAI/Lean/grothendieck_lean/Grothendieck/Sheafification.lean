/-
Grothendieck tribute — Part 13: Sheafification (the associated sheaf functor)
Alexandre Grothendieck (1928-2014).

Phase 8 extension (#2159, Epic #1646).

Part 7 (SheafBasics.lean) established that every sheaf is separated,
and that the sheaf condition transfers along topology comparisons.
Part 12 (DenseTopology.lean) studied the dense topology between ⊥ and ⊤.

This module introduces the **sheafification functor** (a.k.a. the "associated
sheaf functor" or "faisceau associé"), the left adjoint to the inclusion
of sheaves into presheaves:

  presheafToSheaf J : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D    ⊣    sheafToPresheaf

Its defining properties are:

  - Adjunction: for every presheaf P and sheaf F, morphisms from P to
    the underlying presheaf of F correspond bijectively to sheaf morphisms
    from the sheafification of P to F.
  - Unit: every presheaf P admits a canonical map `toSheafify J P : P ⟶ sheafify J P`.
  - Idempotency: if P is already a sheaf, the unit is an isomorphism.

We index Mathlib's `CategoryTheory.Sites.Sheafification` and
`CategoryTheory.Sites.LeftExact` into the `Grothendieck` namespace,
following the same bridge-theorem pattern as Parts 1-12.

Universe note: following Mathlib's `LeftExact.lean`, the sheafification
for `Type (max u v)`-valued presheaves on `C : Type u` with
`[Category.{v} C]` requires `HasSheafify J (Type (max u v))`.

Epic #1646, Phase 8 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact

universe v u

namespace Grothendieck

open CategoryTheory

/-!
## The sheafification adjunction

The sheafification functor `presheafToSheaf` is left adjoint to the
inclusion `sheafToPresheaf` of sheaves into presheaves. This adjunction
is the fundamental universal property of sheafification:

  Hom_Sheaf(sheafify P, F) ≅ Hom_Presheaf(P, underlying F)

The instance `HasSheafify J (Type (max u v))` (from LeftExact.lean)
provides sheafification for Type-valued presheaves on `C : Type u`
with `[Category.{v} C]`.
-/

/-- The sheafification adjunction: `presheafToSheaf ⊣ sheafToPresheaf`.
    This universal property says that maps from a presheaf P to the
    underlying presheaf of a sheaf F correspond bijectively to sheaf
    morphisms from the sheafification of P to F. -/
noncomputable def sheafification_universal {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    presheafToSheaf J (Type (max u v)) ⊣ sheafToPresheaf J (Type (max u v)) :=
  sheafificationAdjunction J (Type (max u v))

/-!
## The canonical map to the sheafification

Given a presheaf P, `toSheafify J P : P ⟶ sheafify J P` is the unit of
the adjunction. It sends each section of P to its image in the sheafification.
Every morphism from P to a sheaf factors uniquely through this map.

This is the "universal way to turn a presheaf into a sheaf".
-/

/-- The canonical map `toSheafify` is the unit of the sheafification
    adjunction. Uses `sheafificationAdjunction_unit_app` from Mathlib. -/
theorem toSheafify_is_unit {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    toSheafify J P = (sheafificationAdjunction J (Type (max u v))).unit.app P :=
  sheafificationAdjunction_unit_app J P

/-!
## Idempotency: sheafification of a sheaf is itself

If P is already a sheaf, then `toSheafify J P` is an isomorphism.
Intuitively, sheafifying a sheaf changes nothing — the construction
is idempotent.

This is the key property that makes sheafification a "reflection" along
the inclusion of sheaves into presheaves (a localization).
-/

/-- If P is a sheaf for J, then the canonical map `toSheafify J P` is
    an isomorphism. Sheafification is idempotent. Uses
    `isIso_toSheafify` from Mathlib. -/
theorem sheafify_of_sheaf_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (hP : Presheaf.IsSheaf J P) :
    IsIso (toSheafify J P) :=
  isIso_toSheafify J hP

/-- If P is a sheaf, then P is isomorphic to its own sheafification.
    This gives a concrete isomorphism rather than just an IsIso instance.
    Uses `isoSheafify` from Mathlib. -/
noncomputable def sheafify_iso_of_sheaf {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (hP : Presheaf.IsSheaf J P) :
    P ≅ sheafify J P :=
  isoSheafify J hP

/-!
## Naturality: sheafify commutes with presheaf morphisms

Given a morphism of presheaves η : P ⟶ Q, the sheafification functor
induces a morphism `sheafifyMap J η : sheafify P ⟶ sheafify Q`.

This makes sheafification functorial: it is not just an operation on
objects but a genuine functor.
-/

/-- A presheaf map η induces a map between the sheafifications.
    This is the functorial action of the sheafification endofunctor.
    Uses `sheafification_map` from Mathlib. -/
theorem sheafify_map_def {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (η : P ⟶ Q) :
    sheafifyMap J η = (sheafification J (Type (max u v))).map η :=
  have h : (sheafification J (Type (max u v))).map η = sheafifyMap J η :=
    @sheafification_map C _ J (Type (max u v)) _ _ _ _ η
  h.symm

/-!
## The sheafification endofunctor on presheaves

Composing the sheafification functor with the forgetful functor gives
an endofunctor on presheaves: `sheafification J (Type (max u v))`. It
maps every presheaf to a presheaf that happens to be a sheaf — the
"round-trip": presheaf → sheaf → presheaf.
-/

/-- `(sheafification J (Type (max u v))).obj P = sheafify J P`: the
    sheafification endofunctor applied to a presheaf gives its sheafification.
    Uses `sheafification_obj` from Mathlib. -/
theorem sheafification_obj_eq {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    (sheafification J (Type (max u v))).obj P = sheafify J P :=
  @sheafification_obj C _ J (Type (max u v)) _ _ P

/-!
## The unit is a natural transformation

The canonical map `toSheafify` is natural in the presheaf: for any
morphism η : P ⟶ Q, the obvious square commutes.
-/

/-- Naturality of the unit: `η ≫ toSheafify Q = toSheafify P ≫ sheafifyMap η`.
    Uses `toSheafify_naturality` from Mathlib. -/
theorem toSheafify_natural {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (η : P ⟶ Q) :
    η ≫ toSheafify J Q = toSheafify J P ≫ sheafifyMap J η :=
  toSheafify_naturality J η

end Grothendieck
