/-
Grothendieck Part 27 — Equivalences of categories [English mirror of Equivalences.lean]

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Equivalence of categories is the "right" notion of sameness in category
theory: two equivalent categories are indistinguishable from the viewpoint
of the theory, even though they need not be equal as sets of objects.
Grothendieck uses it constantly: the Yoneda lemma says every representable
functor is equivalent to a Hom functor; algebraic geometry identifies affine
schemes with the opposite category of commutative rings (an
anti-equivalence of categories); toposes are defined as categories
equivalent to the category of sheaves of sets on a site; and all of derived
category theory rests on equivalences of triangulated categories.

An **equivalence of categories** `C ≌ D` is the data of two functors
`functor : C ⥤ D` and `inverse : D ⥤ C`, together with two natural
isomorphisms `unitIso : 𝟭 C ≅ functor ⋙ inverse` and
`counitIso : inverse ⋙ functor ≅ 𝟭 D` satisfying the triangle identities.
It is the categorical analogue of an isomorphism, but "up to isomorphism on
objects" — which is the correct notion: objects have no intrinsic substance
in category theory, only arrows matter.

The practical criterion (the most used one): a functor is an equivalence if
and only if it is **fully faithful** (bijects the Homs) and **essentially
surjective** (every target object is isomorphic to the image of a source
object). Mathlib encodes this in the `Functor.IsEquivalence` class.

Mathlib 4 formalises all of this infrastructure in
`Mathlib.CategoryTheory.Equivalence`:
  - `CategoryTheory.Equivalence : Type*` — the C ≌ D structure
  - `CategoryTheory.Equivalence.functor` / `inverse` — the two functors
  - `CategoryTheory.Equivalence.unitIso` / `counitIso` — the natural isos
  - `CategoryTheory.Equivalence.functor_unitIso_comp` — the triangle identity
  - `CategoryTheory.Equivalence.refl` / `symm` / `trans` — (2-)groupoid structure
  - `CategoryTheory.Functor.FullyFaithful` — the functor bijects the Homs
  - `CategoryTheory.Functor.EssSurj` — essential surjectivity
  - `CategoryTheory.Functor.IsEquivalence` — the property of being an equivalence

This module re-exposes these facts as an organised pedagogical tour, for
learners meeting equivalences for the first time, mirroring the
`Grothendieck.Adjunction` and `Grothendieck.Limits` modules (an adjunction
gives "local" equivalences Hom_D(LX,Y) ≃ Hom_C(X,RY); an equivalence is an
adjunction where the unit and counit are isomorphisms).

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English mirror of `Equivalences.lean`. Theorem statements,
lemma names, Lean tactics and Mathlib references stay in English. Only the
**docstrings `/-- ... -/`** and **comments `-- ...`** differ between the two
files. Anti-§D byte-identity guaranteed.
-/

import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.FullyFaithful

universe v₁ v₂ u₁ u₂

namespace Grothendieck.Equivalences_en

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-!
## 1. The equivalence structure

An equivalence `e : C ≌ D` is the data of a functor `e.functor : C ⥤ D`, an
inverse `e.inverse : D ⥤ C`, and two natural isomorphisms
`e.unitIso : 𝟭 C ≅ e.functor ⋙ e.inverse` and
`e.counitIso : e.inverse ⋙ e.functor ≅ 𝟭 D`. The notation `C ≌ D` denotes
`Equivalence C D`.
-/

-- The structure of an equivalence of categories C ≌ D.
#check @CategoryTheory.Equivalence

-- The "forward" functor e.functor : C ⥤ D of the equivalence.
#check @CategoryTheory.Equivalence.functor

-- The "backward" functor e.inverse : D ⥤ C of the equivalence.
#check @CategoryTheory.Equivalence.inverse

/-!
## 2. Unit and counit, triangle identities

As for an adjunction (see `Grothendieck.Adjunction`), an equivalence
determines a unit `unitIso : 𝟭 C ≅ functor ⋙ inverse` and a counit
`counitIso : inverse ⋙ functor ≅ 𝟭 D` — but these are here **natural
isomorphisms** (not mere natural transformations). This is precisely what
distinguishes an equivalence from an arbitrary adjunction: the unit and
counit are invertible.
-/

-- The unit natural isomorphism 𝟭 C ≅ functor ⋙ inverse.
#check @CategoryTheory.Equivalence.unitIso

-- The counit natural isomorphism inverse ⋙ functor ≅ 𝟭 D.
#check @CategoryTheory.Equivalence.counitIso

-- The first triangle identity (unit × counit compatibility).
#check @CategoryTheory.Equivalence.functor_unitIso_comp

/-!
## 3. The (2-)category of categories: refl, symm, trans

Equivalences of categories compose and invert: they form a (2-)groupoid
structure. `Equivalence.refl` is the identity equivalence, `Equivalence.symm`
inverts an equivalence (swapping functor ↔ inverse), and `Equivalence.trans`
composes two equivalences.
-/

-- The identity equivalence C ≌ C.
#check @CategoryTheory.Equivalence.refl

-- The inverse of an equivalence: if C ≌ D then D ≌ C.
#check @CategoryTheory.Equivalence.symm

-- The composition of two equivalences: C ≌ D and D ≌ E gives C ≌ E.
#check @CategoryTheory.Equivalence.trans

/-!
## 4. The practical criterion: fully faithful + essentially surjective

The most used criterion in practice: a functor `F : C ⥤ D` is an equivalence
if and only if it is **fully faithful** (for all `X Y : C`, the map
`Hom_C(X,Y) → Hom_D(FX,FY)` is bijective) and **essentially surjective**
(every object of `D` is isomorphic to the image of an object of `C`). Mathlib
encodes this in the `Functor.IsEquivalence` class.
-/

-- The structure witnessing that a functor is fully faithful (bijects the Homs).
#check @CategoryTheory.Functor.FullyFaithful

-- The class witnessing that a functor is essentially surjective.
#check @CategoryTheory.Functor.EssSurj

-- The property of a functor being an equivalence (full + faithful + ess. surj.).
#check @CategoryTheory.Functor.IsEquivalence

/-!
## 5. Bridge theorems

Reformulations in the project namespace, bridging the Mathlib facts.
-/

/-- Bridge: the "forward" functor of an equivalence C ≌ D, exposed as a bare
    functor in the functor category. This is the "direct" half of the
    equivalence, the other being `equivalence_inverse`. -/
noncomputable def equivalence_functor (e : C ≌ D) : C ⥤ D :=
  e.functor

/-- Bridge: the "backward" functor of an equivalence C ≌ D. Together with
    `equivalence_functor`, it forms the pair of quasi-inverse functors. -/
noncomputable def equivalence_inverse (e : C ≌ D) : D ⥤ C :=
  e.inverse

/-- Bridge: the unit natural isomorphism of an equivalence — 𝟭 C ≅ functor ⋙
    inverse. This witnesses that "go then come back" is isomorphic to the
    identity (up to isomorphism, not equality). -/
noncomputable def equivalence_unit (e : C ≌ D) : 𝟭 C ≅ e.functor ⋙ e.inverse :=
  e.unitIso

/-- Bridge: the counit natural isomorphism of an equivalence — inverse ⋙
    functor ≅ 𝟭 D. This is the dual witness that "come back then go" is
    isomorphic to the identity. -/
noncomputable def equivalence_counit (e : C ≌ D) : e.inverse ⋙ e.functor ≅ 𝟭 D :=
  e.counitIso

/-- Bridge: the symmetric (inverse) equivalence — if C ≌ D then D ≌ C.
    Swaps the roles of functor and inverse; the unit of `e.symm` is the
    counit of `e` and conversely. -/
noncomputable def equivalence_symm (e : C ≌ D) : D ≌ C :=
  e.symm

/-- Bridge: the composition of two equivalences — C ≌ D and D ≌ E gives
    C ≌ E. Composition preserves equivalences (closure of the 2-groupoid
    structure). -/
noncomputable def equivalence_trans {E : Type*} [Category E] (e : C ≌ D) (f : D ≌ E) : C ≌ E :=
  e.trans f

end Grothendieck.Equivalences_en
