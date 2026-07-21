/-
Grothendieck Part 28 — Kan extensions [English mirror of KanExtensions.lean]

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

The Kan extension is one of the most universal constructions in category
theory: it "extends" a functor `F : C ⥤ H` along a functor `L : C ⥤ D`,
producing a functor `D ⥤ H` that is the "best possible lifting" of `F`
beyond the image of `L`. Grothendieck uses it constantly: limits and
colimits are Kan extensions along the unique functor to the terminal
category; the Yoneda lemma is the Kan extension of the identity; derived
functors (Cartan-Eilenberg, then Grothendieck's derived functors in
algebraic geometry) are Kan extensions; the density of a functor (notably
the Yoneda embedding) is expressed by a Kan extension.

Given `L : C ⥤ D` and `F : C ⥤ H`, a **left Kan extension** of `F` along
`L` is the data of a functor `F' : D ⥤ H` and a natural transformation
`η : F ⟶ L ⋙ F'` (the "unit") satisfying a universal property: for every
`G : D ⥤ H`, composing `(F ⟶ L ⋙ F')` then `(L ⋙ F' ⟶ L ⋙ G)` induces a
bijection `(F' ⟶ G) ≃ (F ⟶ L ⋙ G)`. Dually, a **right Kan extension** is a
functor `F' : D ⥤ H` with `ε : L ⋙ F' ⟶ F` universal via the bijection
`(G ⟶ F') ≃ (L ⋙ G ⟶ F)`.

The definition is therefore purely universal: a left Kan extension is an
**initial object** in the category of pairs `(F', F ⟶ L ⋙ F')`, and a right
Kan extension is a **terminal object** in the category of pairs
`(F', L ⋙ F' ⟶ F)`. Mathlib encodes these categories as
`Functor.LeftExtension L F` and `Functor.RightExtension L F`.

Mathlib 4 formalises all of this infrastructure in
`Mathlib.CategoryTheory.Functor.KanExtension`:
  - `Functor.LeftExtension L F` / `RightExtension L F` — extension categories
  - `Functor.IsLeftKanExtension F' η` / `IsRightKanExtension F' ε` — the universal property
  - `Functor.HasLeftKanExtension L F` / `HasRightKanExtension L F` — existence (initial/terminal object)
  - `Functor.leftKanExtension L F` / `rightKanExtension L F` — the chosen extension
  - `Functor.leftKanExtensionUnit` / `rightKanExtensionCounit` — unit/counit
  - `Functor.lan L` — the "left Kan extension" functor `(C ⥤ H) ⥤ (D ⥤ H)`

This module re-exposes these facts as an organised pedagogical tour, for
learners meeting Kan extensions for the first time, mirroring the
`Grothendieck.YonedaLemma` (the Yoneda embedding is dense — the whole
theory of Kan extensions rests on it, cf §7) and `Grothendieck.Adjunction`
(an adjunction L ⊣ R gives the "pointwise" bijections Hom_D(LX,Y) ≃
Hom_C(X,RY); a left Kan extension generalises to an arbitrary source
functor) modules.

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English mirror of `KanExtensions.lean`. Theorem statements,
lemma names, Lean tactics and Mathlib references stay in English. Only the
**docstrings `/-- ... -/`** and **comments `-- ...`** differ between the two
files. Anti-§D byte-identity guaranteed.
-/

import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Dense

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.KanExtensions_en

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-!
## 1. The problem: extending a functor along another

Given `L : C ⥤ D` and `F : C ⥤ H`, we seek to "extend" `F` to a functor
defined on all of `D` (not only on the image of `L`). A **left extension**
is the data of `F' : D ⥤ H` and a natural transformation `η : F ⟶ L ⋙ F'`.
A **right extension** is `F' : D ⥤ H` and `ε : L ⋙ F' ⟶ F`. Mathlib gathers
this data into the categories `Functor.LeftExtension L F` (initial objects =
left Kan) and `Functor.RightExtension L F` (terminal objects = right Kan).
-/

-- The category of left extensions of F along L: pairs (F', F ⟶ L ⋙ F').
#check @CategoryTheory.Functor.LeftExtension

-- The category of right extensions of F along L: pairs (F', L ⋙ F' ⟶ F).
#check @CategoryTheory.Functor.RightExtension

-- Object constructor for LeftExtension L F.
#check @CategoryTheory.Functor.LeftExtension.mk

-- Object constructor for RightExtension L F.
#check @CategoryTheory.Functor.RightExtension.mk

/-!
## 2. The universal property: IsLeftKanExtension / IsRightKanExtension

The "being a Kan extension" property is stated as a universal property.
`F'.IsLeftKanExtension η` (with `η : F ⟶ L ⋙ F'`) asserts that `(F', η)` is
**initial** in `LeftExtension L F`: for every competitor `(G, F ⟶ L ⋙ G)`,
there is a unique morphism `F' ⟶ G` factoring the transformation. Dually,
`F'.IsRightKanExtension ε` asserts that `(F', ε)` is **terminal** in
`RightExtension L F`. These are `Prop`s (properties, not data) — uniqueness
is part of the definition.
-/

-- The universal property "(F', η) is a left Kan extension".
#check @CategoryTheory.Functor.IsLeftKanExtension

-- The universal property "(F', ε) is a right Kan extension".
#check @CategoryTheory.Functor.IsRightKanExtension

-- Witness of initiality: (F', η) initial in LeftExtension L F.
#check @CategoryTheory.Functor.isUniversalOfIsLeftKanExtension

-- Witness of terminality: (F', ε) terminal in RightExtension L F.
#check @CategoryTheory.Functor.isUniversalOfIsRightKanExtension

/-!
## 3. Existence: HasLeftKanExtension / HasRightKanExtension

The existence of a Kan extension is not guaranteed in general (it depends on
the completeness of `H`). Mathlib states it via the typeclasses
`HasLeftKanExtension L F := HasInitial (LeftExtension L F)` and
`HasRightKanExtension L F := HasTerminal (RightExtension L F)`. When they
hold, we get a **chosen** extension `leftKanExtension L F` (respectively
`rightKanExtension L F`) and its unit (resp. counit).
-/

-- The typeclass "F has a left Kan extension along L".
#check @CategoryTheory.Functor.HasLeftKanExtension

-- The typeclass "F has a right Kan extension along L".
#check @CategoryTheory.Functor.HasRightKanExtension

-- The chosen left Kan extension when [HasLeftKanExtension L F].
#check @CategoryTheory.Functor.leftKanExtension

-- The chosen right Kan extension when [HasRightKanExtension L F].
#check @CategoryTheory.Functor.rightKanExtension

-- The unit of the chosen left Kan extension: F ⟶ L ⋙ leftKanExtension L F.
#check @CategoryTheory.Functor.leftKanExtensionUnit

-- The counit of the chosen right Kan extension: L ⋙ rightKanExtension L F ⟶ F.
#check @CategoryTheory.Functor.rightKanExtensionCounit

/-!
## 4. The universal descent

The universal property rewrites as a natural bijection between morphism
spaces. For a left Kan extension `(F', η)`, every `β : F ⟶ L ⋙ G` factors
uniquely as `F ⟶ L ⋙ F' ⟶ L ⋙ G` via a morphism `F' ⟶ G` (the "descent").
For a right extension, every `β : L ⋙ G ⟶ F` lifts to `G ⟶ F'`. This is the
analogue of the adjunction bijection Hom_D(LX,Y) ≃ Hom_C(X,RY), but
"functorial in all of F'".
-/

-- The universal descent of a left Kan extension: F' ⟶ G from β : F ⟶ L ⋙ G.
#check @CategoryTheory.Functor.descOfIsLeftKanExtension

-- The universal lift of a right Kan extension: G ⟶ F' from β : L ⋙ G ⟶ F.
#check @CategoryTheory.Functor.liftOfIsRightKanExtension

-- The natural bijection (F' ⟶ G) ≃ (L ⋙ G ⟶ F) for a right Kan extension.
#check @CategoryTheory.Functor.homEquivOfIsRightKanExtension

/-!
## 5. The lan functor / lanUnit

When `F ↦ leftKanExtension L F` exists for **every** `F : C ⥤ H` (i.e.
`[∀ F, HasLeftKanExtension L F]`), the left Kan extension packs into a
**functor** `lan L : (C ⥤ H) ⥤ (D ⥤ H)`, left adjoint to the precomposition
functor `(whiskeringLeft C D H).obj L : (D ⥤ H) ⥤ (C ⥤ H)`. The unit of this
adjunction is `lanUnit : 𝟭 (C ⥤ H) ⟶ L.lan ⋙ (precomp L)`.
-/

-- The left Kan extension functor (C ⥤ H) ⥤ (D ⥤ H) along L.
#check @CategoryTheory.Functor.lan

-- The unit natural transformation 𝟭 (C ⥤ H) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L.
#check @CategoryTheory.Functor.lanUnit

/-!
## 6. Pointwise Kan extensions

A Kan extension may be defined "pointwise": `F'` is a pointwise extension of
`F` along `L` if for each `Y : D`, the object `F'.obj Y` is the appropriate
(co)limit indexed by the comma category `L ↓ Y`. This is the computable form
(explicit formulas in terms of (co)limits), as opposed to the abstract
universal form. Mathlib states this via `HasPointwiseLeftKanExtension` /
`HasPointwiseRightKanExtension`.
-/

-- The typeclass "F has a pointwise left Kan extension".
#check @CategoryTheory.Functor.HasPointwiseLeftKanExtension

-- The typeclass "F has a pointwise right Kan extension".
#check @CategoryTheory.Functor.HasPointwiseRightKanExtension

/-!
## 7. Yoneda as a Kan extension; density

The fundamental fact connecting Kan extensions to the rest of the theory:
the Yoneda lemma **is** a Kan extension. More precisely, the Yoneda
embedding `yoneda : C ⥤ (Cᵒᵖ ⥤ Type*)` is **dense**: every functor on `C`
is recovered as a Kan extension (weighted colimit) of the Yoneda embedding.
Density is stated exactly as "the identity is a left Kan extension of the
functor along itself", which Mathlib encodes via `Functor.IsDense`. This is
the deep meaning of the Yoneda lemma: the objects of `C` "generate" every
presheaf by Kan extension.
-/

-- The property "F is dense": 𝟭 D is a left Kan extension of F along F.
#check @CategoryTheory.Functor.IsDense

/-!
## 8. Bridge theorems

Reformulations in the project namespace, bridging the Mathlib facts.
-/

/-- Bridge: the chosen left Kan extension of `F` along `L`, exposed as a
    bare functor `D ⥤ H`. This is the "canonical" extension when
    `[HasLeftKanExtension L F]`. -/
noncomputable def kan_extension_left (L : C ⥤ D) (F : C ⥤ H)
    [L.HasLeftKanExtension F] : D ⥤ H :=
  L.leftKanExtension F

/-- Bridge: the chosen right Kan extension of `F` along `L`. -/
noncomputable def kan_extension_right (L : C ⥤ D) (F : C ⥤ H)
    [L.HasRightKanExtension F] : D ⥤ H :=
  L.rightKanExtension F

/-- Bridge: the unit of the chosen left Kan extension —
    `F ⟶ L ⋙ leftKanExtension L F`. Witness that the extension is universal
    over all competitors. -/
noncomputable def kan_extension_left_unit (L : C ⥤ D) (F : C ⥤ H)
    [L.HasLeftKanExtension F] : F ⟶ L ⋙ L.leftKanExtension F :=
  L.leftKanExtensionUnit F

/-- Bridge: the counit of the chosen right Kan extension —
    `L ⋙ rightKanExtension L F ⟶ F`. -/
noncomputable def kan_extension_right_counit (L : C ⥤ D) (F : C ⥤ H)
    [L.HasRightKanExtension F] : L ⋙ L.rightKanExtension F ⟶ F :=
  L.rightKanExtensionCounit F

/-- Bridge: the left Kan extension functor `(C ⥤ H) ⥤ (D ⥤ H)` along `L`,
    when all pointwise extensions exist. This is the left adjoint to
    precomposition by `L`. -/
noncomputable def lan_functor (L : C ⥤ D)
    [∀ (F : C ⥤ H), L.HasLeftKanExtension F] : (C ⥤ H) ⥤ (D ⥤ H) :=
  L.lan

/-- Bridge: the universal descent of a left Kan extension — given
    `(F', η)` a left Kan extension and `β : F ⟶ L ⋙ G`, the unique morphism
    `F' ⟶ G` factoring `β` via `η`. This is the operational arm of the
    universal property. -/
noncomputable def kan_descent {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (η : F ⟶ L ⋙ F') [F'.IsLeftKanExtension η] (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    F' ⟶ G :=
  F'.descOfIsLeftKanExtension η G β

end Grothendieck.KanExtensions_en
