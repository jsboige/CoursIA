/-
Grothendieck Part 29 — Monoidal categories [English mirror of Monoidal.lean]

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

A **monoidal category** is the categorified analogue of a monoid: a monoid
is a set `M`, a multiplication `M × M → M` and a unit element `e ∈ M`
satisfying associativity and unit laws; a monoidal category is a category
`C`, a **tensor functor** `⊗ : C × C ⥤ C` and a **unit object** `𝟙_ C`,
equipped with coherence constraints (the associator `α_` and the unitors
`λ_`, `ρ_`) that are isomorphisms — not equalities — because, in general,
`(X ⊗ Y) ⊗ Z` and `X ⊗ (Y ⊗ Z)` are not *equal* but *canonically
isomorphic*.

Grothendieck constantly uses monoidal structures: the tensor product of
sheaves, the symmetric monoidal categories underlying derived categories,
monoidal sites. More deeply, sheaf theory rests on a monoidal category
(cartesian product or tensor) that makes internal operations possible
(sheaf Hom, ⊗ of sheaves). Mac Lane's coherence theorem (every well-typed
diagram of associators and unitors commutes) guarantees that one may
manipulate parentheses "as if" associativity were strict.

The definition proceeds in two stages:
  - `MonoidalCategoryStruct C` — the raw **data** (tensorObj, tensorUnit,
    whiskerLeft, whiskerRight, tensorHom, associator, leftUnitor,
    rightUnitor);
  - `MonoidalCategory C` — the **coherence property**: Mac Lane's pentagon
    and the unit/associativity triangle commute.

Mathlib 4 formalises all of this infrastructure in
`Mathlib.CategoryTheory.Monoidal.Category`:
  - `MonoidalCategoryStruct C` — the structure (with notations `⊗`, `𝟙_`,
    `◁`, `▷`, `α_`, `λ_`, `ρ_`)
  - `MonoidalCategory C` — the coherent structure (extends the above +
    pentagon/triangle axioms)
  - `Pentagon` / lemmas `triangle_*` — the coherence diagrams
  - `BraidedCategory C` / `SymmetricCategory C` — braiding and symmetry
    (in `Mathlib.CategoryTheory.Monoidal.Braided`)
  - `instance prodMonoidal` — any pair of monoidal categories is monoidal
    (termwise product)

This module re-exposes these facts as an organised pedagogical tour, for
learners meeting monoidal categories for the first time, mirroring the
`Grothendieck.YonedaLemma` (the presheaf category `(Cᵒᵖ ⥤ Type*)` is
cartesian monoidal) and `Grothendieck.Adjunction` (a monoidal adjunction
is a pair of adjoint monoidal functors) modules. Monoidal categories also
ground the forthcoming modules on closed categories (CCC) and elementary
toposes.

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English mirror of `Monoidal.lean`. Theorem statements,
lemma names, Lean tactics and Mathlib references stay in English. Only the
**docstrings `/-- ... -/`** and **comments `-- ...`** differ between the two
files. Anti-§D byte-identity guaranteed.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete

universe v u

namespace Grothendieck.MonoidalCategories_en

open CategoryTheory
open scoped MonoidalCategory

variable {C : Type u} [Category.{v} C]

/-!
## 1. The problem: categorifying the monoid structure

A monoid `(M, ·, e)` is a set `M`, a multiplication `· : M × M → M` and a
unit `e ∈ M` such that `(x · y) · z = x · (y · z)` and `e · x = x = x · e`.
To "categorify" this notion, one replaces:
  - the set `M` by a category `C`;
  - the multiplication `·` by a **tensor functor** `⊗ : C × C ⥤ C`;
  - the equality of objects `(X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)` by a **canonical
    isomorphism** `α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` (the associator).
Associativity is no longer strict but "up to coherent isomorphism". The
coherence constraints (pentagon, triangle) guarantee that no ambiguity
remains.
-/

-- The tensor functor: on objects. `tensorObj X Y = X ⊗ Y`.
#check @MonoidalCategoryStruct.tensorObj

-- The unit object of the monoidal category. Notation `𝟙_ C`.
#check @MonoidalCategoryStruct.tensorUnit

-- The tensor product of morphisms (via left/right whiskerings).
#check @MonoidalCategoryStruct.tensorHom

-- Left whiskering: `X ◁ f : X ⊗ Y₁ ⟶ X ⊗ Y₂`.
#check @MonoidalCategoryStruct.whiskerLeft

-- Right whiskering: `f ▷ Y : X₁ ⊗ Y ⟶ X₂ ⊗ Y`.
#check @MonoidalCategoryStruct.whiskerRight

/-!
## 2. The structure: MonoidalCategoryStruct

`MonoidalCategoryStruct C` gathers the raw **data** of a monoidal structure
on `C`: the tensor product `⊗` (on objects and morphisms), the unit `𝟙_ C`,
the associator `α_`, and the left/right unitors `λ_`, `ρ_`. At this stage,
**no coherence** is required — only the existence of the data. The
isomorphisms `α_`, `λ_`, `ρ_` witness that the product is associative and
unital "up to iso".
-/

-- The associator: `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. Notation `α_`.
#check @MonoidalCategoryStruct.associator

-- The left unitor: `𝟙_ C ⊗ X ≅ X`. Notation `λ_`.
#check @MonoidalCategoryStruct.leftUnitor

-- The right unitor: `X ⊗ 𝟙_ C ≅ X`. Notation `ρ_`.
#check @MonoidalCategoryStruct.rightUnitor

-- The class gathering all this data (without coherence).
#check @MonoidalCategoryStruct

/-!
## 3. The coherence: MonoidalCategory (pentagon + triangle)

`MonoidalCategory C` extends `MonoidalCategoryStruct C` by requiring that
Mac Lane's two coherence diagrams commute:
  - the **pentagon**: the two ways to reassociate `(W ⊗ X) ⊗ Y ⊗ Z` into
    `W ⊗ (X ⊗ (Y ⊗ Z))` via `α_` coincide;
  - the **triangle**: unit and associativity interact coherently
    (`(X ⊗ 𝟙_) Y` simplifies via `α_` and `ρ_`).
Mac Lane's **coherence theorem** then ensures that *every* well-typed
diagram built from `α_`, `λ_`, `ρ_` commutes — so one may manipulate
parentheses as if the structure were strictly associative. This is what
makes the theory workable.
-/

-- The class of coherent monoidal categories (pentagon + triangle).
#check @MonoidalCategory

-- The pentagon diagram (associativity coherence) — a `Prop`.
#check @MonoidalCategory.Pentagon

-- A triangle witness lemma: `α_` and `ρ_` interact coherently.
#check @MonoidalCategory.triangle_assoc_comp_right

/-!
## 4. Canonical examples

Any category with finite products is monoidal (the cartesian product `×`
plays the role of `⊗`, the terminal object plays the role of `𝟙_`). Mathlib
also provides the general instance: the product of two monoidal categories
is monoidal (`prodMonoidal`). The category `Type*` is cartesian monoidal
(product `×`) and also monoidal for the tensor product of types.
-/

-- The product of two monoidal categories is monoidal.
#check @MonoidalCategory.prodMonoidal

/-!
## 5. Braiding and symmetry: BraidedCategory / SymmetricCategory

A **braided** monoidal category is equipped with a natural isomorphism
`braiding : X ⊗ Y ≅ Y ⊗ X` (the "braiding") satisfying the Yang-Baxter
braiding equations (hexagons). A **symmetric** category is a braiding such
that `braiding ∘ braiding = id` (involutive). This is the natural setting
for tensor products of sheaves and derived categories.
-/

-- The class of braided monoidal categories.
#check @BraidedCategory

-- The braiding `X ⊗ Y ≅ Y ⊗ X`.
#check @BraidedCategory.braiding

-- The class of symmetric monoidal categories (involutive braiding).
#check @SymmetricCategory

/-!
## 6. Link to the sequel: closed categories, CCC, topos

A **closed** monoidal category has an "internal Hom" `ihom` such that
`ihom X ⟶ Y` represents the functor `X ⊗ (-)`. The cartesian case (product
`×`) yields **cartesian closed categories** (CCC) — the setting of the
Curry-Howard-Lambek correspondence (logic ↔ types ↔ categories). An
**elementary topos** is a CCC with a subobject classifier `Ω`: the purely
categorial axiomatisation of set theory and sheaves. Monoidal categories
are their foundation.
-/

-- A monoid `M` yields a monoidal category `Discrete M` (minimal categorification).
#check @Discrete.monoidal

-- A monoid homomorphism `M →* N` yields a monoidal functor `Discrete M ⥤ Discrete N`.
#check @Discrete.monoidalFunctor

/-!
## 7. Bridge theorems

Reformulations in the project namespace, bridging the Mathlib facts.
-/

/-- Bridge: the tensor product of two objects, exposed as a bare function.
    This is `X ⊗ Y` in any monoidal category. -/
noncomputable def tensor_product [MonoidalCategory C] (X Y : C) : C :=
  X ⊗ Y

/-- Bridge: the unit object of the monoidal category, exposed as a bare
    object. This is `𝟙_ C`, neutral for `⊗` up to iso (`λ_`, `ρ_`). -/
noncomputable def tensor_unit_obj [MonoidalCategory C] : C :=
  𝟙_ C

/-- Bridge: the associator `(X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`, exposed as a bare
    isomorphism. Witness that the tensor product is associative "up to
    coherent isomorphism" — the raw data, before coherence. -/
noncomputable def associator_iso [MonoidalCategory C] (X Y Z : C) :
    (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) :=
  α_ X Y Z

/-- Bridge: the left unitor `𝟙_ C ⊗ X ≅ X`. -/
noncomputable def left_unitor_iso [MonoidalCategory C] (X : C) :
    𝟙_ C ⊗ X ≅ X :=
  λ_ X

/-- Bridge: the right unitor `X ⊗ 𝟙_ C ≅ X`. -/
noncomputable def right_unitor_iso [MonoidalCategory C] (X : C) :
    X ⊗ 𝟙_ C ≅ X :=
  ρ_ X

/-- Bridge: the braiding `X ⊗ Y ≅ Y ⊗ X` in a braided monoidal category.
    Witness of the "up to iso" commutativity of the tensor product. -/
noncomputable def braiding_iso [MonoidalCategory C] [BraidedCategory C]
    (X Y : C) : X ⊗ Y ≅ Y ⊗ X :=
  BraidedCategory.braiding X Y

end Grothendieck.MonoidalCategories_en
