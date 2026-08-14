/-
Grothendieck Part 31 — Kan extensions [English mirror of KanExtensions.lean]

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

All `sorry` eliminated at creation (c.8228): 0/0 sorry, 4/4 theorems clean
(cast on Mathlib 4 v4.31.0-rc1 definitions and theorems, without non-trivial
tactics). Bridges to `Mathlib.CategoryTheory.Functor.KanExtension.{Basic,Adjunction,Pointwise,Dense}`
via `L.lanAdjunction`, `lanAdjunction_unit`, `descOfIsLeftKanExtension_fac`,
`leftKanExtensionIso`. See c.8224 (lesson L902 ★ EXTENDED: `rfl` is a
sufficient bridge when equality is definitional or when we **are** the value).

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
import Mathlib.CategoryTheory.Whiskering

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

/-- Bridge: `L.lan` is left adjoint to the precomposition functor
    `(whiskeringLeft C D H).obj L : (D ⥤ H) ⥤ (C ⥤ H)`. This is the
    formulation in functor categories of the lemma "the left Kan
    extension is the best left lifting" — Mathlib attaches the adjunction
    directly to `L` via the class `L.HasLeftKanExtension` once and for all.

    Note: `noncomputable def` (not `theorem`) because the type
    `L.lan ⊣ (Functor.whiskeringLeft C D H).obj L` is an **adjunction**
    (data: object with unit + counit + homEquiv), not a `Prop`. -/
noncomputable def lan_functor_is_left_adjoint_to_precomp (L : C ⥤ D) (H : Type u₃)
    [Category.{v₃, u₃} H] [∀ (F : C ⥤ H), L.HasLeftKanExtension F] :
    L.lan ⊣ (Functor.whiskeringLeft C D H).obj L :=
  L.lanAdjunction H

/-- Bridge: the unit of the adjunction `lan ⊣ precomp L` is exactly
    `L.lanUnit`. This is Mathlib's `@[simp]` lemma — `lanAdjunction_unit`
    is a **theorem** (NOT a definitional equality), so we use it as the
    proof body. (L902 ★ EXTENDED c.8224 reaffirmed: `rfl` does NOT work
    for `@[simp]` lemmas, must use the theorem.) -/
theorem lan_unit_eq_lan_adjunction_unit (L : C ⥤ D) (H : Type u₃)
    [Category.{v₃, u₃} H] [∀ (F : C ⥤ H), L.HasLeftKanExtension F] :
    (L.lanAdjunction H).unit = L.lanUnit :=
  CategoryTheory.Functor.lanAdjunction_unit L H

/-- Bridge: the universal descent `kan_descent` satisfies the
    factorization condition — this is the naturality of the adjunction.
    The morphism `F' ⟶ G` produced by `descOfIsLeftKanExtension` makes
    `η` and `β` compatible via whiskering: `α ≫ L.whiskerLeft
    (F'.descOfIsLeftKanExtension α G β) = β`. -/
theorem kan_descent_fac {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (η : F ⟶ L ⋙ F') [F'.IsLeftKanExtension η] (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    η ≫ L.whiskerLeft (F'.descOfIsLeftKanExtension η G β) = β :=
  F'.descOfIsLeftKanExtension_fac η G β

/-- Bridge: if `L` is a dense functor, then its left Kan extension along
    itself is isomorphic to the identity on `D`. This is the formulation
    of density of `L` (the special Yoneda case: the identity is its own
    Kan extension along itself).

    Note: we use `noncomputable def` (not `theorem`) because the type
    `F.leftKanExtension F ≅ 𝟭 D` is **data** (a structure), not a
    proposition — the Mathlib theorem `IsDense.leftKanExtensionIso` is
    itself `noncomputable def`. A `theorem ... := x` requires a `Prop`
    as type, which `≅` is not. -/
noncomputable def dense_functor_left_kan_extension_iso_id (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtension F ≅ 𝟭 D :=
  CategoryTheory.Functor.IsDense.leftKanExtensionIso F

/-!
## 9. Additional bridges: dual factorisation, natural bijection, Yoneda density

The 4 following bridges complete the picture of the fundamental Mathlib 4
lemmas on Kan extensions, covering the symmetric branches of the existing
bridges (10 → 14 theorems/decls):
  - `kan_lift_fac`: dual on the **right** side of `kan_descent_fac` — the
    universal factorisation of a right Kan verifies its factorisation
    condition.
  - `kan_right_hom_equiv`: natural bijection `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` for
    a right Kan — pointwise symmetric of the adjunction `homEquiv`.
  - `dense_left_kan_unit_iso`: for a dense functor `F`, the unit of its
    left Kan extension along itself composed with the isomorphism
    `leftKanExtension F ≅ 𝟭 D` equals `rightUnitor.inv` (NatTrans-level).
  - `dense_left_kan_unit_iso_app`: pointwise version of the previous one,
    descended to `app X` for `X : C` — the coherence seen on each object.

Pattern winner (L902 ★★ c.8261): explicit universes, direct Mathlib aliases,
signatures aligned with the source lemma. For lemmas in Mathlib `section`
(lift/homEquiv are under `variable (F') {L F} (α) [IsRightKanExtension α]`)
all variables must be passed explicitly.
-/

/-- Bridge: dual on the **right** side of `kan_descent_fac` — for a right
    Kan extension `(F', α)`, the universal factorisation
    `liftOfIsRightKanExtension α G β : G ⟶ F'` verifies its factorisation
    condition `whiskerLeft L (lift) ≫ α = β`. This is the symmetric of
    `kan_descent_fac` (left side), witnessed by the Mathlib lemma
    `@[reassoc, simp] lemma CategoryTheory.Functor.liftOfIsRightKanExtension_fac`.
    Namespace theorem (L902 ★★ Tier 4) — direct alias with explicit args
    (lemma inside a Mathlib `section`, all variables must be passed). -/
theorem kan_lift_fac {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α] (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    CategoryTheory.Functor.whiskerLeft L (F'.liftOfIsRightKanExtension α G β) ≫ α = β :=
  CategoryTheory.Functor.liftOfIsRightKanExtension_fac F' α G β

/-- Bridge: natural bijection `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` for a right Kan
    extension `(F', α)`. Pointwise symmetric of the adjunction `homEquiv` —
    the universal property encoded as an **equivalence** (not as two
    adjoint arrows). This is the Mathlib lemma
    `@[simps!] noncomputable def CategoryTheory.Functor.homEquivOfIsRightKanExtension`.
    Namespace def (L902 ★★ Tier 4) — direct alias, explicit args. -/
noncomputable def kan_right_hom_equiv {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α] (G : D ⥤ H) :
    (G ⟶ F') ≃ (L ⋙ G ⟶ F) :=
  CategoryTheory.Functor.homEquivOfIsRightKanExtension F' α G

/-- Bridge: for a dense functor `F : C ⥤ D`, the unit of its left Kan
    extension along itself composed with the isomorphism
    `leftKanExtension F ≅ 𝟭 D` equals `rightUnitor.inv` at the NatTrans
    level. This is the Mathlib lemma
    `@[reassoc, simp] lemma CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom`.
    Namespace theorem (L902 ★★ Tier 4) — direct alias. -/
theorem dense_left_kan_unit_iso (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtensionUnit F ≫
      F.whiskerLeft (Functor.IsDense.leftKanExtensionIso F).hom = F.rightUnitor.inv :=
  CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom F

/-- Bridge: pointwise version of `dense_left_kan_unit_iso` — descended to
    `app X` for `X : C`, the coherence becomes:
    `(leftKanExtensionUnit F).app X ≫ (leftKanExtensionIso F).hom.app (F.obj X)
     = F.rightUnitor.inv.app X`.
    This is the Mathlib lemma
    `@[reassoc, simp] lemma CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app`.
    Namespace theorem (L902 ★★ Tier 4) — direct alias. The `{F.IsDense}`
    implicit is auto-deduced from the bridge scope. -/
theorem dense_left_kan_unit_iso_app (F : C ⥤ D) [F.IsDense] (X : C) :
    (F.leftKanExtensionUnit F).app X ≫
      (Functor.IsDense.leftKanExtensionIso F).hom.app (F.obj X) =
        F.rightUnitor.inv.app X :=
  CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app F X

/-!
## 9. Bridges on extension categories, universal properties and density

The 7 bridges below close sections 1-3 and 7 of the `#check` documentary
repertoire: the **extension categories** (`LeftExtension`/`RightExtension`),
the **universal properties** (`IsLeftKanExtension`/`IsRightKanExtension`),
the **existence typeclasses** (`HasLeftKanExtension`/`HasRightKanExtension`),
and **density** (`IsDense`) which ties Yoneda to Kan extensions. The chosen
extensions, units/counits, descent, the adjunction bijection and the `lan`
functor are already bridged by section 8 (existing decls); these 7 bridges
complete the picture with the **abstract form** (categories, Propositions,
typeclasses) on which the chosen form rests.

Retained form (L902 ★★ Tier 5): the two categories are type-sig re-exports of
data (`Type _` inferred), the two universal properties are Props with explicit
args (`F'` then `η`/`ε`, applied as `F'.IsLeftKanExtension η`), the two
existence typeclasses are type-sig Props (pattern `has_enough_points_field`
c.1301+139), and density is a type-sig Prop on `F : C ⥤ D` (Mathlib class,
`F.IsDense`). Resident arguments (universes `v₁ v₂ v₃ u₁ u₂ u₃`), structural
instances, no polymorphic universe constructor.
-/

/-- Bridge: the **category of left extensions** of `F` along `L` — pairs
    `(F' : D ⥤ H, η : F ⟶ L ⋙ F')`, whose initial objects are exactly the
    left Kan extensions. Type-sig re-export of the Mathlib category
    `CategoryTheory.Functor.LeftExtension L F`. -/
def left_extension_field (L : C ⥤ D) (F : C ⥤ H) : Type _ :=
  CategoryTheory.Functor.LeftExtension L F

/-- Bridge: the **category of right extensions** of `F` along `L` — pairs
    `(F' : D ⥤ H, ε : L ⋙ F' ⟶ F)`, whose terminal objects are exactly the
    right Kan extensions. Dual of `left_extension_field`, type-sig re-export
    of the Mathlib category `CategoryTheory.Functor.RightExtension L F`. -/
def right_extension_field (L : C ⥤ D) (F : C ⥤ H) : Type _ :=
  CategoryTheory.Functor.RightExtension L F

/-- Bridge: the **universal property of being a left Kan extension** —
    `(F', η)` is **initial** in `LeftExtension L F`: for every concurrent
    `(G, F ⟶ L ⋙ G)`, there is a unique morphism `F' ⟶ G` factoring the
    transformation. Type-sig re-export of the Mathlib Prop
    `F'.IsLeftKanExtension η` (uniqueness is part of the definition).
    Explicit args: `F'` then `η`. -/
def is_left_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) (F' : D ⥤ H) (η : F ⟶ L ⋙ F') : Prop :=
  F'.IsLeftKanExtension η

/-- Bridge: the **universal property of being a right Kan extension** —
    `(F', ε)` is **terminal** in `RightExtension L F`: every concurrent
    factors uniquely through `F'`. Dual of `is_left_kan_extension_field`,
    type-sig re-export of the Mathlib Prop `F'.IsRightKanExtension ε`.
    Explicit args: `F'` then `ε`. -/
def is_right_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) (F' : D ⥤ H) (ε : L ⋙ F' ⟶ F) : Prop :=
  F'.IsRightKanExtension ε

/-- Bridge: the **existence typeclass** — `F` has a left Kan extension along
    `L`, i.e. `HasInitial (LeftExtension L F)`: the category of left
    extensions has an initial object. This is not guaranteed in general (it
    depends on the completeness of `H`). Type-sig re-export of the Mathlib
    Prop `HasLeftKanExtension L F`, on which the **chosen** extension
    `kan_extension_left` (section 8) rests. -/
def has_left_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) : Prop :=
  CategoryTheory.Functor.HasLeftKanExtension L F

/-- Bridge: the dual **existence typeclass** — `F` has a right Kan extension
    along `L` (`HasTerminal (RightExtension L F)`). Type-sig re-export of the
    Mathlib Prop `HasRightKanExtension L F`, on which the chosen extension
    `kan_extension_right` (section 8) rests. -/
def has_right_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) : Prop :=
  CategoryTheory.Functor.HasRightKanExtension L F

/-- Bridge: **density** — `F : C ⥤ D` is dense if the identity of `D` is a
    left Kan extension of `F` along itself. This is the fundamental fact
    tying Yoneda to Kan extensions: the Yoneda embedding is dense, so every
    functor on `C` is recovered as a Kan extension (weighted colimit) of the
    embedding — the objects of `C` "generate" every presheaf. Type-sig
    re-export of the Mathlib class `F.IsDense` (used as a bracket by
    `dense_left_kan_unit_iso`/`_app`, section 8). -/
def is_dense_field (F : C ⥤ D) : Prop :=
  F.IsDense

end Grothendieck.KanExtensions_en
