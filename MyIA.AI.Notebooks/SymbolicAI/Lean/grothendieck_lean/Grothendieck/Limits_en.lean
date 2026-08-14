/-
Grothendieck Part 28 — Limits and colimits (beyond Yoneda) [English mirror of Limits.lean]

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Limits and colimits are the universal syntax that turns a category into a
space where existence problems are solved "by universal property".
Grothendieck makes them the pillar of algebraic geometry: the fibre product
of schemes (a limit of a V-shaped diagram), the product of schemes over a
base, kernels and cokernels of sheaf morphisms, projective limits of étale
fundamental groups, and — above all — cohomology as a derived functor of the
"global sections" functor Γ, itself a right adjoint and therefore continuous
(it preserves limits, see the `Grothendieck.Adjunction` module).

A **limit** of a functor `F : J ⥤ C` (a "diagram") is an object representing
the "compatible families" of elements of `F`. It is the universal solution to
the problem: "give an object `L` and projections to each `F j` compatible with
the arrows of the diagram, through which any other such cone factors,
uniquely". The **colimit** is the dual notion (universal factorisation of
cocones). Products, pullbacks and equalisers are limits; pushouts, coproducts
and cokernels are colimits.

Mathlib 4 formalises all of this infrastructure in `Mathlib.CategoryTheory.Limits`:
  - `CategoryTheory.Limits.Cone` / `Cocone` — cones and cocones over a diagram
  - `CategoryTheory.Limits.IsLimit` / `IsColimit` — the universal property
  - `CategoryTheory.Limits.HasLimit` / `HasColimit` — existence of a chosen (co)limit
  - `CategoryTheory.Limits.limit` / `colimit` — the (co)limit object
  - `CategoryTheory.Limits.limit.cone` / `colimit.cocone` — the limiting cone/cocone
  - `CategoryTheory.Limits.limit.π` / `colimit.ι` — projections / injections
  - `CategoryTheory.Limits.limit.lift` / `colimit.desc` — universal factorisation
  - `CategoryTheory.Limits.HasLimitsOfSize` / `HasColimitsOfSize` — (co)complete category
  - `CategoryTheory.Limits.PreservesLimitsOfSize` / `PreservesColimitsOfSize` — continuous/cocontinuous functor
  - `CategoryTheory.Limits.HasProducts` / `HasBinaryProducts` / `HasEqualizers` — classical shapes

This module re-exposes these facts as an organised pedagogical tour, for
learners meeting (co)limits for the first time, mirroring the
`Grothendieck.Adjunction` module (where one sees that preserving limits is
precisely the property of right adjoints).

Epic #1646, See #2159. No `sorry` at creation.

### i18n — convention #4980 ratified 2026-07-04

This module is the English mirror of `Limits.lean`. Theorem statements,
lemma names, Lean tactics and Mathlib references stay in English. Only the
**docstrings `/-- ... -/`** and **comments `-- ...`** differ between the two
files. Anti-§D byte-identity guaranteed.
-/

import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

universe v v' u u'

namespace Grothendieck.Limits_en

open CategoryTheory Limits

variable {J : Type u} [Category.{v} J]
variable {C : Type u'} [Category.{v'} C]

/-!
## 1. Cones and the universal property of the limit

A **cone** `c : Cone F` over a diagram `F : J ⥤ C` is the data of an apex
`c.pt : C` together with a family of arrows `c.π.app j : c.pt ⟶ F j`
compatible with the morphisms of the diagram (a natural transformation from
the constant functor at `c.pt` to `F`). The limit is the universal cone:
every other cone factors through it uniquely.
-/

-- The structure of a cone over a diagram F : J ⥤ C.
#check @Cone

-- The dual structure: a cocone (a compatible outgoing family).
#check @Cocone

-- The universal property: a cone t is limiting if every cone factors through t
-- in a unique way.
#check @IsLimit

-- The dual universal property: a cocone is colimiting.
#check @IsColimit

/-!
## 2. Existence and choice of a limit

`HasLimit F` asserts that a limit of `F` exists (a classical proposition);
`limit F` is then the chosen limit object, `limit.cone F` the limiting cone,
`limit.π F j` its projection to `F j`, and `limit.lift F c` the universal
factorisation of an arbitrary cone `c` through the limiting cone.
-/

-- The proposition that a limit of F exists.
#check @HasLimit

-- The proposition that a colimit of F exists (dual).
#check @HasColimit

-- The chosen limit object (under HasLimit F).
#check @limit

-- The chosen colimit object (under HasColimit F).
#check @colimit

-- The universal limiting cone.
#check @limit.cone

-- The projection of the limiting cone to the j-th component of the diagram.
#check @limit.π

-- The witness that `limit.cone F` satisfies the universal property.
#check @limit.isLimit

-- The universal factorisation: every cone c factors through the limiting cone.
#check @limit.lift

/-!
## 3. Dual colimits

By duality, `colimit.cocone F` is the colimiting cocone, `colimit.ι F j` its
injection from `F j`, and `colimit.desc F c` the universal factorisation of
an arbitrary cocone through the colimiting cocone.
-/

-- The universal colimiting cocone.
#check @colimit.cocone

-- The injection from the j-th component into the colimit object.
#check @colimit.ι

-- The witness that `colimit.cocone F` satisfies the universal property.
#check @colimit.isColimit

-- The universal factorisation: every cocone c factors through the colimiting cocone.
#check @colimit.desc

/-!
## 4. Complete and cocomplete categories

A category is **complete** (`HasLimitsOfSize.{w} C`) if every diagram indexed
by a suitably-sized small category admits a limit; **cocomplete** is the
dual. These properties are stable under most useful categorical constructions
(categories of sheaves, functor categories).
-/

-- A category that has all limits of the indicated size.
#check @HasLimitsOfSize

-- A category that has all colimits of the indicated size.
#check @HasColimitsOfSize

/-!
## 5. Classical shapes of limits

The most useful limits in algebraic geometry are products
(`HasProducts`, `HasBinaryProducts`) and equalisers (`HasEqualizers`).
A theorem of Freyd states that a category has all (small) limits if and only
if it has products and equalisers — hence their centrality.
-/

-- The category has all products (limits over discrete types).
#check @HasProducts

-- The category has all binary products.
#check @HasBinaryProducts

-- The category has all equalisers.
#check @HasEqualizers

/-!
## 6. Preservation of limits

A functor `G : C ⥤ D` **preserves limits** (`PreservesLimitsOfSize G`) if the
image by `G` of a limiting cone is still limiting. This is precisely the
property of right adjoints (see the `Grothendieck.Adjunction` module): the
"global sections" functor Γ thus preserves limits of sheaves, which
underpins the continuity of cohomological functors.
-/

-- A functor that preserves all limits of the indicated size.
#check @PreservesLimitsOfSize

-- A functor that preserves all colimits of the indicated size.
#check @PreservesColimitsOfSize

/-!
## 7. Bridge theorems

Reformulations in the project namespace, bridging the Mathlib facts.
-/

/-- Bridge: the limit object of a diagram F, as a chosen representative.
    This is the universal object through which every compatible cone factors. -/
noncomputable def limit_object (F : J ⥤ C) [HasLimit F] : C :=
  limit F

/-- Bridge: the colimit object of a diagram F, as a chosen representative.
    This is the universal object from which every compatible cocone factors. -/
noncomputable def colimit_object (F : J ⥤ C) [HasColimit F] : C :=
  colimit F

/-- Bridge: the universal property of the limit — the cone `limit.cone F`
    is indeed limiting, i.e. every cone factors through it uniquely. -/
noncomputable def limit_is_universal (F : J ⥤ C) [HasLimit F] : IsLimit (limit.cone F) :=
  limit.isLimit F

/-- Bridge: the dual universal property of colimits. -/
noncomputable def colimit_is_universal (F : J ⥤ C) [HasColimit F] : IsColimit (colimit.cocone F) :=
  colimit.isColimit F

/-- Bridge: the projection of the limiting cone to the j-th component. This is
    the categorical analogue of a "coordinate" in a product. -/
noncomputable def limit_projection (F : J ⥤ C) [HasLimit F] (j : J) : limit F ⟶ F.obj j :=
  limit.π F j

/-- Bridge: the injection of the colimiting cocone from the j-th component.
    This is the categorical analogue of an "inclusion" into a sum. -/
noncomputable def colimit_injection (F : J ⥤ C) [HasColimit F] (j : J) : F.obj j ⟶ colimit F :=
  colimit.ι F j

/-- Bridge: the universal factorisation of the limit — every cone `c` over `F`
    factors uniquely through the limiting cone. This is the "mediating"
    morphism embodying the universal property. -/
noncomputable def cone_factorisation (F : J ⥤ C) [HasLimit F] (c : Cone F) : c.pt ⟶ limit F :=
  limit.lift F c

/-- Bridge: the dual universal factorisation of colimits — every cocone `c`
    over `F` factors uniquely through the colimiting cocone. -/
noncomputable def cocone_factorisation (F : J ⥤ C) [HasColimit F] (c : Cocone F) : colimit F ⟶ c.pt :=
  colimit.desc F c

/-!
## 8. Bridge theorems: naturality of projections and injections

The projections `limit.π F j` and injections `colimit.ι F j` are not mere
families of morphisms: they are **natural transformations** in the index `j`.
Naturality is witnessed by the Mathlib 4 theorems `limit.w` and `colimit.w`
(each `@[simp]`). We re-expose them here as bridges into the project namespace,
with application of their explicit arguments (L902 ★★ ÉTENDUE c.8228: a Mathlib
theorem with explicit arguments must be APPLIED in the body, otherwise it is
a `∀` that produces `Type mismatch`).
-/

/-- Bridge: the universal factorisation `cone_factorisation` is a direct
    reformulation of Mathlib 4's `limit.lift`. Cast by application of `F`. -/
noncomputable def limit_lift_eq (F : J ⥤ C) [HasLimit F] (c : Cone F) :
    c.pt ⟶ limit F :=
  CategoryTheory.Limits.limit.lift F c

/-- Bridge: naturality of the limit cone's projections — for any arrow
    `f : j ⟶ j'` of the diagram, `limit.π F j ≫ F.map f = limit.π F j'`. This is
    the **naturality equality** of the natural transformation `limit.π`,
    witnessed by the theorem `@[simp] lemma CategoryTheory.Limits.limit.w
    F j j' f`. -/
theorem limit_w_natural (F : J ⥤ C) [HasLimit F] {j j' : J} (f : j ⟶ j') :
    limit.π F j ≫ F.map f = limit.π F j' := by
  rw [CategoryTheory.Limits.limit.w]

/-- Bridge: the universal factorisation `cocone_factorisation` is a direct
    reformulation of Mathlib 4's `colimit.desc`. Cast by application of `F`. -/
noncomputable def colimit_desc_eq (F : J ⥤ C) [HasColimit F] (c : Cocone F) :
    colimit F ⟶ c.pt :=
  CategoryTheory.Limits.colimit.desc F c

/-- Bridge: naturality of the colimit cocone's injections — for any arrow
    `f : j' ⟶ j` of the diagram, `F.map f ≫ colimit.ι F j = colimit.ι F j'`. This
    is the **naturality equality** of the natural transformation `colimit.ι`,
    witnessed by the theorem `@[simp] lemma CategoryTheory.Limits.colimit.w
    F j j' f` (note: the arrow goes from `j'` to `j`, dual of `limit.w`). -/
theorem colimit_w_natural (F : J ⥤ C) [HasColimit F] {j j' : J} (f : j' ⟶ j) :
    F.map f ≫ colimit.ι F j = colimit.ι F j' := by
  rw [CategoryTheory.Limits.colimit.w]

/-!
## 9. Additional bridges: cone factorisation, extension, and limit cones

The 4 following bridges complete the picture of the fundamental Mathlib 4
lemmas on limits and colimits:
  - `limit_lift_π`: the projection `limit.π F j` followed by the `limit.lift`
    of an arbitrary cone returns exactly the `j`-th component of the cone —
    the leg that any cone on `F` provides.
  - `limit_hom_ext_apply`: extension criterion — **two morphisms into the
    limit that agree on every projection are equal**, application of the
    `@[ext] lemma limit.hom_ext`.
  - `limit_lift_cone`: the `limit.lift` of the limit cone is the identity —
    the limit is a **fixed point** of its own factorisation operation.
  - `colimit_ι_desc`: dual on the colimit side — the `colimit.desc F c`
    followed by `colimit.ι F j` of an arbitrary cocone returns the `j`-th
    component of the cocone.

Pattern winner (L902 ★★ c.8261): explicit universes, direct Mathlib aliases,
signatures aligned with the source lemma. For `limit.hom_ext` (`@[ext]`),
application gives the equality lemma, not a function — written explicitly
with its pointwise arguments.
-/

/-- Bridge: for any cone `c` on `F`, the projection `limit.π F j` composed
    with `limit.lift F c` returns the `j`-th component of the cone. This is the
    **leg that any cone** on the diagram provides, witnessed by the Mathlib
    lemma `@[reassoc, simp] lemma CategoryTheory.Limits.limit.lift_π F c j`.
    Namespace theorem (L902 ★★ Tier 4) — direct alias. -/
theorem limit_lift_π (F : J ⥤ C) [HasLimit F] (c : Cone F) (j : J) :
    limit.lift F c ≫ limit.π F j = c.π.app j :=
  CategoryTheory.Limits.limit.lift_π c j

/-- Bridge: extension criterion between the limit and the cone — given
    two morphisms `f, f' : X ⟶ limit F`, if they coincide on every projection
    `limit.π F j`, then `f = f'`. This is the lemma
    `@[ext] lemma CategoryTheory.Limits.limit.hom_ext F {X} (w : ∀ j, ...) :
    f = f'`. Namespace theorem (L902 ★★ Tier 4) — direct alias. -/
theorem limit_hom_ext_apply (F : J ⥤ C) [HasLimit F] {X : C} {f f' : X ⟶ limit F}
    (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  CategoryTheory.Limits.limit.hom_ext w

/-- Bridge: the `limit.lift` of the limit cone is the identity — the limit
    is a fixed point of its own factorisation. Witnessed by the Mathlib lemma
    `@[simp] lemma CategoryTheory.Limits.limit.lift_cone {F : J ⥤ C}
    [HasLimit F] : limit.lift F (limit.cone F) = 𝟙 (limit F)`. The `F`
    is implicit — we omit the explicit argument to let Lean unify it. -/
theorem limit_lift_cone (F : J ⥤ C) [HasLimit F] :
    limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  CategoryTheory.Limits.limit.lift_cone

/-- Bridge: dual on the colimit side — for any cocone `c` on `F`, the
    injection `colimit.ι F j` composed with `colimit.desc F c` returns the
    `j`-th component of the cocone. This is the **leg that any cocone** on
    the diagram provides, witnessed by the Mathlib lemma
    `@[reassoc, simp] lemma CategoryTheory.Limits.colimit.ι_desc F c j`.
    Namespace theorem (L902 ★★ Tier 4) — direct alias. -/
theorem colimit_ι_desc (F : J ⥤ C) [HasColimit F] (c : Cocone F) (j : J) :
    colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
  CategoryTheory.Limits.colimit.ι_desc c j

/-!
## 10. Bridges on completeness and preservation classes

The 7 bridges below close sections 4-6 of the `#check` documentary
repertoire: the **completeness** classes (`HasLimitsOfSize`/
`HasColimitsOfSize`), the **classical shapes** (`HasProducts`/
`HasBinaryProducts`/`HasEqualizers`) and **preservation** of limits
(`PreservesLimitsOfSize`/`PreservesColimitsOfSize`). Each is a type-sig
re-export of the Mathlib Prop class (pattern winner L902 ★★ Tier 5): resident
arguments (the diagram universes `v v' u u'`), structural instances only, no
polymorphic universe constructor.

Universe note (lesson c.1301+141-L1): `HasLimitsOfSize.{u, v} C` takes **two**
explicit universes — the Shape universe (`J : Type u`) and the Shape morphism
universe (`[Category.{v} J]`) — and covers exactly our diagrams.
`HasProducts.{u} C` takes **one** explicit universe (the universe of product
index types, `HasProducts := ∀ J : Type w, HasLimitsOfShape (Discrete J) C`),
aligned on our Shape universe; omitting it yields `universe level
metavariables`. `HasBinaryProducts`/`HasEqualizers` have fixed shapes
(`Discrete WalkingPair`/`WalkingParallelPair`) — no explicit universe.
-/

/-- Bridge: the category `C` is **complete** — every diagram indexed by a
    small category in our Shape universe (`J : Type u` with
    `[Category.{v} J]`) has a limit. This is the completeness assertion for
    diagram categories of size `(u, v)`, a type-sig re-export of the Mathlib
    class `HasLimitsOfSize.{u, v} C`. Completeness is stable under the
    useful categorical constructions (sheaf categories, functor categories). -/
def has_limits_of_size_field : Prop :=
  HasLimitsOfSize.{u, v} C

/-- Bridge: the category `C` is **cocomplete** — every diagram indexed by a
    small category in our Shape universe has a colimit. Dual of
    `has_limits_of_size_field`, type-sig re-export of the Mathlib class
    `HasColimitsOfSize.{u, v} C`. -/
def has_colimits_of_size_field : Prop :=
  HasColimitsOfSize.{u, v} C

/-- Bridge: the category `C` has all **products** indexed by types in our
    Shape universe — limits over the discretised types `Discrete J` with
    `J : Type u`. A Freyd theorem reduces (small) completeness to products
    and equalizers — hence their centrality. Type-sig re-export of the
    Mathlib class `HasProducts.{u} C`. -/
def has_products_field : Prop :=
  HasProducts.{u} C

/-- Bridge: the category `C` has all **binary products** — limits over the
    fixed shape `Discrete WalkingPair` (the two-object pair). Type-sig
    re-export of the Mathlib class `HasBinaryProducts C` (no explicit
    universe: the shape is fixed). -/
def has_binary_products_field : Prop :=
  HasBinaryProducts C

/-- Bridge: the category `C` has all **equalizers** — limits over the fixed
    shape `WalkingParallelPair` (the parallel-arrow pair), the second brick
    of the Freyd theorem together with products. Type-sig re-export of the
    Mathlib class `HasEqualizers C` (no explicit universe). -/
def has_equalizers_field : Prop :=
  HasEqualizers C

/-- Bridge: an endofunctor `F : C ⥤ C` **preserves limits** of size `(u, v)`
    — the image by `F` of a limit cone is still a limit cone. This is
    precisely the property of right adjoints (cf the `Grothendieck.Adjunction`
    module): the "global sections" functor Γ thus preserves limits of
    sheaves. Type-sig re-export of the Mathlib class
    `PreservesLimitsOfSize.{u, v} F`. -/
def preserves_limits_of_size_field (F : C ⥤ C) : Prop :=
  PreservesLimitsOfSize.{u, v} F

/-- Bridge: an endofunctor `F : C ⥤ C` **preserves colimits** of size `(u, v)`
    — the image by `F` of a colimit cocone is still a colimit cocone. This is
    the property of left adjoints. Dual of `preserves_limits_of_size_field`,
    type-sig re-export of the Mathlib class
    `PreservesColimitsOfSize.{u, v} F`. -/
def preserves_colimits_of_size_field (F : C ⥤ C) : Prop :=
  PreservesColimitsOfSize.{u, v} F

end Grothendieck.Limits_en
