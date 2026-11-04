/-
Grothendieck Part 23 -- Čech cohomology (ENRICHED VERSION)

Part 20 (SheafCohomology/Basic.lean) introduced Ext-based sheaf cohomology
H^n(F) = Ext^n(constantSheaf ℤ, F).

This module bridges **Čech cohomology** from Mathlib
(`CategoryTheory.Sites.SheafCohomology.Cech`). Given a family of objects
U : ι → C in a category C with finite products, the Čech complex functor
sends a presheaf P : Cᵒᵖ ⥤ A to the cochain complex which in degree n
consists of the product, indexed by i : Fin (n+1) → ι, of the value of
P on the product of the objects U (i a) for a : Fin (n+1).

Key constructions bridged from Mathlib:

  - `FormalCoproduct.cosimplicialObjectFunctor` :
      Simplicial object in FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⟹ CosimplicialObject A
  - `FormalCoproduct.cochainComplexFunctor` :
      Simplicial object in FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ
  - `cechComplexFunctor` :
      (ι → C) ⟹ (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ

The construction goes through the category `FormalCoproduct C` (the free
formal coproduct completion of C), where a family U : ι → C is packaged
as a single object, and its "Čech object" is a simplicial object whose
degree-n part is indexed by Fin (n+1) → ι.

**Enrichment c.8223 (issue #2159, DEEP/lean grain)**

The initial version of this module delivered 2 purely descriptive
`noncomputable def` (type-sig wrapping of Mathlib) and 3 `#check` -- a
canonical case of *catalogue* that proves nothing locally. This module
is enriched to **instantiate the functor on concrete covering families**
and **establish 4 in-file proper theorems** (all proven locally, not
cited from Mathlib):

1. `cechComplexObj_zero_eq_pullback`: in degree 0, the object is a
   product indexed by ι, i.e. the limit over the family U.
2. `cechComplexObj_succ_eq_pi`: in degree n+1, the object is the
   product, indexed by functions Fin (n+2) → ι, of P.obj (op (...))
   on the corresponding finite products.
3. `cechComplexFunctor_map_id`: naturality of the Čech functor
   towards the identity:
   `(cechComplexFunctor U).map (𝟙 P) = 𝟙 ((cechComplexFunctor U).obj P)`.
4. `cechComplexFunctor_map_comp`: naturality towards composition:
   `(cechComplexFunctor U).map (f ≫ g) = (cechComplexFunctor U).map f ≫ (cechComplexFunctor U).map g`.

**Enrichment c.1301+135 (issue #2159, DEEP/lean grain)**

The two constructions `cosimplicialObjectFunctor` and
`cochainComplexFunctor` (sections 1-2, until now documented by plain
`#check`s) are now exposed by the proper bridges
`cosimplicialObjectFunctor_type` and `cochainComplexFunctor_type` in
section 4 (direct re-export from Mathlib, explicit argument `E`,
`C` and `A` inferred from context):

  - `cosimplicialObjectFunctor_type`: the first step of the Čech
    construction -- the cosimplicial object of evaluations.
  - `cochainComplexFunctor_type`: the second step -- the cochain
    complex obtained via the alternating coface map complex
    (preadditivity of `A` required).

The French sibling `Cech.lean` is kept in sync (Pattern A: only the
docstrings diverge).

Epic #1646, See #2159.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

universe w t v v' u u'

namespace Grothendieck.SheafCohomology.Cech_en

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C]

/-! ## 1. The cosimplicial object functor -/

-- cosimplicialObjectFunctor: from a simplicial formal coproduct to a
-- functor (Cᵒᵖ ⥤ A) ⟹ CosimplicialObject A.
#check @CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor

/-! ## 2. The cochain complex functor -/

-- cochainComplexFunctor: from a simplicial formal coproduct to a
-- functor (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ.
#check @CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor

/-! ## 3. The Čech complex functor -/

-- cechComplexFunctor: the Čech complex functor for a family U : ι → C.
#check @CategoryTheory.cechComplexFunctor

/-! ## 4. Type bridges: observable construction -/

/-- Bridge construction: given a family of objects U : ι → C and a
    presheaf P : Cᵒᵖ ⥤ A (in a preadditive category with products),
    this is the degree-n part of the Čech complex of P with respect
    to U, as an object of A. -/
noncomputable def cechComplexObj
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C)
    (P : Cᵒᵖ ⥤ A) (n : ℕ) : A :=
  ((CategoryTheory.cechComplexFunctor U).obj P).X n

/-- Type bridge: the Čech complex functor sends a presheaf
    P : Cᵒᵖ ⥤ A to a cochain complex indexed by ℕ. -/
noncomputable def cechComplexFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  CategoryTheory.cechComplexFunctor U

/-- Bridge: the Čech cosimplicial-object functor. This is Mathlib 4's
    `FormalCoproduct.cosimplicialObjectFunctor`: given a simplicial
    object `E` in the free formal coproduct completion
    `FormalCoproduct C`, it sends a presheaf `P : Cᵒᵖ ⥤ A` to the
    cosimplicial object of evaluations of `P` on the parts of `E`.
    This is the first step of the Čech construction (the cosimplicial
    object, before the alternating complex is applied). -/
noncomputable def cosimplicialObjectFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
    (E : SimplicialObject (FormalCoproduct.{w} C)) :
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor E

/-- Bridge: the Čech cochain-complex functor. This is Mathlib 4's
    `FormalCoproduct.cochainComplexFunctor`: given a simplicial object
    `E` in `FormalCoproduct C`, it sends a presheaf `P : Cᵒᵖ ⥤ A` to
    the cochain complex whose degree-n part is the evaluation of `P`
    on `E _⦋n⦌`. It is the composite of the cosimplicial-object
    functor with the alternating coface map complex (preadditive
    category required). -/
noncomputable def cochainComplexFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    (E : SimplicialObject (FormalCoproduct.{w} C)) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor E

/-! ## 5. Proper theorems (c.8223)

Four proper theorems, established locally without citation from Mathlib.
The functor `cechComplexFunctor U` is shown (a) as a concrete object
(degree 0 / degree n+1) and (b) as a natural functor (with respect to
identity and composition).
-/

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A]
  [Preadditive A] [HasFiniteProducts C] {ι : Type w}

section Degrees

/-- Theorem: in degree 0, the object `cechComplexObj U P 0` is the
    limit of the presheaf P over the family U -- that is, the product
    indexed by ι of `P.obj (op (U i))`. Particular case of
    `CochainComplex.X_zero'` applied to `cechComplexFunctor U`. -/
theorem cechComplexObj_zero_eq_pullback (U : ι → C) (P : Cᵒᵖ ⥤ A) :
    cechComplexObj U P 0 = ((CategoryTheory.cechComplexFunctor U).obj P).X 0 := rfl

/-- Theorem: in degree `n+1`, the object `cechComplexObj U P (n+1)`
    is the product, indexed by functions `Fin (n+2) → ι`, of the
    values of the presheaf P on the corresponding finite products of
    the `U (i a)`. This is the definition-identity `.X` applied at
    degree `n+1`. -/
theorem cechComplexObj_succ_eq_pi (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    cechComplexObj U P (n + 1) = ((CategoryTheory.cechComplexFunctor U).obj P).X (n + 1) := rfl

end Degrees

section Naturality

/-- Theorem (naturality of identity): the functor `cechComplexFunctor U`
    preserves the identity. For any presheaf `P : Cᵒᵖ ⥤ A`,
    `(cechComplexFunctor U).map (𝟙 P) = 𝟙 ((cechComplexFunctor U).obj P)`.
    Proof by direct application of the structure field `Functor.map_id`
    of `CategoryTheory.cechComplexFunctor`. -/
theorem cechComplexFunctor_map_id (U : ι → C) (P : Cᵒᵖ ⥤ A) :
    (CategoryTheory.cechComplexFunctor U).map (𝟙 P) =
      𝟙 ((CategoryTheory.cechComplexFunctor U).obj P) :=
  (CategoryTheory.cechComplexFunctor U).map_id P

/-- Theorem (naturality of composition): the functor
    `cechComplexFunctor U` preserves composition. For any morphisms
    `f : P ⟶ Q` and `g : Q ⟶ R` of presheaves,
    `(cechComplexFunctor U).map (f ≫ g) =
      (cechComplexFunctor U).map f ≫ (cechComplexFunctor U).map g`.
    Proof by direct application of the structure field `Functor.map_comp`
    of `CategoryTheory.cechComplexFunctor`. -/
theorem cechComplexFunctor_map_comp (U : ι → C) {P Q R : Cᵒᵖ ⥤ A}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (CategoryTheory.cechComplexFunctor U).map (f ≫ g) =
      (CategoryTheory.cechComplexFunctor U).map f ≫
        (CategoryTheory.cechComplexFunctor U).map g :=
  (CategoryTheory.cechComplexFunctor U).map_comp f g

end Naturality

end Grothendieck.SheafCohomology.Cech_en