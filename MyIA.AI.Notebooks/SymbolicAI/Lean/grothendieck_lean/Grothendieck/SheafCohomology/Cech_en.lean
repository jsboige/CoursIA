/-
Grothendieck Part 23 -- Čech cohomology

Part 20 (SheafCohomology/Basic.lean) introduced Ext-based sheaf cohomology
H^n(F) = Ext^n(constantSheaf ℤ, F).

This module bridges **Čech cohomology** from Mathlib
(`CategoryTheory.Sites.SheafCohomology.Cech`). Given a family of objects
U : ι → C in a category C with finite products, the Čech complex functor
sends a presheaf P : Cᵒᵖ ⥤ A to the cochain complex which in degree n
consists of the product, indexed by i : Fin (n+1) → ι, of the value of
P on the product of the objects U (i a) for a : Fin (n+1).

This is the combinatorial cochain complex associated to a covering family.
In good situations (e.g. sheaves on a site with enough structure), the
cohomology of this complex computes the sheaf cohomology H^n.

Key constructions bridged from Mathlib:

  - `FormalCoproduct.cosimplicialObjectFunctor` :
      Simplicial object in FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A
  - `FormalCoproduct.cochainComplexFunctor` :
      Simplicial object in FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ
  - `cechComplexFunctor` :
      (ι → C) ⟹ (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ

The construction goes through the category `FormalCoproduct C` (the free
formal coproduct completion of C), where a family U : ι → C is packaged
as a single object, and its "Čech object" is a simplicial object whose
degree-n part is indexed by Fin (n+1) → ι.

Epic #1646, See #2159. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

universe w t v v' u u'

namespace Grothendieck.SheafCohomology.Cech_en

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C]

/-! ## 1. The cosimplicial object functor

Given a simplicial object `E` in the category `FormalCoproduct C` of
formal coproducts, `cosimplicialObjectFunctor E` is the functor

  (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A

which sends a presheaf P : Cᵒᵖ ⥤ A to the cosimplicial object obtained
by "evaluating" P on E (using the formal-coproduct structure).

This is the input to the alternating-coface-map construction of the
cochain complex.
-/

-- cosimplicialObjectFunctor: from a simplicial formal coproduct to a
-- functor (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A.
#check @CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor

/-! ## 2. The cochain complex functor

Composing `cosimplicialObjectFunctor` with the alternating coface map
construction (`AlgebraicTopology.alternatingCofaceMapComplex`) gives
the cochain complex functor

  (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ

which sends a presheaf to the associated alternating cochain complex.
-/

-- cochainComplexFunctor: from a simplicial formal coproduct to a
-- functor (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ.
#check @CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor

/-! ## 3. The Čech complex functor

Given a family of objects U : ι → C in a category C with finite products,
`cechComplexFunctor U` is the functor

  (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ

which sends a presheaf P : Cᵒᵖ ⥤ A to the Čech cochain complex. In
degree n, this complex consists of the product, indexed by
i : Fin (n + 1) → ι, of the value of P on the product of the objects
U (i a) for a : Fin (n + 1).

This is the classical Čech complex associated to the covering family {U j}.
-/

-- cechComplexFunctor: the Čech complex functor for a family U : ι → C.
#check @CategoryTheory.cechComplexFunctor

/-! ## 4. Bridge theorems

Bridge theorems connecting the Čech complex functor to concrete
verification.
-/

/-- Bridge construction: given a family of objects U : ι → C and a
    presheaf P : Cᵒᵖ ⥤ A (in a preadditive category with products),
    this is the degree-n part of the Čech complex of P with respect
    to U, as an object of A. -/
noncomputable def cechComplexObj
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C)
    (P : Cᵒᵖ ⥤ A) (n : ℕ) : A :=
  ((CategoryTheory.cechComplexFunctor U).obj P).X n

/-- Bridge theorem (type restatement): the Čech complex functor sends a
    presheaf P : Cᵒᵖ ⥤ A to a cochain complex indexed by ℕ. This is the
    type-level restatement that `cechComplexFunctor U` has source
    `(Cᵒᵖ ⥤ A)` and target `CochainComplex A ℕ`. Marked `noncomputable`
    because it delegates to the noncomputable Mathlib definition. -/
noncomputable def cechComplexFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  CategoryTheory.cechComplexFunctor U

end Grothendieck.SheafCohomology.Cech_en
