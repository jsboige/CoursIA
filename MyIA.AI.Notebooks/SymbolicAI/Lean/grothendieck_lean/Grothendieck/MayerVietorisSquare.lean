/-
Grothendieck Part 21 -- Mayer-Vietoris squares

Part 20 (SheafCohomology/Basic.lean) introduced Ext-based sheaf cohomology
groups H^n(F), the cohomology presheaf, and functoriality.

This module introduces **Mayer-Vietoris squares**, the geometric input for
the Mayer-Vietoris long exact sequence in sheaf cohomology. Given a site
(C, J), a Mayer-Vietoris square is a commutative square in C:

  X₁ --f₁₂--> X₂
  |            |
  f₁₃         f₂₄
  |            |
  v            v
  X₃ --f₃₄--> X₄

such that f₁₃ is a monomorphism and the square becomes a pushout in the
category of sheaves of sets (after applying yoneda >> presheafToSheaf).

This is the abstract formulation of the classical situation where X₄ is
covered by two open subsets X₂ and X₃ with intersection X₁.

Key constructions bridged from Mathlib (`CategoryTheory.Sites.MayerVietorisSquare`):

  - `MayerVietorisSquare` : the structure (extends Square C)
  - `mk'` : constructor via sheaf pullback condition
  - `mk_of_isPullback` : constructor via pullback square + covering sieve
  - `SheafCondition` : presheaf satisfies the pullback condition
  - `SheafCondition.ext` : injectivity of restrictions to X₄
  - `SheafCondition.glue` : gluing sections over X₂ and X₃
  - `sheafCondition_of_sheaf` : sheaves satisfy the condition
  - `shortComplex` : ℤ[X₁] ⟶ ℤ[X₂] ⊞ ℤ[X₃] ⟶ ℤ[X₄]
  - `shortComplex_exact` : the short complex is exact
  - `shortComplex_shortExact` : it is short exact (Mono f + Epi g)

This is the geometric foundation for the Mayer-Vietoris long exact
sequence (Part 22, SheafCohomology/MayerVietoris.lean).

Epic #1646, See #2159. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.MayerVietorisSquare

universe w v v' u u'

namespace Grothendieck.MayerVietorisSquare

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ## 1. The Mayer-Vietoris square structure

A Mayer-Vietoris square for a site (C, J) is a commutative square in C
that becomes a pushout in the category of sheaves of sets. The structure
extends `Square C` (with fields f₁₂, f₁₃, f₂₄, f₃₄ and condition
f₁₂ >> f₂₄ = f₁₃ >> f₃₄) and adds:

  - `mono_f₁₃` : the map X₁ ⟶ X₃ is a monomorphism
  - `isPushout` : the square is a pushout in Sheaf J (Type v)

The dissymmetry (only f₁₃ is required Mono) allows the Nisnevich case
where f₂₄ is an open immersion and f₃₄ is etale.
-/

-- A Mayer-Vietoris square: extends Square C, mono f₁₃, pushout in sheaves.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare

/-! ## 2. Constructors

Two constructors for Mayer-Vietoris squares:

1. `mk'` : given a square with Mono f₁₃, if for every sheaf of types F
   the square `sq.op.map F.val` is a pullback, then it is a MV square.

2. `mk_of_isPullback` : given a pullback square with Mono f₂₄ and
   Mono f₃₄, if Sieve.ofTwoArrows f₂₄ f₃₄ is J-covering on X₄,
   then it is a MV square.
-/

-- Constructor: MV square from sheaf pullback condition.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk'

-- Constructor: MV square from pullback + covering sieve.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback

/-! ## 3. The sheaf condition

Given a Mayer-Vietoris square S and a presheaf P : Cᵒᵖ ⥤ A,
`S.SheafCondition P` asserts that the square `S.toSquare.op.map P`
is a pullback square. This is the abstract sheaf condition for P
with respect to the MV square.

For presheaves of types, this is equivalent to bijectivity of the
map `toPullbackObj P` from P(X₄) to the fiber product.
-/

-- The sheaf condition: the presheaf sees a pullback square.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition

-- The canonical map from P(X₄) to the fiber product.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toPullbackObj

-- Sheaf condition iff toPullbackObj is bijective (Type-valued presheaves).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_iff_bijective_toPullbackObj

/-! ## 4. Consequences of the sheaf condition

When S.SheafCondition P holds for a Type-valued presheaf P:

  - `ext` : if two elements of P(X₄) agree on X₂ and X₃, they are equal
    (injectivity of restrictions)

  - `glue` : given matching sections u : P(X₂) and v : P(X₃) that agree
    on X₁, there exists a glued section glue u v huv : P(X₄)

  - `map_f₂₄_op_glue` : the restriction of glue to X₂ is u
  - `map_f₃₄_op_glue` : the restriction of glue to X₃ is v
-/

-- Injectivity: two sections agreeing on X₂ and X₃ are equal.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.ext

-- Gluing: matching sections over X₂ and X₃ glue to a section over X₄.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.glue

-- Restriction of glued section to X₂ is the original.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₂₄_op_glue

-- Restriction of glued section to X₃ is the original.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₃₄_op_glue

/-! ## 5. Sheaves satisfy the sheaf condition

Every sheaf (of types) satisfies the Mayer-Vietoris sheaf condition.
This is the key fact that makes MV squares useful: the pullback
condition is automatic for sheaves.
-/

-- Every sheaf satisfies the MV sheaf condition.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf

/-! ## 6. The associated short complex

Given a MV square S, there is an associated short complex of abelian sheaves:

  ℤ[X₁] ⟶ ℤ[X₂] ⊞ ℤ[X₃] ⟶ ℤ[X₄]

where ℤ[X] denotes the free abelian sheaf on yoneda.obj X, the left map
is the difference (f₁₂ - f₁₃), and the right map is the sum (f₂₄ + f₃₄).

This short complex is short exact (Mono f + Epi g + Exact), which is
the input for the Mayer-Vietoris long exact sequence in sheaf cohomology.
-/

-- The short complex ℤ[X₁] ⟶ ℤ[X₂] ⊞ ℤ[X₃] ⟶ ℤ[X₄].
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex

-- The short complex is exact.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_exact

-- The short complex is short exact (Mono f + Epi g + Exact).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_shortExact

/-! ## 7. Bridge theorems

Bridge theorems connecting Mayer-Vietoris squares to concrete verification.
-/

/-- Bridge theorem: every sheaf of types satisfies the Mayer-Vietoris
    sheaf condition for a given MV square S. This means the pullback
    diagram is automatic for sheaves. -/
theorem sheaf_satisfies_MV_condition
    [HasWeakSheafify J (Type v)]
    (S : J.MayerVietorisSquare)
    (F : Sheaf J (Type v)) :
    S.SheafCondition F.obj :=
  CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf S F

/-- Bridge theorem: given a Mayer-Vietoris square S and a presheaf P
    satisfying the sheaf condition, matching sections over X₂ and X₃
    that agree on X₁ can be glued into a section over X₄. -/
noncomputable def glue_sections
    [HasWeakSheafify J (Type v)]
    (S : J.MayerVietorisSquare)
    (P : Cᵒᵖ ⥤ Type v')
    (h : S.SheafCondition P)
    (u : P.obj (op S.X₂)) (v : P.obj (op S.X₃))
    (huv : P.map (CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toSquare S).f₁₂.op u =
           P.map (CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toSquare S).f₁₃.op v) :
    P.obj (op S.X₄) :=
  CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.glue h u v huv

end Grothendieck.MayerVietorisSquare
