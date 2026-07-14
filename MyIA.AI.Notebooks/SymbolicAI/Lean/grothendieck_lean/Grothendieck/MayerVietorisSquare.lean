/-
Grothendieck Partie 21 — Carrés de Mayer-Vietoris

La Partie 20 (SheafCohomology/Basic.lean) a introduit les groupes de cohomologie
des faisceaux basés sur Ext H^n(F), le préfaisceau de cohomologie, et la fonctorialité.

Ce module introduit les **carrés de Mayer-Vietoris**, l'entrée géométrique de
la suite exacte longue de Mayer-Vietoris en cohomologie des faisceaux. Étant donné
un site (C, J), un carré de Mayer-Vietoris est un carré commutatif dans C :

  X₁ --f₁₂--> X₂
  |            |
  f₁₃         f₂₄
  |            |
  v            v
  X₃ --f₃₄--> X₄

tel que f₁₃ est un monomorphisme et le carré devient un pushout dans la
catégorie des faisceaux d'ensembles (après application de yoneda >> presheafToSheaf).

C'est la formulation abstraite de la situation classique où X₄ est
recouvert par deux ouverts X₂ et X₃ d'intersection X₁.

Constructions clés pontées depuis Mathlib (`CategoryTheory.Sites.MayerVietorisSquare`) :

  - `MayerVietorisSquare` : la structure (étend Square C)
  - `mk'` : constructeur via condition de pullback de faisceau
  - `mk_of_isPullback` : constructeur via carré pullback + tamis couvrant
  - `SheafCondition` : le préfaisceau satisfait la condition de pullback
  - `SheafCondition.ext` : injectivité des restrictions à X₄
  - `SheafCondition.glue` : recollement de sections sur X₂ et X₃
  - `sheafCondition_of_sheaf` : les faisceaux satisfont la condition
  - `shortComplex` : ℤ[X₁] ⟶ ℤ[X₂] ⊞ ℤ[X₃] ⟶ ℤ[X₄]
  - `shortComplex_exact` : le court complexe est exact
  - `shortComplex_shortExact` : il est court exact (Mono f + Epi g)

C'est le fondement géométrique de la suite exacte longue de Mayer-Vietoris
(Partie 22, SheafCohomology/MayerVietoris.lean).

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.MayerVietorisSquare

universe w v v' u u'

namespace Grothendieck.MayerVietorisSquare

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ## 1. La structure de carré de Mayer-Vietoris

Un carré de Mayer-Vietoris pour un site (C, J) est un carré commutatif dans C
qui devient un pushout dans la catégorie des faisceaux d'ensembles. La structure
étend `Square C` (avec champs f₁₂, f₁₃, f₂₄, f₃₄ et condition
f₁₂ >> f₂₄ = f₁₃ >> f₃₄) et ajoute :

  - `mono_f₁₃` : l'application X₁ ⟶ X₃ est un monomorphisme
  - `isPushout` : le carré est un pushout dans Sheaf J (Type v)

La dissymétrie (seul f₁₃ est requis Mono) permet le cas Nisnevich
où f₂₄ est une immersion ouverte et f₃₄ est étale.
-/

-- Un carré de Mayer-Vietoris : étend Square C, mono f₁₃, pushout dans les faisceaux.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare

/-! ## 2. Constructeurs

Deux constructeurs pour les carrés de Mayer-Vietoris :

1. `mk'` : étant donné un carré avec Mono f₁₃, si pour tout faisceau de types F
   le carré `sq.op.map F.val` est un pullback, alors c'est un carré MV.

2. `mk_of_isPullback` : étant donné un carré pullback avec Mono f₂₄ et
   Mono f₃₄, si Sieve.ofTwoArrows f₂₄ f₃₄ est J-couvrant sur X₄,
   alors c'est un carré MV.
-/

-- Constructeur : carré MV depuis condition de pullback de faisceau.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk'

-- Constructeur : carré MV depuis pullback + tamis couvrant.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback

/-! ## 3. La condition de faisceau

Étant donné un carré de Mayer-Vietoris S et un préfaisceau P : Cᵒᵖ ⥤ A,
`S.SheafCondition P` affirme que le carré `S.toSquare.op.map P`
est un carré pullback. C'est la condition de faisceau abstraite pour P
relativement au carré MV.

Pour les préfaisceaux de types, cela équivaut à la bijectivité de
l'application `toPullbackObj` de P(X₄) vers le produit fibré.
-/

-- La condition de faisceau : le préfaisceau voit un carré pullback.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition

-- L'application canonique de P(X₄) vers le produit fibré.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toPullbackObj

-- Condition de faisceau ssi toPullbackObj est bijective (préfaisceaux à valeurs Type).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_iff_bijective_toPullbackObj

/-! ## 4. Conséquences de la condition de faisceau

Quand S.SheafCondition P tient pour un préfaisceau à valeurs Type P :

  - `ext` : si deux éléments de P(X₄) coïncident sur X₂ et X₃, ils sont égaux
    (injectivité des restrictions)

  - `glue` : étant données des sections compatibles u : P(X₂) et v : P(X₃) qui coïncident
    sur X₁, il existe une section recollée glue u v huv : P(X₄)

  - `map_f₂₄_op_glue` : la restriction de glue à X₂ est u
  - `map_f₃₄_op_glue` : la restriction de glue à X₃ est v
-/

-- Injectivité : deux sections coïncidant sur X₂ et X₃ sont égales.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.ext

-- Recollement : des sections compatibles sur X₂ et X₃ se recollent en une section sur X₄.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.glue

-- La restriction de la section recollée à X₂ est l'originale.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₂₄_op_glue

-- La restriction de la section recollée à X₃ est l'originale.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₃₄_op_glue

/-! ## 5. Les faisceaux satisfont la condition de faisceau

Tout faisceau (de types) satisfait la condition de faisceau de Mayer-Vietoris.
C'est le fait clé qui rend les carrés MV utiles : la condition de pullback
est automatique pour les faisceaux.
-/

-- Tout faisceau satisfait la condition de faisceau MV.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf

/-! ## 6. Le court complexe associé

Étant donné un carré MV S, il y a un court complexe associé de faisceaux abéliens :

  ℤ[X₁] ⟶ ℤ[X₂] ⊞ ℤ[X₃] ⟶ ℤ[X₄]

où ℤ[X] dénote le faisceau abélien libre sur yoneda.obj X, l'application à gauche
est la différence (f₁₂ - f₁₃), et l'application à droite est la somme (f₂₄ + f₃₄).

Ce court complexe est court exact (Mono f + Epi g + Exact), ce qui est
l'entrée de la suite exacte longue de Mayer-Vietoris en cohomologie des faisceaux.
-/

-- Le court complexe ℤ[X₁] ⟶ ℤ[X₂] ⊞ ℤ[X₃] ⟶ ℤ[X₄].
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex

-- Le court complexe est exact.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_exact

-- Le court complexe est court exact (Mono f + Epi g + Exact).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.shortComplex_shortExact

/-! ## 7. Théorèmes ponts

Théorèmes ponts connectant les carrés de Mayer-Vietoris à la vérification concrète.
-/

/-- Théorème pont : tout faisceau de types satisfait la condition de faisceau
    de Mayer-Vietoris pour un carré MV donné S. Cela signifie que le diagramme
    de pullback est automatique pour les faisceaux. -/
theorem sheaf_satisfies_MV_condition
    [HasWeakSheafify J (Type v)]
    (S : J.MayerVietorisSquare)
    (F : Sheaf J (Type v)) :
    S.SheafCondition F.obj :=
  CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sheafCondition_of_sheaf S F

/-- Théorème pont : étant donné un carré de Mayer-Vietoris S et un préfaisceau P
    satisfaisant la condition de faisceau, des sections compatibles sur X₂ et X₃
    qui coïncident sur X₁ peuvent être recollées en une section sur X₄. -/
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
