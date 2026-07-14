/-
Grothendieck Partie 23 -- cohomologie de Čech

La Partie 20 (SheafCohomology/Basic.lean) a introduit la cohomologie
des faisceaux basée sur Ext H^n(F) = Ext^n(faisceauConstant ℤ, F).

Ce module établit un pont vers la **cohomologie de Čech** de
Mathlib (`CategoryTheory.Sites.SheafCohomology.Cech`). Étant donnée
une famille d'objets U : ι → C dans une catégorie C
avec produits finis, le foncteur du complexe de Čech envoie un
préfaisceau P : Cᵒᵖ ⥤ A sur le complexe de cochaênes
dont le degré n consiste en le produit, indexé par i : Fin (n+1) → ι,
de la valeur de P sur le produit des objets U (i a) pour a : Fin (n+1).

Il s'agit du complexe de cochaênes combinatoire associé à une famille
recouvrante. Dans les bonnes situations (par exemple les faisceaux sur
un site avec suffisamment de structure), la cohomologie de ce complexe
calcule la cohomologie des faisceaux H^n.

Constructions clés pontées depuis Mathlib :

  - `FormalCoproduct.cosimplicialObjectFunctor` :
      Objet simplicial dans FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⟹ CosimplicialObject A
  - `FormalCoproduct.cochainComplexFunctor` :
      Objet simplicial dans FormalCoproduct C ⟹ (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ
  - `cechComplexFunctor` :
      (ι → C) ⟹ (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ

La construction passe par la catégorie `FormalCoproduct C` (la
complétion par coproduits formels libres de C), oê une famille
U : ι → C est encapsulée dans un objet unique, et son
"objet de Čech" est un objet simpliciel dont la partie de degré n
est indexée par Fin (n+1) → ι.

Epic #1646, Voir #2159. Tous les `sorry` éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

universe w t v v' u u'

namespace Grothendieck.SheafCohomology.Cech

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C]

/-! ## 1. Le foncteur en objet cosimplicial

Étant donné un objet simpliciel `E` dans la catégorie `FormalCoproduct C`
des coproduits formels, `cosimplicialObjectFunctor E` est le foncteur

  (Cᵒᵖ ⥤ A) ⟹ CosimplicialObject A

qui envoie un préfaisceau P : Cᵒᵖ ⥤ A sur l'objet cosimpliciel
obtenu en “evaluant” P sur E (grâce à la structure de
coproduit formel).

C'est l'entrée de la construction du complexe de cochaênes par la carte
de coface alternée.
-/

-- cosimplicialObjectFunctor : d'un coproduit formel simpliciel vers un
-- foncteur (Cᵒᵖ ⥤ A) ⟹ CosimplicialObject A.
#check @CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor

/-! ## 2. Le foncteur en complexe de cochaênes

En composant `cosimplicialObjectFunctor` avec la construction de la carte
de coface alternée (`AlgebraicTopology.alternatingCofaceMapComplex`) on
obtient le foncteur de complexe de cochaênes

  (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ

qui envoie un préfaisceau sur le complexe de cochaênes alternées associé.
-/

-- cochainComplexFunctor : d'un coproduit formel simpliciel vers un
-- foncteur (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ.
#check @CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor

/-! ## 3. Le foncteur du complexe de Čech

Étant donnée une famille d'objets U : ι → C dans une catégorie C
avec produits finis, `cechComplexFunctor U` est le foncteur

  (Cᵒᵖ ⥤ A) ⟹ CochainComplex A ℕ

qui envoie un préfaisceau P : Cᵒᵖ ⥤ A sur le complexe de
cochaênes de Čech. En degré n, ce complexe est constitué du produit,
indexé par i : Fin (n + 1) → ι, de la valeur de P sur le produit
des objets U (i a) pour a : Fin (n + 1).

Il s'agit du complexe de Čech classique associé à la famille
recouvrante {U j}.
-/

-- cechComplexFunctor : le foncteur du complexe de Čech pour une
-- famille U : ι → C.
#check @CategoryTheory.cechComplexFunctor

/-! ## 4. Théorèmes ponts

Théorèmes ponts connectant le foncteur du complexe de Čech à une
vérification concrète.
-/

/-- Construction pont : étant donnée une famille d'objets U : ι → C
    et un préfaisceau P : Cᵒᵖ ⥤ A (dans une catégorie préadditive
    avec produits), c'est la partie de degré n du complexe de Čech de P
    par rapport à U, en tant qu'objet de A. -/
noncomputable def cechComplexObj
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C)
    (P : Cᵒᵖ ⥤ A) (n : ℕ) : A :=
  ((CategoryTheory.cechComplexFunctor U).obj P).X n

/-- Théorème pont (reformulation de type) : le foncteur du complexe de
    Čech envoie un préfaisceau P : Cᵒᵖ ⥤ A sur un complexe de
    cochaênes indexé par ℕ. C'est la reformulation au niveau des types
    du fait que `cechComplexFunctor U` a pour source `(Cᵒᵖ ⥤ A)` et
    pour cible `CochainComplex A ℕ`. Marqué `noncomputable` car il
    délègue à la définition noncomputable de Mathlib. -/
noncomputable def cechComplexFunctor_type
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    [HasFiniteProducts C] {ι : Type w} (U : ι → C) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  CategoryTheory.cechComplexFunctor U

end Grothendieck.SheafCohomology.Cech
