/-
Grothendieck Partie 19 — Les familles conservatives de points

La Partie 18 (ConstantSheaf.lean) a introduit le foncteur faisceau constant et son
adjonction avec les sections globales.

Ce module introduit les **familles conservatives de points** (SGA 4 IV 6.5) :
une famille P de points d'un site (C, J) est conservative si les foncteurs
fibres correspondants Sheaf J (Type w) ⥤ Type w réfléchissent conjointement les
isomorphismes. C'est la formulation abstraite du principe selon lequel « suffisamment
de points détectent tout » — la généralisation catégorique de « suffisamment de
stalks détectent les isomorphismes/monos/epis ».

Constructions clés pontées depuis Mathlib (`CategoryTheory.Sites.Point.Conservative`) :

  - `ObjectProperty.IsConservativeFamilyOfPoints` : la structure centrale
  - `jointlyReflectIsomorphisms` : les foncteurs fibres réfléchissent les isos (A général)
  - `jointlyReflectMonomorphisms` : les foncteurs fibres réfléchissent les monos
  - `jointlyReflectEpimorphisms` : les foncteurs fibres réfléchissent les epis
  - `jointlyFaithful` : les foncteurs fibres sont conjointement fidèles
  - `mk'` : constructeur via condition de tamis couvrant (SGA 4 IV 6.5 (a))
  - `jointly_reflect_ofArrows_mem` : détection des tamis couvrants via points
  - `GrothendieckTopology.HasEnoughPoints` : le site a suffisamment de points

Plus les faisceaux gratte-ciel depuis `CategoryTheory.Sites.Point.Skyscraper` :
  - `skyscraperPresheaf` / `skyscraperSheaf` : constructions gratte-ciel
  - `skyscraperSheafAdjunction` : fibre ⊣ adjonction gratte-ciel
  - `presheafToSheafCompSheafFiberIso` : fibre comme localisation

C'est un ingrédient clé pour comprendre quand un topos a « suffisamment de points »
et pour la théorie de la détection stalk-à-stalk des propriétés de morphismes.

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.Point.Conservative

universe v v' u u' w

namespace Grothendieck.Conservative

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (P : ObjectProperty (GrothendieckTopology.Point.{w} J))

/-! ## 1. Familles conservatives de points

Une famille P de points est « conservative » si les foncteurs fibres
`Sheaf J (Type w) ⥤ Type w` correspondant aux points de P
réfléchissent conjointement les isomorphismes. C'est `ObjectProperty.IsConservativeFamilyOfPoints`
depuis Mathlib, étiqueté Stacks 00YK (1).

Intuitivement : un morphisme f : F ⟶ G entre faisceaux est un iso ssi
il induit un iso sur chaque stalk (fibre) en chaque point de P.
-/

-- Une famille conservative de points : les foncteurs fibres réfléchissent conjointement les isomorphismes.
#check @ObjectProperty.IsConservativeFamilyOfPoints

/-! ## 2. Conséquences pour les catégories de coefficients générales

Quand la catégorie de coefficients A a des propriétés adaptées (concrite, AB5, etc.),
la conservativité implique que les foncteurs fibres Sheaf J A ⥤ A réfléchissent
conjointement les isomorphismes, monomorphismes et épimorphismes, et sont conjointement fidèles.
-/

-- Les foncteurs fibres réfléchissent conjointement les isomorphismes (A général).
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomorphisms

-- Les foncteurs fibres réfléchissent conjointement les monomorphismes (catégorie de coefficients AB5).
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonomorphisms

-- Les foncteurs fibres réfléchissent conjointement les épimorphismes (avec sheafify + produits).
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectEpimorphisms

-- Les foncteurs fibres sont conjointement fidèles.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointlyFaithful

/-! ## 3. Détection via tamis couvrants (SGA 4 IV 6.5 (a))

Le constructeur `mk'` montre que P est une famille conservative si :
pour tout tamis S sur X, si pour chaque point Phi de P les flèches de S
sont conjointement surjectives sur les fibres, alors S est J-couvrant.

C'est le critère pratique : pour vérifier la conservativité, vérifier
la condition de tamis couvrant point par point.
-/

-- Constructeur : famille conservative via condition de tamis couvrant.
#check @ObjectProperty.IsConservativeFamilyOfPoints.mk'

/-! ## 4. Détection des tamis couvrants via les points

Quand P est conservative, une famille de flèches {f_i : U_i ⟶ X} couvre X
(cad. engendre un tamis J-couvrant) ssi pour chaque point Phi de P
et chaque x dans la fibre de X, une f_i atteint x.
-/

-- Tamis couvrants détectés via surjectivité conjointe fibre par fibre.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem

-- Variante pour les petites familles de points.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofArrows_mem_of_small

/-! ## 5. Détection de la surjectivité locale

Un morphisme de préfaisceaux est localement surjectif ssi il est surjectif
sur les fibres en chaque point d'une famille conservative.
-/

-- Surjectivité locale détectée fibre par fibre via famille conservative.
#check @ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_isLocallySurjective

/-! ## 6. W ssi iso sur toutes les fibres

Pour un morphisme f : F ⟶ G de préfaisceaux, f appartient à J.W (la classe
des morphismes inversés par la faisceautisation) ssi f induit un iso sur
les fibres en chaque point de la famille conservative.
-/

-- Appartenance à J.W détectée fibre par fibre.
#check @ObjectProperty.IsConservativeFamilyOfPoints.W_iff

/-! ## 7. HasEnoughPoints

Un site (C, J) « a suffisamment de points » s'il existe une petite famille
conservative de points. C'est la condition garantissant que le raisonnement
stalk par stalk est complet : tout ce qui est détectable stalk par stalk est vrai.
-/

-- Un site a suffisamment de points s'il existe une petite famille conservative.
#check @GrothendieckTopology.HasEnoughPoints

/-! ## 8. Faisceaux gratte-ciel et l'adjonction fibre-gratte-ciel

Étant donné un point Phi et un objet M : A, le faisceau gratte-ciel en M
(relativement à Phi) est le faisceau qui envoie X : C sur le produit
de copies de M indexé par Phi.fiber.obj X. Le foncteur faisceau gratte-ciel
est adjoint à droite du foncteur fibre faisceau :

  Phi.sheafFiber ⊣ Phi.skyscraperSheafFunctor
-/

-- Le foncteur préfaisceau gratte-ciel.
#check @GrothendieckTopology.Point.skyscraperPresheafFunctor

-- Le préfaisceau gratte-ciel de valeur M.
#check @GrothendieckTopology.Point.skyscraperPresheaf

-- Le préfaisceau gratte-ciel est un faisceau.
#check @GrothendieckTopology.Point.isSheaf_skyscraperPresheaf

-- Le foncteur faisceau gratte-ciel : A ⥤ Sheaf J A.
#check @GrothendieckTopology.Point.skyscraperSheafFunctor

-- Le faisceau gratte-ciel de valeur M.
#check @GrothendieckTopology.Point.skyscraperSheaf

-- L'adjonction : foncteur fibre ⊣ foncteur faisceau gratte-ciel (niveau préfaisceau).
#check @GrothendieckTopology.Point.skyscraperPresheafAdjunction

-- L'adjonction : foncteur fibre ⊣ foncteur faisceau gratte-ciel (niveau faisceau).
#check @GrothendieckTopology.Point.skyscraperSheafAdjunction

/-! ## 9. Foncteur fibre comme localisation

Le foncteur fibre sur les faisceaux s'obtient à partir du foncteur fibre sur les préfaisceaux
par localisation relativement à J.W. L'isomorphisme
`presheafToSheafCompSheafFiberIso` en témoigne.
-/

-- Le foncteur fibre sur les faisceaux comme localisation du fibre préfaisceau.
#check @GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso

-- J.W est inversé par le foncteur fibre préfaisceau.
#check @GrothendieckTopology.Point.W_isInvertedBy_presheafFiber

/-! ## 10. Théorèmes ponts

Théorèmes ponts connectant les familles conservatives à la vérification concrète.
-/

/-- Théorème pont : quand P est une famille conservative de points, les foncteurs
    fibres aux points de P réfléchissent conjointement les isomorphismes pour les faisceaux
    à valeurs dans une catégorie générale A (étant données des hypothèses adaptées sur A).
    C'est la conséquence principale de la conservativité. -/
theorem jointly_reflect_iso_bridge {A : Type u'} [Category.{v'} A]
    [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    (hP : P.IsConservativeFamilyOfPoints) :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  hP.jointlyReflectIsomorphisms A

/-- Théorème pont : une famille conservative de points rend les foncteurs fibres
    conjointement fidèles. Cela signifie : si deux morphismes coïncident sur tous les stalks
    (fibres en tous les points de P), ils sont égaux. -/
theorem jointly_faithful_bridge {A : Type u'} [Category.{v'} A]
    [LocallySmall.{w} C] [HasColimitsOfSize.{w, w} A]
    {FC : A → A → Type*} {CC : A → Type w}
    [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory.{w} A FC]
    [(forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
    [J.HasSheafCompose (forget A)]
    [AB5OfSize.{w, w} A] [HasFiniteLimits A]
    (hP : P.IsConservativeFamilyOfPoints) :
    JointlyFaithful
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  hP.jointlyFaithful A

/-- Construction pont : l'adjonction faisceau gratte-ciel pour un point Phi.
    Phi.sheafFiber est adjoint à gauche de Phi.skyscraperSheafFunctor. -/
noncomputable def skyscraper_adjunction_bridge {A : Type u'} [Category.{v'} A]
    [HasProducts.{w} A] [HasColimitsOfSize.{w, w} A]
    (Φ : GrothendieckTopology.Point.{w} J) :
    Φ.sheafFiber (A := A) ⊣ Φ.skyscraperSheafFunctor :=
  Φ.skyscraperSheafAdjunction

end Grothendieck.Conservative
