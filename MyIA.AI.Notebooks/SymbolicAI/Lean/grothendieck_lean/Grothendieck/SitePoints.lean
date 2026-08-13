/-
Hommage à Grothendieck — Partie 15 : Points d'un site (foncteurs fibres)
Alexandre Grothendieck (1928-2014).

Extension Phase 9 (#2159, EPIC #1646).

La Partie 14 (LeftExact.lean) a montré que la faisceautisation préserve les
limites finies, rendant les catégories de faisceaux finitairement extensives,
adhésives et équilibrées.

Ce module introduit les **points de Grothendieck** (SGA 4 IV 6.3) : un point
d'un site (C, J) est un « foncteur fibre » Φ.fiber : C ⥤ Type qui est
cofiltre et respecte les cribles couvrants. On en dérive :

  - Φ.presheafFiber : le foncteur fibre colimite sur les préfaisceaux
  - Φ.sheafFiber : le foncteur fibre restreint aux faisceaux
  - La structure de catégorie sur les points (morphismes = transformations
    naturelles en sens inverse, SGA 4 IV 3.2)

Un point Φ permet de « sonder » les faisceaux fibre par fibre — la fibre
d'un faisceau F en Φ est Φ.sheafFiber.obj F. C'est la généralisation
catégorielle de la fibre d'un faisceau sur un espace topologique en un point.

Nous indexons les modules Mathlib `CategoryTheory.Sites.Point.Basic` et
`CategoryTheory.Sites.Point.Category` dans le namespace `Grothendieck`.

EPIC #1646, Phase 9 (#2159). Toutes les `sorry` éliminées à la création.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Category

universe v u w

namespace Grothendieck

open CategoryTheory
open CategoryTheory.Limits

/-!
## Qu'est-ce qu'un point d'un site ?

En topologie, un « point » x d'un espace X permet d'évaluer les fonctions
en x, donnant une application Γ(U) → stalk_x pour chaque ouvert U.
Grothendieck a généralisé ceci aux sites arbitraires : un point Φ de
(C, J) donne un « foncteur fibre » qui évalue les faisceaux en des
« points » abstraits, sans requérir un espace topologique sous-jacent.

Formellement, `GrothendieckTopology.Point J` est une structure consistant en :
  - `fiber : C ⥤ Type w` — un foncteur vers les types (le « foncteur tige »)
  - `isCofiltered` — la catégorie des éléments de `fiber` est cofiltre
    (ceci assure l'exactitude : les foncteurs fibres commutent aux limites finies)
  - `jointly_surjective` — tout crible couvrant rencontre tout élément de
    la fibre (ceci relie la topologie au foncteur fibre)

Référence : SGA 4 IV 6.3.
-/

-- A point of a site (C, J) is a fiber functor Φ : C ⥤ Type satisfying
-- cofilteredness and a coverage condition. It generalizes the notion
-- of "point" in topology to arbitrary sites.
-- This is `GrothendieckTopology.Point` from Mathlib's Sites.Point.Basic.
#check @GrothendieckTopology.Point

/-!
## Le foncteur fibre d'un préfaisceau

Étant donné un point Φ, le foncteur fibre d'un préfaisceau évalue un
préfaisceau P en Φ en prenant la colimite de P sur la catégorie des
éléments de Φ.fiber.

Intuitivement : Φ.presheafFiber.obj P est la « tige de P en Φ », définie
comme une colimite filtrée sur toutes les paires (X, x) où X : C et
x : Φ.fiber.obj X.
-/

-- The presheaf fiber functor: evaluates presheaves at a point.
-- Defined as the colimit `(Cᵒᵖ ⥤ A) ⥤ A` obtained by composing
-- the whiskering of `CategoryOfElements.π Φ.fiber` with `colim`.
#check @GrothendieckTopology.Point.presheafFiber

-- The canonical map from P.obj (op X) to the fiber of P at Φ,
-- given a witness x : Φ.fiber.obj X. This is the colimit inclusion.
#check @GrothendieckTopology.Point.toPresheafFiber

/-!
## Le foncteur fibre d'un faisceau

La restriction du foncteur fibre des préfaisceaux à la sous-catégorie des
faisceaux donne Φ.sheafFiber : Sheaf J A ⥤ A. C'est le foncteur clé
pour étudier les faisceaux « fibre par fibre ».

Comme le foncteur fibre commute avec les colimites et les limites finies
(sous des hypothèses convenables sur A), il préserve les suites exactes,
ce qui en fait un outil clé en cohomologie des faisceaux.
-/

-- The sheaf fiber functor: evaluates sheaves at a point.
-- This is the restriction of presheafFiber to the full subcategory of sheaves.
-- Concretely `sheafFiber = sheafToPresheaf ⋙ presheafFiber` BY DEFINITION
-- (Mathlib `CategoryTheory.Sites.Point.Basic`): evaluating a sheaf at a point Φ
-- is evaluating its underlying presheaf at Φ. We promote the `#check` into a
-- proven canonical iso below.

/-- Le foncteur fibre des faisceaux se factorise par le foncteur fibre des
    préfaisceaux via le plongement « faisceau ↦ préfaisceau sous-jacent »
    `sheafToPresheaf`. Évaluer un faisceau en un point revient donc à évaluer
    le préfaisceau sous-jacent en ce même point : c'est exactement la
    définition de `sheafFiber` comme `sheafToPresheaf ⋙ presheafFiber` donnée
    par Mathlib dans `CategoryTheory.Sites.Point.Basic`. On obtient l'iso
    canonique via `sheafToPresheafCompPresheafFiberIso` (une réflexion). -/
noncomputable def sheaf_fiber_presheaf_fiber_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J) :
    sheafToPresheaf J (Type (max u w)) ⋙ Φ.presheafFiber ≅ Φ.sheafFiber :=
  Φ.sheafToPresheafCompPresheafFiberIso

/-!
## Morphismes entre points

Les points d'un site forment une catégorie (SGA 4 IV 3.2). Un morphisme
Φ₁ ⟶ Φ₂ est une transformation naturelle
Φ₂.fiber ⟶ Φ₁.fiber (noter l'inversion du sens !).

Cette inversion est naturelle : une « application d'espaces » f : X → Y
induit une application sur les tiges dans le sens opposé (tirage en
arrière le long de f).
-/

-- A morphism between points consists of a natural transformation
-- between fiber functors, in the opposite direction.
#check @GrothendieckTopology.Point.Hom

/-!
## Les topologies triviale et discrète

Pour la topologie triviale (⊥), tout préfaisceau est un faisceau, donc
les foncteurs fibres coïncident avec les foncteurs d'évaluation aux objets.

Pour la topologie discrète (⊤), seul le préfaisceau terminal est un
faisceau, rendant la théorie des points moins intéressante.
-/

-- The trivial Grothendieck topology (coarsest): every presheaf is a sheaf.
#check @GrothendieckTopology.trivial

-- The discrete Grothendieck topology (finest): only representable presheaves.
#check @GrothendieckTopology.discrete

/-!
## La condition de couverture

La condition `jointly_surjective` assure que les cribles couvrants
rencontrent tout élément de la fibre. Ceci relie la topologie à la
perspective fibre par fibre : si R est un crible couvrant de X, alors
pour tout x dans la fibre de X, il existe un morphisme f : Y ⟶ X dans R
et y dans la fibre de Y tel que Φ.fiber.map f y = x.
-/

-- The coverage condition: every covering sieve hits every element of the fiber.
#check @GrothendieckTopology.Point.jointly_surjective

/-!
## Bridge theorems : la fibre d'un préfaisceau représentable

Pour un préfaisceau représentable `yoneda.obj X`, la fibre en un point Φ
récupère la valeur du foncteur fibre en X :
  Φ.presheafFiber.obj (yoneda.obj X) ≅ Φ.fiber.obj X

Ceci fait le pont entre la perspective Yoneda (les préfaisceaux comme
« objets généralisés ») et la perspective fibre par fibre (les points comme
« sondes »).

Note : ceci requiert `LocallySmall.{w} C` pour faire correspondre les
niveaux d'univers entre `shrinkYoneda` et `Φ.fiber`.
-/

/-- La fibre du plongement de Yoneda (réduit) en un point retrouve la
    valeur du foncteur fibre. C'est `shrinkYonedaCompPresheafFiberIso` de Mathlib :
    `shrinkYoneda ⋙ Φ.presheafFiber ≅ Φ.fiber`.
    Cela montre que le foncteur fibre des préfaisceaux étend le foncteur fibre
    des objets aux préfaisceaux via le plongement de Yoneda. -/
noncomputable def fiber_yoneda_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [LocallySmall.{w} C]
    (Φ : GrothendieckTopology.Point.{w} J) :
    shrinkYoneda.{w} ⋙ Φ.presheafFiber ≅ Φ.fiber :=
  Φ.shrinkYonedaCompPresheafFiberIso

/-!
## La fibre d'un préfaisceau comme colimite

La fibre Φ.presheafFiber.obj P est définie comme une colimite sur la
catégorie des éléments de Φ.fiber. Mathlib fournit :
  - `presheafFiberCocone P` : le cocône canonique
  - `isColimitPresheafFiberCocone P` : c'est une colimite

Ceci permet de construire des applications *depuis* la fibre en utilisant
la propriété universelle des colimites.
-/

/-- Le cocône colimite qui définit la fibre du préfaisceau.
    Utilise `presheafFiberCocone` de Mathlib. -/
noncomputable def presheaf_fiber_cocone {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) (P : Cᵒᵖ ⥤ Type (max u w)) :
    Cocone ((CategoryOfElements.π Φ.fiber).op ⋙ P) :=
  Φ.presheafFiberCocone P

/-- Le cocône de fibre du préfaisceau est une colimite. Cela donne la
    propriété universelle : toute famille compatible d'éléments indexée par
    (X, x) se prolonge de manière unique en une application depuis la fibre.
    Utilise `isColimitPresheafFiberCocone` de Mathlib. -/
noncomputable def is_colimit_presheaf_fiber {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) (P : Cᵒᵖ ⥤ Type (max u w)) :
    IsColimit (Φ.presheafFiberCocone P) :=
  Φ.isColimitPresheafFiberCocone P

/-!
## Extensionalité pour les morphismes depuis la fibre

Deux applications depuis la fibre d'un préfaisceau coïncident si elles
coïncident sur tous les « germes » (X, x) : pour tout X : C et x :
Φ.fiber.obj X, les applications coïncident après précomposition avec
l'inclusion canonique.
-/

/-- Extensionnalité pour les applications depuis la fibre du préfaisceau :
    deux applications f, g depuis Φ.presheafFiber.obj P coïncident si et
    seulement si elles coïncident sur toutes les inclusions `toPresheafFiber`.
    Utilise `presheafFiber_hom_ext` de Mathlib. -/
theorem presheaf_fiber_hom_ext {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) {P : Cᵒᵖ ⥤ Type (max u w)}
    {T : Type (max u w)} {f g : Φ.presheafFiber.obj P ⟶ T}
    (h : ∀ (X : C) (x : Φ.fiber.obj X),
      Φ.toPresheafFiber X x P ≫ f = Φ.toPresheafFiber X x P ≫ g) :
    f = g :=
  Φ.presheafFiber_hom_ext h

/-!
## Naturalité de `toPresheafFiber` le long des morphismes de `C`

Pour tout morphisme `f : X ⟶ Y` dans la catégorie de base et tout élément
`x : Φ.fiber.obj X`, l'application `toPresheavFiber X x P : P.obj (op X) ⟶ Φ.fiber`
commute avec `P.map f.op`. C'est la naturalité du cocône `presheafFiberCocone`
par rapport aux morphismes de `C`.

C'est `toPresheafFiber_w` de Mathlib.
-/

/-- Naturalité de `toPresheafFiber` le long d'un morphisme de la catégorie
    de base : pour `f : X ⟶ Y` et `x : Φ.fiber.obj X`, l'égalité
    `P.map f.op ≫ toPresheafFiber X x = toPresheafFiber Y (Φ.fiber.map f x)`
    relie l'action du préfaisceau (pullback P.map) au foncteur fibre.
    Utilise `toPresheafFiber_w` de Mathlib. -/
theorem to_presheaf_fiber_w {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) {X Y : C} (f : X ⟶ Y)
    (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ Type (max u w)) :
    P.map f.op ≫ Φ.toPresheafFiber X x P = Φ.toPresheafFiber Y (Φ.fiber.map f x) P :=
  Φ.toPresheafFiber_w f x P

/-!
## Naturalité de `toPresheafFiber` le long des morphismes de préfaisceaux

Pour tout morphisme de préfaisceaux `g : P ⟶ Q`, l'inclusion dans la fibre
`toPresheafFiber X x` commute avec `presheafFiber.map g`. C'est la naturalité
du cocône colimite par rapport aux morphismes de préfaisceaux.

C'est `toPresheafFiber_naturality` de Mathlib.
-/

/-- Naturalité de `toPresheafFiber` le long d'un morphisme de préfaisceaux :
    pour `g : P ⟶ Q`, on a `toPresheafFiber X x P ≫ presheafFiber.map g =
    g.app (op X) ≫ toPresheafFiber X x Q`.
    Utilise `toPresheafFiber_naturality` de Mathlib. -/
theorem to_presheaf_fiber_naturality {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{w} J) {P Q : Cᵒᵖ ⥤ Type (max u w)}
    (g : P ⟶ Q) (X : C) (x : Φ.fiber.obj X) :
    Φ.toPresheafFiber X x P ≫ Φ.presheafFiber.map g =
      g.app (Opposite.op X) ≫ Φ.toPresheafFiber X x Q :=
  Φ.toPresheafFiber_naturality g X x

/-!
## Les topologies triviale et discrète dans le treillis des topologies

La topologie triviale (la plus grossière) coïncide avec l'élément minimum
du treillis des topologies de Grothendieck ; la topologie discrète (la plus
fine) coïncide avec l'élément maximum. Ces deux identités ancrent les
topologies extrêmes dans le langage de l'ordre, ce qui rend leur rôle
canonique transparent.

Ce sont `trivial_eq_bot` et `discrete_eq_top` de Mathlib (CategoryTheory.Sites.Grothendieck).
-/

/-- La topologie triviale est l'élément minimum du treillis des topologies :
    `trivial C = ⊥`. Chaque ensemble est couvrant pour la topologie triviale,
    donc tout préfaisceau est un faisceau — c'est ce qui rend la topologie
    triviale « la plus grossière ». Utilise `trivial_eq_bot` de Mathlib. -/
theorem trivial_topology_eq_bot (C : Type u) [Category.{v} C] :
    GrothendieckTopology.trivial C = ⊥ :=
  CategoryTheory.GrothendieckTopology.trivial_eq_bot

/-- La topologie discrète est l'élément maximum du treillis des topologies :
    `discrete C = ⊤`. Seul le crible maximal est couvrant, donc seul
    le préfaisceau terminal est un faisceau — c'est ce qui rend la topologie
    discrète « la plus fine ». Utilise `discrete_eq_top` de Mathlib. -/
theorem discrete_topology_eq_top (C : Type u) [Category.{v} C] :
    GrothendieckTopology.discrete C = ⊤ :=
  CategoryTheory.GrothendieckTopology.discrete_eq_top

end Grothendieck
