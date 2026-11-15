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

/-!
## 10. Bridges : la forme abstraite des points de Grothendieck

Les 7 bridges ci-dessous ferment le répertoire `#check` documentaire du
module : la **structure** `Point` (le « foncteur tige » `Φ.fiber` cofiltre
rencontrant tout crible couvrant), le **foncteur fibre préfaisceau**
`Φ.presheafFiber` (la colimite sur la catégorie des éléments) et son
**inclusion canonique** `Φ.toPresheafFiber`, la **catégorie des points**
`Point.Hom` (les morphismes entre points, SGA 4 IV 3.2), les topologies
**triviale** et **discrète**, et la **condition de couverture**
`jointly_surjective` (SGA 4 IV 6.3). Chacun est un re-export type-sig de
l'API Mathlib (pattern winner L902 ★★ Tier 5) : args résidents
(`{C : Type u} [Category.{v} C]` + `(Φ : GrothendieckTopology.Point.{w} J)`),
instances structurelles uniquement, zéro constructeur polymorphe d'univers.

Universe note (leçon c.1301+143-L1) : `Point.{w} J` vit dans
`Type (max (max u v) (w + 1))` — le 3ᵉ univers `w` est celui des fibres
(`Φ.fiber : C ⥤ Type w`). Le foncteur fibre préfaisceau exige en sus la
cocomplétude de la cible (`HasColimitsOfSize`), que la catégorie des types
`Type (max u w)` satisfait toujours ; il est `noncomputable` (le colimite
n'a pas de choix canonique).
-/

/-- Bridge : la **structure de point** d'un site `(C, J)` — un foncteur
    `Φ.fiber : C ⥤ Type w` dont la catégorie des éléments est cofiltre
    (ce qui assure l'exactitude : commutation aux limites finies) et qui
    rencontre tout crible couvrant. C'est la généralisation
    grothendieckienne du point d'un espace topologique (SGA 4 IV 6.3).
    Type-sig re-export de `GrothendieckTopology.Point.{w} J`. -/
def point_field {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) : Type _ :=
  GrothendieckTopology.Point.{w} J

/-- Bridge : le **foncteur fibre des préfaisceaux** en un point `Φ` —
    évalue un préfaisceau `P` en prenant la colimite de `P` sur la
    catégorie des éléments de `Φ.fiber`. Intuitivement, `presheafFiber.obj P`
    est la « tige de P en Φ », la colimite filtrée sur toutes les paires
    `(X, x)` avec `x : Φ.fiber.obj X`. Re-export type-sig de
    `GrothendieckTopology.Point.presheafFiber` (le type cible est la
    catégorie des types de notre univers fibre `Type (max u w)`). -/
noncomputable def presheaf_fiber_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J) :
    (Cᵒᵖ ⥤ Type (max u w)) ⥤ Type (max u w) :=
  Φ.presheafFiber

/-- Bridge : l'**inclusion canonique** dans la fibre — pour un témoin
    `x : Φ.fiber.obj X`, le morphisme `P.obj (op X) ⟶ Φ.presheafFiber.obj P`
    envoyant une section en la classe de `(X, x)` dans la colimite. C'est
    la lég du cocône colimite qui définit `presheafFiber`. Re-export
    type-sig de `GrothendieckTopology.Point.toPresheafFiber`. -/
noncomputable def to_presheaf_fiber_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J)
    (X : C) (x : Φ.fiber.obj X) (P : Cᵒᵖ ⥤ Type (max u w)) :
    P.obj (Opposite.op X) ⟶ Φ.presheafFiber.obj P :=
  Φ.toPresheafFiber X x P

/-- Bridge : les **morphismes entre points** d'un site — une
    transformation naturelle en sens inverse entre les foncteurs fibres
    (SGA 4 IV 3.2). Les points d'un site forment une catégorie : c'est ce
    qui permet de comparer les « sondes » d'un site entre elles.
    Type-sig re-export de `GrothendieckTopology.Point.Hom`. -/
def point_hom_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ₁ Φ₂ : GrothendieckTopology.Point.{w} J) :
    Type _ :=
  GrothendieckTopology.Point.Hom Φ₁ Φ₂

/-- Bridge : la **topologie triviale** sur `C` — la plus grossière : tout
    crible est couvrant, donc tout préfaisceau est un faisceau (cf
    `trivial_topology_eq_bot` : `trivial C = ⊥`). Re-export type-sig de
    `GrothendieckTopology.trivial`. -/
def trivial_field (C : Type u) [Category.{v} C] :
    GrothendieckTopology C :=
  GrothendieckTopology.trivial C

/-- Bridge : la **topologie discrète** sur `C` — la plus fine : seul le
    crible maximal est couvrant, donc seul le préfaisceau terminal est un
    faisceau (cf `discrete_topology_eq_top` : `discrete C = ⊤`). Re-export
    type-sig de `GrothendieckTopology.discrete`. -/
def discrete_field (C : Type u) [Category.{v} C] :
    GrothendieckTopology C :=
  GrothendieckTopology.discrete C

/-- Bridge : la **condition de couverture** d'un point (SGA 4 IV 6.3) —
    pour tout objet `X` et tout crible couvrant `R ∈ J X`, tout élément
    `x : Φ.fiber.obj X` provient d'un élément de la fibre au-dessus d'une
    flèche couvrante : `∃ Y f, R.arrows f ∧ ∃ y, Φ.fiber.map f y = x`.
    C'est ce qui relie la topologie au foncteur fibre — sans elle, le
    foncteur fibre ne « verrait » pas les recouvrements. Re-export type-sig
    du champ `GrothendieckTopology.Point.jointly_surjective`. -/
def jointly_surjective_field {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{w} J) :
    ∀ {X : C}, ∀ R ∈ J X, ∀ x : Φ.fiber.obj X,
      ∃ (Y : C) (f : Y ⟶ X), ∃ (_ : R.arrows f), ∃ y : Φ.fiber.obj Y,
        Φ.fiber.map f y = x :=
  Φ.jointly_surjective

end Grothendieck
