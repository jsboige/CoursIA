/-
Grothendieck Partie 27 — La construction de Grothendieck (catégories fibrées)

Alexander Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

La construction de Grothendieck — le « yoga des foncteurs » — est l'une des
idées les plus fécondes de Grothendieck. À un foncteur `F : C ⥤ Cat` elle
associe une catégorie `∫ F` (la catégorie totale) munie d'un foncteur
`forget : ∫ F ⥤ C` (la fibration) dont les fibres au-dessus de chaque
objet `c : C` retrouvent la catégorie `F(c)`. C'est le langage des
catégories fibrées, central dans la théorie de la descente (SGA 1), les
champs algébriques (stacks = champs fibrés en groupoïdes), et la
géométrie algébrique relative (un schéma sur S est un objet de la fibre
d'une fibration au-dessus de S).

Grothendieck utilise cette construction pour réifier les familles
paramétrées d'objets : une famille d'objets de F indexée par les objets
de C n'est plus une collection externe mais un objet interne de ∫ F. La
descente effective (caractériser quels morphismes de C permettent de
recoller les familles) s'exprime alors comme une propriété de la fibration.

Mathlib 4 formalise cette construction dans
`Mathlib.CategoryTheory.Grothendieck` :
  - `CategoryTheory.Grothendieck : (C ⥤ Cat) → Type*` — la catégorie totale ∫ F
  - `CategoryTheory.Grothendieck.Hom` — les morphismes (flèche de base + flèche de fibre)
  - `CategoryTheory.Grothendieck.forget : ∫ F ⥤ C` — le foncteur d'oubli (la fibration)
  - `CategoryTheory.Grothendieck.map : (F ⟶ G) → (∫ F ⥤ ∫ G)` — fonctorialité en F
  - `CategoryTheory.Grothendieck.transport` / `toTransport` — le transport cartésien
  - `CategoryTheory.Grothendieck.isoMk` — un isomorphisme depuis des iso de base + fibre
  - `CategoryTheory.FiberedCategory` — le langage des fibrations/cartésiennes

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant les catégories fibrées pour la première fois.

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `Construction_en.lean`. Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti.
-/

import Mathlib.CategoryTheory.Grothendieck

universe v v₂ u u₂

namespace Grothendieck.Construction

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ Cat.{v₂, u₂})

/-!
## 1. La catégorie totale ∫ F

À un foncteur `F : C ⥤ Cat`, la construction de Grothendieck associe une
catégorie totale `∫ F` dont les objets sont les couples `(c, x)` avec
`c : C` et `x : F(c)`, et les morphismes `(c, x) ⟶ (d, y)` sont les couples
`(f, φ)` où `f : c ⟶ d` dans C et `φ : x ⟶ F(f)(y)` dans la fibre.
-/

-- La catégorie totale ∫ F associée au foncteur F : C ⥤ Cat.
#check @CategoryTheory.Grothendieck

-- Les morphismes de ∫ F : un couple (flèche de base, flèche de fibre).
#check @CategoryTheory.Grothendieck.Hom

/-!
## 2. Le foncteur d'oubli (la fibration)

Le foncteur `forget : ∫ F ⥤ C` oublie la donnée de fibre et ne retient que
la base. C'est le foncteur structural de la construction : ses fibres
(préimages des objets de C) retrouvent exactement les catégories `F(c)`.
Une fibration est, en pratique, « un foncteur qui ressemble à un forget ».
-/

-- Le foncteur d'oubli ∫ F ⥤ C (le foncteur fibration).
#check @CategoryTheory.Grothendieck.forget

/-!
## 3. Fonctorialité en F

La construction de Grothendieck est elle-même fonctorielle : une
transformation naturelle `α : F ⟶ G` induit un foncteur `∫ F ⥤ ∫ G` qui
préserve la base (commute avec les deux foncteurs d'oubli).
-/

-- L'action fonctorielle d'une transformation naturelle α : F ⟶ G sur ∫ F ⥤ ∫ G.
#check @CategoryTheory.Grothendieck.map

/-!
## 4. Transport cartésien

Pour un objet `x : ∫ F` au-dessus de `c` et une flèche `t : c ⟶ d` dans C,
le transport `x.transport t` est l'objet au-dessus de `d` obtenu en
appliquant `F(t)` à la fibre de x. Le morphisme `toTransport` est la
flèche cartésienne canonique `x ⟶ x.transport t`. Les flèches cartésiennes
sont les « bons » morphismes d'une fibration (ceux qui se relèvent
exactement, au sens de la descente).
-/

-- Le transport d'un objet de ∫ F le long d'une flèche de la base.
#check @CategoryTheory.Grothendieck.transport

-- La flèche cartésienne canonique x ⟶ x.transport t induite par t.
#check @CategoryTheory.Grothendieck.toTransport

/-!
## 5. Isomorphismes dans ∫ F

Un isomorphisme dans ∫ F se décompose en un isomorphisme de la base et un
isomorphisme de la fibre — c'est `isoMk`. Cette décomposition est centrale
pour transporter des structures le long d'isos dans la base (descente).
-/

-- Construction d'un iso dans ∫ F depuis un iso de base + un iso de fibre.
#check @CategoryTheory.Grothendieck.isoMk

/-!
## 6. Théorèmes ponts

Reformulations dans l'espace de noms du projet, pontant les faits Mathlib.
-/

/-- Pont : le foncteur d'oubli de la construction de Grothendieck ∫ F ⥤ C.
    C'est le foncteur fibration canonique dont les fibres au-dessus de chaque
    `c : C` retrouvent la catégorie `F(c)`. -/
def forget_family : CategoryTheory.Grothendieck F ⥤ C :=
  CategoryTheory.Grothendieck.forget F

/-- Pont : la construction de Grothendieck est fonctorielle en F. Une
    transformation naturelle α : F ⟶ G induit un foncteur ∫ F ⥤ ∫ G qui
    commute avec les foncteurs d'oubli (préserve la base). -/
def map_family {G : C ⥤ Cat.{v₂, u₂}} (α : F ⟶ G) :
    CategoryTheory.Grothendieck F ⥤ CategoryTheory.Grothendieck G :=
  CategoryTheory.Grothendieck.map α

/-- Pont : le transport cartésien d'un objet de ∫ F le long d'une flèche de
    la base. C'est l'opération de relèvement qui définit le caractère
    « fibré » de la projection (existence de flèches cartésiennes). -/
def transport_family (x : CategoryTheory.Grothendieck F) {c : C}
    (t : (CategoryTheory.Grothendieck.forget F).obj x ⟶ c) :
    CategoryTheory.Grothendieck F :=
  CategoryTheory.Grothendieck.transport x t

end Grothendieck.Construction
