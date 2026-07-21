/-
Grothendieck Partie 28 — Extensions de Kan

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

L'extension de Kan est l'une des constructions les plus universelles de la
théorie des catégories : elle « étend » un foncteur `F : C ⥤ H` le long d'un
foncteur `L : C ⥤ D`, produisant un foncteur `D ⥤ H` qui est le « meilleur
relèvement possible » de `F` au-delà de l'image de `L`. Grothendieck en fait
un usage constant : les limites et colimites sont des extensions de Kan
le long du foncteur unique vers la catégorie terminale ; le lemme de Yoneda
est l'extension de Kan de l'identité ; les foncteurs dérivés (Cartan-Eilenberg,
puis les foncteurs dérivés de Grothendieck en géométrie algébrique) sont des
extensions de Kan ; la densité d'un foncteur (notamment le plongement de
Yoneda) s'exprime par une extension de Kan.

Étant donnés `L : C ⥤ D` et `F : C ⥤ H`, une **extension de Kan à gauche**
de `F` le long de `L` est la donnée d'un foncteur `F' : D ⥤ H` et d'une
transformation naturelle `η : F ⟶ L ⋙ F'` (l'« unité ») satisfaisant une
propriété universelle : pour tout `G : D ⥤ H`, la composition
`(F ⟶ L ⋙ F') ⟶ (L ⋙ G)` induit une bijection `(F' ⟶ G) ≃ (F ⟶ L ⋙ G)`.
Duallement, une **extension de Kan à droite** est un foncteur `F' : D ⥤ H`
avec `ε : L ⋙ F' ⟶ F` universelle au sens de la bijection
`(G ⟶ F') ≃ (L ⋙ G ⟶ F)`.

La définition est donc purement universelle : une extension de Kan à gauche
est un **objet initial** dans la catégorie des paires `(F', F ⟶ L ⋙ F')`, et
une extension de Kan à droite est un **objet terminal** dans la catégorie des
paires `(F', L ⋙ F' ⟶ F)`. Mathlib encode ces catégories comme
`Functor.LeftExtension L F` et `Functor.RightExtension L F`.

Mathlib 4 formalise toute cette infrastructure dans
`Mathlib.CategoryTheory.Functor.KanExtension` :
  - `Functor.LeftExtension L F` / `RightExtension L F` — catégories d'extensions
  - `Functor.IsLeftKanExtension F' η` / `IsRightKanExtension F' ε` — la propriété universelle
  - `Functor.HasLeftKanExtension L F` / `HasRightKanExtension L F` — existence (objet initial/terminal)
  - `Functor.leftKanExtension L F` / `rightKanExtension L F` — l'extension choisie
  - `Functor.leftKanExtensionUnit` / `rightKanExtensionCounit` — unité/coïnité
  - `Functor.lan L` — le foncteur « extension de Kan à gauche » `(C ⥤ H) ⥤ (D ⥤ H)`

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant les extensions de Kan pour la première fois, en
miroir des modules `Grothendieck.YonedaLemma` (le plongement de Yoneda est
dense — toute la théorie des extensions de Kan repose sur lui, cf §7) et
`Grothendieck.Adjunction` (une adjonction L ⊣ R donne les bijections
Hom_D(LX,Y) ≃ Hom_C(X,RY) « ponctuelles » ; une extension de Kan à gauche
généralise à un foncteur source arbitraire).

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `KanExtensions_en.lean`. Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti.
-/

import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Dense

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Grothendieck.KanExtensions

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {H : Type u₃} [Category.{v₃} H]

/-!
## 1. Le problème : étendre un foncteur le long d'un autre

Étant donnés `L : C ⥤ D` et `F : C ⥤ H`, on cherche à « étendre » `F` en un
foncteur défini sur tout `D` (pas seulement sur l'image de `L`). Une
**extension à gauche** est la donnée de `F' : D ⥤ H` et d'une transformation
naturelle `η : F ⟶ L ⋙ F'`. Une **extension à droite** est `F' : D ⥤ H` et
`ε : L ⋙ F' ⟶ F`. Mathlib regroupe ces données dans les catégories
`Functor.LeftExtension L F` (objets initiaux = Kan gauche) et
`Functor.RightExtension L F` (objets terminaux = Kan droite).
-/

-- La catégorie des extensions à gauche de F le long de L : paires (F', F ⟶ L ⋙ F').
#check @CategoryTheory.Functor.LeftExtension

-- La catégorie des extensions à droite de F le long de L : paires (F', L ⋙ F' ⟶ F).
#check @CategoryTheory.Functor.RightExtension

-- Constructeur d'objet de LeftExtension L F.
#check @CategoryTheory.Functor.LeftExtension.mk

-- Constructeur d'objet de RightExtension L F.
#check @CategoryTheory.Functor.RightExtension.mk

/-!
## 2. La propriété universelle : IsLeftKanExtension / IsRightKanExtension

La propriété « être une extension de Kan » s'énonce comme une propriété
universelle. `F'.IsLeftKanExtension η` (avec `η : F ⟶ L ⋙ F'`) affirme que
`(F', η)` est **initial** dans `LeftExtension L F` : pour tout concurrent
`(G, F ⟶ L ⋙ G)`, il existe un unique morphisme `F' ⟶ G` factorisant la
transformation. Duallement, `F'.IsRightKanExtension ε` affirme que `(F', ε)`
est **terminal** dans `RightExtension L F`. Ce sont des `Prop` (propriétés,
pas données) — l'unicité est partie de la définition.
-/

-- La propriété universelle « (F', η) est une extension de Kan à gauche ».
#check @CategoryTheory.Functor.IsLeftKanExtension

-- La propriété universelle « (F', ε) est une extension de Kan à droite ».
#check @CategoryTheory.Functor.IsRightKanExtension

-- Témoignage de l'initialité : (F', η) initial dans LeftExtension L F.
#check @CategoryTheory.Functor.isUniversalOfIsLeftKanExtension

-- Témoignage de la terminalité : (F', ε) terminal dans RightExtension L F.
#check @CategoryTheory.Functor.isUniversalOfIsRightKanExtension

/-!
## 3. Existence : HasLeftKanExtension / HasRightKanExtension

L'existence d'une extension de Kan n'est pas garantie en général (elle
dépend de la complétude de `H`). Mathlib l'énonce par les typeclasses
`HasLeftKanExtension L F := HasInitial (LeftExtension L F)` et
`HasRightKanExtension L F := HasTerminal (RightExtension L F)`. Quand elles
tiennent, on dispose d'une extension **choisie** `leftKanExtension L F`
(respectivement `rightKanExtension L F`) et de son unité (resp. coïnité).
-/

-- Le typeclass « F admet une extension de Kan à gauche le long de L ».
#check @CategoryTheory.Functor.HasLeftKanExtension

-- Le typeclass « F admet une extension de Kan à droite le long de L ».
#check @CategoryTheory.Functor.HasRightKanExtension

-- L'extension de Kan à gauche choisie quand [HasLeftKanExtension L F].
#check @CategoryTheory.Functor.leftKanExtension

-- L'extension de Kan à droite choisie quand [HasRightKanExtension L F].
#check @CategoryTheory.Functor.rightKanExtension

-- L'unité de l'extension de Kan à gauche choisie : F ⟶ L ⋙ leftKanExtension L F.
#check @CategoryTheory.Functor.leftKanExtensionUnit

-- La coïnité de l'extension de Kan à droite choisie : L ⋙ rightKanExtension L F ⟶ F.
#check @CategoryTheory.Functor.rightKanExtensionCounit

/-!
## 4. La descente universelle

La propriété universelle se réécrit comme une bijection naturelle entre
espaces de morphismes. Pour une extension de Kan à gauche `(F', η)`, tout
`β : F ⟶ L ⋙ G` se factorise de manière unique en
`F ⟶ L ⋙ F' ⟶ L ⋙ G` via un morphisme `F' ⟶ G` (la « descente »).
Pour une extension à droite, tout `β : L ⋙ G ⟶ F` se relève en `G ⟶ F'`.
C'est l'analogue de la bijection d'adjonction Hom_D(LX,Y) ≃ Hom_C(X,RY),
mais « fonctorielle en F' tout entier ».
-/

-- La descente universelle d'une extension de Kan à gauche : F' ⟶ G depuis β : F ⟶ L ⋙ G.
#check @CategoryTheory.Functor.descOfIsLeftKanExtension

-- Le relèvement universel d'une extension de Kan à droite : G ⟶ F' depuis β : L ⋙ G ⟶ F.
#check @CategoryTheory.Functor.liftOfIsRightKanExtension

-- La bijection naturelle (F' ⟶ G) ≃ (L ⋙ G ⟶ F) pour une Kan droite.
#check @CategoryTheory.Functor.homEquivOfIsRightKanExtension

/-!
## 5. Le foncteur lan / lanUnit

Quand `F ↦ leftKanExtension L F` existe pour **tout** `F : C ⥤ H`
(c'est-à-dire `[∀ F, HasLeftKanExtension L F]`), l'extension de Kan à gauche
se packe en un **foncteur** `lan L : (C ⥤ H) ⥤ (D ⥤ H)`, adjoint à gauche du
foncteur de précomposition `whiskeringLeft C D H).obj L : (D ⥤ H) ⥤ (C ⥤ H)`.
L'unité de cette adjonction est `lanUnit : 𝟭 (C ⥤ H) ⟶ L.lan ⋙ (precomp L)`.
-/

-- Le foncteur extension de Kan à gauche (C ⥤ H) ⥤ (D ⥤ H) le long de L.
#check @CategoryTheory.Functor.lan

-- L'unité naturelle 𝟭 (C ⥤ H) ⟶ L.lan ⋙ (whiskeringLeft C D H).obj L.
#check @CategoryTheory.Functor.lanUnit

/-!
## 6. Extensions de Kan ponctuelles (pointwise)

Une extension de Kan peut être définie « ponctuellement » : `F'` est une
extension ponctuelle de `F` le long de `L` si pour chaque `Y : D`, l'objet
`F'.obj Y` est la (co)limente appropriée indexée par la catégorie fibre
`L ↓ Y`. C'est la forme calculable (formules explicites en termes de
(co)limites), par opposition à la forme universelle abstraite. Mathlib
énonce cela via `HasPointwiseLeftKanExtension` / `HasPointwiseRightKanExtension`.
-/

-- Le typeclass « F admet une extension de Kan à gauche ponctuelle ».
#check @CategoryTheory.Functor.HasPointwiseLeftKanExtension

-- Le typeclass « F admet une extension de Kan à droite ponctuelle ».
#check @CategoryTheory.Functor.HasPointwiseRightKanExtension

/-!
## 7. Yoneda comme extension de Kan ; densité

Le fait fondamental qui relie les extensions de Kan au reste de la théorie :
le lemme de Yoneda **est** une extension de Kan. Plus précisément, le
plongement de Yoneda `yoneda : C ⥤ (Cᵒᵖ ⥤ Type*)` est **dense** : tout
foncteur sur `C` se récupère comme extension de Kan (colimite pondérée) du
plongement de Yoneda. La densité s'énonce exactement comme « l'identité est
une extension de Kan à gauche du foncteur le long de lui-même », ce que
Mathlib encode via `Functor.IsDense`. C'est le sens profond du lemme de
Yoneda : les objets de `C` « engendrent » tout préfaisceau par extension de Kan.
-/

-- La propriété « F est dense » : 𝟭 D est extension de Kan de F le long de F.
#check @CategoryTheory.Functor.IsDense

/-!
## 8. Théorèmes ponts

Reformulations dans l'espace de noms du projet, pontant les faits Mathlib.
-/

/-- Pont : l'extension de Kan à gauche choisie de `F` le long de `L`,
    exposée comme foncteur nu `D ⥤ H`. C'est l'extension « canonique » quand
    `[HasLeftKanExtension L F]`. -/
noncomputable def kan_extension_left (L : C ⥤ D) (F : C ⥤ H)
    [L.HasLeftKanExtension F] : D ⥤ H :=
  L.leftKanExtension F

/-- Pont : l'extension de Kan à droite choisie de `F` le long de `L`. -/
noncomputable def kan_extension_right (L : C ⥤ D) (F : C ⥤ H)
    [L.HasRightKanExtension F] : D ⥤ H :=
  L.rightKanExtension F

/-- Pont : l'unité de l'extension de Kan à gauche choisie —
    `F ⟶ L ⋙ leftKanExtension L F`. Témoignage que l'extension est
    universelle au-dessus de tous les concurrents. -/
noncomputable def kan_extension_left_unit (L : C ⥤ D) (F : C ⥤ H)
    [L.HasLeftKanExtension F] : F ⟶ L ⋙ L.leftKanExtension F :=
  L.leftKanExtensionUnit F

/-- Pont : la coïnité de l'extension de Kan à droite choisie —
    `L ⋙ rightKanExtension L F ⟶ F`. -/
noncomputable def kan_extension_right_counit (L : C ⥤ D) (F : C ⥤ H)
    [L.HasRightKanExtension F] : L ⋙ L.rightKanExtension F ⟶ F :=
  L.rightKanExtensionCounit F

/-- Pont : le foncteur extension de Kan à gauche `(C ⥤ H) ⥤ (D ⥤ H)` le long
    de `L`, quand toutes les extensions ponctuelles existent. C'est l'adjoint
    à gauche du précomposition par `L`. -/
noncomputable def lan_functor (L : C ⥤ D)
    [∀ (F : C ⥤ H), L.HasLeftKanExtension F] : (C ⥤ H) ⥤ (D ⥤ H) :=
  L.lan

/-- Pont : la descente universelle d'une extension de Kan à gauche — étant
    donné `(F', η)` Kan gauche et `β : F ⟶ L ⋙ G`, le morphisme unique
    `F' ⟶ G` factorisant `β` via `η`. C'est le bras opérationnel de la
    propriété universelle. -/
noncomputable def kan_descent {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (η : F ⟶ L ⋙ F') [F'.IsLeftKanExtension η] (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    F' ⟶ G :=
  F'.descOfIsLeftKanExtension η G β

end Grothendieck.KanExtensions
