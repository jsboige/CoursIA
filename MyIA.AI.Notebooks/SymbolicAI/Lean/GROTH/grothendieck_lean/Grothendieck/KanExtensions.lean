/-
Grothendieck Partie 31 — Extensions de Kan

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Tous les `sorry` éliminés à la création (c.8228) : 0/0 sorry, 4/4 theorems
propres (cast sur les définitions et théorèmes Mathlib 4 v4.31.0-rc1,
sans tactique non triviale). Ponts vers `Mathlib.CategoryTheory.Functor.KanExtension.{Basic,Adjunction,Pointwise,Dense}`
via `L.lanAdjunction`, `lanAdjunction_unit`, `descOfIsLeftKanExtension_fac`,
`leftKanExtensionIso`. Voir c.8224 (leçon L902 ★ ÉTENDU : `rfl` est pont
suffisant quand l'égalité est définitionnelle ou quand on **est** la valeur).

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
import Mathlib.CategoryTheory.Whiskering

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

/-- Pont : `L.lan` est adjoint à gauche du foncteur de précomposition
    `(whiskeringLeft C D H).obj L : (D ⥤ H) ⥤ (C ⥤ H)`. C'est la
    formulation en catégorie de foncteurs du lemme « l'extension de Kan
    gauche est le meilleur relèvement à gauche » — Mathlib attache
    directement l'adjonction à `L` via la classe `L.HasLeftKanExtension`
    une fois pour toutes.

    Note : `noncomputable def` (pas `theorem`) parce que le type
    `L.lan ⊣ (Functor.whiskeringLeft C D H).obj L` est une **adjonction**
    (data : un objet avec unit + counit + homEquiv), pas une Prop. -/
noncomputable def lan_functor_is_left_adjoint_to_precomp (L : C ⥤ D) (H : Type u₃)
    [Category.{v₃, u₃} H] [∀ (F : C ⥤ H), L.HasLeftKanExtension F] :
    L.lan ⊣ (Functor.whiskeringLeft C D H).obj L :=
  L.lanAdjunction H

/-- Pont : l'unité de l'adjonction `lan ⊣ precomp L` est exactement
    `L.lanUnit`. C'est le `@[simp]` lemma de Mathlib — `lanAdjunction_unit`
    est un **théorème** (pas une égalité définitionnelle), donc on
    l'utilise comme corps de la preuve. (L902 ★ ÉTENDU c.8224 reaffirmed :
    `rfl` ne marche PAS pour `simp` lemmas, il faut le théorème.) -/
theorem lan_unit_eq_lan_adjunction_unit (L : C ⥤ D) (H : Type u₃)
    [Category.{v₃, u₃} H] [∀ (F : C ⥤ H), L.HasLeftKanExtension F] :
    (L.lanAdjunction H).unit = L.lanUnit :=
  CategoryTheory.Functor.lanAdjunction_unit L H

/-- Pont : la descente universelle `kan_descent` vérifie la condition
    de factorisation — c'est la naturalité de l'adjonction. Le morphisme
    `F' ⟶ G` produit par `descOfIsLeftKanExtension` rend `η` et `β`
    compatibles via whiskering : `α ≫ L.whiskerLeft (F'.descOfIsLeftKanExtension
    α G β) = β`. -/
theorem kan_descent_fac {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (η : F ⟶ L ⋙ F') [F'.IsLeftKanExtension η] (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    η ≫ L.whiskerLeft (F'.descOfIsLeftKanExtension η G β) = β :=
  F'.descOfIsLeftKanExtension_fac η G β

/-- Pont : si `L` est un foncteur dense, alors son extension de Kan
    gauche le long de lui-même est isomorphe à l'identité sur `D`. C'est
    la formulation de la densité de `L` (le cas particulier de Yoneda :
    l'identité est sa propre extension de Kan le long d'elle-même).

    Note : on utilise `noncomputable def` (pas `theorem`) parce que le
    type `F.leftKanExtension F ≅ 𝟭 D` est une **structure** (data), pas
    une proposition — le théorème Mathlib `IsDense.leftKanExtensionIso`
    est lui-même `noncomputable def`. Un `theorem ... := x` exige une
    Prop comme type, ce que `≅` n'est pas. -/
noncomputable def dense_functor_left_kan_extension_iso_id (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtension F ≅ 𝟭 D :=
  CategoryTheory.Functor.IsDense.leftKanExtensionIso F

/-!
## 9. Ponts additionnels : factorisation duale, bijection naturelle, densité Yoneda

Les 4 ponts suivants complètent le tableau des lemmes Mathlib 4 fondamentaux
sur les extensions de Kan, en couvrant les branches symétriques des bridges
existants (10 → 14 theoremes/decls) :
  - `kan_lift_fac` : dual côté **droite** de `kan_descent_fac` — la factorisation
    universelle d'un Kan droite vérifie sa condition de factorisation.
  - `kan_right_hom_equiv` : bijection naturelle `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` pour
    une Kan droite — symétrique pointwise du `homEquiv` de l'adjonction.
  - `dense_left_kan_unit_iso` : pour un foncteur dense `F`, l'unité de son
    extension de Kan gauche le long de lui-même composée avec l'isomorphisme
    `leftKanExtension F ≅ 𝟭 D` vaut `rightUnitor.inv` (NatTrans-level).
  - `dense_left_kan_unit_iso_app` : version pointwise du précédent, descendu
    à `app X` pour `X : C` — la cohérence vue sur chaque objet.

Pattern winner (L902 ★★ c.8261) : univers explicites, alias directs Mathlib,
signatures alignées sur le lemme source. Pour les lemmes dans `section`
Mathlib (lift/homEquiv sont sous `variable (F') {L F} (α) [IsRightKanExtension α]`)
on **doit** passer toutes les variables en argument.
-/

/-- Pont : dual côté **droite** de `kan_descent_fac` — pour une extension de
    Kan à droite `(F', α)`, la factorisation universelle
    `liftOfIsRightKanExtension α G β : G ⟶ F'` vérifie sa condition de
    factorisation `whiskerLeft L (lift) ≫ α = β`. C'est le symétrique
    de `kan_descent_fac` (côté gauche), démontré par le lemme Mathlib
    `@[reassoc, simp] lemma CategoryTheory.Functor.liftOfIsRightKanExtension_fac`.
    Namespace theorem (L902 ★★ Tier 4) — alias direct avec args explicites
    (lemme dans une `section` Mathlib, toutes les variables doivent
    être passées). -/
theorem kan_lift_fac {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α] (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    CategoryTheory.Functor.whiskerLeft L (F'.liftOfIsRightKanExtension α G β) ≫ α = β :=
  CategoryTheory.Functor.liftOfIsRightKanExtension_fac F' α G β

/-- Pont : bijection naturelle `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` pour une extension
    de Kan à droite `(F', α)`. Symétrique pointwise de l'homEquiv d'une
    adjonction — la propriété universelle encodée comme **équivalence**
    (et non comme deux flèches adjointes). C'est le lemme Mathlib
    `@[simps!] noncomputable def CategoryTheory.Functor.homEquivOfIsRightKanExtension`.
    Namespace def (L902 ★★ Tier 4) — alias direct, args explicites. -/
noncomputable def kan_right_hom_equiv {L : C ⥤ D} {F : C ⥤ H} {F' : D ⥤ H}
    (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α] (G : D ⥤ H) :
    (G ⟶ F') ≃ (L ⋙ G ⟶ F) :=
  CategoryTheory.Functor.homEquivOfIsRightKanExtension F' α G

/-- Pont : pour un foncteur dense `F : C ⥤ D`, l'unité de son extension de
    Kan gauche le long de lui-même composée avec l'isomorphisme
    `leftKanExtension F ≅ 𝟭 D` vaut `rightUnitor.inv` au niveau NatTrans.
    C'est le lemme Mathlib
    `@[reassoc, simp] lemma CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom`.
    Namespace theorem (L902 ★★ Tier 4) — alias direct. -/
theorem dense_left_kan_unit_iso (F : C ⥤ D) [F.IsDense] :
    F.leftKanExtensionUnit F ≫
      F.whiskerLeft (Functor.IsDense.leftKanExtensionIso F).hom = F.rightUnitor.inv :=
  CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom F

/-- Pont : version pointwise de `dense_left_kan_unit_iso` — descendu à
    `app X` pour `X : C`, la cohérence devient :
    `(leftKanExtensionUnit F).app X ≫ (leftKanExtensionIso F).hom.app (F.obj X)
     = F.rightUnitor.inv.app X`.
    C'est le lemme Mathlib
    `@[reassoc, simp] lemma CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app`.
    Namespace theorem (L902 ★★ Tier 4) — alias direct. Le `{F.IsDense}`
    implicite est auto-déduit du scope du bridge. -/
theorem dense_left_kan_unit_iso_app (F : C ⥤ D) [F.IsDense] (X : C) :
    (F.leftKanExtensionUnit F).app X ≫
      (Functor.IsDense.leftKanExtensionIso F).hom.app (F.obj X) =
        F.rightUnitor.inv.app X :=
  CategoryTheory.Functor.IsDense.leftKanExtensionUnit_leftKanExtensionIso_hom_app F X

/-!
## 9. Ponts sur les catégories d'extensions, les propriétés universelles et la densité

Les 7 bridges suivants ferment les sections 1-3 et 7 du répertoire documentaire
(`#check`) : les **catégories d'extensions** (`LeftExtension`/`RightExtension`),
les **propriétés universelles** (`IsLeftKanExtension`/`IsRightKanExtension`)
et les **typeclasses d'existence** (`HasLeftKanExtension`/`HasRightKanExtension`),
plus la **densité** (`IsDense`) qui relie Yoneda aux extensions de Kan. Les
extensions choisies, unités/coïnités, la descente, la bijection d'adjonction
et le foncteur `lan` sont déjà bridgés par les sections 8 (decls existantes) ;
ces 7 bridges complètent le tableau par la **forme abstraite** (catégories,
Propositions, typeclasses) sur laquelle la forme choisie repose.

Forme retenue (L902 ★★ Tier 5) : les deux catégories sont des re-exports
type-sig de data (`Type _` inféré), les deux propriétés universelles sont des
Prop à args explicites (`F'` puis `η`/`ε`, appliquées par `F'.IsLeftKanExtension
η`), les deux typeclasses d'existence sont des Prop type-sig (pattern
`has_enough_points_field` c.1301+139), et la densité est une Prop type-sig sur
`F : C ⥤ D` (classe Mathlib, `F.IsDense`). Args résidents (univers
`v₁ v₂ v₃ u₁ u₂ u₃`), instances structurelles, pas de constructeur polymorphe
d'univers.
-/

/-- Pont : la **catégorie des extensions à gauche** de `F` le long de `L` —
    les paires `(F' : D ⥤ H, η : F ⟶ L ⋙ F')`, dont les objets initiaux sont
    exactement les extensions de Kan à gauche. Re-export type-sig de la
    catégorie Mathlib `CategoryTheory.Functor.LeftExtension L F`. -/
def left_extension_field (L : C ⥤ D) (F : C ⥤ H) : Type _ :=
  CategoryTheory.Functor.LeftExtension L F

/-- Pont : la **catégorie des extensions à droite** de `F` le long de `L` —
    les paires `(F' : D ⥤ H, ε : L ⋙ F' ⟶ F)`, dont les objets terminaux
    sont exactement les extensions de Kan à droite. Duale de
    `left_extension_field`, re-export type-sig de la catégorie Mathlib
    `CategoryTheory.Functor.RightExtension L F`. -/
def right_extension_field (L : C ⥤ D) (F : C ⥤ H) : Type _ :=
  CategoryTheory.Functor.RightExtension L F

/-- Pont : la **propriété universelle d'être une extension de Kan à gauche** —
    `(F', η)` est **initial** dans `LeftExtension L F` : pour tout concurrent
    `(G, F ⟶ L ⋙ G)`, il existe un unique morphisme `F' ⟶ G` factorisant la
    transformation. Re-export type-sig de la Prop Mathlib
    `F'.IsLeftKanExtension η` (l'unicité est partie de la définition).
    Args explicites : `F'` puis `η`. -/
def is_left_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) (F' : D ⥤ H) (η : F ⟶ L ⋙ F') : Prop :=
  F'.IsLeftKanExtension η

/-- Pont : la **propriété universelle d'être une extension de Kan à droite** —
    `(F', ε)` est **terminal** dans `RightExtension L F` : tout concurrent
    se factorise de manière unique à travers `F'`. Duale de
    `is_left_kan_extension_field`, re-export type-sig de la Prop Mathlib
    `F'.IsRightKanExtension ε`. Args explicites : `F'` puis `ε`. -/
def is_right_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) (F' : D ⥤ H) (ε : L ⋙ F' ⟶ F) : Prop :=
  F'.IsRightKanExtension ε

/-- Pont : la **typeclasse d'existence** `F` admet une extension de Kan à
    gauche le long de `L` — `HasInitial (LeftExtension L F)` : la catégorie
    des extensions à gauche a un objet initial. Ce n'est pas garanti en
    général (cela dépend de la complétude de `H`). Re-export type-sig de la
    Prop Mathlib `HasLeftKanExtension L F`, sur laquelle repose l'extension
    **choisie** `kan_extension_left` (section 8). -/
def has_left_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) : Prop :=
  CategoryTheory.Functor.HasLeftKanExtension L F

/-- Pont : la **typeclasse d'existence** duale — `F` admet une extension de
    Kan à droite le long de `L` (`HasTerminal (RightExtension L F)`).
    Re-export type-sig de la Prop Mathlib `HasRightKanExtension L F`, sur
    laquelle repose l'extension choisie `kan_extension_right` (section 8). -/
def has_right_kan_extension_field (L : C ⥤ D) (F : C ⥤ H) : Prop :=
  CategoryTheory.Functor.HasRightKanExtension L F

/-- Pont : la **densité** — `F : C ⥤ D` est dense si l'identité de `D` est
    une extension de Kan à gauche de `F` le long de lui-même. C'est le fait
    fondamental qui relie Yoneda aux extensions de Kan : le plongement de
    Yoneda est dense, donc tout foncteur sur `C` se récupère comme extension
    de Kan (colimite pondérée) du plongement — les objets de `C`
    « engendrent » tout préfaisceau. Re-export type-sig de la classe Mathlib
    `F.IsDense` (utilisée en bracket par `dense_left_kan_unit_iso`/`_app`,
    section 8). -/
def is_dense_field (F : C ⥤ D) : Prop :=
  F.IsDense

end Grothendieck.KanExtensions
