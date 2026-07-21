/-
Grothendieck hommage — Partie 24 : Le lemme de Yoneda

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Le lemme de Yoneda est LE théorème fondamental de la théorie des catégories.
C'est l'épine dorsale de la reformulation grothendieckienne de la géométrie
algébrique : par Yoneda, les objets d'une catégorie sont déterminés par les
préfaisceaux qu'ils représentent.

Mathlib 4 formalise déjà toute l'infrastructure Yoneda dans
`Mathlib.CategoryTheory.Yoneda` :
  - `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` — le plongement de Yoneda
  - `yonedaEquiv : (yoneda.obj X ⟶ F) ≃ F.obj (op X)` — l'équivalence au
    niveau des types
  - `yonedaEquiv_naturality` — la naturalité en `X`
  - `yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C` — l'isomorphisme
    naturel
  - `fullyFaithful yoneda` — le plongement de Yoneda est pleinement fidèle
    (corollaire)

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant le lemme de Yoneda pour la première fois :

  1. Énoncé du plongement de Yoneda.
  2. Le lemme de Yoneda comme équivalence au niveau des types.
  3. Naturalité : la bijection est naturelle en `X` et en `F`.
  4. Plénitude et fidélité : le plongement de Yoneda est pleinement fidèle.
  5. Le dual covariant (`coyoneda`).
  6. La fonctorialité retrouve `Hom(y, x) → Nat(yoneda.y, yoneda.x)`.

Epic #1646, #2159 (Phase 2+). Aucun but non-résolu à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `YonedaLemma_en.lean` (modèle sibling pair, voir PR #6154 pour le
pilote sur `Utility.lean`). Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais (Mathlib 4,
tactic DSL standard). Seules les **docstrings `/-- ... -/`** et les
**commentaires `-- ...`** diffèrent entre les deux fichiers. Anti-§D
byte-identity garanti : le namespace body est préservé bit-pour-bit
(énoncés et preuves byte-identiques entre `YonedaLemma.lean` et
`YonedaLemma_en.lean`).
-/

import Mathlib.CategoryTheory.Yoneda

namespace Grothendieck

open CategoryTheory Opposite

/-!
## Le plongement de Yoneda

`yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` envoie chaque objet `X : C` sur le préfaisceau
représentable `yoneda.obj X : Cᵒᵖ ⥤ Type v₁` dont la valeur en `op Y` est
l'ensemble de morphismes `Y ⟶ X`, le morphisme étant induit par la
précomposition.

C'est le pont canonique entre les objets de `C` et les préfaisceaux sur `C`.
-/

/-- Le plongement de Yoneda envoie `X : C` sur le préfaisceau représenté par
    `X` : `yoneda.obj X` évalué en `op Y` est l'ensemble de morphismes
    `Y ⟶ X`. -/
example {C : Type*} [Category C] (X : C) :
    yoneda.obj X = yoneda.obj X :=
  rfl

/-- Pour `f : X ⟶ Y`, `yoneda.map f : yoneda.obj X ⟶ yoneda.obj Y` est la
    post-composition par `f`. -/
example {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    yoneda.obj X ⟶ yoneda.obj Y :=
  yoneda.map f

/-!
## Le lemme de Yoneda (équivalence au niveau des types)

Le lemme de Yoneda établit une bijection canonique au niveau des types
`(yoneda.obj X ⟶ F) ≃ F.obj (op X)`
pour tout `F : Cᵒᵖ ⥤ Type v₁`. Mathlib nomme cela `yonedaEquiv`.

Direction avant : une transformation naturelle `η` donne un élément
`η.app (op X) (𝟙 X)`.
Inverse : un élément `x : F.obj (op X)` donne la transformation naturelle
`fun Y f ↦ F.map f.op x`.
-/

/-- Direction avant du lemme de Yoneda : une transformation naturelle
    `η : yoneda.obj X ⟶ F` est déterminée par sa valeur en l'identité sur `X`. -/
theorem yoneda_equiv_apply {C : Type*} [Category C] {X : C}
    {F : Cᵒᵖ ⥤ Type*} (η : yoneda.obj X ⟶ F) :
    yonedaEquiv η = η.app (op X) (𝟙 X) :=
  yonedaEquiv_apply η

/-- Direction inverse : un élément `x : F.obj (op X)` détermine la
    transformation naturelle dont la valeur en `Y` et `f : Y.unop ⟶ X` est
    `F.map f.op x`. -/
theorem yoneda_equiv_symm_app_apply {C : Type*} [Category C] {X : C}
    {F : Cᵒᵖ ⥤ Type*} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) :
    (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  yonedaEquiv_symm_app_apply x Y f

/-- Appliquer l'équivalence de Yoneda à `yoneda.map g` retrouve `g` lui-même. -/
theorem yoneda_equiv_yoneda_map {C : Type*} [Category C] {X Y : C}
    (f : X ⟶ Y) :
    yonedaEquiv (yoneda.map f) = f :=
  yonedaEquiv_yoneda_map f

/-!
## Naturalité de la bijection de Yoneda

La bijection `(yoneda.obj X ⟶ F) ≃ F.obj (op X)` est naturelle en ses deux
arguments. Mathlib formalise cela comme un isomorphisme naturel
`yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C`.
-/

/-- Naturalité en `X` : la pré-composition de `η : yoneda.obj X ⟶ F` par
    `yoneda.map g` correspond sous l'équivalence de Yoneda à `F.map g.op`. -/
theorem yoneda_equiv_naturality {C : Type*} [Category C] {X Y : C}
    {F : Cᵒᵖ ⥤ Type*} (η : yoneda.obj X ⟶ F) (g : Y ⟶ X) :
    F.map g.op (yonedaEquiv η) = yonedaEquiv (yoneda.map g ≫ η) :=
  yonedaEquiv_naturality η g

/-- Le lemme de Yoneda comme isomorphisme naturel entre les foncteurs
    d'appariement et d'évaluation. -/
def yonedaPairingIsoEvaluation (C : Type*) [Category C] :
    yonedaPairing C ≅ yonedaEvaluation C :=
  yonedaLemma C

/-!
## Plénitude et fidélité du plongement de Yoneda

Le plongement de Yoneda `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)` est pleinement fidèle :
la flèche `X ⟶ Y ↦ yoneda.map f` est une bijection sur les ensembles de
morphismes.

C'est le corollaire de Yoneda que Grothendieck a le plus utilisé : les
préfaisceaux reflètent fidèlement la structure de la catégorie.
-/

/-- Le plongement de Yoneda est plein. C'est la première moitié de la pleine
    fidélité : la pré-composition des morphismes se relève le long de
    `yoneda`. -/
theorem yoneda_full (C : Type*) [Category C] :
    (yoneda (C := C)).Full :=
  Yoneda.yoneda_full

/-- Le plongement de Yoneda est fidèle. C'est l'autre moitié : le plongement
    n'identifie pas des morphismes distincts. -/
theorem yoneda_faithful (C : Type*) [Category C] :
    (yoneda (C := C)).Faithful :=
  Yoneda.yoneda_faithful

/-- La pleine fidélité de `yoneda` (le plongement de Yoneda
    `C ⥤ Cᵒᵖ ⥤ Type v₁` est pleinement fidèle) découle de `Full` et `Faithful`
    ci-dessus et du constructeur canonique `Functor.FullyFaithful.ofFullyFaithful`. -/
example {C : Type*} [Category C] : (yoneda (C := C)).FullyFaithful :=
  Yoneda.fullyFaithful

/-!
## Le dual covariant (coyoneda)

Le plongement de Yoneda covariant est `coyoneda : Cᵒᵖ ⥤ (C ⥤ Type v₁)`. Il a
son propre lemme : `(coyoneda.obj (op X) ⟶ F) ≃ F.obj X` pour
`F : C ⥤ Type v₁`.
-/

/-- Le lemme de Yoneda covariant comme isomorphisme naturel. -/
def coyonedaPairingIsoEvaluation (C : Type*) [Category C] :
    coyonedaPairing C ≅ coyonedaEvaluation C :=
  coyonedaLemma C

/-!
### Plénitude et fidélité du plongement covariant

Tout comme son dual contravariant, le plongement covariant `coyoneda` est
pleinement fidèle : c'est le miroir exact du plongement de Yoneda. Cette
pleine fidélité est centrale pour la théorie des foncteurs coreprésentables
(la face covariante des représentables), utilisée notamment en théorie des
faisceaux et en cohomologie.
-/

/-- Le plongement de Yoneda covariant est plein. Miroir covariant de
    `yoneda_full` : la pré-composition se relève le long de `coyoneda`. -/
theorem coyoneda_full (C : Type*) [Category C] :
    (coyoneda (C := C)).Full :=
  Coyoneda.coyoneda_full

/-- Le plongement de Yoneda covariant est fidèle. Miroir covariant de
    `yoneda_faithful`. -/
theorem coyoneda_faithful (C : Type*) [Category C] :
    (coyoneda (C := C)).Faithful :=
  Coyoneda.coyoneda_faithful

/-- La pleine fidélité de `coyoneda` (le plongement covariant
    `Cᵒᵖ ⥤ C ⥤ Type v₁` est pleinement fidèle) découle de `Full` et `Faithful`
    ci-dessus et du constructeur canonique `Functor.FullyFaithful.ofFullyFaithful`. -/
example {C : Type*} [Category C] : (coyoneda (C := C)).FullyFaithful :=
  Coyoneda.fullyFaithful

/-!
## La fonctorialité retrouve l'ensemble de morphismes

Le plongement de Yoneda relève l'ensemble de morphismes dans la catégorie des
préfaisceaux. Plus précisément, pour `X Y : C`, l'ensemble de morphismes
`Y ⟶ X` est `yoneda.obj X` évalué en `op Y`. C'est l'interprétation canonique
des morphismes comme transformations naturelles (entre représentables) — le
fait profond derrière Yoneda.
-/

/-- L'ensemble de morphismes de `Y` vers `X` dans `C` est `yoneda.obj X` évalué
    en `op Y`. Cela retrouve l'ensemble de morphismes depuis le préfaisceau
    représentable. -/
example {C : Type*} [Category C] (X Y : C) :
    (yoneda.obj X).obj (op Y) ≃ (Y ⟶ X) :=
  Equiv.refl _

end Grothendieck