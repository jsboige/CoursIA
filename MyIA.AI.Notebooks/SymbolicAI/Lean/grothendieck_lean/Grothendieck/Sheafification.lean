/-
Hommage à Grothendieck — Partie 13 : Faisceautisation (le foncteur faisceau associé)
Alexandre Grothendieck (1928-2014).

Phase 8 extension (#2159, EPIC #1646).

La Partie 7 (SheafBasics.lean) a établi que tout faisceau est séparé,
et que la condition de faisceau se transfère le long des comparaisons
de topologies. La Partie 12 (DenseTopology.lean) a étudié la topologie
dense entre ⊥ et ⊤.

Ce module introduit le **foncteur de faisceautisation** (aussi appelé
« faisceau associé » ou « associated sheaf functor »), l'adjoint à
gauche de l'inclusion des faisceaux dans les préfaisceaux :

  presheafToSheaf J : (Cᵒᵖ ⥤ D) ⥤ Sheaf J D    ⊣    sheafToPresheaf

Ses propriétés fondamentales sont :

  - Adjonction : pour tout préfaisceau P et tout faisceau F, les
    morphismes de P vers le préfaisceau sous-jacent de F sont en
    bijection avec les morphismes de faisceaux de la faisceautisation
    de P vers F.
  - Unité : tout préfaisceau P admet une application canonique
    `toSheafify J P : P ⟶ sheafify J P`.
  - Idempotence : si P est déjà un faisceau, l'unité est un isomorphisme.

Nous indexons `CategoryTheory.Sites.Sheafification` et
`CategoryTheory.Sites.LeftExact` de Mathlib dans le namespace
`Grothendieck`, suivant le même pattern bridge-theorem que les Parties 1-12.

Note d'univers : suivant `LeftExact.lean` de Mathlib, la
faisceautisation pour les préfaisceaux à valeurs dans `Type (max u v)`
sur `C : Type u` avec `[Category.{v} C]` requiert
`HasSheafify J (Type (max u v))`.

EPIC #1646, Phase 8 (#2159). Tous les `sorry` éliminés à la création.

JUMELAGE i18n (EPIC #4980) : ce fichier est la version canonique FR.
Son miroir anglais est `Grothendieck/Sheafification_en.lean` (namespace
suffixé `Grothendieck_en` pour éviter toute collision). Les deux
fichiers partagent le même corps de code (imports, namespace,
théorèmes, defs, preuves) octet pour octet — seuls le docstring de
fichier (`/- ... -/`) et les docstrings de section (`/-! ... -/`)
diffèrent. Vérifié par `scripts/lean/check_i18n_siblings.py` (statut : OK).
-/
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact

universe v u

namespace Grothendieck

open CategoryTheory

/-!
## L'adjonction de faisceautisation

Le foncteur de faisceautisation `presheafToSheaf` est l'adjoint à gauche
de l'inclusion `sheafToPresheaf` des faisceaux dans les préfaisceaux.
Cette adjonction est la propriété universelle fondamentale de la
faisceautisation :

  Hom_Sheaf(sheafify P, F) ≅ Hom_Presheaf(P, F sous-jacent)

L'instance `HasSheafify J (Type (max u v))` (de LeftExact.lean) fournit
la faisceautisation pour les préfaisceaux à valeurs dans `Type` sur
`C : Type u` avec `[Category.{v} C]`.
-/

/-- L'adjonction de faisceautisation : `presheafToSheaf ⊣ sheafToPresheaf`.
    Cette propriété universelle dit que les applications d'un préfaisceau P
    vers le préfaisceau sous-jacent d'un faisceau F correspondent
    bijectivement aux morphismes de faisceaux de la faisceautisation de P
    vers F. -/
noncomputable def sheafification_universal {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    presheafToSheaf J (Type (max u v)) ⊣ sheafToPresheaf J (Type (max u v)) :=
  sheafificationAdjunction J (Type (max u v))

/-!
## L'application canonique vers la faisceautisation

Étant donné un préfaisceau P, `toSheafify J P : P ⟶ sheafify J P` est
l'unité de l'adjonction. Elle envoie chaque section de P vers son image
dans la faisceautisation. Tout morphisme de P vers un faisceau se factorise
de manière unique à travers cette application.

C'est la « manière universelle de transformer un préfaisceau en faisceau ».
-/

/-- L'application canonique `toSheafify` est l'unité de l'adjonction de
    faisceautisation. Utilise `sheafificationAdjunction_unit_app` de Mathlib. -/
theorem toSheafify_is_unit {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    toSheafify J P = (sheafificationAdjunction J (Type (max u v))).unit.app P :=
  sheafificationAdjunction_unit_app J P

/-!
## Idempotence : la faisceautisation d'un faisceau est lui-même

Si P est déjà un faisceau, alors `toSheafify J P` est un isomorphisme.
Intuitivement, faisceautiser un faisceau ne change rien — la construction
est idempotente.

C'est la propriété clé qui fait de la faisceautisation une « réflexion »
le long de l'inclusion des faisceaux dans les préfaisceaux (une localisation).
-/

/-- Si P est un faisceau pour J, alors l'application canonique `toSheafify J P`
    est un isomorphisme. La faisceautisation est idempotente. Utilise
    `isIso_toSheafify` de Mathlib. -/
theorem sheafify_of_sheaf_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (hP : Presheaf.IsSheaf J P) :
    IsIso (toSheafify J P) :=
  isIso_toSheafify J hP

/-- Si P est un faisceau, alors P est isomorphe à sa propre faisceautisation.
    Ceci donne un isomorphisme concret plutôt qu'une simple instance `IsIso`.
    Utilise `isoSheafify` de Mathlib. -/
noncomputable def sheafify_iso_of_sheaf {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P : Cᵒᵖ ⥤ Type (max u v)}
    (hP : Presheaf.IsSheaf J P) :
    P ≅ sheafify J P :=
  isoSheafify J hP

/-!
## Naturalité : sheafify commute avec les morphismes de préfaisceaux

Étant donné un morphisme de préfaisceaux η : P ⟶ Q, le foncteur de
faisceautisation induit un morphisme `sheafifyMap J η : sheafify P ⟶ sheafify Q`.

Ceci rend la faisceautisation fonctorielle : ce n'est pas seulement une
opération sur les objets mais un véritable foncteur.
-/

/-- Une application de préfaisceaux η induit une application entre les
    faisceautisations. C'est l'action fonctorielle de l'endofoncteur de
    faisceautisation. Utilise `sheafification_map` de Mathlib. -/
theorem sheafify_map_def {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (η : P ⟶ Q) :
    sheafifyMap J η = (sheafification J (Type (max u v))).map η :=
  have h : (sheafification J (Type (max u v))).map η = sheafifyMap J η :=
    @sheafification_map C _ J (Type (max u v)) _ _ _ _ η
  h.symm

/-!
## L'endofoncteur de faisceautisation sur les préfaisceaux

En composant le foncteur de faisceautisation avec le foncteur d'oubli,
on obtient un endofoncteur sur les préfaisceaux :
`sheafification J (Type (max u v))`. Il envoie chaque préfaisceau vers un
préfaisceau qui se trouve être un faisceau — le « aller-retour » :
préfaisceau → faisceau → préfaisceau.
-/

/-- `(sheafification J (Type (max u v))).obj P = sheafify J P` :
    l'endofoncteur de faisceautisation appliqué à un préfaisceau donne sa
    faisceautisation. Utilise `sheafification_obj` de Mathlib. -/
theorem sheafification_obj_eq {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    (sheafification J (Type (max u v))).obj P = sheafify J P :=
  @sheafification_obj C _ J (Type (max u v)) _ _ P

/-!
## L'unité est une transformation naturelle

L'application canonique `toSheafify` est naturelle dans le préfaisceau :
pour tout morphisme η : P ⟶ Q, le carré évident commute.
-/

/-- Naturalité de l'unité : `η ≫ toSheafify Q = toSheafify P ≫ sheafifyMap η`.
    Utilise `toSheafify_naturality` de Mathlib. -/
theorem toSheafify_natural {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (η : P ⟶ Q) :
    η ≫ toSheafify J Q = toSheafify J P ≫ sheafifyMap J η :=
  toSheafify_naturality J η

end Grothendieck