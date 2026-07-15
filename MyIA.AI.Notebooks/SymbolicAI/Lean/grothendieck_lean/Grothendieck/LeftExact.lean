/-
Hommage Grothendieck — Partie 14 : Exactitude à gauche de la faisceautisation
Alexandre Grothendieck (1928-2014).

Extension Phase 8 (#2159, Epic #1646).

La Partie 13 (Sheafification.lean) a introduit le foncteur de faisceautisation
et sa propriété universelle : `presheafToSheaf ⊣ sheafToPresheaf`.

Ce module enregistre les **propriétés d'exactitude** de la faisceautisation,
à la suite de `CategoryTheory.Sites.LeftExact` de Mathlib :

  - La faisceautisation préserve les limites finies (elle est exacte à gauche).
  - La construction plus préserve les limites finies.
  - Les catégories de faisceaux héritent des propriétés d'exactitude de la
    catégorie cible : elles sont finitairement extensives, adhésives et équilibrées.

Ce sont toutes des instances (résolution par classe de types), donc nos théorèmes
ponts les ré-exposent simplement dans l'espace de noms `Grothendieck` avec des
docstrings expliquant leur signification.

Note d'univers : comme la Partie 13 — `Type (max u v)` pour les préfaisceaux sur
`C : Type u` avec `[Category.{v} C]`, via `HasSheafify J (Type (max u v))`
de LeftExact.lean.

Epic #1646, Phase 8 (#2159). Tous les `sorry`s éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LeftExact

universe v u

namespace Grothendieck

open CategoryTheory
open CategoryTheory.Limits

/-!
## La construction plus préserve les limites finies

La « construction plus » `P ↦ P⁺` est la première étape de la faisceautisation.
L'appliquer deux fois donne la faisceautisation. Que `plusFunctor` préserve les
limites finies est le cœur technique de l'exactitude à gauche : cela signifie
que la construction respecte les produits, les égaliseurs et les pullbacks.

Pour les préfaisceaux à valeurs dans `Type (max u v)`, toutes les instances
requises (`HasFiniteLimits`, `PreservesFiniteLimits (forget)`, etc.) sont
fournies par la machinerie de théorie des types de Mathlib.
-/

/-- La construction plus `J.plusFunctor` préserve les limites finies
    pour les préfaisceaux à valeurs dans Type. C'est le résultat intermédiaire
    clé : la faisceautisation = plus ∘ plus, donc si plus préserve les limites
    finies, la faisceautisation aussi.
    Utilise `preserveFiniteLimits_plusFunctor` du LeftExact de Mathlib. -/
instance plus_preserves_finite_limits {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (J.plusFunctor (Type (max u v))) :=
  inferInstance

/-!
## presheafToSheaf préserve les limites finies

Le foncteur concret de faisceautisation `presheafToSheaf` (qui va des
préfaisceaux aux faisceaux, contrairement à `sheafification` qui est
l'endofoncteur sur les préfaisceaux) préserve lui aussi les limites finies.
-/

/-- Le foncteur concret de faisceautisation `presheafToSheaf` préserve
    les limites finies. C'est la version énoncée pour le foncteur atterrissant
    dans la catégorie des faisceaux (plutôt que l'endofoncteur sur les préfaisceaux).
    Utilise `presheafToSheaf_preservesFiniteLimits` de Mathlib. -/
instance presheaf_to_sheaf_left_exact {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    PreservesFiniteLimits (presheafToSheaf J (Type (max u v))) :=
  inferInstance

/-!
## Les catégories de faisceaux sont finitairement extensives

Une catégorie est **finitairement extensive** lorsque les pullbacks le long des
inclusions de coproduits existent et la structure de fibration est bien élevée.
Puisque la faisceautisation est une localisation exacte à gauche, la catégorie
des faisceaux hérite de l'extensivité finitaire de la catégorie cible.

Pour les faisceaux à valeurs dans `Type`, cela signifie que les coproduits finis
dans `Sheaf J` se comportent comme des unions disjointes avec des pullbacks
bien élevés.
-/

/-- La catégorie des faisceaux à valeurs dans Type sur un site est finitairement
    extensive. Cela découle de la localisation réflexe donnée par la faisceautisation.
    Utilise `SheafOfTypes.finitary_extensive` de Mathlib. -/
instance sheaf_finitary_extensive {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    FinitaryExtensive (Sheaf J (Type (max u v))) :=
  inferInstance

/-!
## Les catégories de faisceaux sont adhésives

Une catégorie est **adhésive** si elle a des pullbacks, des pushouts le long
de monomorphismes, et des colimites de van Kampen. Les catégories de faisceaux
sur un site héritent de l'adhésivité de la cible via la localisation réflexe.
-/

/-- La catégorie des faisceaux à valeurs dans Type sur un site est adhésive.
    Utilise `SheafOfTypes.adhesive` de Mathlib. -/
instance sheaf_adhesive {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    Adhesive (Sheaf J (Type (max u v))) :=
  inferInstance

/-!
## Les catégories de faisceaux sont équilibrées

Une catégorie est **équilibrée** si tout morphisme à la fois monique et épique
est déjà un isomorphisme. Pour les catégories de faisceaux de types, cela
signifie qu'un morphisme de faisceaux qui est injectif et surjectif sur les
sections est nécessairement un isomorphisme.
-/

/-- La catégorie des faisceaux à valeurs dans Type sur un site est équilibrée.
    Un morphisme à la fois monique et épique est un isomorphisme.
    Utilise `SheafOfTypes.balanced` de Mathlib. -/
instance sheaf_balanced {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    Balanced (Sheaf J (Type (max u v))) :=
  inferInstance

/-!
## Ponts vers les isomorphismes de faisceautisation

Ces 4 théorèmes-ponts complètent l'inventaire des instances de LeftExact en
exposant les isomorphismes canoniques de la **faisceautisation itérée** depuis
Mathlib `CategoryTheory.Sites.LeftExact`. Chaque énoncé est un re-export nu
(`:=`) de la déclaration Mathlib correspondante ; aucune tactique requise
(puisque le code source est byte-identique à `inferInstance` au namespace près).

### 1. `plusPlusSheafIsoPresheafToSheaf` — double-plus ≅ préfaisceau-vers-faisceau

Pour tout site (C, J) et catégorie D, le foncteur de faisceautisation itérée
`J.plusPlusSheaf D` (deux passages successifs par `sheafify`) est isomorphe au
foncteur de préfaisceau-vers-faisceau `presheafToSheaf J D`. C'est
l'**idempotence de la faisceautisation** : faisceautiser deux fois donne le
même résultat qu'une seule fois, à isomorphismes canoniques près.
-/

/-- Theoreme-pont : la faisceautisation double `plusPlusSheaf` est isomorphe au
    foncteur `presheafToSheaf` (canoniquement). Re-exporte
    `plusPlusSheafIsoPresheafToSheaf` de Mathlib sans modification,
    specialise a `D := Type (max u v)` pour beneficier des instances
    automatiques de la theorie des types (HasColimitsOfShape, ConcreteCategory,
    HasMultiequalizer). -/
noncomputable def plusPlusSheafIsoPresheafToSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    CategoryTheory.plusPlusSheaf J (Type (max u v)) ≅ presheafToSheaf J (Type (max u v)) :=
  CategoryTheory.plusPlusSheafIsoPresheafToSheaf J _

/-!
### 2. `plusPlusFunctorIsoSheafification` — double-plus ≅ faisceautisation

Reformulation du même phénomène au niveau du foncteur `sheafification J D` :
deux passes successives de la **construction explicite** `J.sheafification D`
donnent le même résultat que la **construction classique** `sheafification J D`,
à isomorphismes canoniques près. C'est le pendant de (1) au niveau du
`plus` interne.
-/

/-- Theoreme-pont : `J.plusPlusSheafification D` est isomorphe au foncteur
    `sheafification J D`. Re-exporte `plusPlusFunctorIsoSheafification` de
    Mathlib, specialise a `Type (max u v)`. -/
noncomputable def plusPlusFunctorIsoSheafification {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.sheafification (Type (max u v)) ≅ sheafification J (Type (max u v)) :=
  CategoryTheory.plusPlusFunctorIsoSheafification J _

/-!
### 3. `plusPlusIsoSheafify` — foncteur induit sur les préfaisceaux

L'**isomorphisme au niveau des objets préfaisceau** : pour tout préfaisceau P
sur (C, J), le préfaisceau `J.sheafify P` (passage par `plus` du préfaisceau
puis faisceautisation explicite) est canoniquement isomorphe au faisceau
`sheafify J P`. C'est l'instance naturelle de (1) et (2) sur les objets.
-/

/-- Theoreme-pont : pour tout prefaisceau P, `J.sheafify P ≅ sheafify J P`.
    Re-exporte `plusPlusIsoSheafify` de Mathlib, specialise a
    `Type (max u v)`. -/
noncomputable def plusPlusIsoSheafify {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    J.sheafify P ≅ sheafify J P :=
  CategoryTheory.plusPlusIsoSheafify J _ P

/-!
### 4. `toSheafify_plusPlusIsoSheafify_hom` — naturalité du morphisme unité

**Compatibilité** entre l'isomorphisme (3) et le morphisme canonique
`toSheafify` (cf. `Sheafification.lean`, théoréme `toSheafify_is_unit`) :
le carré formé par `J.toSheafify P` et `toSheafify J P ≫ (plusPlusIsoSheafify J (Type _) P).hom`
commute identiquement. C'est la **cohérence des deux routes** vers
`sheafify J P` (directe vs via `J.sheafify`).
-/

/-- Theoreme-pont : compatibilité naturelle entre `toSheafify` et l'isomorphisme
    `plusPlusIsoSheafify.hom`. Re-exporte `toSheafify_plusPlusIsoSheafify_hom`
    de Mathlib, specialise a `Type (max u v)`. -/
theorem toSheafify_plusPlusIsoSheafify_hom {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    J.toSheafify P ≫ (plusPlusIsoSheafify J P).hom = toSheafify J P :=
  CategoryTheory.toSheafify_plusPlusIsoSheafify_hom J _ P

end Grothendieck
