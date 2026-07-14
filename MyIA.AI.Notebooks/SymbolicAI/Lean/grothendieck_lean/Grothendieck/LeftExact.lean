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

end Grothendieck
