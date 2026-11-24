/-
Hommage à Grothendieck — Partie 10 : Topologie canonique et sites sous-canoniques
Alexandre Grothendieck (1928-2014).

Phase 6 extension (#2159, EPIC #1646).

Les Parties 1-4 ont établi les fondamentaux : catégories, tamis,
topologies, opérations de treillis, identités de pullback, bases
faisceaux, et clôture par recouvrement. Les Parties 5-8 ont construit
par-dessus avec calibration, lois de treillis, propriétés de faisceau,
ordre sur les topologies, et génération de recouvrement.

Ce module étudie la **topologie canonique** : la topologie de
Grothendieck la plus fine pour laquelle tout préfaisceau représentable
(`yoneda.obj X`) est un faisceau.

  - La topologie canonique fait de tous les représentables des faisceaux.
  - Une topologie est **sous-canonique** ssi elle est plus grossière
    ou égale à la topologie canonique.
  - La sous-canonicité est close vers le bas : J ≤ K et K sous-canonique
    ⟹ J sous-canonique.
  - Dans une topologie sous-canonique, tout préfaisceau représentable
    est un faisceau.
  - La topologie triviale ⊥ est sous-canonique.

La topologie canonique est le point de référence naturel : la topologie
de Zariski sur les schémas est sous-canonique (cf ZariskiSite.lean).

EPIC #1646, Phase 6 (#2159). Tous les `sorry` éliminés à la création.

JUMELAGE i18n (EPIC #4980) : ce fichier est la version canonique FR.
Son miroir anglais est `Grothendieck/CanonicalProps_en.lean` (namespace
suffixé `Grothendieck_en` pour éviter toute collision). Les deux
fichiers partagent le même corps de code (imports, namespace,
théorèmes, preuves) octet pour octet — seuls le docstring de
fichier (`/- ... -/`) et les docstrings de section (`/-! ... -/`)
diffèrent. Vérifié par `scripts/lean/check_i18n_siblings.py` (statut : OK).
-/
import Mathlib.CategoryTheory.Sites.Canonical

namespace Grothendieck

open CategoryTheory

/-!
## La topologie canonique

La topologie canonique sur une catégorie C est la topologie de
Grothendieck la plus fine pour laquelle tout préfaisceau représentable
`yoneda.obj X` est un faisceau. Elle est définie comme
`Sheaf.finestTopology` appliquée à l'ensemble des représentables.

Fait clé : une topologie est sous-canonique (tous les représentables
sont des faisceaux) si et seulement si elle est plus grossière ou
égale à la topologie canonique.
-/

/-- Le préfaisceau de Yoneda en X est un faisceau pour la topologie
    canonique. C'est la propriété définitoire de la topologie canonique.
    Utilise `Sheaf.isSheaf_yoneda_obj`. -/
theorem yoneda_isSheaf_canonical {C : Type*} [Category C] (X : C) :
    Presieve.IsSheaf (Sheaf.canonicalTopology C) (yoneda.obj X) :=
  Sheaf.isSheaf_yoneda_obj X

/-- Tout préfaisceau représentable est un faisceau pour la topologie
    canonique. Généralise `yoneda_isSheaf_canonical` à tout préfaisceau
    qui a une représentation, pas seulement `yoneda.obj X`.
    Utilise `Sheaf.isSheaf_of_isRepresentable`. -/
theorem isSheaf_repr_canonical {C : Type*} [Category C]
    (P : Cᵒᵖ ⥤ Type*) [P.IsRepresentable] :
    Presieve.IsSheaf (Sheaf.canonicalTopology C) P :=
  Sheaf.isSheaf_of_isRepresentable P

/-!
## Topologies sous-canoniques

Une topologie J est *sous-canonique* si tout préfaisceau représentable
est un J-faisceau. Équivalent à J ≤ la topologie canonique. La classe
`Subcanonical J` encapsule cette relation d'ordre. La topologie
canonique elle-même est sous-canonique.

La sous-canonicité est la propriété qui fait que le plongement de Yoneda
atterrit dans les faisceaux : C → SheafOfTypes J. C'est crucial pour les
schémas (Zariski est sous-canonique).
-/

/-- Une topologie sous-canonique J est plus grossière ou égale à la
    topologie canonique. Accède au champ `le_canonical` de la classe
    `Subcanonical`. -/
theorem subcanonical_le {C : Type*} [Category C]
    {J : GrothendieckTopology C} [hJ : J.Subcanonical] :
    (J : GrothendieckTopology C) ≤ Sheaf.canonicalTopology C :=
  hJ.le_canonical

/-- Si tout préfaisceau représentable est un faisceau pour J, alors J
    est sous-canonique. C'est la *converse* de `subcanonical_le` : pour
    prouver la sous-canonicité, il suffit de vérifier la condition de
    faisceau sur tous les `yoneda.obj X`.
    Utilise `GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`. -/
theorem subcanonical_of_yoneda_sheaf {C : Type*} [Category C]
    (J : GrothendieckTopology C)
    (h : ∀ X : C, Presieve.IsSheaf J (yoneda.obj X)) :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj J h

/-- La sous-canonicité est close vers le bas : J ≤ K et K sous-canonique
    ⟹ J sous-canonique. Une topologie plus grossière a moins de tamis
    couvrants, donc la condition de faisceau est plus facile à satisfaire.
    Utilise `GrothendieckTopology.Subcanonical.of_le`. -/
theorem subcanonical_of_le {C : Type*} [Category C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le h

/-- Dans une topologie sous-canonique, tout préfaisceau représentable est
    un faisceau. C'est la conséquence clé de la sous-canonicité : les
    représentables détectent la condition de faisceau. Utilise
    `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`. -/
theorem isSheaf_repr_subcanonical {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.Subcanonical]
    (P : Cᵒᵖ ⥤ Type*) [P.IsRepresentable] :
    Presieve.IsSheaf J P :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

/-!
## La topologie canonique est sous-canonique

La topologie canonique est sous-canonique par définition : c'est la
topologie sous-canonique la plus fine. Toute topologie plus grossière
qu'elle est également sous-canonique.
-/

/-- La topologie canonique elle-même est sous-canonique.
    C'est une instance, résolue par inférence de classes de types. -/
theorem canonical_is_subcanonical {C : Type*} [Category C] :
    (Sheaf.canonicalTopology C).Subcanonical :=
  inferInstance

/-!
## Tout préfaisceau est un faisceau pour la topologie triviale

La topologie triviale (bottom) ⊥ n'a que le tamis maximal comme
recouvrement. Tout préfaisceau satisfait trivialement la condition
de faisceau pour le tamis maximal. Ceci est aussi couvert dans
Calibration.lean et SheafBasics.lean, inclus ici par complétude dans
le contexte canonique.
-/

/-- Tout préfaisceau à valeurs dans Type est un faisceau pour la topologie
    triviale (bottom). Utilise `Presieve.isSheaf_bot`. -/
theorem isSheaf_bot_all {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot

end Grothendieck