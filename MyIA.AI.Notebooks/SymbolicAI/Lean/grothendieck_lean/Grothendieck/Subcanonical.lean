/-
# Hommage Grothendieck — Partie 16 : Topologies de Grothendieck sous-canoniques

Copyright (c) 2026 CoursIA. All rights reserved.
Libéré sous licence Apache 2.0, voir fichier LICENSE.

## Topologies sous-canoniques (FR canonical)

Une topologie de Grothendieck J sur une catégorie C est dite **sous-canonique**
lorsque tout préfaisceau représentable y(X) = Hom(—, X) est déjà un J-faisceau. C'est le pont entre le plongement de Yoneda
et la catégorie des faisceaux : lorsque J est sous-canonique, le lemme de Yoneda
descend des préfaisceaux aux faisceaux, donnant l'équivalence  (y(X) → F) ≃ F(X)  pour tout faisceau F de types.

SGA 4 I 3.4 — la topologie canonique est la plus fine sous-canonique ; la topologie
triviale est toujours sous-canonique ; la topologie atomique est sous-canonique ssi les
images réciproques de familles couvrantes sont couvrantes.

### Note d'accessibilité (Epics #1452/#1453)

Ce module expose **5 theorem + 1 def** sur la **sous-canonicalité** (bridge Yoneda → faisceaux),
accessibilité progressive par 4 sections thématiques : (1) hypothèse sous-canonique et ordre,
(2) pont représentables = faisceaux, (3) construction d'un faisceau à partir d'un représentable, (4)
transfert le long de foncteurs pleinement fidèles.

### Convention i18n (EPIC #4980 ratifiée par user 2026-07-04, voir code-style.md Lean i18n)

Ce module substantiel est apparié avec son jumeau anglais dans le fichier sibling Subcanonical_en.lean
(modèle sibling pair, voir PR #6154 pour le pilote sur Utility.lean).
-/

import Mathlib.CategoryTheory.Sites.Subcanonical

universe w v u

namespace Grothendieck.Subcanonical

open CategoryTheory GrothendieckTopology Opposite Functor Sheaf

/-! ## 1. Hypothèse de sous-canonicalité et ordre

Une topologie est sous-canonique ssi elle est plus fine que la topologie canonique.
Équivalemment, tout préfaisceau représentable est un faisceau.
-/

/-- Si J ≤ K et K est sous-canonique, alors J est sous-canonique.
Les topologies plus fines ont moins de faisceaux ; les topologies plus grossières héritent
de la sous-canonicalité. -/
theorem subcanonical_of_le {C : Type u} [Category.{v} C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical := Subcanonical.of_le h

/-- Construction de la sous-canonicalité à partir de la condition de faisceau
sur les objets yoneda. -/
theorem subcanonical_of_yoneda_sheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    (h : ∀ X : C, Presieve.IsSheaf J (yoneda.obj X)) :
    J.Subcanonical := Subcanonical.of_isSheaf_yoneda_obj J h

/-! ## 2. Théorème pont : les préfaisceaux représentables sont des faisceaux

Quand J est sous-canonique, le plongement de Yoneda se factorise à travers la
catégorie des faisceaux. La faisceautification agit comme l'identité sur les représentables.
-/

/-- Pour une topologie sous-canonique, tout préfaisceau représentable est un J-faisceau
(au sens Presieve). -/
theorem isSheaf_presieve_of_subcanonical {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] (X : C) :
    Presieve.IsSheaf J (yoneda.obj X) :=
  Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)

/-- Pour une topologie sous-canonique, tout préfaisceau représentable est un J-faisceau
(au sens Presheaf). Cela utilise l'équivalence entre les deux notions
de faisceau pour les préfaisceaux à valeurs dans Type. -/
theorem isSheaf_presheaf_of_subcanonical {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] (X : C) :
    Presheaf.IsSheaf J (yoneda.obj X) :=
  (isSheaf_iff_isSheaf_of_type J (yoneda.obj X)).mpr
    (Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))

/-! ## 3. Construction d'un faisceau à partir d'un représentable (faisceau de Yoneda) -/

/-- Le plongement de Yoneda se factorise à travers la catégorie des faisceaux
quand J est sous-canonique : tout préfaisceau représentable est automatiquement
un faisceau. -/
noncomputable def yonedaSheaf {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] (X : C) :
    Sheaf J (Type v) :=
  ⟨yoneda.obj X, isSheaf_presheaf_of_subcanonical X⟩

/-! ## 4. Transfert de sous-canonicalité le long de foncteurs pleinement fidèles

Si un foncteur pleinement fidèle est continu (préserve les recouvrements) et que
la topologie cible est sous-canonique, alors la topologie source est sous-canonique.
-/

/-- Stabilité par image réciproque de la sous-canonicalité le long de foncteurs
pleinement fidèles continus. -/
theorem subcanonical_pullback {C : Type u} [Category.{v} C]
    {D : Type*} [Category.{v} D] (F : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.Full] [F.Faithful] [F.IsContinuous J K] [K.Subcanonical] :
    J.Subcanonical := subcanonical_of_full_of_faithful F J K

/-! ## 5. Bridges Mathlib canoniques (hommage Grothendieck)

Ponts vers les 4 constructeurs canoniques de `Mathlib/CategoryTheory/Sites/Canonical.lean`
qui étendent le namespace `Grothendieck` avec les opérateurs fondamentaux de la sous-canonicalité :
(5.1) instance Subcanonical sur la topologie canonique + extraction du champ `le_canonical`,
(5.2) les foncteurs `J.yoneda` / `J.uliftYoneda` qui relient la catégorie C à la catégorie
des J-faisceaux, et (5.3) le théorème `isSheaf_yoneda_obj` pour la topologie canonique. -/

/-! ### 5.1 Pont-instance : la topologie canonique est sous-canonique

La topologie canonique `canonicalTopology C` est la **plus fine** sous-canonique
(la borne supérieure des topologies sous-canoniques sur C). -/
instance subcanonical_canonical {C : Type u} [Category.{v} C] :
    (canonicalTopology C).Subcanonical :=
  inferInstance

/-- Pont-lemma : extraction du champ `le_canonical` d'une instance Subcanonical. -/
theorem subcanonical_le_canonical {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] :
    J ≤ canonicalTopology C :=
  Subcanonical.le_canonical

/-! ### 5.2 Pont-def : le foncteur de Yoneda vers la catégorie des J-faisceaux

Pour une topologie J sous-canonique, le plongement de Yoneda se factorise à
travers la catégorie des J-faisceaux : l'opérateur `J.yoneda` retourne
explicitement un foncteur `C ⥤ Sheaf J (Type v)`. -/
noncomputable def subcanonical_yoneda {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [h : Subcanonical J] :
    C ⥤ Sheaf J (Type v) :=
  J.yoneda

/-- Variante ulift du plongement de Yoneda vers la catégorie des J-faisceaux,
permettant une montée en univers vers `Sheaf J (Type (max v w))`. -/
noncomputable def subcanonical_uliftYoneda {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} [Subcanonical J] :
    C ⥤ Sheaf J (Type (max v w)) :=
  J.uliftYoneda

/-! ### 5.3 Pont-theorem : yoneda.obj est faisceau pour la topologie canonique

Pour la topologie canonique, tout objet `yoneda.obj X` est automatiquement un
faisceau (point clé : c'est la définition de `canonicalTopology C` comme
topologie engendrée par les représentables). -/
theorem isSheaf_yoneda_obj_canonical {C : Type u} [Category.{v} C] (X : C) :
    Presieve.IsSheaf (canonicalTopology C) (yoneda.obj X) :=
  isSheaf_yoneda_obj X

end Grothendieck.Subcanonical
