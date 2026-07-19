/-
Grothendieck Partie 25 — Foncteurs adjoints

Alexandre Grothendieck (1928-2014).

Extension Phase 2+ (#2159, Epic #1646).

Les foncteurs adjoints sont, avec le lemme de Yoneda, l'outil catégorique le
plus universel de la géométrie algébrique grothendieckienne. Grothendieck les
utilise partout : l'adjonction Spec ⊣ Γ (géométrie ↔ algèbre), l'adjonction
faisceautisation ⊣ inclusion (préfaisceaux ↔ faisceaux), l'adjonction fibre ⊣
faisceau gratte-ciel (points ↔ faisceaux), et les foncteurs dérivés adjoints
de la cohomologie.

Une adjonction L ⊣ R entre deux catégories est une équivalence naturelle
`Hom_D(L X, Y) ≃ Hom_C(X, R Y)`. Elle équilibre deux points de vue
duaux : « résoudre à gauche » (L construit les objets libres) et
« oublier à droite » (R ramène dans la catégorie de base). Toute construction
universelle (limites, colimites, objets libres) s'exprime comme une adjonction.

Mathlib 4 formalise toute cette infrastructure dans `Mathlib.CategoryTheory.Adjunction` :
  - `CategoryTheory.Adjunction : C ⥤ D → Type*` — la structure d'adjonction L ⊣ R
  - `CategoryTheory.Adjunction.homEquiv` — l'équivalence Hom naturelle
  - `CategoryTheory.Adjunction.unit` / `counit` — les transformations naturelles
  - `CategoryTheory.Adjunction.left_triangle` / `right_triangle` — identités triangulaires
  - `CategoryTheory.IsLeftAdjoint` — propriété d'avoir un adjoint à droite
  - `CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit` — pleine fidélité via l'unité

Ce module ré-expose ces faits comme un parcours pédagogique organisé, pour
des apprenants découvrant les adjonctions pour la première fois.

Epic #1646, See #2159. Tous les `sorry` éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Ce module est jumelé avec sa version anglaise canonique dans le fichier
sibling `Adjunction_en.lean`. Les énoncés de théorèmes, les noms de lemmes,
les tactiques Lean et les références Mathlib restent en anglais. Seules les
**docstrings `/-- ... -/`** et les **commentaires `-- ...`** diffèrent entre
les deux fichiers. Anti-§D byte-identity garanti.
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

universe v₁ v₂ u₁ u₂

namespace Grothendieck.Adjunction

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-!
## 1. La structure d'adjonction

Une adjonction `L ⊣ R` entre un foncteur `L : C ⥤ D` (adjoint à gauche) et
`R : D ⥤ C` (adjoint à droite) est l'équivalence naturelle en les deux
variables : `Hom_D(L X, Y) ≃ Hom_C(X, R Y)`.
-/

-- La structure d'adjonction L ⊣ R entre deux foncteurs.
#check @CategoryTheory.Adjunction

-- L'équivalence Hom naturelle Hom_D(L X, Y) ≃ Hom_C(X, R Y).
#check @CategoryTheory.Adjunction.homEquiv

-- La notation `L ⊣ R` dénote `Adjunction L R` (L adjoint à gauche de R).
#check @CategoryTheory.Adjunction

/-!
## 2. L'unité et la coïnité, identités triangulaires

Toute adjonction `L ⊣ R` détermine l'unité `η : 𝟭 C ⟶ R ⋙ L` et la coïnité
`ε : L ⋙ R ⟶ 𝟭 D`, satisfaisant les identités triangulaires. Les composantes
en un objet s'obtiennent par `h.unit.app X` et `h.counit.app Y` (application
d'une transformation naturelle).
-/

-- L'unité η : 𝟭 C ⟶ R ⋙ L de l'adjonction.
#check @CategoryTheory.Adjunction.unit

-- La coïnité ε : L ⋙ R ⟶ 𝟭 D de l'adjonction.
#check @CategoryTheory.Adjunction.counit

-- Première identité triangulaire (coïnité après L de l'unité = identité).
#check @CategoryTheory.Adjunction.left_triangle

-- Seconde identité triangulaire (unité après R de la coïnité = identité).
#check @CategoryTheory.Adjunction.right_triangle

/-!
## 3. Existence d'un adjoint

Un foncteur qui a un adjoint à droite est un « adjoint à gauche »
(`CategoryTheory.Functor.IsLeftAdjoint`). C'est une classe de proposition :
elle enregistre l'existence d'un `R` avec `L ⊣ R`.
-/

-- La propriété pour un foncteur d'être adjoint à gauche (avoir un R avec L ⊣ R).
#check @CategoryTheory.Functor.IsLeftAdjoint

/-!
## 4. Conservation des limites et colimites

Théorème pratique : un adjoint à droite préserve les limites, un adjoint à
gauche préserve les colimites.
-/

-- Un adjoint à droite préserve les limites.
#check @CategoryTheory.Adjunction.rightAdjoint_preservesLimits

-- Un adjoint à gauche préserve les colimites.
#check @CategoryTheory.Adjunction.leftAdjoint_preservesColimits

/-!
## 5. Pleine fidélité d'un adjoint

L'unité est un isomorphisme naturel ssi l'adjoint à gauche est pleinement
fidèle ; symétriquement pour la coïnité et l'adjoint à droite.
-/

-- L'adjoint à gauche est pleinement fidèle si l'unité est un isomorphisme.
#check @CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit

-- L'adjoint à droite est pleinement fidèle si la coïnité est un isomorphisme.
#check @CategoryTheory.Adjunction.fullyFaithfulROfIsIsoCounit

/-!
## 6. Théorèmes ponts

Reformulations dans l'espace de noms du projet, pontant les faits Mathlib.
-/

/-- Pont : l'hom-équivalence d'une adjonction L ⊣ R, vue comme famille
    naturelle en X et Y. C'est la donnée qui fait d'une adjonction une
    bijection naturelle, pas juste ponctuelle. -/
def homEquiv_family {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    (X : C) → (Y : D) → (L.obj X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  fun X Y ↦ h.homEquiv X Y

/-- Pont : un adjoint à gauche préserve les colimites. Fait structurel le plus
    utilisé en géométrie algébrique pour transporter les colimites le long des
    foncteurs « libres » (faisceautisation, tensorisation, image inverse). -/
theorem leftAdjoint_preserves_colimits {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    PreservesColimitsOfSize L :=
  h.leftAdjoint_preservesColimits

/-- Pont : un adjoint à droite préserve les limites. -/
theorem rightAdjoint_preserves_limits {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    PreservesLimitsOfSize R :=
  h.rightAdjoint_preservesLimits

/-- Pont : dans une adjonction L ⊣ R, si l'unité est un isomorphisme naturel
    alors l'adjoint à gauche L est pleinement fidèle (critère de réflexion
    pleine). -/
noncomputable def fully_faithful_of_unit_iso {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    [IsIso h.unit] : L.FullyFaithful :=
  h.fullyFaithfulLOfIsIsoUnit

/-- Pont : dans une adjonction L ⊣ R, si la coïnité est un isomorphisme naturel
    alors l'adjoint à droite R est pleinement fidèle. -/
noncomputable def fully_faithful_of_counit_iso {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    [IsIso h.counit] : R.FullyFaithful :=
  h.fullyFaithfulROfIsIsoCounit

end Grothendieck.Adjunction
