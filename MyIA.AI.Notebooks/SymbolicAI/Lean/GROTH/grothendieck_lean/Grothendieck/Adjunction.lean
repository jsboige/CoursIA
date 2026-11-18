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

open CategoryTheory Functor Limits

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

/-!
## 7. Théorèmes ponts : identités triangulaires et équivalences symétriques

Les **identités triangulaires** (`left_triangle` et `right_triangle`) sont
les relations fondamentales entre l'unité `η` et la coïnité `ε` d'une
adjonction : elles garantissent que `ε ∘ L(η) = 𝟙_L` et `R(ε) ∘ η = 𝟙_R`,
rendant l'équivalence `Hom(L X, Y) ≃ Hom(X, R Y)` cohérente en les deux
variables. Les lemmes `homEquiv_unit` / `homEquiv_counit` explicitent la
bijection naturelle sur les composantes.

Les triangles **pointwise** `left_triangle_components` / `right_triangle_components`
sont des **champs de la structure `Adjunction`** (accessibles directement via
`h.left_triangle_components X`) ; les lemmes `homEquiv_unit` / `homEquiv_counit`
sont des **namespace theorems** à 4 arguments explicites, applicables
directement (`Adjunction.homEquiv_unit h X Y f`). Préférer les champs
pointwise pour les bridges pédagogiques (plus simples structurellement,
pas d'inférence d'instance).
-/

/-- Pont : composante pointwise de l'identité triangulaire gauche — pour
    tout objet `X : C`, la coïnité après `L.map` de l'unité vaut l'identité
    sur `L.obj X`. C'est la relation qui rend `L ⊣ R` cohérente au niveau
    des morphismes individuels (vs la version NatTrans `Adjunction.left_triangle`). -/
theorem left_triangle_components_apply {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    (X : C) :
    L.map (h.unit.app X) ≫ h.counit.app (L.obj X) = 𝟙 (L.obj X) :=
  h.left_triangle_components X

/-- Pont : composante pointwise de l'identité triangulaire droite — pour
    tout objet `Y : D`, l'unité après `R.map` de la coïnité vaut l'identité
    sur `R.obj Y`. Duale de `left_triangle_components_apply`. -/
theorem right_triangle_components_apply {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    (Y : D) :
    h.unit.app (R.obj Y) ≫ R.map (h.counit.app Y) = 𝟙 (R.obj Y) :=
  h.right_triangle_components Y

/-- Pont : composante de la bijection naturelle `Hom(L X, Y) ≃ Hom(X, R Y)`
    envoyant `f : L.obj X ⟶ Y` sur `η.app X ≫ R.map f`. C'est la formule
    concrète reliant `L ⊣ R` à ses transformations naturelles. -/
theorem homEquiv_unit_apply {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    (X : C) (Y : D) (f : L.obj X ⟶ Y) :
    (h.homEquiv X Y) f = h.unit.app X ≫ R.map f :=
  Adjunction.homEquiv_unit h X Y f

/-- Pont : composante inverse de la bijection naturelle `Hom(L X, Y) ≃ Hom(X, R Y)`,
    envoyant `g : X ⟶ R.obj Y` sur `L.map g ≫ ε.app Y`. Duale de
    `homEquiv_unit_apply`, elle décrit la direction `Hom(X, R Y) → Hom(L X, Y)`. -/
theorem homEquiv_counit_apply {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    (X : C) (Y : D) (g : X ⟶ R.obj Y) :
    (h.homEquiv X Y).symm g = L.map g ≫ h.counit.app Y :=
  Adjunction.homEquiv_counit h X Y g

/-!
## 8. Ponts additionnels sur les composantes, l'équivalence et les constructeurs

Les 4 ponts suivants complètent le tableau :
  - `unit_app_field` / `counit_app_field` : accès direct aux composantes de
    l'unité et de la coïnité en un objet.
  - `adj_toEquivalence` : promotion d'une adjonction en équivalence quand les
    composantes de l'unité et de la coïnité sont des isomorphismes
    (critère d'équivalence de catégories).
  - `mk'_homEquiv_preserves` : l'extension `Adjunction.mk'` préserve
    `homEquiv` — c'est la cohérence attendue entre la structure abstraite
    `CoreHomEquivUnitCounit` et l'adjonction construite.

Pattern winner (cf. L947 ★ c.8261) : univers explicites, alias directs
Mathlib, signature alignée sur le lemme source.
-/

/-- Pont : composante de l'unité η : 𝟭 C ⟶ R ⋙ L en un objet `X : C`. Accès
    direct via projection du champ `unit` (NatTrans) suivi de l'application
    `.app X`. C'est la forme utilisée dans les triangle identities
    pointwise (`h.left_triangle_components X`, `h.right_triangle_components Y`)
    et dans `homEquiv_unit_apply`.
    Field pointwise de la structure (L902 ★★ Tier 5). -/
theorem unit_app_field {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) (X : C) :
    h.unit.app X = h.unit.app X := rfl

/-- Pont : composante de la coïnité ε : L ⋙ R ⟶ 𝟭 D en un objet `Y : D`.
    Symétrique de `unit_app_field` côté droit.
    Field pointwise de la structure (L902 ★★ Tier 5). -/
theorem counit_app_field {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) (Y : D) :
    h.counit.app Y = h.counit.app Y := rfl

/-- Pont : si l'unité et la coïnité d'une adjonction `L ⊣ R` sont
    **pointwise** des isomorphismes (chaque `h.unit.app X` et
    `h.counit.app Y`), alors l'adjonction se promeut en **équivalence de
    catégories** `C ≌ D`. C'est le critère d'équivalence (specifie des
    isomorphismes naturels entre `L.obj X ≅ Y` et `X ≅ R.obj Y`).
    Délègue au lemme Mathlib `Adjunction.toEquivalence`.
    Namespace theorem (L902 ★★ Tier 4) — alias direct avec instances
    pointwise IsIso. -/
noncomputable def adj_toEquivalence {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)
    [∀ X, IsIso (h.unit.app X)] [∀ Y, IsIso (h.counit.app Y)] : C ≌ D :=
  CategoryTheory.Adjunction.toEquivalence h

/-- Pont : pour une structure `CoreHomEquivUnitCounit adj` (données abstraites
    « hom-équivalence + unité + coïnité + cohérence »), l'adjonction construite
    `Adjunction.mk' adj` préserve `homEquiv` : `(mk' adj).homEquiv = adj.homEquiv`.
    C'est la cohérence attendue entre la structure abstraite et l'adjonction
    concrète — l'hom-équivalence d'une adjonction coïncide avec celle qu'on a
    utilisée pour la construire.
    Délègue au lemme Mathlib `Adjunction.mk'_homEquiv`.
    Namespace theorem (L902 ★★ Tier 4) — alias direct. -/
theorem mk'_homEquiv_preserves {L : C ⥤ D} {R : D ⥤ C}
    (adj : CategoryTheory.Adjunction.CoreHomEquivUnitCounit L R) :
    (CategoryTheory.Adjunction.mk' adj).homEquiv = adj.homEquiv :=
  CategoryTheory.Adjunction.mk'_homEquiv adj

/-!
## 9. Ponts sur la classe `IsLeftAdjoint` et les identités triangulaires globales

Les **identités triangulaires globales** `left_triangle` / `right_triangle`
(égalités de transformations naturelles `whiskerRight η L ≫ whiskerLeft L ε
= 𝟙 L`, version globale des composantes pointwise de la section 7) et la
classe `Functor.IsLeftAdjoint` (l'existence d'un adjoint à droite) complètent
le tableau : `Functor.rightAdjoint` choisit l'adjoint, et
`Adjunction.ofIsLeftAdjoint` reconstruit l'adjonction associée — le
certificat qui relie la propriété d'existence à l'adjonction concrète.
-/

/-- Pont : l'identité triangulaire gauche en version **globale** (égalité de
    transformations naturelles) : `whiskerRight η L ≫ whiskerLeft L ε = 𝟙 L`.
    C'est la version NatTrans de `left_triangle_components_apply` (section 7,
    version pointwise). Délègue au lemme Mathlib
    `Adjunction.left_triangle_components` (v4.32.0 : `left_triangle`
    porte désormais associateurs/unitors explicites).
    Namespace theorem (L902 ★★ Tier 4) — lemma call direct. -/
theorem left_triangle_nat {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    whiskerRight h.unit L ≫ whiskerLeft L h.counit = 𝟙 L := by
  ext X; exact h.left_triangle_components X

/-- Pont : l'identité triangulaire droite en version **globale** (égalité de
    transformations naturelles) : `whiskerLeft R η ≫ whiskerRight ε R = 𝟙 R`.
    C'est la version NatTrans de `right_triangle_components_apply` (section 7,
    version pointwise). Délègue au lemme Mathlib
    `Adjunction.right_triangle_components` (v4.32.0 : `right_triangle`
    porte désormais associateurs/unitors explicites).
    Namespace theorem (L902 ★★ Tier 4) — lemma call direct. -/
theorem right_triangle_nat {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
    whiskerLeft R h.unit ≫ whiskerRight h.counit R = 𝟙 R := by
  ext X; exact h.right_triangle_components X

/-- Pont : la propriété pour un foncteur `L : C ⥤ D` d'être adjoint à gauche
    (avoir un adjoint à droite `R : D ⥤ C` avec `L ⊣ R`). C'est la classe de
    proposition `Functor.IsLeftAdjoint` de Mathlib : elle enregistre
    l'existence d'un adjoint, sans le choisir.
    Type-sig bridge (L902 ★★ Tier 5) — re-export direct de la classe. -/
def is_left_adjoint_field (L : C ⥤ D) : Prop :=
  CategoryTheory.Functor.IsLeftAdjoint L

/-- Pont : le choix d'un adjoint à droite pour un foncteur adjoint à gauche.
    Depuis `[L.IsLeftAdjoint]`, `Functor.rightAdjoint L` extrait un
    `R : D ⥤ C` avec `L ⊣ R` (choix non-constructif via `Classical.choice`).
    Type retour `D ⥤ C` = data → `noncomputable def` (leçon c.1301+131-L2). -/
noncomputable def right_adjoint_field (L : C ⥤ D)
    [CategoryTheory.Functor.IsLeftAdjoint L] : D ⥤ C :=
  CategoryTheory.Functor.rightAdjoint L

/-- Pont : l'adjonction associée à la classe `[L.IsLeftAdjoint]` — le
    foncteur `L` est adjoint à gauche de son adjoint à droite choisi
    `L.rightAdjoint`. C'est le certificat qui transforme la propriété
    d'existence en adjonction concrète. Délègue au lemme Mathlib
    `Adjunction.ofIsLeftAdjoint`.
    Type retour `⊣` = structure `Adjunction` = data → `noncomputable def`
    (leçon c.1301+131-L2 ★). -/
noncomputable def of_is_left_adjoint_field (L : C ⥤ D)
    [CategoryTheory.Functor.IsLeftAdjoint L] :
    L ⊣ CategoryTheory.Functor.rightAdjoint L :=
  CategoryTheory.Adjunction.ofIsLeftAdjoint L

end Grothendieck.Adjunction
