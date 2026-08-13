/-
Hommage à Grothendieck — Partie 2 : Schémas
Alexandre Grothendieck (1928-2014).

L'idée la plus transformatrice de Grothendieck : remplacer les variétés par
des *schémas* — des espaces localement annelés qui sont localement affines
(isomorphes à Spec R pour un anneau commutatif R). Cela fournit un cadre
unifié pour l'arithmétique et la géométrie.

Mathlib 4 formalise les schémas comme `AlgebraicGeometry.Scheme`, étendant
`LocallyRingedSpace` avec la condition d'affinité locale.

Epic #1646. Toutes les `sorry` éliminées à la création.

Sub-grain Phase 2+ (#2159, Epic #1646) — c.8267+3 : ajout de 6 ponts Mathlib
réutilisables à la place des `example` énoncés pédagogiques. Permet de citer
les lemmes canoniques depuis le namespace `Grothendieck` (homogénéité avec
les autres modules : `SitePoints`, `SheafBasics`, `MayerVietorisSquare`,
`Adjunction`, `Limits`, `KanExtensions`).
-/

/-
  `Grothendieck.SchemesTour` — Schémas (Partie 2)
  =================================================

  Hommage à Alexandre Grothendieck (1928-2014).

  L'idée la plus transformante de Grothendieck : remplacer les variétés
  par des *schémas* — des espaces annelés en anneaux locaux qui sont
  localement affines (isomorphes à Spec R pour un anneau commutatif R).
  Ce cadre unifie l'arithmétique et la géométrie.

  Mathlib 4 formalise les schémas comme `AlgebraicGeometry.Scheme`, qui
  étend `LocallyRingedSpace` par la condition d'affinité locale.

  Ce module parcourt :
    - Le type `Scheme` et sa structure de catégorie, avec ses foncteurs
      d'oubli vers les espaces topologiques et les espaces annelés en
      anneaux locaux.
    - La construction Spec, qui associe à chaque anneau commutatif un
      schéma affine ; Spec est l'adjoint à gauche du foncteur de sections
      globales Γ.
    - Les propriétés de base : un isomorphisme de schémas induit un
      homéomorphisme des espaces sous-jacents.
    - L'adjonction Spec Γ, cœur de la géométrie algébrique : pour les
      schémas affines, Spec et Γ sont des équivalences inverses.

  Epic #1646. Tous les `sorry`s éliminés à la création.

### i18n — convention #4980 ratifiée 2026-07-04

Module jumelé avec sa version anglaise canonique dans le fichier sibling
`SchemesTour_en.lean` (modèle sibling pair, voir PR #6154 sur `Utility.lean`).
Seules les **docstrings `/-- ... -/`** et **commentaires `-- ...`** diffèrent ;
les énoncés de théorèmes, les noms de lemmes, les tactiques Lean et les
références Mathlib restent en anglais (Mathlib 4, tactic DSL standard).
Anti-§D byte-identity garanti : signatures et corps byte-identiques entre
`SchemesTour.lean` et `SchemesTour_en.lean`.

Sub-grain Phase 2+ (#2159, Epic #1646) — c.8267+3 : 6 ponts Mathlib
réutilisables dans le namespace `Grothendieck` (homogénéité avec les autres
modules Grothendieck : `SitePoints`, `SheafBasics`, `MayerVietorisSquare`,
`Adjunction`, `Limits`, `KanExtensions`). Remplace les `example` énoncés
pédagogiques par des bridges canoniques.
-/

import Mathlib.AlgebraicGeometry.Scheme

namespace Grothendieck

open AlgebraicGeometry CategoryTheory

/-!
## Le type des schémas

`Scheme` est le type des schémas. Il porte une structure de catégorie.
Chaque schéma a un espace localement annelé sous-jacent, un espace
topologique, et un préfaisceau d'anneaux commutatifs.
-/

-- The type of schemes
#check @AlgebraicGeometry.Scheme

-- The forgetful functor from schemes to topological spaces
#check @Scheme.forgetToTop

/-!
## Spec : des anneaux aux espaces

La construction Spec transforme un anneau commutatif en un schéma affine.
C'est l'adjoint à gauche du foncteur sections globales Γ.
-/

/-- Spec est un foncteur de CommRingCatᵒᵖ vers Scheme.
    Marqué `noncomputable` car `Scheme.Spec` est noncomputable. -/
noncomputable example : CommRingCatᵒᵖ ⥤ Scheme := Scheme.Spec

/-!
## Propriétés de base

Les schémas ont une structure d'ordre issue de la spécialisation, et les
morphismes entre schémas respectent la structure de faisceau.
-/

/-- Un isomorphisme de schémas induit un homéomorphisme des espaces sous-jacents.
    Note : `Scheme.homeoOfIso` retourne `X ≃ₜ Y` (supports). -/
noncomputable example {X Y : Scheme} (i : X ≅ Y) : X ≃ₜ Y :=
  Scheme.homeoOfIso i

-- The forgetful functor from schemes to locally ringed spaces (fully faithful)
#check @Scheme.forgetToLocallyRingedSpace

-- The FullyFaithful type for the forgetful functor
#check Scheme.forgetToLocallyRingedSpace.FullyFaithful

/-!
## La vue d'ensemble : des anneaux aux espaces et retour

L'adjonction Spec-Γ est le cœur de la géométrie algébrique :
  - Spec : CommRingCatᵒᵖ → Scheme  (anneau vers espace)
  - Γ     : Schemeᵒᵖ → CommRingCat  (espace vers anneau, sections globales)

Pour les schémas affines, ce sont des équivalences inverses.
-/

/-- Chaque schéma a des sections globales (l'anneau Γ(X)).
    Note : `Scheme.Γ` a pour domaine `Schemeᵒᵖ`. -/
example (X : Scheme) : CommRingCat :=
  Scheme.Γ.obj (Opposite.op X)

/-!
## Ponts Mathlib canoniques

Les ponts suivants ré-exposent depuis le namespace `Grothendieck` des lemmes
Mathlib 4 (`Mathlib.AlgebraicGeometry.Scheme`, `Mathlib.AlgebraicGeometry.Spec`).
Ils servent deux objectifs :

  1. **Référence pédagogique** : un apprenant qui lit le namespace
     `Grothendieck` trouve les énoncés canoniques des schémas, sans avoir
     à naviguer dans la hiérarchie `Mathlib.AlgebraicGeometry.*`.
  2. **Réutilisation in-module** : les modules frères (`Subcanonical`,
     `ZariskiSite`, `Calibration`, `MathlibMap`) peuvent citer ces ponts
     au lieu de répéter la qualification `AlgebraicGeometry.Scheme.*`.

Les corps sont triviaux (lemmes `@[simp]` ou `rfl` dans Mathlib) — c'est la
valeur de **référencement**, pas de calcul.
-/

/-- **Continuité d'un morphisme de schémas.** Un morphisme de schémas
    `f : X ⟶ Y` est continu (entre les espaces topologiques sous-jacents) :
    `f : X ⟶ Y` ⇒ `Continuous f` — c'est la définition même d'un morphisme
    de schémas vu comme application continue entre les `TopCat` sous-jacents. -/
theorem scheme_hom_continuous {X Y : Scheme} (f : X ⟶ Y) : Continuous f :=
  Scheme.Hom.continuous f

/-- **Symétrie du homéomorphisme induit.** Si `e : X ≅ Y` est un isomorphisme
    de schémas, alors l'inverse du homéomorphisme `homeoOfIso e : X ≃ₜ Y`
    coïncide avec le homéomorphisme construit à partir de `e.symm`. C'est
    la cohérence symmétrique canonique de `Scheme.homeoOfIso`. -/
theorem scheme_homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) :
    (Scheme.homeoOfIso e).symm = Scheme.homeoOfIso e.symm :=
  Scheme.homeoOfIso_symm e

/-- **Coefficient du symm de homéomorphisme.** Appliquer le homéomorphisme
    construit depuis `e.symm` à un point `x` redonne `e.inv x`, c'est-à-dire
    l'image par le foncteur d'oubli vers `TopCat` de l'inverse de
    l'isomorphisme `e`. -/
theorem scheme_coe_homeoOfIso_symm {X Y : Scheme} (e : X ≅ Y) :
    ⇑(Scheme.homeoOfIso e.symm) = e.inv :=
  Scheme.coe_homeoOfIso_symm e

/-- **Composition des foncteurs d'oubli.** L'oubli `Scheme → TopCat` suivi
    de l'oubli `TopCat → Type` coïncide avec l'oubli direct `Scheme → Type`
    défini comme `Scheme.forget`. C'est la cohérence des deux chemins
    d'oubli vers `Type u`. -/
theorem scheme_forgetToTop_comp_forget :
    Scheme.forgetToTop ⋙ CategoryTheory.forget TopCat = Scheme.forget :=
  Scheme.forgetToTop_comp_forget

/-- **Compatibilité de l'image réciproque avec la composition.** L'image
    réciproque d'un ouvert `U` par un morphisme composé `f ≫ g`
    coïncide avec l'image réciproque de l'image réciproque :
    `(f ≫ g)⁻¹ᵁ U = f⁻¹ᵁ (g⁻¹ᵁ U)`. -/
theorem scheme_comp_preimage {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ (g ⁻¹ᵁ U) :=
  Scheme.Hom.comp_preimage f g U

/-- **Identité du foncteur Spec sur les objets.** Le morphisme de schémas
    `Spec.topMap (𝟙 R)` coïncide avec l'identité sur `Spec R` — c'est la
    loi d'identité du foncteur Spec (dans sa composante `Spec.toTop`,
    `CommRingCatᵒᵖ → TopCat`). -/
theorem spec_topMap_id (R : CommRingCat) :
    Spec.topMap (𝟙 R) = 𝟙 (Spec.topObj R) :=
  Spec.topMap_id R

end Grothendieck
