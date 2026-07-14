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

end Grothendieck
