/-
Grothendieck tribute — Part 2: Schemes
Alexandre Grothendieck (1928-2014).

Grothendieck's most transformative idea: replace varieties by *schemes* — locally
ringed spaces that are locally affine (isomorphic to Spec R for a commutative ring R).
This gives a single framework for arithmetic and geometry.

Mathlib 4 formalizes schemes as `AlgebraicGeometry.Scheme`, extending
`LocallyRingedSpace` with the local-affineness condition.

Epic #1646. All `sorry`s eliminated at creation.
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
## The type of schemes

`Scheme` is the type of schemes. It carries a category structure.
Every scheme has an underlying locally ringed space, topological space, and
presheaf of commutative rings.
-/

-- The type of schemes
#check @AlgebraicGeometry.Scheme

-- The forgetful functor from schemes to topological spaces
#check @Scheme.forgetToTop

/-!
## Spec: from rings to spaces

The Spec construction turns a commutative ring into an affine scheme.
It is the left adjoint to the global sections functor Γ.
-/

/-- Spec is a functor from CommRingCatᵒᵖ to Scheme.
    Marked `noncomputable` because `Scheme.Spec` is noncomputable. -/
noncomputable example : CommRingCatᵒᵖ ⥤ Scheme := Scheme.Spec

/-!
## Basic properties

Schemes have an order structure from specialization, and morphisms
between schemes respect the sheaf structure.
-/

/-- An isomorphism of schemes induces a homeomorphism of underlying spaces.
    Note: `Scheme.homeoOfIso` returns `X ≃ₜ Y` (carriers). -/
noncomputable example {X Y : Scheme} (i : X ≅ Y) : X ≃ₜ Y :=
  Scheme.homeoOfIso i

-- The forgetful functor from schemes to locally ringed spaces (fully faithful)
#check @Scheme.forgetToLocallyRingedSpace

-- The FullyFaithful type for the forgetful functor
#check Scheme.forgetToLocallyRingedSpace.FullyFaithful

/-!
## The big picture: from rings to spaces and back

The Spec-Γ adjunction is the heart of algebraic geometry:
  - Spec : CommRingCatᵒᵖ → Scheme  (ring to space)
  - Γ     : Schemeᵒᵖ → CommRingCat  (space to ring, global sections)

For affine schemes, these are inverse equivalences.
-/

/-- Every scheme has global sections (the ring Γ(X)).
    Note: `Scheme.Γ` has domain `Schemeᵒᵖ`. -/
example (X : Scheme) : CommRingCat :=
  Scheme.Γ.obj (Opposite.op X)

end Grothendieck
