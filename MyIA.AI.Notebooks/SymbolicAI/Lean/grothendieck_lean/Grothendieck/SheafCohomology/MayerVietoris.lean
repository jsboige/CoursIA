/-
Grothendieck Part 22 -- Mayer-Vietoris long exact sequence in sheaf cohomology

Part 21 (MayerVietorisSquare.lean) introduced Mayer-Vietoris squares: the
geometric input (a pushout square in sheaves) and the associated short
exact complex of free abelian sheaves.

This module bridges the **Mayer-Vietoris long exact sequence** in sheaf
cohomology from Mathlib (`CategoryTheory.Sites.SheafCohomology.MayerVietoris`).

Given a Mayer-Vietoris square S for a site (C, J) and an abelian sheaf F,
there is a long exact sequence:

  ... ⟶ H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F) ⟶ H^{n+1}(X₄, F) ⟶ ...

where X₁ = intersection, X₂/X₃ = covering opens, X₄ = covered space.

Key constructions bridged from Mathlib:

  - `toBiprod` : sum of restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃)
  - `fromBiprod` : difference of restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁)
  - `toBiprod_fromBiprod` : composition is zero
  - `δ` : connecting homomorphism H^{n₀}(X₁) → H^{n₁}(X₄) (n₁ = n₀ + 1)
  - `sequence` : the full long exact sequence (ComposableArrows AddCommGrp 5)
  - `sequence_exact` : the sequence is exact
  - `δ_toBiprod` : δ >> toBiprod = 0
  - `fromBiprod_δ` : fromBiprod >> δ = 0

This completes the Mayer-Vietoris machinery: from a geometric covering
condition (Part 21) to the cohomological consequence (this part).

Epic #1646, See #2159. All `sorry`s eliminated at creation.
-/

/-
  Bloc miroir FR (convention i18n EPIC #4980, Option A inline)
  =============================================================

  Hommage a Grothendieck -- Partie 22 : suite exacte longue de Mayer-Vietoris
  en cohomologie des faisceaux.

  La Partie 21 (MayerVietorisSquare.lean) a introduit les carres de
  Mayer-Vietoris : l'entree geometrique (un carre pushout de faisceaux) et
  le complexe court exact de faisceaux abeliens libres associe.

  Ce module fait le pont avec la **suite exacte longue de Mayer-Vietoris**
  en cohomologie des faisceaux depuis Mathlib
  (CategoryTheory.Sites.SheafCohomology.MayerVietoris).

  Etant donne un carre de Mayer-Vietoris S pour un site (C, J) et un
  faisceau abelien F, il existe une suite exacte longue :

    ... -> H^n(X_4, F) -> H^n(X_2, F) (+) H^n(X_3, F) -> H^n(X_1, F) -> H^(n+1)(X_4, F) -> ...

  ou X_1 = intersection, X_2/X_3 = ouverts du recouvrement, X_4 = espace
  recouvert.

  Constructions cles recuperees de Mathlib :

    - toBiprod : somme des restrictions H^n(X_4) -> H^n(X_2) (+) H^n(X_3)
    - fromBiprod : difference des restrictions H^n(X_2) (+) H^n(X_3) -> H^n(X_1)
    - toBiprod_fromBiprod : la composition est nulle
    - delta : homomorphisme de connexion H^{n_0}(X_1) -> H^{n_1}(X_4) (n_1 = n_0 + 1)
    - sequence : la suite exacte longue complete (ComposableArrows AddCommGrp 5)
    - sequence_exact : la suite est exacte
    - delta_toBiprod : delta >> toBiprod = 0
    - fromBiprod_delta : fromBiprod >> delta = 0

  EPIC #1646. Tous les sorry elimines a la creation.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

universe w v u

namespace Grothendieck.SheafCohomology.MayerVietoris

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-! ## 1. Restriction maps in cohomology

Given a Mayer-Vietoris square S and an abelian sheaf F, the maps
between cohomology groups are induced by the restriction maps
in the square.

`toBiprod` is the sum of restrictions:
  H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F)
sending y to (f₂₄* y, f₃₄* y).

`fromBiprod` is the difference of restrictions:
  H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F)
sending (y₁, y₃) to f₁₂* y₁ - f₁₃* y₃.
-/

-- Sum of restrictions: H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod

-- Explicit formula for toBiprod.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_apply

-- Difference of restrictions: H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod

/-! ## 2. Composition and the zero condition

The composition toBiprod >> fromBiprod is zero:
  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁)
This is the cohomological shadow of the commutativity of the square.
-/

-- toBiprod >> fromBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_fromBiprod

-- Explicit formula for fromBiprod applied to a pair.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply

/-! ## 3. The connecting homomorphism

The connecting homomorphism δ : H^{n₀}(X₁, F) ⟶ H^{n₁}(X₄, F) (where
n₁ = n₀ + 1) is the key map in the long exact sequence. It measures
the obstruction to lifting a cohomology class from the intersection
to the covered space.

This is defined as `shortComplex_shortExact.extClass.precomp`.
-/

-- The connecting homomorphism δ : H^{n₀}(X₁) ⟶ H^{n₁}(X₄).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ

/-! ## 4. The long exact sequence

The Mayer-Vietoris long exact sequence is packaged as a
`ComposableArrows AddCommGrp 5`:

  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁) ⟶ H^{n+1}(X₄) ⟶ H^{n+1}(X₂) ⊞ H^{n+1}(X₃) ⟶ H^{n+1}(X₁)

This is `sequence S F n₀ n₁ h` where `h : n₀ + 1 = n₁`.
-/

-- The Mayer-Vietoris long exact sequence (6 terms, ComposableArrows 5).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence

/-! ## 5. Exactness

The long exact sequence is exact at every position. This is the main
theorem of the module, proven by comparison with the contravariant
sequence of Ext-groups.
-/

-- The Mayer-Vietoris sequence is exact.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact

/-! ## 6. Boundary conditions

The connecting homomorphism satisfies two boundary conditions:
  - δ >> toBiprod = 0  (δ lands in the kernel of toBiprod)
  - fromBiprod >> δ = 0  (δ factors through the cokernel of fromBiprod)
-/

-- δ >> toBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ_toBiprod

-- fromBiprod >> δ = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_δ

/-! ## 7. Bridge theorems

Bridge theorems connecting the Mayer-Vietoris long exact sequence
to concrete verification.
-/

/-- Bridge theorem: the Mayer-Vietoris sequence is exact. For a
    Mayer-Vietoris square S and abelian sheaf F, the sequence of
    cohomology groups is exact at every position. -/
theorem mv_sequence_exact
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (S.sequence F n₀ n₁ h).Exact :=
  S.sequence_exact F n₀ n₁ h

/-- Bridge theorem: the connecting homomorphism composed with the
    sum of restrictions is zero: δ >> toBiprod = 0. -/
theorem mv_delta_toBiprod_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0 :=
  S.δ_toBiprod F n₀ n₁ h

/-- Bridge theorem: the difference of restrictions composed with the
    connecting homomorphism is zero: fromBiprod >> δ = 0. -/
theorem mv_fromBiprod_delta_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0 :=
  S.fromBiprod_δ F n₀ n₁ h

end Grothendieck.SheafCohomology.MayerVietoris
