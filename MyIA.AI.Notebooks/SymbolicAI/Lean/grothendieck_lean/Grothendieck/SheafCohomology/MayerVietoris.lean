/-
Grothendieck Partie 22 — Suite exacte longue de Mayer-Vietoris en cohomologie des faisceaux

La Partie 21 (MayerVietorisSquare.lean) a introduit les carrés de
Mayer-Vietoris : l'entrée géométrique (un carré pushout de faisceaux) et
le complexe court exact de faisceaux abéliens libres associé.

Ce module fait le pont avec la **suite exacte longue de Mayer-Vietoris**
en cohomologie des faisceaux depuis Mathlib
(`CategoryTheory.Sites.SheafCohomology.MayerVietoris`).

Étant donné un carré de Mayer-Vietoris S pour un site (C, J) et un
faisceau abélien F, il existe une suite exacte longue :

  ... ⟶ H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F) ⟶ H^{n+1}(X₄, F) ⟶ ...

où X₁ = intersection, X₂/X₃ = ouverts du recouvrement, X₄ = espace
recouvert.

Constructions clés récupérées de Mathlib :

  - `toBiprod` : somme des restrictions H^n(X₄) → H^n(X₂) ⊞ H^n(X₃)
  - `fromBiprod` : différence des restrictions H^n(X₂) ⊞ H^n(X₃) → H^n(X₁)
  - `toBiprod_fromBiprod` : la composition est nulle
  - `δ` : homomorphisme de connexion H^{n₀}(X₁) → H^{n₁}(X₄) (n₁ = n₀ + 1)
  - `sequence` : la suite exacte longue complète (ComposableArrows AddCommGrp 5)
  - `sequence_exact` : la suite est exacte
  - `δ_toBiprod` : δ >> toBiprod = 0
  - `fromBiprod_δ` : fromBiprod >> δ = 0

Ceci complète la machinerie de Mayer-Vietoris : de la condition
géométrique de recouvrement (Partie 21) à la conséquence cohomologique
(cette partie).

EPIC #1646, See #2159. Tous les `sorry` éliminés à la création.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

universe w v u

namespace Grothendieck.SheafCohomology.MayerVietoris

open CategoryTheory Category Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-! ## 1. Applications de restriction en cohomologie

Étant donné un carré de Mayer-Vietoris S et un faisceau abélien F, les
applications entre groupes de cohomologie sont induites par les
applications de restriction dans le carré.

`toBiprod` est la somme des restrictions :
  H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F)
envoyant y sur (f₂₄* y, f₃₄* y).

`fromBiprod` est la différence des restrictions :
  H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F)
envoyant (y₁, y₃) sur f₁₂* y₁ - f₁₃* y₃.
-/

-- Somme des restrictions : H^n(X₄, F) ⟶ H^n(X₂, F) ⊞ H^n(X₃, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod

-- Formule explicite pour toBiprod.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_apply

-- Différence des restrictions : H^n(X₂, F) ⊞ H^n(X₃, F) ⟶ H^n(X₁, F).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod

/-! ## 2. Composition et la condition de nullité

La composition toBiprod >> fromBiprod est nulle :
  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁)
C'est l'ombre cohomologique de la commutativité du carré.
-/

-- toBiprod >> fromBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.toBiprod_fromBiprod

-- Formule explicite pour fromBiprod appliqué à un couple.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply

/-! ## 3. L'homomorphisme de connexion

L'homomorphisme de connexion δ : H^{n₀}(X₁, F) ⟶ H^{n₁}(X₄, F) (où
n₁ = n₀ + 1) est l'application clé de la suite exacte longue. Elle mesure
l'obstruction à relever une classe de cohomologie de l'intersection
vers l'espace recouvert.

Ceci est défini comme `shortComplex_shortExact.extClass.precomp`.
-/

-- L'homomorphisme de connexion δ : H^{n₀}(X₁) ⟶ H^{n₁}(X₄).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ

/-! ## 4. La suite exacte longue

La suite exacte longue de Mayer-Vietoris est encapsulée comme un
`ComposableArrows AddCommGrp 5` :

  H^n(X₄) ⟶ H^n(X₂) ⊞ H^n(X₃) ⟶ H^n(X₁) ⟶ H^{n+1}(X₄) ⟶ H^{n+1}(X₂) ⊞ H^{n+1}(X₃) ⟶ H^{n+1}(X₁)

Ceci est `sequence S F n₀ n₁ h` où `h : n₀ + 1 = n₁`.
-/

-- La suite exacte longue de Mayer-Vietoris (6 termes, ComposableArrows 5).
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence

/-! ## 5. Exactitude

La suite exacte longue est exacte en toute position. Ceci est le théorème
principal du module, prouvé par comparaison avec la suite contravariante
des groupes Ext.
-/

-- La suite de Mayer-Vietoris est exacte.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.sequence_exact

/-! ## 6. Conditions de bord

L'homomorphisme de connexion satisfait deux conditions de bord :
  - δ >> toBiprod = 0  (δ atterrit dans le noyau de toBiprod)
  - fromBiprod >> δ = 0  (δ factorise par le conoyau de fromBiprod)
-/

-- δ >> toBiprod = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.δ_toBiprod

-- fromBiprod >> δ = 0.
#check @CategoryTheory.GrothendieckTopology.MayerVietorisSquare.fromBiprod_δ

/-! ## 7. Théorèmes ponts

Théorèmes ponts reliant la suite exacte longue de Mayer-Vietoris
à une vérification concrète.
-/

/-- Théorème pont : la suite de Mayer-Vietoris est exacte. Pour un
    carré de Mayer-Vietoris S et un faisceau abélien F, la suite de
    groupes de cohomologie est exacte en toute position. -/
theorem mv_sequence_exact
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (S.sequence F n₀ n₁ h).Exact :=
  S.sequence_exact F n₀ n₁ h

/-- Théorème pont : l'homomorphisme de connexion composé avec la
    somme des restrictions est nul : δ >> toBiprod = 0. -/
theorem mv_delta_toBiprod_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.δ F n₀ n₁ h ≫ S.toBiprod F n₁ = 0 :=
  S.δ_toBiprod F n₀ n₁ h

/-- Théorème pont : la différence des restrictions composée avec
    l'homomorphisme de connexion est nulle : fromBiprod >> δ = 0. -/
theorem mv_fromBiprod_delta_eq_zero
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    S.fromBiprod F n₀ ≫ S.δ F n₀ n₁ h = 0 :=
  S.fromBiprod_δ F n₀ n₁ h

end Grothendieck.SheafCohomology.MayerVietoris
