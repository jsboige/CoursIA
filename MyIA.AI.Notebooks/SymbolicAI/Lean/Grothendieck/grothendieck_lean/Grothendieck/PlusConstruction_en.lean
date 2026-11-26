/-
Grothendieck tribute — Part 62: the Plus construction
Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

The Godement–Grothendieck sheafification is obtained in two passes of the
**Plus construction**: `P⁺ = P.plus J`, then `P⁺⁺`, and the associativity
theorem makes `P⁺⁺` the sheaf associated to `P`. Part 20
(`Sheafification.lean`) established the adjunction; this part records its
constructive ingredient, as Mathlib exposes it in
`CategoryTheory.Sites.Plus` (namespace `GrothendieckTopology`):

  - `J.plusObj P`: the presheaf of locally compatible sections — at each
    `X`, the colimit of the multiequalizer diagram indexed by the covering
    sieves `J.Cover X`. The colimit hypotheses are carried by the
    `HasMultiequalizer` / `HasColimitsOfShape` instances.
  - `J.plusMap η`: functoriality in `P` — a morphism of presheaves
    induces `P⁺ ⟶ Q⁺`.
  - `J.toPlus P`: the canonical arrow `P ⟶ P⁺` ("put a section into its
    local class").

This module records the fundamental identities:

  - `plusFunctor_obj_field`, `plusMap_id_field`, `plusMap_comp_field`:
    `plusFunctor` is a functor (object, identity, composition)
  - `toPlusNatTrans_app_field`, `toPlus_naturality_field`: `toPlus` is a
    natural transformation `𝟭 ⟶ plusFunctor`
  - `plusMap_toPlus_field`: **the key algebraic identity**
    `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺` — this is what makes the double construction
    associative
  - `isoToPlus_hom_field`, `isoToPlus_inv_field`: a **sheaf is a fixed
    point of Plus** — `P ≅ P⁺` as soon as `P` is a sheaf
  - `plusLift_toPlus_field`, `plusLift_unique_field`, `plus_hom_ext_field`,
    `plusMap_plusLift_field`: the **universal property** — every arrow
    `P ⟶ Q` to a sheaf `Q` factors uniquely through `P ⟶ P⁺ ⟶ Q`, and
    `toPlus` is an epimorphism towards sheaves (`plus_hom_ext`: two arrows
    from `P⁺` to a sheaf, equal after composition with `toPlus`, are
    equal)

The link with SGA: the Plus construction is exposé II.3 of SGA 4
(associated sheaves via Godement's 1958 two-step procedure, taken up by
Grothendieck). The universal property below is its operational heart:
`P⁺` is the universal "partial sheafification" with respect to sheaves.

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Plus

namespace Grothendieck_en

open CategoryTheory CategoryTheory.Limits

section Bridges

variable {C : Type*} [Category C] {D : Type*} [Category D]
  (J : GrothendieckTopology C)
  [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]

/-!
## Functoriality of Plus

`J.plusFunctor D` sends `P` to `J.plusObj P` and `η` to `J.plusMap η`.
The three identities below certify that it is a functor: the object action
is `plusObj`, the action on `𝟙` is `𝟙`, the action preserves composition.
-/

/-- PLUS (rfl): the object action of the Plus functor is `plusObj`. -/
theorem plusFunctor_obj_field (P : Cᵒᵖ ⥤ D) :
    (J.plusFunctor D).obj P = J.plusObj P := rfl

/-- PLUS (plusMap_id): the Plus functor preserves identities. -/
theorem plusMap_id_field (P : Cᵒᵖ ⥤ D) :
    (J.plusFunctor D).map (𝟙 P) = 𝟙 (J.plusObj P) :=
  J.plusMap_id P

/-- PLUS (plusMap_comp): the Plus functor preserves composition. -/
theorem plusMap_comp_field {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R) :
    (J.plusFunctor D).map (η ≫ γ) = J.plusMap η ≫ J.plusMap γ :=
  J.plusMap_comp η γ

/-!
## The canonical arrow `toPlus` is natural

`J.toPlus P : P ⟶ P⁺` is the component at `P` of a natural transformation
`𝟭 ⟶ plusFunctor` (`J.toPlusNatTrans D`): it commutes with every morphism
of presheaves.
-/

/-- PLUS (rfl): the component of `toPlusNatTrans` at `P` is `toPlus P`. -/
theorem toPlusNatTrans_app_field (P : Cᵒᵖ ⥤ D) :
    (J.toPlusNatTrans D).app P = J.toPlus P := rfl

/-- PLUS (toPlus_naturality): `toPlus` is natural — every arrow `η`
    commutes with the insertion into the Plus construction. -/
theorem toPlus_naturality_field {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) :
    η ≫ J.toPlus Q = J.toPlus P ≫ J.plusMap η :=
  J.toPlus_naturality η

/-!
## The key algebraic identity: `(P ⟶ P⁺)⁺ = P⁺ ⟶ P⁺⁺`

Applying Plus to the canonical arrow of `P` gives the canonical arrow of
`P⁺`. This identity is what makes the double construction `P⁺⁺`
compatible with iteration and prepares the associativity of the two-pass
sheafification.
-/

/-- PLUS (plusMap_toPlus): the key algebraic identity — applying Plus to
    the canonical arrow gives the canonical arrow of the Plus. -/
theorem plusMap_toPlus_field (P : Cᵒᵖ ⥤ D) :
    J.plusMap (J.toPlus P) = J.toPlus (J.plusObj P) :=
  J.plusMap_toPlus P

/-!
## A sheaf is a fixed point of Plus

If `P` is a sheaf for `J`, the canonical arrow `P ⟶ P⁺` is an isomorphism
(`J.isoToPlus`): the Plus construction does not modify sheaves. This
fixed-point coherence guarantees that the double construction stops at a
stable object.
-/

/-- PLUS (isoToPlus_hom): for a sheaf `P`, the homomorphism of the iso
    `P ≅ P⁺` is the canonical arrow `toPlus`. -/
theorem isoToPlus_hom_field (P : Cᵒᵖ ⥤ D) (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).hom = J.toPlus P :=
  J.isoToPlus_hom P hP

/-- PLUS (isoToPlus_inv): for a sheaf `P`, the inverse of the iso
    `P ≅ P⁺` is the lift of the identity. -/
theorem isoToPlus_inv_field (P : Cᵒᵖ ⥤ D) (hP : Presheaf.IsSheaf J P) :
    (J.isoToPlus P hP).inv = J.plusLift (𝟙 P) hP :=
  J.isoToPlus_inv P hP

/-!
## The universal property: unique factorization through `P⁺`

Every arrow `η : P ⟶ Q` to a **sheaf** `Q` factors uniquely through
`toPlus`: `η = toPlus P ≫ plusLift η`. Conversely, an arrow from `P⁺` to a
sheaf is determined by its composite with `toPlus` (`plus_hom_ext`) —
`toPlus` is an epimorphism towards sheaves. This is the operational heart
of SGA 4 II.3: `P⁺` is the universal "partial sheafification".
-/

/-- PLUS (toPlus_plusLift): the factorization — composing `toPlus` with
    the lift gives back the original arrow. -/
theorem plusLift_toPlus_field {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) :
    J.toPlus P ≫ J.plusLift η hQ = η :=
  J.toPlus_plusLift η hQ

/-- PLUS (plusLift_unique): uniqueness of the lift — any factorization
    through `toPlus` coincides with `plusLift`. -/
theorem plusLift_unique_field {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q) (γ : J.plusObj P ⟶ Q)
    (hγ : J.toPlus P ≫ γ = η) :
    γ = J.plusLift η hQ :=
  J.plusLift_unique η hQ γ hγ

/-- PLUS (plus_hom_ext): extensionality — two arrows from `P⁺` to a
    sheaf, equal after composition with `toPlus`, are equal. -/
theorem plus_hom_ext_field {P Q : Cᵒᵖ ⥤ D} (η γ : J.plusObj P ⟶ Q)
    (hQ : Presheaf.IsSheaf J Q)
    (h : J.toPlus P ≫ η = J.toPlus P ≫ γ) :
    η = γ :=
  J.plus_hom_ext η γ hQ h

/-- PLUS (plusMap_plusLift): the lift is compatible with composition —
    composing then lifting equals lifting the composite. -/
theorem plusMap_plusLift_field {P Q R : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (γ : Q ⟶ R)
    (hR : Presheaf.IsSheaf J R) :
    J.plusMap η ≫ J.plusLift γ hR = J.plusLift (η ≫ γ) hR :=
  J.plusMap_plusLift η γ hR

end Bridges

end Grothendieck_en
