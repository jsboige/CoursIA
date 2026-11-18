/-
Grothendieck tribute — Part 61: Continuous functors and the comparison lemma
Alexandre Grothendieck (1928-2014).

Phase 2 extension (#2159, Epic #1646).

A morphism of sites does not merely transport sieves: it transports
**sheaves**. Part 60 (TopologyDictionary.lean) closed the Grothendieck ↔
Lawvere–Tierney frontier on topologies; this part closes it on sheaves.
The central bridge is the continuous functor:

  - `Functor.IsContinuous F J K`: `F : C ⥤ D` is continuous when
    precomposition by `F.op` preserves the sheaf condition — the datum
    `op_comp_isSheaf_of_types`. This is the exact sheaf-level analogue of
    what `pullback_monotone` (SieveLattice.lean) establishes at the sieve
    level: pulling back respects the structure.

  - `Functor.sheafPushforwardContinuous`: the induced functor
    `Sheaf K A ⥤ Sheaf J A`. At the presheaf level, pushing forward is
    mere precomposition (`whiskeringLeft`); at the sheaf level, `F` must
    be continuous for the image of a sheaf to remain a sheaf — the square
    `sheafPushforwardContinuousCompSheafToPresheafIso` expresses this
    compatibility.

This module records the fundamental identities of the continuous
pushforward:

  - `sheafPushforwardContinuous_comp_sheafToPresheaf`: the square commutes —
    forgetting the sheaf structure after a continuous pushforward equals
    precomposing first
  - `sheafPushforwardContinuous_id`: pushforward along the identity
  - `sheafPushforwardContinuous_comp`: continuous pushforwards compose
    (contravariance in the functors)
  - `adjunction_sheafPushforwardContinuous`: **the comparison lemma** —
    if `F ⊣ G` with both `F` and `G` continuous, the induced continuous
    pushforwards on sheaf categories are themselves adjoint (SGA 4
    III.1.6). This is the operational ingredient of the comparison
    theorem: it transports adjunctions from presheaves to sheaves without
    ever invoking sheafification by hand.

These identities complete the picture started by Parts 8-9
(SieveOps.lean, SieveLattice.lean: pullback at the sieve level) and
DirectImage.lean (the adjunction `f^* ⊣ f_*` at the scheme level): they
provide its generalization to **arbitrary sites**.

Epic #1646, Phase 2 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Continuous

namespace Grothendieck_en

open CategoryTheory

/-!
## The square commutes: continuous pushforward and forgetting sheaves

Pushing a sheaf forward then forgetting it is a sheaf equals precomposing
the underlying presheaf by `F.op`. This is the very definition of the
functor `sheafPushforwardContinuous` (built by `ObjectProperty.lift`):
the diagram

    Sheaf K A --sheafPushforwardContinuous--> Sheaf J A
       |                                      |
       sheafToPresheaf                        sheafToPresheaf
       v                                      v
    Cᵒᵖ ⥤ A ---(whiskeringLeft).obj F.op---> Dᵒᵖ ⥤ A

commutes strictly (the iso is `Iso.refl`).
-/

/-- COMPARISON (Iso.refl): the continuous-pushforward / forget-sheaves
    square commutes — implemented via
    `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`. (A `def`: an
    `Iso` is a data-carrying structure, not a `Prop`.) -/
def sheafPushforwardContinuous_comp_sheafToPresheaf
    {C D : Type*} [Category C] [Category D] {A : Type*} [Category A]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous F J K] :
    F.sheafPushforwardContinuous A J K ⋙ sheafToPresheaf J A ≅
      sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ _).obj F.op :=
  Functor.sheafPushforwardContinuousCompSheafToPresheafIso F A J K

/-!
## Continuous pushforward along the identity

The identity functor is continuous (`Functor.isContinuous_id`), and
pushing forward along the identity is the identity on sheaves.
-/

/-- COMPARISON (Iso.refl): continuous pushforward along the identity
    functor = identity on sheaves. (A `def`: an `Iso` is a data-carrying
    structure, not a `Prop`.) -/
def sheafPushforwardContinuous_id
    {C : Type*} [Category C] {A : Type*} [Category A]
    (J : GrothendieckTopology C) :
    Functor.sheafPushforwardContinuous (𝟭 C) A J J ≅ 𝟭 (Sheaf J A) :=
  Functor.sheafPushforwardContinuousId A J

/-!
## Continuous pushforwards compose

If `F : C ⥤ D` and `G : D ⥤ E` are continuous, pushing forward along `G`
then along `F` equals pushing forward along `F ⋙ G` — contravariance in
the functors, mirroring `pullback_pullback` (SieveLattice.lean) at the
sieve level. Continuity of the composite is provided by
`Functor.isContinuous_comp`.
-/

/-- COMPARISON (Iso.refl): continuous pushforwards compose — contravariance
    in the functors, the sheaf-level mirror of `pullback_pullback`. (A `def`:
    an `Iso` is a data-carrying structure, not a `Prop`; the continuity
    instance of the composite is derived by `letI`, as in
    `Functor.sheafPushforwardContinuousComp`.) -/
def sheafPushforwardContinuous_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {A : Type*} [Category A] (F : C ⥤ D) (G : D ⥤ E)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K L] :
    letI := Functor.isContinuous_comp F G J K L
    G.sheafPushforwardContinuous A K L ⋙ F.sheafPushforwardContinuous A J K ≅
      (F ⋙ G).sheafPushforwardContinuous A J L :=
  Functor.sheafPushforwardContinuousComp F G A J K L

/-!
## The comparison lemma: adjunctions descend to sheaves

If `F ⊣ G` is an adjunction between continuous functors, the induced
continuous pushforwards on sheaf categories are themselves adjoint. This is
the **comparison lemma** of SGA 4 (exposé III, 1.6) in operational form:
any adjunction of presheaves compatible with the topologies descends to
sheaves **without explicit sheafification** — units and counits are
inherited componentwise from the opposite adjunction
(`adj.op.whiskerLeft _`).

This is the arbitrary-sites generalization of the adjunction
`pullbackPushforwardAdjunction` (DirectImage.lean, scheme level): no
geometry is required here, only continuity.
-/

/-- COMPARISON (SGA 4 III.1.6): if `F ⊣ G` with `F` and `G` continuous,
    the continuous pushforwards on sheaf categories are adjoint — the
    comparison lemma, operational form. (A `def`, not a `theorem`: an
    `Adjunction` is a data-carrying structure, not a `Prop` — the exact
    mirror of `Adjunction.sheafPushforwardContinuous`.) -/
def adjunction_sheafPushforwardContinuous
    {C D : Type*} [Category C] [Category D] {A : Type*} [Category A]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous F J K] [Functor.IsContinuous G K J] :
    F.sheafPushforwardContinuous A J K ⊣ G.sheafPushforwardContinuous A K J :=
  Adjunction.sheafPushforwardContinuous (E := A) adj J K

end Grothendieck_en
