/-
Grothendieck tribute — Part 7: Sheaf basics
Alexandre Grothendieck (1928-2014).

Phase 3 extension (#2159, Epic #1646).

Part 1 (CategoryAndSites.lean) introduced Grothendieck topologies and sieves.
Part 5 (Calibration.lean) showed that every presheaf is a sheaf for the trivial
topology. Part 6 (SieveLattice.lean) established pullback identities on sieves.

This module records fundamental properties of sheaves and separated presheaves:

  - Every sheaf is separated (the fundamental inclusion).
  - Every presheaf is separated for the trivial (coarsest) topology.
  - For a subcanonical topology, every representable presheaf is a sheaf.
  - Sheaf condition transfers along topology comparisons (J₁ ≤ J₂).

These are the basic algebraic facts about sheaves on a site, connecting
the lattice-theoretic properties of sieves (Part 1/6) with the sheaf
condition (Part 5).

Epic #1646, Phase 3 (#2159). All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.Canonical

namespace Grothendieck_en

universe v u w w'

open CategoryTheory

/-!
## Sheaf ⇒ Separated

The fundamental inclusion: every sheaf is automatically a separated
presheaf. Intuitively, if a presheaf admits unique gluings, then
compatible families have at most one gluing (uniqueness).
-/

/-- Every sheaf is separated. Uses `Presieve.IsSheaf.isSeparated` from Mathlib. -/
theorem sheaf_is_separated {C : Type*} [Category C]
    {J : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type*}
    (h : Presieve.IsSheaf J P) :
    Presieve.IsSeparated J P :=
  h.isSeparated

/-!
## Separated presheaves for the trivial topology

The trivial topology ⊥ (coarsest) has only the maximal sieve ⊤ as
covering. Since every presheaf is a sheaf for ⊥, every presheaf is
also separated.
-/

/-- Every Type-valued presheaf is separated for the trivial (coarsest)
    topology. This follows from `isSheaf_bot` combined with
    `sheaf_is_separated`. -/
theorem isSeparated_trivial {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSeparated (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot.isSeparated

/-!
## Subcanonical topologies and representable sheaves

A Grothendieck topology J is *subcanonical* if every representable presheaf
(i.e., `yoneda.obj X` for any X) is a sheaf. This is equivalent to saying
that J ≤ the canonical topology (the finest subcanonical topology).

The Zariski topology on schemes is subcanonical (see ZariskiSite.lean).
-/

/-- For a subcanonical topology J, the Yoneda presheaf at X is a sheaf.
    This is the key bridge: the Yoneda embedding lands in sheaves.
    Uses `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`. -/
theorem yoneda_isSheaf_subcanonical {C : Type*} [Category C]
    (J : GrothendieckTopology C) [J.Subcanonical] (X : C) :
    Presieve.IsSheaf J (yoneda.obj X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X)

/-!
## Sheaf condition along topology comparisons

If J₁ ≤ J₂ (J₁ has fewer covering sieves) and P is a sheaf for J₂,
then P is a sheaf for J₁. The coarser the topology, the more presheaves
are sheaves.
-/

/-- A presheaf that is a sheaf for a finer topology is also a sheaf for
    a coarser topology. Uses `Presieve.isSheaf_of_le` from Mathlib. -/
theorem isSheaf_of_le {C : Type*} [Category C]
    {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂)
    {P : Cᵒᵖ ⥤ Type*} (hP : Presieve.IsSheaf J₂ P) :
    Presieve.IsSheaf J₁ P :=
  Presieve.isSheaf_of_le P h hP

/-!
## Subcanonical is downward-closed

If K is subcanonical and J ≤ K, then J is also subcanonical.
This follows because having fewer covering sieves makes the
sheaf condition easier to satisfy.
-/

/-- Subcanonicity is downward-closed: if K is subcanonical and J ≤ K,
    then J is subcanonical. Uses `GrothendieckTopology.Subcanonical.of_le`. -/
theorem subcanonical_of_le {C : Type*} [Category C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le h

/-!
## The trivial topology is subcanonical

Since the trivial (coarsest) topology ⊥ is below every topology,
and every topology is below the canonical topology (which is subcanonical),
the trivial topology is subcanonical.
-/

/-- The trivial (coarsest) topology is subcanonical.
    Every presheaf is a sheaf for ⊥, so in particular every representable
    presheaf is a sheaf. Uses `GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`. -/
theorem trivial_subcanonical {C : Type*} [Category C] :
    @GrothendieckTopology.Subcanonical C _ (⊥ : GrothendieckTopology C) :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj ⊥
    (fun _ => Presieve.isSheaf_bot)

/-!
## Preservation of sheaf conditions via presheaf isomorphisms

The conditions `IsSheaf` and `IsSeparated` are **properties of the isomorphism
class** of the presheaf. If `P ≅ P'`, then `P` is a sheaf (resp. separated)
if and only if `P'` is. This invariance is necessary for the full theory:
sheaves form a full subcategory of the presheaf category, and full-faithfulness
requires isomorphisms between objects to preserve the property.

These are `isSheaf_iso` and `isSeparated_iso` from Mathlib (`SheafOfTypes.lean`).
-/

/-- The condition `IsSheaf` is preserved by presheaf isomorphism:
    if `P ≅ P'` and `P` is a sheaf, then `P'` is a sheaf. This is the
    stability of sheaves under isomorphisms — a property needed for
    full-faithfulness of the inclusion `Sheaf J A ↪ Presheaf A`.
    Uses `Presieve.isSheaf_iso` from Mathlib. -/
theorem isSheaf_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {P P' : Cᵒᵖ ⥤ Type w}
    (i : P ≅ P') (h : Presieve.IsSheaf J P) :
    Presieve.IsSheaf J P' :=
  Presieve.isSheaf_iso J i h

/-- The condition `IsSeparated` is preserved by presheaf isomorphism:
    if `P ≅ P'` and `P` is separated, then `P'` is separated. Symmetric to
    `isSheaf_iso` for separation. Uses `Presieve.isSeparated_iso`
    from Mathlib. -/
theorem isSeparated_iso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {P P' : Cᵒᵖ ⥤ Type w}
    (i : P ≅ P') (hP : Presieve.IsSeparated J P) :
    Presieve.IsSeparated J P' :=
  Presieve.isSeparated_iso J i hP

/-!
## Symmetry: separation descends along topology comparisons

Just as `IsSheaf` descends along `J₁ ≤ J₂` (cf. `isSheaf_of_le`),
the condition `IsSeparated` also descends. The coarser the topology,
the easier it is to be separated.

This is `isSeparated_of_le` from Mathlib (`SheafOfTypes.lean`).
-/

/-- The condition `IsSeparated` descends along topology comparisons:
    if `J₁ ≤ J₂` and `P` is separated for `J₂`, then `P` is separated for `J₁`.
    Symmetric to `isSheaf_of_le` for separation. Uses
    `Presieve.isSeparated_of_le` from Mathlib. -/
theorem isSeparated_of_le {C : Type u} [Category.{v} C]
    {J₁ J₂ : GrothendieckTopology C}
    (P : Cᵒᵖ ⥤ Type w) (h : J₁ ≤ J₂)
    (hP : Presieve.IsSeparated J₂ P) :
    Presieve.IsSeparated J₁ P :=
  Presieve.isSeparated_of_le P h hP

/-!
## Equivalence of IsSheaf via natural equivalence of presheaves

A **natural equivalence** between presheaves `e : P₁ ≅ P₂` (a natural
isomorphism, i.e. component-by-component) also preserves the condition
`IsSheaf`, and this in **both directions**. This is strictly stronger than
invariance under a global presheaf isomorphism: we have
`IsSheaf J P₁ ↔ IsSheaf J P₂` via a natural equivalence.

This is `isSheaf_iff_of_nat_equiv` from Mathlib (`SheafOfTypes.lean`).
-/

/-- A natural equivalence between presheaves preserves the condition
    `IsSheaf` in both directions: `IsSheaf J P₁ ↔ IsSheaf J P₂` via a
    family of component-by-component equivalences. Stronger than a global
    presheaf isomorphism: the condition is preserved component-by-component.
    Uses `Presieve.isSheaf_iff_of_nat_equiv` from Mathlib. -/
theorem isSheaf_iff_of_nat_equiv {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : ∀ ⦃X : C⦄, P₁.obj (Opposite.op X) ≃ P₂.obj (Opposite.op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (Opposite.op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x)) :
    Presieve.IsSheaf J P₁ ↔ Presieve.IsSheaf J P₂ :=
  Presieve.isSheaf_iff_of_nat_equiv e he

end Grothendieck_en