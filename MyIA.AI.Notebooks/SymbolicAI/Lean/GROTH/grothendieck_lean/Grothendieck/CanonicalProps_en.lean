/-
Grothendieck tribute — Part 10: Canonical topology and subcanonical sites
Alexandre Grothendieck (1928-2014).

Phase 6 extension (#2159, Epic #1646).

Parts 1-4 established fundamentals: categories, sieves, topologies,
lattice operations, pullback identities, sheaf basics, and covering closure.
Parts 5-8 built on that with calibration, lattice laws, sheaf properties,
topology ordering, and coverage generation.

This module studies the **canonical topology**: the finest Grothendieck
topology for which every representable presheaf (yoneda.obj X) is a sheaf.

  - The canonical topology makes all representables into sheaves.
  - A topology is **subcanonical** iff it is below the canonical topology.
  - Subcanonicity is downward-closed: J ≤ K and K subcanonical ⟹ J subcanonical.
  - In a subcanonical topology, every representable presheaf is a sheaf.
  - The trivial topology ⊥ is subcanonical.

The canonical topology is the natural reference point: the Zariski topology
on schemes is subcanonical (see ZariskiSite.lean).

Epic #1646, Phase 6 (#2159). All `sorry`s eliminated at creation.

SIBLING PAIR (EPIC #4980): this file is the EN mirror of
`Grothendieck/CanonicalProps.lean` (FR canonical). The two files share
the same code body (imports, namespace, theorems, proofs) byte-for-byte
— only the file-level docstring (`/- ... -/` header) and the
section-divider docstrings (`/-! ... -/`) differ between FR and EN.
Verified by `scripts/lean/check_i18n_siblings.py` (status: OK).
-/
import Mathlib.CategoryTheory.Sites.Canonical

namespace Grothendieck_en

open CategoryTheory

/-!
## The canonical topology

The canonical topology on a category C is the finest Grothendieck topology
for which every representable presheaf `yoneda.obj X` is a sheaf. It is
defined as `Sheaf.finestTopology` applied to the set of all representables.

Key fact: a topology is subcanonical (all representables are sheaves)
if and only if it is below the canonical topology.
-/

/-- The Yoneda presheaf at X is a sheaf for the canonical topology.
    This is the defining property of the canonical topology.
    Uses `Sheaf.isSheaf_yoneda_obj`. -/
theorem yoneda_isSheaf_canonical {C : Type*} [Category C] (X : C) :
    Presieve.IsSheaf (Sheaf.canonicalTopology C) (yoneda.obj X) :=
  Sheaf.isSheaf_yoneda_obj X

/-- Every representable presheaf is a sheaf for the canonical topology.
    Generalizes `yoneda_isSheaf_canonical` to any presheaf that has a
    representation, not just `yoneda.obj X`.
    Uses `Sheaf.isSheaf_of_isRepresentable`. -/
theorem isSheaf_repr_canonical {C : Type*} [Category C]
    (P : Cᵒᵖ ⥤ Type*) [P.IsRepresentable] :
    Presieve.IsSheaf (Sheaf.canonicalTopology C) P :=
  Sheaf.isSheaf_of_isRepresentable P

/-!
## Subcanonical topologies

A topology J is *subcanonical* if every representable presheaf is a J-sheaf.
Equivalently, J ≤ the canonical topology. The class `Subcanonical J` bundles
this order relation. The canonical topology itself is subcanonical.

Subcanonicity is the property that makes the Yoneda embedding land in sheaves:
C → SheafOfTypes J. This is crucial for schemes (Zariski is subcanonical).
-/

/-- A subcanonical topology J is below the canonical topology.
    Accesses the `le_canonical` field of the `Subcanonical` class. -/
theorem subcanonical_le {C : Type*} [Category C]
    {J : GrothendieckTopology C} [hJ : J.Subcanonical] :
    (J : GrothendieckTopology C) ≤ Sheaf.canonicalTopology C :=
  hJ.le_canonical

/-- If every representable presheaf is a sheaf for J, then J is subcanonical.
    This is the * converse of `subcanonical_le`: to prove subcanonicity,
    it suffices to verify the sheaf condition on all `yoneda.obj X`.
    Uses `GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`. -/
theorem subcanonical_of_yoneda_sheaf {C : Type*} [Category C]
    (J : GrothendieckTopology C)
    (h : ∀ X : C, Presieve.IsSheaf J (yoneda.obj X)) :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj J h

/-- Subcanonicity is downward-closed: J ≤ K and K subcanonical ⟹ J subcanonical.
    A coarser topology has fewer covering sieves, so the sheaf condition is
    easier to satisfy. Uses `GrothendieckTopology.Subcanonical.of_le`. -/
theorem subcanonical_of_le {C : Type*} [Category C]
    {J K : GrothendieckTopology C} (h : J ≤ K) [K.Subcanonical] :
    J.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le h

/-- In a subcanonical topology, every representable presheaf is a sheaf.
    This is the key consequence of subcanonicity: representables detect
    the sheaf condition. Uses `GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable`. -/
theorem isSheaf_repr_subcanonical {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.Subcanonical]
    (P : Cᵒᵖ ⥤ Type*) [P.IsRepresentable] :
    Presieve.IsSheaf J P :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

/-!
## The canonical topology is subcanonical

The canonical topology is subcanonical by definition: it is the finest
subcanonical topology. Every topology below it is also subcanonical.
-/

/-- The canonical topology itself is subcanonical.
    This is an instance, resolved by typeclass inference. -/
theorem canonical_is_subcanonical {C : Type*} [Category C] :
    (Sheaf.canonicalTopology C).Subcanonical :=
  inferInstance

/-!
## Every presheaf is a sheaf for the trivial topology

The trivial (bottom) topology ⊥ has only the maximal sieve as covering.
Every presheaf trivially satisfies the sheaf condition for the maximal sieve.
This is also covered in Calibration.lean and SheafBasics.lean, included
here for completeness in the canonical context.
-/

/-- Every Type-valued presheaf is a sheaf for the trivial (bottom) topology.
    Uses `Presieve.isSheaf_bot`. -/
theorem isSheaf_bot_all {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot

end Grothendieck_en