/-
Grothendieck tribute — Part 5: Calibration targets for the prover harness
Alexandre Grothendieck (1928-2014).

Micro-proof targets for the harness calibration ladder (Epic #1453).
These are deliberately simple facts about Grothendieck topologies that
exercise different proof strategies:

  - P1 (closed-eval): trivial ≤ discrete (lattice order)
  - P2 (case-decomposition): Sieve.pullback of ⊤ is ⊤
  - P3 (rewriting): zariskiTopology_eq bridge theorem
  - P4 (integration): every presheaf is a sheaf for the trivial topology

Epic #1646, #1453. All `sorry`s eliminated at creation.
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.AlgebraicGeometry.Sites.BigZariski

namespace Grothendieck

open CategoryTheory AlgebraicGeometry

/-!
## P1: Lattice order — trivial ≤ discrete (closed evaluation)

The trivial topology (only ⊤ covers) is coarser than the discrete topology
(every sieve covers). This is a lattice-level fact: ⊥ ≤ ⊤.
-/

/-- CALIBRATION (decide/rfl): the trivial topology is below the discrete topology
    in the lattice of Grothendieck topologies. -/
theorem trivial_le_discrete {C : Type*} [Category C] :
    (GrothendieckTopology.trivial C : GrothendieckTopology C) ≤
    GrothendieckTopology.discrete C := by
  rw [GrothendieckTopology.trivial_eq_bot, GrothendieckTopology.discrete_eq_top]
  exact bot_le

/-!
## P2: Sieve.pullback of ⊤ is ⊤ (direct proof)

Pulling back the maximal sieve along any morphism gives the maximal sieve.
-/

/-- CALIBRATION (simp): pullback of the top sieve is the top sieve. -/
theorem pullback_top {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X) :
    (Sieve.⊤ X).pullback f = Sieve.⊤ Y := by
  ext Z g
  simp [Sieve.⊤, Sieve.pullback]
  exact fun _ => trivial

/-!
## P3: The Zariski topology equals the pretopology-generated topology

This is `Scheme.zariskiTopology_eq`, restated here as a calibration
target that the prover must find and apply.
-/

/-- CALIBRATION (exact): the Zariski topology equals the pretopology-generated one.
    The prover must discover `exact Scheme.zariskiTopology_eq`. -/
theorem zariski_eq_pretopology :
    (Scheme.zariskiTopology : GrothendieckTopology Scheme) =
    Scheme.zariskiPretopology.toGrothendieck :=
  Scheme.zariskiTopology_eq

/-!
## P4: Every presheaf is a sheaf for the trivial topology

For the coarsest Grothendieck topology (only ⊤ covers), every presheaf
automatically satisfies the sheaf condition. This is because there is
only one covering sieve per object, and the sheaf condition on ⊤ is trivial.
-/

/-- CALIBRATION (exact): every Type-valued presheaf is a sheaf for the
    trivial (coarsest) Grothendieck topology. -/
theorem isSheaf_trivial {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (GrothendieckTopology.trivial C) P :=
  Presieve.isSheaf_bot P

end Grothendieck
