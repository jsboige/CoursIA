/-
# Hommage Grothendieck — Part 5: Calibration targets for the prover harness

Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Calibration targets for the prover harness (English mirror)

This module hosts **4 theorem** of P1-P4 calibration for the
**co-evolution of the prover harness** (Epic #1453) — the multi-agent
proof instrument of the cluster. Each target is voluntarily simple but
**didactic**: it exercises a different Lean 4 kernel tactic to gradually
widen the register covered by the autonomous prover.

### Accessibility note Epic #1452/#1453

This module is **voluntarily minimalist**: 4 calibration theorem each
< 5 lines of proof. The substance is not in the mathematical difficulty
but in the **tactical diversity** (4 different tactics per target). This
is precisely the target calibration for Epic #1453: graded exercises for
the autonomous prover harness.

Convention i18n (EPIC #4980 ratified by user 2026-07-04, see
`code-style.md` §Lean i18n): this substantial module is paired with
its French canonical counterpart in the sibling file `Calibration.lean`
(sibling pair model, see PR #6154 for the pilot on `Utility.lean`).
-/

import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.AlgebraicGeometry.Sites.BigZariski

namespace Grothendieck_en

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
    (Sieve.pullback f (⊤ : Sieve X)) = (⊤ : Sieve Y) := by
  ext Z g
  simp [Sieve.pullback]

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
    trivial (coarsest) Grothendieck topology (= ⊥).
    Uses `Presieve.isSheaf_bot` which works with `⊥`. -/
theorem isSheaf_trivial {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) :
    Presieve.IsSheaf (⊥ : GrothendieckTopology C) P :=
  Presieve.isSheaf_bot

end Grothendieck_en
