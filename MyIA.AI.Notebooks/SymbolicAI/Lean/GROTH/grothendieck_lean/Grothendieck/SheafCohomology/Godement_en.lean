/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.SheafCohomology.Godement

/-!
# Part 95, brick 1: Godement cohomology — definition and calibrations

The P95 route stopped by Part 94 (see README, rank 94): the direct sheaf
corollary remains behind abelian sheafification (absent from Mathlib at the
lake's pin); the **flabby resolution** is the retained route — and it starts
by *naming* what the resolution computes. This module poses the **Godement
cohomology** of `F` on `U`: the homology of the complex of sections on `U`
of the canonical complex ([God58, Chap. II §5.1] — the historical
definition, prior to any Ext presentation).

## Content

1. `sectionsFunctorAdditive`: the "sections on `U`" functor
   `F ↦ F.obj (op U)`, with its `Additive` instance (single field
   `map_add`, by `rfl` — addition of natural transformations is
   componentwise; `PreservesZeroMorphisms` follows through Mathlib's
   `preservesZeroMorphisms_of_additive` bridge). Written by hand rather
   than through a generic evaluator — no dependency on an uncertain
   Mathlib instance name at the pin.
2. `godementSectionsComplex`: the complex of sections — the image of the
   canonical complex (Part 92) under the sections functor, via
   `Functor.mapHomologicalComplex`. Each stage is the group of sections
   `CⁿF(U)`, each differential the fieldwise action of `dⁿ`.
3. `godementCohomologyObj`: **Godement cohomology** `Hⁿ_God(U, F)` — the
   homology of that complex in degree `n`.
4. `godementSectionsComplex_X`: the definitional calibration of the stage —
   `(Γ(U, C^●F)).X n = godementCanonicalObj F n (op U)` by `rfl`, a bridge
   to the notations of Parts 89-92.
5. `godementSectionsComplex_d_zero`: the calibration of the degree-0
   differential — `(Γ(U, C^●F)).d 0 1 = d⁰(U)`, the component at `U` of the
   canonical step.
6. `exact_app_toGodement_godementCanonicalDZero`: **Part 91's step-B
   exactness, evaluated at `U`** — the sequence of sections
   `F(U) → C⁰F(U) → C¹F(U)` is exact. Evaluation at an open set is an exact
   functor (limits and colimits of presheaves are pointwise:
   `evaluationPreservesLimits`, `evaluation_preservesColimits`), so
   exactness transports along `Functor.exact_tfae` — no recourse to stalks
   or AB5.
7. `godementZerothCohomologyIso`: **brick 2 — `H⁰_God(U, F) ≅ F(U)` for
   `F` a sheaf** ([God58] II §5.1). Assembly without sheafification:
   `H⁰ = ker d⁰` (nothing in degree −1), then `ker d⁰(U) ≅ F(U)` because
   the kernel lift `F(U) ⟶ ker d⁰(U)` is epi (evaluated exactness,
   `Exact.epi_kernelLift`) and mono (the Godement unit is mono, Part 90,
   evaluated at `U`) — hence an iso (`isIso_iff_epi_and_mono`,
   `AddCommGrpCat` is balanced).

## What this brick poses vs. what it leaves open

**Posed**: the full definition `Hⁿ_God(U, F) = Hⁿ(Γ(U, C^●F))`, the stage
and `d⁰` calibrations, the additive sections functor (a reusable brick — the
"flabby ⇒ Γ-acyclic" capstone (Part 94, merged #21072) will connect to it
after the stack is retargeted onto main), and **brick 2**:
`H⁰_God(U, F) ≅ F(U)` for `F` a sheaf — the sheafification wall identified
in the P95 plan is not needed here: the monomorphism of the unit (Part 90)
and step-B exactness (Part 91), both evaluated at `U`, suffice.
Sheafification remains required by brick 3 alone.

**Not posed** — named frontiers:
- **functoriality in `F`**: it first requires functoriality of the
  *canonical complex* itself (`F ↦ C^●F` on morphisms), which Part 92 did
  not pose — a distinct grain `godementCanonicalComplex_map`;
- the long exact sequence (brick 3: cone or dimension-shift — it is the one
  that will require abelian sheafification).

## References

* [God58] R. Godement, *Topologie algébrique et théorie des faisceaux*,
  Hermann 1958, Chap. II §5.1 (definition), Th. 5.2.1 (acyclicity).
-/

universe u

namespace Grothendieck.SheafCohomology_en

open CategoryTheory CategoryTheory.Limits Opposite

-- **OK-CONSUMER sibling**: the declarations `sectionsFunctorAdditive`
-- (with its `Additive` instance), `godementSectionsComplex`,
-- `godementCohomologyObj`, and `godementSectionsComplex_X` are imported
-- from `Grothendieck.SheafCohomology.Godement` (FR) and accessed in this
-- namespace as `Grothendieck.SheafCohomology.sectionsFunctorAdditive`,
-- `Grothendieck.SheafCohomology.godementSectionsComplex`,
-- `Grothendieck.SheafCohomology.godementCohomologyObj`, and
-- `Grothendieck.SheafCohomology.godementSectionsComplex_X`. We do not
-- redeclare them here to keep bodies byte-identical with FR (the
-- OK-CONSUMER i18n invariant of [docs/lean/i18n-sibling-patterns.md]).
--
-- **Part 95, brick 1, landed in the FR twin of this module**: the Godement
-- cohomology `Hⁿ_God(U, F)` is now *named* — it is the homology in degree
-- `n` of the complex of sections `Γ(U, C^●F)` of the canonical complex
-- (Part 92). The sections functor is written by hand (`F ↦ F.obj (op U)`,
-- additive fieldwise), so the definition carries no dependency on an
-- uncertain Mathlib instance name at the pin. **Scope note (rescope at
-- write time, 2026-10-18)**: functoriality in `F` is *deferred* — the
-- canonical complex itself is not yet functorial in `F` (Part 92 posed the
-- object, not the action on morphisms); that is the distinct grain
-- `godementCanonicalComplex_map`. The flabby-resolution route (Part 94,
-- `isFlasque_godementCanonicalComplex`; capstone #21072 "flabby ⇒
-- Γ-acyclic") will consume this definition: brick 2 `H⁰_God(U, F) ≅ Γ(U,F)`
-- for `F` a sheaf, then brick 3 the long exact sequence.
--
-- **Part 95, brick 2, landed in the FR twin (2026-10-19)**: the zeroth
-- Godement cohomology is the group of sections —
-- `godementZerothCohomologyIso : godementCohomologyObj U F 0 ≅ F.obj (op U)`
-- for `F` a sheaf, proved WITHOUT sheafification: the P95-plan wall belongs
-- to brick 3 only. The three moves, all named in the FR docstring:
-- (1) `exact_app_toGodement_godementCanonicalDZero` — Part 91's step-B
-- exactness evaluated at `U`, via `Functor.exact_tfae` and the pointwise
-- evaluation functor (`evaluationPreservesLimits`,
-- `evaluation_preservesColimits`) — no stalks, no AB5;
-- (2) the evaluated unit is mono (Part 90, `mono_iff_mono_app`);
-- (3) the kernel lift `F(U) ⟶ ker d⁰(U)` is epi (exactness) and mono
-- (composition over the evaluated unit), hence an iso in balanced
-- `AddCommGrpCat`.

end Grothendieck.SheafCohomology_en
