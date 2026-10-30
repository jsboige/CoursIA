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

## What this brick poses vs. what it leaves open

**Posed**: the full definition `Hⁿ_God(U, F) = Hⁿ(Γ(U, C^●F))`, the stage
calibrations, and the additive sections functor (a reusable brick — the
"flabby ⇒ Γ-acyclic" capstone (Part 94, merged #21072) will connect to it
after the stack is retargeted onto main).

**Not posed** — named frontiers:
- **functoriality in `F`**: it first requires functoriality of the
  *canonical complex* itself (`F ↦ C^●F` on morphisms), which Part 92 did
  not pose — a distinct grain `godementCanonicalComplex_map`;
- `H⁰_God(U, F) ≅ F(U)` for `F` a sheaf (brick 2 of the P95 plan —
  sheafification wall identified, to be instructed cold);
- the long exact sequence (brick 3: cone or dimension-shift).

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
-- for `F` a sheaf (sheafification wall to instruct cold), then brick 3 the
-- long exact sequence.

end Grothendieck.SheafCohomology_en
