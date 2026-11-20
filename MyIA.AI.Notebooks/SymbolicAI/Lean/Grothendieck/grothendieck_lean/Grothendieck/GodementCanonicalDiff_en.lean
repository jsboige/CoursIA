/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementCanonicalDiff

/-!
# The Godement canonical step: the differential through the cokernel of the unit

Part 89 — the named frontier of Parts 87 and 88. Those parts posed the
**iterated unit sequence** `F → C⁰F → C⁰²F → ⋯` and proved it is **not a
complex** (`godementUnit_comp_injective`, P87: on a sheaf, the composite of
two units is injective, hence nonzero on every nonzero section). The canonical
construction of [God58, Chap. II §4.1] passes at each step through the
**cokernel of the previous arrow**: that step is what this module poses.

## The canonical step, in general then in degree 0

1. `godementStep`: for every morphism of presheaves `f : A ⟶ B`, the
   **canonical step** is the composite `B ⟶ C⁰(coker f)` given by the cokernel
   projection followed by the Godement unit of the cokernel:
   `cokernel.π f ≫ toGodement (coker f)`. This is a uniform pattern: applied to
   each arrow of the resolution, it generates the next arrow.
2. `comp_godementStep_zero`: **the null-composition of the canonical step** —
   `f ≫ godementStep f = 0`, by the universal condition of the cokernel
   (`cokernel.condition`) and annihilation of the zero composite. The proof is
   two rewrites: associate, apply the cokernel condition.
3. `godementCanonicalDZero`: the **degree-0 differential** of the canonical
   resolution, obtained by applying the canonical step to the unit:
   `d⁰ := godementStep (toGodement F) : C⁰F ⟶ C⁰(coker μ)`.
4. `toGodement_comp_godementCanonicalDZero`: **the start of the augmented
   complex is a complex** — `μ ≫ d⁰ = 0`, immediate instance of fact 2.

## What this Part poses vs. what it leaves open

**Posed**: the canonical-step pattern (cokernel + unit), the differential
`d⁰`, and the null-composition `μ ≫ d⁰ = 0` — the exact contrast with Part
87: for the unit iteration this equality was **false** (injective witness);
for the canonical step it is **true and proved**.

**Not posed** — named frontier of Part 90: **exactness** at `C⁰F`
(`ker d⁰ = im μ`, [God58] II.4.1), the **iteration** of the step (`d¹`, `d²`,
… and the complex structure at all degrees), and **acyclicity**
`H^n(C⁰F) = 0` for `n ≥ 1` ([God58] II.5). Each of these facts requires
ingredients (flabbiness of `C⁰F` already posed P84, monomorphism of the unit
on sheaves P84, stability of the cokernel) that remain to be assembled.

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The canonical resolution `0 → F → C⁰F → C¹F → ⋯`: each step
    passes through the cokernel of the previous arrow — the pattern posed here.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity `H^n(C⁰F) = 0` for `n ≥ 1` — named frontier of
    Part 90.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

-- **OK-CONSUMER sibling**: the declarations `godementStep`,
-- `comp_godementStep_zero`, `godementCanonicalDZero`, and
-- `toGodement_comp_godementCanonicalDZero` are imported from
-- `Grothendieck.GodementCanonicalDiff` (FR) and accessed in the
-- `Grothendieck_en` namespace as `Grothendieck.godementStep`,
-- `Grothendieck.comp_godementStep_zero`, `Grothendieck.godementCanonicalDZero`,
-- and `Grothendieck.toGodement_comp_godementCanonicalDZero`. We do not
-- redeclare them here to keep bodies byte-identical with FR (the OK-CONSUMER
-- i18n invariant of [docs/lean/i18n-sibling-patterns.md]).

-- **The canonical step in degree 0**: with `d⁰ := godementStep (toGodement F)`,
-- the augmented resolution `0 → F → C⁰F → C⁰(coker μ)` satisfies `μ ≫ d⁰ = 0`
-- (`toGodement_comp_godementCanonicalDZero`) — the complex condition that the
-- iterated unit sequence of P87 provably fails. Exactness at `C⁰F`, the
-- further differentials, and acyclicity are the named frontier of Part 90.

end Grothendieck_en
