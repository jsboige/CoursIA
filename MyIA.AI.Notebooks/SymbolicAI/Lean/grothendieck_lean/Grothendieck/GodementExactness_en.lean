/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementExactness

/-!
# The augmented Godement complex: d¹, the mono of the unit, the separatedness of the cokernel

Part 90 — the announced continuation of Part 89. The latter posed the canonical
step `godementStep f := cokernel.π f ≫ toGodement (coker f)` and the differential
`d⁰ := godementCanonicalDZero` with its null-composition `μ ≫ d⁰ = 0`. This
Part takes two more steps on the same thread (the third — the **reduction of
exactness** — has been withdrawn : see the author's note at the end of the
namespace). **Part 91 opens its step A here** : the separatedness of the
cokernel of the unit, proved at the end of the module.

## Two facts, in the order of the narrative

1. `godementCanonicalDOne` : the **degree-1 differential** — the canonical step
   applied to `d⁰`. The next term `C²F := C⁰(coker d⁰)` is the Godement
   presheaf of the cokernel of `d⁰`, and `d¹ : C¹F ⟶ C²F` is the connecting
   arrow. The null-composition `d⁰ ≫ d¹ = 0`
   (`godementCanonicalDZero_comp_godementCanonicalDOne`) is an instance of
   `comp_godementStep_zero` (P89) : **the canonical resolution is a complex
   beyond degree 0** — each degree is obtained by applying the canonical step
   to the previous differential, and the null-composition is free at each
   step.
2. `mono_toGodement_of_isSheaf` : **the Godement unit is a categorical
   monomorphism on sheaves**. Part 84 had proved the injectivity section by
   section (`godementUnit_injective_of_isSheaf`) ; this fact is its categorical
   ascent : mono in the category of presheaves, via
   `NatTrans.mono_iff_mono_app` (the mono of a natural transformation between
   presheaves of abelian groups is exactly the pointwise mono). It is the
   exactness of `0 → F → C⁰F` **at F**, now stated in the language of complexes.

## What this Part poses vs. what it leaves open

**Posed** : the complex at degrees 0 and 1 (and the iteration pattern that
extends to all degrees), and the categorical mono of the unit on sheaves.

**Not posed** — named frontier of Part 91 : the **reduction of exactness at
`C⁰F` to the mono of the cokernel's unit**
(`exact_toGodement_godementCanonicalDZero_of_mono`), whose ingredient — the
**separatedness of the cokernel** `coker μ` for `F` sheaf — is now **proved in
this module** (step A, below : gluing of local sections of the quotient via
separatedness of `F` and injectivity of `μ`). Remaining are **step B** (from
separatedness to the mono of `toGodement (coker μ)`, then to `Exact μ d⁰`),
the **complete iteration** of the reduction to higher degrees, and the
**acyclicity** `H^n(C⁰F) = 0` for `n ≥ 1` ([God58] II.5).

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The canonical resolution `0 → F → C⁰F → C¹F → ⋯` : complex
    (d⁰ ≫ d¹ = 0) and exactness at `C⁰F` — reduced here to the mono of the
    cokernel's unit.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity — named frontier of Part 91.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

-- **OK-CONSUMER sibling**: the declarations `godementCanonicalDOne`,
-- `godementCanonicalDZero_comp_godementCanonicalDOne`, and
-- `mono_toGodement_of_isSheaf` are imported from
-- `Grothendieck.GodementExactness` (FR) and accessed in the `Grothendieck_en`
-- namespace as `Grothendieck.godementCanonicalDOne`, etc. We do not redeclare
-- them here to keep bodies byte-identical with FR (the OK-CONSUMER i18n
-- invariant of [docs/lean/i18n-sibling-patterns.md]).

-- **The complex beyond degree 0** : with `d¹ := godementCanonicalDOne F` and
-- the null-composition `d⁰ ≫ d¹ = 0`
-- (`godementCanonicalDZero_comp_godementCanonicalDOne`), the canonical resolution
-- extends to a chain complex. **The unit on sheaves is mono**
-- (`mono_toGodement_of_isSheaf`) — the categorical ascent of Part 84's
-- pointwise injectivity. The draft r65 of Part 90 carried the exactness
-- reduction with a `sorry` tactical proof; the gate `proof-integrity` of the
-- caller workflow elevated that `sorry` to a `sorryAx` transitive at import
-- (forbidden axiom, pr-review-discipline §B), and the honest option was the
-- **withdrawal** of the statement from that Part. Part 91 picks the thread
-- back up in two steps, **the first of which is closed in this module**.

-- **Part 91, step A (landed in the FR twin of this module)** :
-- `Grothendieck.eq_zero_of_locally_zero_cokernel_toGodement` — for `F` a
-- sheaf, a section `s` of `coker μ` whose restriction to every open of a
-- covering family `V` of `U` vanishes is zero. The cokernel is not a sheaf
-- in general — but it remains **separated**, which is all that step B (the
-- reduction of exactness at `C⁰F` to the mono of the cokernel's unit) will
-- require. The proof transposes the gluing of Part 84 to the quotient: lift
-- `s` to a Godement section (sectionwise surjectivity of the cokernel
-- projection, via `coequalizer.π_epi` + `NatTrans.epi_iff_epi_app` +
-- `AddCommGrpCat.epi_iff_surjective`), lift back locally through the
-- quotient-presheaf descent `C⁰F ⟶ C⁰F/im μ`
-- (`exists_of_cokernelπ_app_eq_zero`, private — the pointwise quotient
-- presheaf and its cokernel descent bridge the presheaf-level projection to
-- the algebraic quotient, section by section), prove compatibility on
-- intersections by injectivity of the unit (P84), glue via the sheaf
-- condition and uniqueness of gluing in `C⁰F`, conclude by the cokernel
-- condition. Step B — from separatedness to `Mono (toGodement (coker μ))`,
-- then `Exact μ d⁰` — remains the open frontier.

end Grothendieck_en
