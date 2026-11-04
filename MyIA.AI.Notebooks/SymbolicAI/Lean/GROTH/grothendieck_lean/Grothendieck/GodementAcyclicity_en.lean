/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementAcyclicity

/-!
# Iterating the Godement unit: lengthening the sequence `F → C⁰F → C⁰²F → C⁰³F`

Continuation of Parts 84-87 and next thread of the lake [God58, Chap. II §4.1].
Part 87 posed the **iterated unit sequence** `F → C⁰F → C⁰²F` (morphism
`godementUnitIter`), its injectivity witness (`godementUnit_comp_injective`)
and exactness at F (`godementUnit_injective_of_isSheaf`). This Part 88
**lengthens the sequence by one link**: the morphism `C⁰²F ⟶ C⁰³F` is the
unit re-applied at the iterated presheaf `C⁰F`. The unit sequence now has
three arrows: `F → C⁰F → C⁰²F → C⁰³F`.

## Three facts, in narrative order

1. `godementUnitIter_at_iterate`: the morphism `C⁰²F ⟶ C⁰³F` is **defined**
   as `godementUnitIter (godementPresheaf F)` — the application of the Part 87
   construction to the presheaf `C⁰F` (a legitimate presheaf on `X`). This
   definition is **type-correct**: `C⁰(C⁰F)` is also a presheaf of abelian
   groups on `X`.
2. `godementUnitIter_at_iterate_def`: the **definitional equality** —
   `godementUnitIter_at_iterate F` is by construction exactly
   `godementUnitIter (godementPresheaf F)`. This is an `rfl` equality: it
   names the link, it proves no algebraic property.
3. `godementUnitChain_extends`: the unit sequence goes from two arrows (P87)
   to three arrows (P88) — a **structural extension** by composition of
   existing morphisms.

## What this Part poses vs. what it leaves open

**Posed**: the lengthening of the unit sequence by one link, by **explicit
construction** of the morphism `C⁰²F ⟶ C⁰³F` and **identification** of the
iterated unit at the next level. The three facts above are **proved** by
re-execution of the constructions of P85 and P87 (`C⁰` is an endofunctor on
`X.Presheaf AddCommGrpCat`, and preserves morphisms).

**Not posed** — for a reason: the unit sequence is **not a complex**
(`godementUnit_comp_injective`, P87: the composite of two units is injective
on sheaves, hence non-zero on any non-zero section). Any question of
**exactness** (`ker/im`), **null-composition** or **acyclicity**
`H^n(C⁰F) = 0` for `n ≥ 1` (God58 II.5.1) first requires the **true**
differential of the canonical resolution — the one going through the cokernel
of the unit at each step ([God58] II §4.1). This is the **named frontier** of
Part 89, tracked outside this delivery.

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The canonical resolution through the cokernel of the unit,
    to be distinguished from the unit iteration posed here.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity `H^n(C⁰F) = 0` for `n ≥ 1` — **named frontier**
    of this delivery.

i18n (EPIC #4980) — OK-CONSUMER sibling: this `_en` file imports its FR
counterpart `Grothendieck.GodementAcyclicity` and re-exports the same
definitions under the `Grothendieck_en` namespace, prefixed `Grothendieck.` for
disambiguation. The proof bodies are byte-identical to the FR sibling — the
sole document is the English docstring at the top of the module.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

-- **OK-CONSUMER sibling**: the declarations `godementUnitIter_at_iterate`,
-- `godementUnitIter_at_iterate_def`, and `godementUnitChain_extends` are
-- imported from `Grothendieck.GodementAcyclicity` (FR) and accessed in the
-- `Grothendieck_en` namespace as `Grothendieck.godementUnitIter_at_iterate`,
-- `Grothendieck.godementUnitIter_at_iterate_def`, and
-- `Grothendieck.godementUnitChain_extends`. We do not redeclare them here to
-- keep bodies byte-identical with FR (the OK-CONSUMER i18n invariant of
-- [docs/lean/i18n-sibling-patterns.md]).

-- **The unit sequence at three arrows**: `F → C⁰F → C⁰²F → C⁰³F`, obtained at
-- this Part 88 (compared to the two-arrow sequence of Part 87). This is a
-- sequence of morphisms, **not** a complex — `godementUnit_comp_injective`
-- (P87) proves the composite of two units injective on sheaves, so no
-- null-composition holds. The full canonical resolution, its differential
-- (through the cokernel of the unit, [God58] II §4.1) and the acyclicity
-- `H^n(C⁰F) = 0` for `n ≥ 1` are the **named frontier** of Part 89 — not
-- part of this Part.

end Grothendieck_en
