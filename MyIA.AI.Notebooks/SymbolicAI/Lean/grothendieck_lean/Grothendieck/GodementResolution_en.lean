/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Grothendieck.GodementResolution

/-!
# The iterated unit sequence `F → C⁰F → C⁰²F → ⋯` — and why it is not
the canonical resolution

Continuation of Part 86 and next thread of the lake [God58, Chap. II §4.1]. Part 86
closed the prerequisite named by Part 85: `C⁰` preserves monomorphisms
(`godementFunctor_preservesMonomorphisms`). With the flasquity of `C⁰F`
(`isFlasque_godementPresheaf`, P84) and the injectivity of `F → C⁰F` on
sheaves (`injective_toGodement_of_isSheaf`, P84), this module poses the
**iterated unit sequence** of a presheaf `F` of abelian groups on `X`:

```
  F --μ--> C⁰F --μ(C⁰F)--> C⁰²F --μ(C⁰²F)--> C⁰³F → ⋯
```

where every arrow is the unit `toGodement` evaluated at the source presheaf:
the second arrow, `godementUnitIter`, is exactly `toGodement (F := C⁰F)`, the
unit re-applied.

## What this sequence is not

This sequence of morphisms is **not** a complex, hence not the canonical
Godement resolution. The theorem `godementUnit_comp_injective` below shows it:
on a sheaf `F`, the composite `μ ≫ μ(C⁰F)` is **injective** on every open —
the composite of the unit (injective on sheaves, P84) and the re-applied unit
(injective without hypothesis, since `C⁰F` is always a sheaf, P84). On a
non-zero section the composite stays non-zero (elementary witness: one point,
the constant sheaf `ℤ`, the section `1`). The equality `μ ≫ d⁰ = 0` required
of a differential is therefore not an open statement nor a postponed proof:
it is **false** for this morphism.

The canonical construction of [God58, Chap. II §4.1] goes at each step through
the **cokernel of the unit** and its embedding into the next Godement term;
re-applying the unit without this cokernel does not replace it. Building the
true differential of the canonical resolution (via `coker μ`) is the **named
frontier** treated in Part 89.

## What this module poses, honestly

1. `godementUnitIter`: the second arrow `C⁰F ⟶ C⁰²F`, defined as
   `toGodement (F := C⁰F)` — the re-applied unit, named for what it is.
   (The alias `godementDZero` of the first versions of this PR, which called
   it a "degree-0 differential", is withdrawn: the name was mathematically
   unfaithful, and no proof depended on it.)
2. `godementUnit_comp_injective`: the **witness** described above — the
   composite `μ ≫ μ(C⁰F)` is injective on sheaves, so the unit sequence
   admits no complex-like null-composition.
3. `godementUnit_injective_of_isSheaf`: injectivity of `μ` on sheaves
   (`injective_toGodement_of_isSheaf`, P84, replayed) — the exactness of
   `0 → F → C⁰F` **at F**, the only exactness fact posed at this stage.

i18n (EPIC #4980) — OK-CONSUMER sibling: this `_en` file imports its FR
counterpart `Grothendieck.GodementResolution` and re-exports the same
definitions under the `Grothendieck_en` namespace, prefixed `Grothendieck.` for
disambiguation. The proof bodies are byte-identical to the FR sibling — the
sole document is the English docstring at the top of the module.

## References

  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §4.1. The canonical resolution `0 → F → C⁰F → C¹F → ⋯`, each step
    of which goes through the cokernel of the unit.
  - R. Godement, *Topologie algébrique et théorie des faisceaux* [God58],
    Chap. II §5. Acyclicity `H^n(C⁰F) = 0` for `n ≥ 1`, frontier of Part 89.
-/

universe u

open CategoryTheory Category Limits TopCat TopologicalSpace Opposite

namespace Grothendieck_en

variable {X : TopCat.{u}}

-- **OK-CONSUMER sibling**: the declarations `godementUnitIter`,
-- `godementUnit_comp_injective`, and `godementUnit_injective_of_isSheaf`
-- are imported from `Grothendieck.GodementResolution` (FR) and accessed in
-- the `Grothendieck_en` namespace as `Grothendieck.godementUnitIter`,
-- `Grothendieck.godementUnit_comp_injective`, and
-- `Grothendieck.godementUnit_injective_of_isSheaf`. We do not redeclare them
-- here to keep bodies byte-identical with FR (the OK-CONSUMER i18n invariant
-- of [docs/lean/i18n-sibling-patterns.md]).

-- **The iterated unit sequence at degree 1**: `F --μ→ C⁰F --μ(C⁰F)→ C⁰²F`,
-- with `μ := toGodement F` (the unit of `C⁰`) and `μ(C⁰F) := godementUnitIter F`
-- (the unit re-applied to `C⁰F`). This is a sequence of morphisms, **not** a
-- complex: `godementUnit_comp_injective` proves the composite injective on
-- sheaves, so `μ ≫ μ(C⁰F) = 0` is false in general.
--
-- **NOTE**: no `ShortComplex` is posed in the FR companion module — the field
-- `zero : f ≫ g = 0` cannot hold for this composite, which is exactly what
-- the witness theorem proves. The true differential of the canonical
-- resolution (through the cokernel of the unit, [God58] II §4.1) is the
-- named frontier of Part 89. The EN sibling therefore re-exports neither a
-- `ShortComplex` nor a null-composition statement.

-- **Injectivity at F** is inherited from
-- `Grothendieck.godementUnit_injective_of_isSheaf` via the OK-CONSUMER import
-- — for every open `U`, the morphism `(toGodement F).app (op U) : F(U) ⟶ C⁰F(U)`
-- is injective when `F` is a sheaf. This is the only exactness fact posed:
-- exactness at the term `C⁰F` (and acyclicity `H¹ = 0`) requires the true
-- differential of the canonical resolution — Part 89.

end Grothendieck_en
