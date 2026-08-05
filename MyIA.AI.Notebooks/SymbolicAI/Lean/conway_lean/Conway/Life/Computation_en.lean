/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Conway's Game of Life — Life-as-Computation

Cross-validation of the Hashlife quadtree algorithm against the reference
B3/S23 step, plus computational primitives (eaters, multi-period glider
composition). This module is part of Epic #1647 (Life-as-Computation).

Design choices:
- All predicates return `Bool` for computability via `decide`.
- The `eater1` (fishhook) is the simplest signal-absorbing primitive,
  the first building block of Spartan logic gates.
- Consistency theorems `evolveHashlife n g = evolve n g` verify the
  quadtree algorithm against the list-based reference for small inputs.

This module is fully proven (no gaps).
-/

import Conway.Life
import Conway.Life.MacroCell
import Conway.Life.Hashlife


/-
  English mirror of `Computation.lean` (FR canonical). Convention EPIC #4980
  (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n): distinct FR + EN sibling
  files — no inline bilingual block in a single file (Option B rejected). The module
  docstring and the public theorem docstrings below differ from the FR version; the body
  signatures, proofs and tactics remain byte-identical between the two files.
-/

namespace Conway_en
open Conway
namespace Life_en
open Life

/-! ## Section 1: Hashlife/Reference consistency

The Hashlife algorithm (`Conway.Life.Hashlife`) computes evolution via
quadtree decomposition. The reference algorithm (`step`) operates on
`List (Int × Int)` directly. The consistency theorems below verify that
both algorithms agree on canonical small patterns.

For level-2 inputs, `evolveHashlife` routes through `step4x4` (the
quadtree base case). For larger inputs, it falls back to `step`. In both
cases, the result should match `evolve n g`.

### Computability by reflection (`decide`, zero axiom) — #8869 resolved by #9536

These theorems are proved by `decide` in the kernel (zero axiom added). The
prior diagnosis (c.8126, #8749) concluded the `MacroCell` layer was
**intrinsically** opaque (and that `Int` arithmetic was non-reducible); it was
**refuted** by sub-expression bisect (c.847, 2026-08-05). The only stuck point
was `MacroCell.ceilLog2` (`WellFounded` recursion on `(k+2+1)/2`, not
structurally smaller → opaque to the kernel reducer), one level deeper than the
implicated `MacroCell` / `Int` layer. PR #9536 (merged) rewrites
`ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1` (Mathlib structural
recursion, kernel-reducible, same values, spec re-proved via
`Nat.lt_pow_succ_log_self` + `omega`). After this fix, these theorems pass
`decide` (kernel, zero axiom), removing the `native_decide` axioms from the
trusted computing base. Native `#eval` witnesses in section 5.
-/

/-- Hashlife and reference agree on `block` after 1 generation.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_block_1 : evolveHashlife 1 block = evolve 1 block := by decide

/-- Hashlife and reference agree on `block` after 4 generations.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_block_4 : evolveHashlife 4 block = evolve 4 block := by decide

/-- Hashlife and reference agree on `blinker_h` after 2 generations.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_blinker_2 : evolveHashlife 2 blinker_h = evolve 2 blinker_h := by decide

/-- Hashlife and reference agree on `glider` after 4 generations.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_glider_4 : evolveHashlife 4 glider = evolve 4 glider := by decide

/-- Hashlife and reference agree on `beacon` after 2 generations.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_beacon_2 : evolveHashlife 2 beacon = evolve 2 beacon := by decide

/-- Hashlife and reference agree on `toad` after 2 generations.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_toad_2 : evolveHashlife 2 toad = evolve 2 toad := by decide

/-! ## Section 2: Eater 1 (Fishhook) — the simplest computational sink

The **eater 1** (also called "fishhook") is a 7-cell still life discovered
by members of Conway's group at Cambridge in 1971. It is the canonical
signal-absorbing primitive in Life-as-Computation constructions: its
boundary "swallows" incoming gliders within ~4 generations, returning to
its original form.

In Spartan logic (Rendell 2000, Goucher 2014), eaters serve as:
- Signal sinks at gate outputs
- Boundary stabilisers in metapixel construction
- Absorbers at wire terminations

Coordinate layout (top-left = (0,0)):
```
XX..
X.X.
..X.
..XX
```

### `isStillLife eater1` — proven by `decide` in the kernel (zero axioms)

After the `mergeSort -> insertionSort` swap (#8895, 2026-07-30), `isStillLife eater1`
reduces under `decide`: the static check (still life, no evolution) exercises only the
`sortDedup` sort on a fixed grid, now decide-reducible. `#print axioms
Conway.Life.eater1_still_life` is empty (zero axioms) — a purely computational kernel
proof. (The #8749 probe of 2026-07-29, prior to #8895, correctly observed the
obstruction under `mergeSort`; it has since been lifted.)

As with the `evolveHashlife n g = evolve n g` equivalences of Section 1, this
theorem is proved by `decide` in the kernel (zero axiom). Historically,
`eater1_still_life` became `decide`-reducible with the `mergeSort -> insertionSort`
swap (#8895), whereas the Section 1 equivalences additionally required rewriting
`ceilLog2` via `Nat.log 2` (#9536): as long as it was a `WellFounded` recursion
opaque to the reducer, they remained `native_decide`. The historical pre-#9536
contrast is documented in Section 1.
-/

/-- The **eater 1** (fishhook), a 7-cell still life. -/
def eater1 : Grid :=
  [(0, 0), (0, 1),
   (1, 0), (1, 2),
   (2, 2),
   (3, 2), (3, 3)]

#eval s!"Eater 1: {eater1}"
#eval s!"step(eater1) = {step eater1}"
#eval s!"isStillLife eater1 = {isStillLife eater1}"

/-- The eater 1 is a still life. Proven by `decide` in the kernel
    (zero axioms, `#print axioms` empty) — `isStillLife` on a fixed grid,
    decide-reducible post-#8895 (criterion 2 of #8869). -/
theorem eater1_still_life : isStillLife eater1 = true := by decide

/-! ## Section 3: Glider composition via multi-period evolution

The glider has period 4 and displacement `(1, -1)` per period. After
`4 * k` generations, it should equal `shift (k, -k) glider`. This
multi-period composition is the basis of signal propagation along
glider wires.

We verify for k = 1 (already in Life.lean), k = 2, and k = 3.
The k = 2 case (8 generations) also verifies via `evolveHashlife`.

### Computability by reflection (`decide`, zero axiom) — #8869 resolved by #9536

These theorems are proved by `decide` in the kernel (zero axiom added). The
prior diagnosis (c.8126, #8749) concluded the `MacroCell` layer was
**intrinsically** opaque (and that `Int` arithmetic was non-reducible); it was
**refuted** by sub-expression bisect (c.847, 2026-08-05). The only stuck point
was `MacroCell.ceilLog2` (`WellFounded` recursion on `(k+2+1)/2`, not
structurally smaller → opaque to the kernel reducer), one level deeper than the
implicated `MacroCell` / `Int` layer. PR #9536 (merged) rewrites
`ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1` (Mathlib structural
recursion, kernel-reducible, same values, spec re-proved via
`Nat.lt_pow_succ_log_self` + `omega`). After this fix, these theorems pass
`decide` (kernel, zero axiom), removing the `native_decide` axioms from the
trusted computing base. Native `#eval` witnesses in section 5.
-/

/-- After 8 generations (2 periods), the glider has shifted by (2, -2).
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem glider_2periods : evolve 8 glider = shift (2, -2) glider := by decide

/-- After 12 generations (3 periods), the glider has shifted by (3, -3).
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem glider_3periods : evolve 12 glider = shift (3, -3) glider := by decide

/-- Hashlife and reference agree on glider after 8 generations (2 periods).
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_glider_8 : evolveHashlife 8 glider = evolve 8 glider := by decide

/-! ## Section 4: MacroCell round-trip verification

Structural sanity check: the `Grid → MacroCell → Grid` round-trip
preserves live cells for canonical patterns. This verifies the quadtree
encoding/decoding at the MacroCell layer (independent of step/evolve).

### Computability by reflection (`decide`, zero axiom) — #8869 resolved by #9536

These theorems are proved by `decide` in the kernel (zero axiom added). The
prior diagnosis (c.8126, #8749) concluded the `MacroCell` layer was
**intrinsically** opaque (and that `Int` arithmetic was non-reducible); it was
**refuted** by sub-expression bisect (c.847, 2026-08-05). The only stuck point
was `MacroCell.ceilLog2` (`WellFounded` recursion on `(k+2+1)/2`, not
structurally smaller → opaque to the kernel reducer), one level deeper than the
implicated `MacroCell` / `Int` layer. PR #9536 (merged) rewrites
`ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1` (Mathlib structural
recursion, kernel-reducible, same values, spec re-proved via
`Nat.lt_pow_succ_log_self` + `omega`). After this fix, these theorems pass
`decide` (kernel, zero axiom), removing the `native_decide` axioms from the
trusted computing base. Native `#eval` witnesses in section 5.
-/

/-- Block survives the MacroCell round-trip. `decide` in the kernel, zero axiom
    — reducible after the `ceilLog2` fix (#9536, #8869). -/
theorem block_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset block
     mc.toGrid off == block) = true := by decide

/-- Glider survives the MacroCell round-trip. `decide` in the kernel, zero axiom
    — reducible after the `ceilLog2` fix (#9536, #8869). -/
theorem glider_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset glider
     mc.toGrid off == glider) = true := by decide

/-- Eater 1 survives the MacroCell round-trip. `decide` in the kernel, zero axiom
    — reducible after the `ceilLog2` fix (#9536, #8869). -/
theorem eater1_macrocell_roundtrip :
    (let (off, mc) := gridToMacroCellWithOffset eater1
     mc.toGrid off == eater1) = true := by decide

/-! ## Section 5: Diagnostic #eval witnesses

Larger computational witnesses verified by `#eval` (kernel evaluation)
rather than `native_decide` (kernel reduction). These demonstrate that
the Hashlife pipeline works on larger inputs and multi-step evolutions.
-/

-- Glider meets eater: after 8 steps, the combined configuration evolves
-- (no claim about exact absorption — that depends on precise geometry).
def glider_meets_eater : Grid :=
  sortDedup (glider ++ (eater1.map (fun p => (p.1, p.2 + 6))))

#eval s!"glider + eater combined: {glider_meets_eater.length} cells"
#eval s!"After 4 steps: {(evolve 4 glider_meets_eater).length} cells"
#eval s!"After 8 steps: {(evolve 8 glider_meets_eater).length} cells"

-- Cross-check: Hashlife vs reference on multi-step glider
#eval evolveHashlife 0 glider == glider
#eval evolveHashlife 1 glider == evolve 1 glider
#eval evolveHashlife 4 glider == evolve 4 glider
#eval evolveHashlife 8 glider == evolve 8 glider

-- Hashlife on the eater (still life = no change at every step)
#eval evolveHashlife 10 eater1 == eater1

/-! ## Section 6: Exponential-speedup Hashlife validation

`evolveHashlifeFast` uses the recursive Hashlife algorithm to jump
forward by `2^level` generations in a single MacroCell step. These
theorems verify correctness of the fast path against the reference
`evolve` for canonical patterns.

### Computability by reflection (`decide`, zero axiom) — #8869 resolved by #9536

These theorems are proved by `decide` in the kernel (zero axiom added). The
prior diagnosis (c.8126, #8749) concluded the `MacroCell` layer was
**intrinsically** opaque (and that `Int` arithmetic was non-reducible); it was
**refuted** by sub-expression bisect (c.847, 2026-08-05). The only stuck point
was `MacroCell.ceilLog2` (`WellFounded` recursion on `(k+2+1)/2`, not
structurally smaller → opaque to the kernel reducer), one level deeper than the
implicated `MacroCell` / `Int` layer. PR #9536 (merged) rewrites
`ceilLog2 k = if k ≤ 1 then 0 else Nat.log 2 (k-1) + 1` (Mathlib structural
recursion, kernel-reducible, same values, spec re-proved via
`Nat.lt_pow_succ_log_self` + `omega`). After this fix, these theorems pass
`decide` (kernel, zero axiom), removing the `native_decide` axioms from the
trusted computing base. Native `#eval` witnesses in section 5.
-/

/-- `evolveHashlifeFast` agrees with reference on block after 4 gens.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_fast_block_4 : evolveHashlifeFast 4 block = evolve 4 block := by decide

/-- `evolveHashlifeFast` agrees with reference on glider after 4 gens.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_fast_glider_4 : evolveHashlifeFast 4 glider = evolve 4 glider := by decide

/-- `evolveHashlifeFast` agrees with reference on glider after 8 gens
    (2 full periods, displacement (2, -2)). `decide` in the kernel, zero axiom — reducible
    after the `ceilLog2` fix (#9536, #8869). -/
theorem hashlife_fast_glider_8 : evolveHashlifeFast 8 glider = shift (2, -2) glider := by decide

/-- `evolveHashlifeFast` agrees with reference on blinker after 2 gens.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_fast_blinker_2 : evolveHashlifeFast 2 blinker_h = evolve 2 blinker_h := by decide

/-- `evolveHashlifeFast` agrees with reference on beacon after 2 gens.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_fast_beacon_2 : evolveHashlifeFast 2 beacon = evolve 2 beacon := by decide

/-- `evolveHashlifeFast` agrees with reference on toad after 2 gens.
    (`decide` in the kernel, zero axiom — reducible after the `ceilLog2` fix #9536, #8869.) -/
theorem hashlife_fast_toad_2 : evolveHashlifeFast 2 toad = evolve 2 toad := by decide

-- #eval witnesses for larger jumps (validates the recursive path)
#eval evolveHashlifeFast 16 block == evolve 16 block
#eval evolveHashlifeFast 12 glider == shift (3, -3) glider
#eval evolveHashlifeFast 4 blinker_h == blinker_h  -- period 2, 4 = 2 periods
#eval evolveHashlifeFast 10 eater1 == eater1  -- still life

end Life_en
end Conway_en
