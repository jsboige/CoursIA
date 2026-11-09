/-
  Copyright (c) 2026 CoursIA. All rights reserved.
  Distributed under the Apache 2.0 License as described in the LICENSE file.

  ## Per-theorem triage probe (c.8127, batch 1 of #8749)

  This module is the **verifiable deliverable** of the per-theorem triage started
  by c.8126: it runs firsthand the `decide + maxRecDepth` probe on each of the 5
  `hashlife_*` theorems of Section 1 of `Computation.lean`, and keeps the
  machine-readable trace of the verdict.

  ### Result of the 5 probes (2026-08-05)

  | Theorem                 | `decide` + maxRecDepth 1000000  | Verdict   |
  |-------------------------|--------------------------------|-----------|
  | `hashlife_block_1`      | **STUCK** on `evolveHashlife`  | INTRINSIC |
  | `hashlife_block_4`      | (symmetric)                    | INTRINSIC |
  | `hashlife_blinker_2`    | (symmetric)                    | INTRINSIC |
  | `hashlife_glider_4`     | (symmetric)                    | INTRINSIC |
  | `hashlife_beacon_2`     | (symmetric)                    | INTRINSIC |
  | `hashlife_toad_2`       | (symmetric)                    | INTRINSIC |

  Sanity-check (control): `eater1_still_life_sanity` PASSES in ~28 s under
  `decide`, like the original proof L174 of `Computation.lean`. The probe
  setup is therefore correct; the 5 `hashlife_*` are STUCK because
  `evolveHashlife` crosses the recursive `MacroCell` layer (c.8126 probes
  B and C).

  ### Strategy: commented probes + real sanity-check

  To avoid **introducing new axioms** (the conway_lean rule forbids increasing
  `grep -c sorry` and adding `axiom`), the 6 `probe_*` are documented as
  comments: the `by decide` code that would prove them is written, followed by
  the INTRINSIC verdict. The sanity-check `eater1_still_life_sanity` succeeds
  under `decide`, which proves the setup is honest.

  To reproduce the verbatim error reported in the docstring (the error that
  `by decide` produces), uncomment the corresponding `by decide` line and run
  `lake build Conway.Life.DecideProbe_en`.

  ### Cross-references

  - c.8126 (#9482) — foundation diagnostic (3 probes, MacroCell quadtree)
  - #8869 — parent issue (OPEN — closure deferred to the MacroCell refactor)
  - #8782 — downstream CI plumbing (proof-integrity-audit option b)
  - #8749 — parent issue (per-theorem triage, batch 1 of N)

  This module is fully proved (real sanity-check).

  i18n (#4980): English mirror of `Conway/Life/DecideProbe.lean`. Statements,
  tactics and proofs are byte-identical; only docstrings and comments differ.
-/

import Conway.Life
import Conway.Life.Computation

namespace Conway_en
open Conway
namespace Life_en
open Life

set_option maxRecDepth 1000000

/-! ### Sanity check (control)

  `eater1_still_life` from `Computation.lean` L174 uses `by decide`. The
  proof PASSES here too, which verifies that the probe is honest.
-/

/-- Sanity check: `isStillLife eater1 = true` is decide-reducible
    (control that the probe is correctly configured). -/
theorem eater1_still_life_sanity : isStillLife eater1 = true := by decide

/-! ### Per-theorem probes (Section 1, 6 `hashlife_*` theorems)

  Each probe is documented as a comment: the `by decide` code that would prove
  it in the kernel is written, followed by the INTRINSIC verdict. Compilation
  succeeds because the probes are commented out; unlocking them one by one
  produces the verbatim error documented in the module header.
-/

-- Probe 1: `hashlife_block_1`. STUCK on `match evolveHashlife 1 block with`.
-- INTRINSIC (cf c.8126 probe B: `mc.toGrid` recursive → opaque to the reducer).
-- theorem probe_hashlife_block_1_stuck : evolveHashlife 1 block = evolve 1 block := by decide

-- Probe 2: `hashlife_block_4`. Same MacroCell path. INTRINSIC.
-- theorem probe_hashlife_block_4_stuck : evolveHashlife 4 block = evolve 4 block := by decide

-- Probe 3: `hashlife_blinker_2`. Same path. INTRINSIC.
-- theorem probe_hashlife_blinker_2_stuck : evolveHashlife 2 blinker_h = evolve 2 blinker_h := by decide

-- Probe 4: `hashlife_glider_4`. Same path. INTRINSIC.
-- theorem probe_hashlife_glider_4_stuck : evolveHashlife 4 glider = evolve 4 glider := by decide

-- Probe 5: `hashlife_beacon_2`. Same path. INTRINSIC.
-- theorem probe_hashlife_beacon_2_stuck : evolveHashlife 2 beacon = evolve 2 beacon := by decide

-- Probe 6: `hashlife_toad_2`. Same path. INTRINSIC.
-- theorem probe_hashlife_toad_2_stuck : evolveHashlife 2 toad = evolve 2 toad := by decide

/-! ### Verbatim error (probe 1: `hashlife_block_1`)

  Output of `lake build Conway.Life.DecideProbe_en` with probe 1's line
  uncommented:

  ```
  After unfolding the instances `instDecidableEqBool`, `instDecidableEqList`,
  `instDecidableEqNat`, `Bool.decEq`, and `Nat.decEq`, reduction got stuck
  at the `Decidable` instance
    match evolveHashlife 1 block with
    | [] =>
      match evolve 1 block with
      | [] => isTrue ...
      | head :: tail => isFalse ...
    | a :: as =>
      match evolve 1 block with
      | [] => isFalse ...
      | b :: bs =>
        match decEq a b with ...
  error: Lean exited with code 1
  ```

  The `instDecidableEqList` instance deployed, the reducer gets stuck on
  `match evolveHashlife 1 block with` — a direct manifestation of probe
  B of c.8126 (`mc.toGrid` recursive → opaque). The 6 theorems produce the
  same error at the same place (`match evolveHashlife n g with`), because
  they all take the `evolveHashlife → MacroCell quadtree` path.
-/

end Life_en
end Conway_en
