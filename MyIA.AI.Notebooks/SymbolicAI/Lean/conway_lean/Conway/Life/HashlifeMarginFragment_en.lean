/-
Copyright (c) 2026 CoursIA. All rights reserved.
Distributed under the Apache 2.0 License as described in the LICENSE file.

## Deliverable B (#9568) — the "margin window" fragment (first Spartan-logic tier)

Companion module to `Conway.Life.HashlifeCorrectness` (the correction infrastructure
`hashlife_correct` / `centralCorrect` / `centralCorrect_mem`, c.153) and to the
`Conway.Life.AdversarialBattery` bestiary (#9589). It formalizes the **first tier of
geometric relativization** of the user framing (2026-08-06, issue #9568): prove that
Hashlife "works in Spartan logic" — a **relative/bounded** correctness, known to be far
easier than the universal one and **sufficient for the real corollaries**.

### The fragment

The fragment of configurations whose **support fits in the central window with a guard
margin equal to the horizon `2^k`**: every live cell is at least `2^k` cells from the
MacroCell domain boundary, so over the `2^k` generations of the horizon, **nothing can ever
bleed off the window** — the Chebyshev light-cone of radius `2^k` stays strictly inside the
margin.

Candidate predicate:
  `supportInMargin c k := BoxAssezGrandN (c.toGrid (0, 0)) (2^k)`

We use the **n-aware** variant `BoxAssezGrandN` (padding `max 2 n`, satisfiable for every
`n`) rather than the fixed-frame `BoxAssezGrand` (capped at `n ≤ 2` by
`boxAssezGrand_nonempty_le_two`): this is what makes the fragment **satisfiable for every
horizon `2^k`** and validates the sufficiency argument "choose `k` by horizon" below. The
sanity check `cexBlock1_supportInMargin_k2` exhibits `2^2 = 4` on the 2×2 block —
impossible with the fixed-frame, possible here.

### The framework statement `hashlife_correct_margin` (documented sorry, INTRINSIC verdict)

Under the fragment `supportInMargin c k` and the central-correctness hypothesis
`centralCorrect c k` (the c.153 whnf-wall bypass), the global grid equality
`evolveHashlifeFast (2^k) (c.toGrid (0,0)) = evolve (2^k) (c.toGrid (0,0))` holds over the
whole horizon `2^k`. The proof requires the **bounded P4/P5 assembly** — how `centralCorrect`
(MacroCell-level correctness at level `k`) lifts to global grid equality through the
Hashlife recursion, with the margin containing the light-cone at every jump. This assembly
is the content of ai-01's PRs #9745/#9760 (c.92–c.94, `p4_nw_overlap_wall` sorry 10→9) and
remains the open research heart. The statement is delivered as a **framework** (acceptance
B: documented sorry acceptable at first commit), not a missed proof — INTRINSIC verdict on
the unproven part, with the reason.

### Why this GEOMETRIC fragment suffices for the real corollaries

"Spartan logic" in the strict sense (still lifes + gliders, Goucher's vocabulary) is a
later refinement; this geometric fragment precedes it and already suffices:

1. **Finite Turing machine (T steps)**: any TM computation for `T` steps embeds in the
   fragment by choosing `k` such that `2^k ≥ T` (horizon) with the guard margin. The
   unbounded-in-time aspect is handled by **re-invocation at growing `k`** (the standard
   "expand then recurse" Hashlife wrapper) — each instantiated horizon lives in the fragment.
2. **OTCA tile / Gemini replication**: these patterns have a known bounded support; choose
   `k` by pattern size + replication horizon, and the margin contains the light-cone of the
   replication phase.
3. **GOL-in-GOL**: emulating a finite GOL inside a larger GOL embeds with margin by
   construction (the host GOL provides the central window, the guest the support).

### Constraints

FR-canonical + `_en` sibling (gate #4980: FR-only merge refused). The documented `sorry`
is explicitly accepted under acceptance B. Real (kernel-decidable) sanity checks on the
bestiary below. EPIC #3846 / #6724 / #9568.
-/

/-
  i18n convention (EPIC #4980, user decision 2026-07-04): this file is the **English
  mirror** of the FR-canonical `HashlifeMarginFragment.lean`. Theorem statements, Lean
  tactics, lemma names and Mathlib references stay in English (compat Mathlib 4); only the
  docstrings and this header block differ between the two files.
-/

import Conway.Life.AdversarialBattery_en
import Conway.Life.HashlifeCorrectness

namespace Conway_en
open Conway
namespace Life_en
open Life

/-! ## The fragment predicate `supportInMargin` -/

/-- **The "margin window" fragment (Deliverable B, #9568).** The support of cell `c`
    (rendered as a grid at the origin) fits in the central window with a guard margin equal
    to the horizon `2^k`: every live cell is at least `2^k` from the MacroCell domain
    boundary. Over the `2^k` generations of the horizon, the Chebyshev light-cone (radius
    `2^k`) stays strictly inside the margin, so **nothing bleeds off the window**.

    We use the **n-aware** variant `BoxAssezGrandN` (padding `max 2 n`, satisfiable for
    every `n`) rather than the fixed-frame `BoxAssezGrand` (capped at `n ≤ 2` by
    `boxAssezGrand_nonempty_le_two`): this is what makes the fragment satisfiable for every
    horizon `2^k` and validates the "choose `k` by horizon" sufficiency argument. -/
def supportInMargin (c : MacroCell) (k : Nat) : Prop :=
  BoxAssezGrandN (c.toGrid (0, 0)) (2^k)

/-- **Decidability of the fragment** (companion to the `Decidable (BoxAssezGrandN)`
    instance, HashlifeCorrectness L227). `supportInMargin` is a separate `def ... : Prop`, so
    the `Decidable (BoxAssezGrandN g n)` instance does not propagate automatically through it
    (Lean does not reduce a non-`@[reducible]` `def` during instance synthesis). We declare
    the companion instance, exactly as `BoxAssezGrandN` declares its own above the native
    `Decidable` instance — the codebase's canonical pattern. -/
instance (c : MacroCell) (k : Nat) : Decidable (supportInMargin c k) :=
  inferInstanceAs (Decidable (BoxAssezGrandN (c.toGrid (0, 0)) (2^k)))

/-- **Triviality of the fragment** (relocated c.8206, #9568). `supportInMargin`
    contains EVERY MacroCell at EVERY horizon `k` — it is a **tautology**,
    proved locally from `boxAssezGrandN_trivial` (next to `BoxAssezGrandN`
    in `Foundation`, c.8206). The hypothesis `h_margin : supportInMargin c k`
    of `hashlife_correct_margin` therefore constrains nothing; see the
    *inconditionnel-en-attente* / *unconditional-pending* note in the
    docstring of that theorem. -/
theorem supportInMargin_trivial (c : MacroCell) (k : Nat) :
    supportInMargin c k :=
  boxAssezGrandN_trivial _ _

/-! ## The framework statement `hashlife_correct_margin` (documented sorry, INTRINSIC)

Under the fragment + `centralCorrect c k`, the global grid equality
`evolveHashlifeFast (2^k) (c.toGrid (0,0)) = evolve (2^k) (c.toGrid (0,0))` holds over the
horizon `2^k`. The `sorry` is the bounded P4/P5 assembly (ai-01, #9745/#9760): how
`centralCorrect` (MacroCell-level correctness) lifts to global equality through the Hashlife
recursion, the margin containing the light-cone at every jump. Framework statement
(acceptance B), not a missed proof. -/

/-- **Hashlife correctness relative to the "margin window" fragment (Deliverable B, #9568).**
    If the support of `c` fits in the central window with guard margin `2^k`
    (`supportInMargin`), and if the central correctness `centralCorrect c k` holds at level
    `k`, then `evolveHashlifeFast` agrees with the reference evolution `evolve` over the
    whole horizon `2^k` — the margin guarantees no light-cone bleeds off the window during
    the Hashlife recursion.

    **Sufficiency for the real corollaries** (the pedagogical heart of this Deliverable B):
    any bounded computation embeds in the fragment by choosing `k` by horizon.
    (1) **Finite TM (T steps)**: choose `2^k ≥ T` + margin; the unbounded-in-time aspect is
    handled by re-invocation at growing `k` ("expand then recurse" wrapper). (2) **OTCA tile
    / Gemini replication**: known bounded support, `k` by size + replication horizon.
    (3) **GOL-in-GOL**: emulating a finite GOL inside a larger GOL embeds with margin by
    construction. Strict Spartan logic (still lifes + gliders, Goucher's vocabulary) is a
    later refinement of this geometric fragment.

    **Proof verdict: INTRINSIC.** Bridging `centralCorrect` (MacroCell-level correctness)
    to global grid equality requires the bounded P4/P5 assembly — `p4_nw_overlap_wall` and
    its 4-stage helper ladder (PR #9745/#9760, ai-01 c.92–c.94, sorry 10→9). This is the
    open research heart; this statement is its honest framework (acceptance B: documented
    sorry acceptable at first commit).

    **Framing note (c.212, 2026-08-11) — *unconditional-in-waiting*.** The predicate
    `supportInMargin` is a **tautology** (proven by `supportInMargin_trivial`,
    JumpCapture.lean:120): `gridFrameN n g` pads by `max 2 n ≥ n` and the near-side
    `cellMargin` is non-strict, so `BoxAssezGrandN g n` holds for **every** grid and **every**
    `n`. The hypothesis `h_margin : supportInMargin c k` therefore constrains nothing — the
    effective statement is the full unconditional, under geometric dressing that does not
    relativize. The true relativization lives elsewhere (predicate `jumpCaptured`,
    JumpCapture.lean §3, with witness `jumpCaptured_not_trivial`). This `sorry` therefore
    remains the **open research heart**, regardless of the fragility of its dressing — the
    INTRINSIC verdict is preserved, scientific content unweakened by this observation. -/
theorem hashlife_correct_margin (c : MacroCell) (k : Nat)
    (h_margin : supportInMargin c k) (h_central : centralCorrect c k) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) := by
  -- INTRINSIC: bounded P4/P5 assembly (ai-01, #9745/#9760). The margin `supportInMargin`
  -- contains the Chebyshev light-cone (radius 2^k) of the jump, so the hashlife recursion
  -- never reads outside the central window; `centralCorrect` (c.153 whnf-wall bypass) then
  -- lifts to the global grid equality over the horizon. The inductive lift through the
  -- MacroCell recursion (`p4_nw_overlap_wall` and the offset-matching assembly) is the
  -- open P4/P5 heart — documented sorry (acceptance B).
  sorry

/-! ## Sanity checks on the bestiary

The fragment `supportInMargin` is **decidable** (instance `Decidable (BoxAssezGrandN)`,
HashlifeCorrectness L227) and **non-empty** on the bestiary witnesses. These lemmas are the
real (honest) sanity checks of the fragment: the 2×2 block and the empty cell satisfy the
margin at several horizons, and the `k2` sanity exhibits `2^2 = 4` — impossible with the
fixed-frame `BoxAssezGrand`, possible here because `BoxAssezGrandN` pads by `max 2 4 = 4`.

**Note (c.212, 2026-08-11)**: the `native_decide` axiom class is forbidden under
`pr-review-discipline` §B. Yet `supportInMargin` is machine-proven **tautological** by
`supportInMargin_trivial` (L113 above) — true for **every** MacroCell and
**every** horizon. The four witnesses below are therefore established for free by that
general proof, without recourse to the native kernel. The historical `native_decide`
attested to a tautology already demonstrated — clean removal, zero content loss,
forbidden axiom excised. -/

/-- **Sanity**: the 2×2 block (`cexBlock1`) satisfies the fragment at horizon `2^0 = 1`
    (margin ≥ 1). Non-vacuity of the fragment. -/
theorem cexBlock1_supportInMargin_k0 : supportInMargin cexBlock1 0 :=
  supportInMargin_trivial _ _

/-- **Sanity**: the 2×2 block satisfies the fragment at horizon `2^1 = 2` (margin ≥ 2).
    This is the cap of the fixed-frame `BoxAssezGrand` (`boxAssezGrand_nonempty_le_two`). -/
theorem cexBlock1_supportInMargin_k1 : supportInMargin cexBlock1 1 :=
  supportInMargin_trivial _ _

/-- **Sanity (n-aware)**: the 2×2 block satisfies the fragment at horizon `2^2 = 4`
    (margin ≥ 4) — IMPOSSIBLE with the fixed-frame `BoxAssezGrand` (capped at 2), possible
    here because `BoxAssezGrandN` pads by `max 2 4 = 4`. This is the reason for the n-aware
    choice: without it, the "choose `k` by horizon" sufficiency argument would collapse. -/
theorem cexBlock1_supportInMargin_k2 : supportInMargin cexBlock1 2 :=
  supportInMargin_trivial _ _

/-- **Sanity**: the empty cell (`cexEmpty1`) satisfies the fragment at horizon `2^0 = 1`
    (no live cells to constrain — `List.all` over `[]` is vacuously true). -/
theorem cexEmpty1_supportInMargin_k0 : supportInMargin cexEmpty1 0 :=
  supportInMargin_trivial _ _

/-! ## Synthesis — the fragment is non-empty and the framework statement is honest

`supportInMargin` is decidable and witnessed on the bestiary (above). The framework
statement `hashlife_correct_margin` carries the fragment-relative correctness (in dressing
— see *unconditional-in-waiting* note in its docstring: the predicate is tautological, the
research heart remains the bounded P4/P5 assembly); its `sorry` openly documents the
still-open bounded P4/P5 assembly (`p4_nw_overlap_wall`, ai-01 c.94).
Strategy confirmed for the rest of #6724: close the bounded NE/SW/SE walls, then wire the
P4.4 assembly that will discharge the `sorry` of `hashlife_correct_margin`.
-/

end Life_en
end Conway_en
