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
import Conway.Life.LightCone_en
import Conway.Life.Oscillators_en
import Conway.Life.PatternTour_en

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

/-! ## P4.4 assembly — sorry-stable reduction (tranche 2, #13483)

Diagnosis of 2026-09-04 (c.5539811910): every preliminary brick is proved
(`p5_large_n_jumpN` b3', full P4, the four bounded walls sorry-free) — the sorry of
`hashlife_correct_margin` is the assembly itself. Decomposition:

- **L1** — the `h_margin` hypothesis is free: `supportInMargin` is tautological
  (`supportInMargin_trivial`), the effective statement is the unconditional one under
  `centralCorrect`.
- **L2** — the goal reduces to the N-machine's hypothesis: `hashlife_correctN` (proved,
  in HashlifeCorrectness) yields the global equality as soon as
  `hcap : ∀ t ≤ 2^k, jumpCaptured …` holds. That is the lemma below, sorry-free.
- **L3 (open heart)** — lift `centralCorrect c k` (grid equality RESTRICTED to the final
  window) to `hcap` (confinement of the WHOLE trajectory). This is the bounded P4/P5
  assembly proper: a structural argument about the Hashlife recursion (the margin contains
  the light cone at every jump), NOT a reversibility argument — GoL is not reversible, the
  retrograde cone does not constrain intermediate states.
- **L4** — the equality leg: `centralCorrect` is a restricted equality, the goal is
  global; closing requires both grids to carry their support inside the window
  (`jumpCaptured` of the final state + forward bound on the support of `evolve`).

`hashlife_correct_margin c k h_margin h_central` would discharge as
`hashlife_correct_margin_of_hcap c k h_central (L3 c k h_central)`: L3/L4 are the only
open links. -/

/-- **P4.4 L2 — local byte-identical copy of `jumpCaptured`** (the lake's
    inlining pattern, cf HashlifeCorrectness L6436: the `jumpCaptured` consumed
    by `hashlife_correctN` is `private` there — an inline of
    `Conway.Life.JumpCapture.jumpCaptured` breaking the A↔B import cycle,
    `JumpCapture.lean` importing THIS module). This module can therefore neither
    see the private nor import `JumpCapture` (cycle): same remedy, byte-identical
    copy. Defeq of the identical bodies (delta-unfolding of both semi-reducible
    `def`s) makes the call to `hashlife_correctN` below typecheck. -/
private def jumpCapturedF (c : MacroCell) : Bool :=
  (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))).all fun p =>
    decide ((2 ^ c.level : Int) ≤ p.1) &&
    decide (p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) &&
    decide ((2 ^ c.level : Int) ≤ p.2) &&
    decide (p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int))

/-- **Interface (c) tranche 3, step 1 — propositional unfolding of `jumpCapturedF`.**
    Same proof as `jumpCaptured_iff` (JumpCapture L264), replicated locally:
    this module cannot import `JumpCapture` (import cycle, cf docstring of
    `jumpCapturedF` above). This is the corridor's entry gate (LightCone,
    `isAlive` language) into the Bool predicate that `hcap` requires. -/
theorem jumpCapturedF_iff (c : MacroCell) :
    jumpCapturedF c = true ↔
      ∀ p ∈ evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)),
        (2 ^ c.level : Int) ≤ p.1 ∧
          p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) ∧
          (2 ^ c.level : Int) ≤ p.2 ∧
          p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) := by
  unfold jumpCapturedF
  rw [List.all_eq_true]
  constructor
  · intro h p hp
    have hb := h p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    tauto
  · intro h p hp
    have hb := h p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    tauto

/-- **Interface (c) tranche 3, step 2 — the forward corridor closes the jump as
    soon as the window absorbs the drift.** Bridge between the corridor's
    language (`evolve_support_dilation_from`, brick (a-b) of tranche 3,
    LightCone: `isAlive` confinement of the trajectory) and the Bool predicate
    `jumpCapturedF`: if the padded grid's support fits in the box `[a, b)`
    (`h₀`) and the box dilated by `2^c.level` — the jump's maximal forward
    drift — stays inside the test window `[2^lvl, 2^lvl + 2^(lvl+1))²`
    (`hwin1..4`), then the jump is captured. The proof makes no reversibility
    assumption (GoL is not reversible): the forward relay bounds the drift from
    `t₀ = 0`, the window inclusion is linear. The `h₀`/`hwin` hypotheses are
    what the geometric half of L3 (characterizing the reconstruction's level
    along the trajectory) must establish — this lemma is the clean partition:
    forward confinement [proved by the corridor] separated from window
    geometry [open]. The `hwin` bounds carry the explicit nat cast
    `((2 ^ c.level : Nat) : Int)` — the same atom as the corridor's (otherwise
    the power is forced into Int and omega sees it disconnected). -/
theorem jumpCapturedF_of_dilation (c : MacroCell) (a b : Int × Int)
    (h₀ : ∀ p, isAlive ((padCenter2 c).toGrid (0, 0)) p = true →
      a.1 ≤ p.1 ∧ p.1 < b.1 ∧ a.2 ≤ p.2 ∧ p.2 < b.2)
    (hwin1 : ((2 ^ c.level : Nat) : Int) ≤ a.1 - ((2 ^ c.level : Nat) : Int))
    (hwin2 : b.1 + ((2 ^ c.level : Nat) : Int) ≤
      ((2 ^ c.level : Nat) : Int) + ((2 ^ (c.level + 1) : Nat) : Int))
    (hwin3 : ((2 ^ c.level : Nat) : Int) ≤ a.2 - ((2 ^ c.level : Nat) : Int))
    (hwin4 : b.2 + ((2 ^ c.level : Nat) : Int) ≤
      ((2 ^ c.level : Nat) : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) :
    jumpCapturedF c = true := by
  rw [jumpCapturedF_iff]
  intro p hp
  have hq : isAlive (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))) p = true := by
    rw [isAlive]
    exact List.elem_iff.mpr hp
  obtain ⟨c1, c2, c3, c4⟩ :=
    evolve_support_dilation_from 0 (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)) a b
      (Nat.zero_le _) h₀ p hq
  simp only [Nat.sub_zero] at c1 c2 c3 c4
  -- the goal (from the definition) speaks in `(2 ^ lvl : Int)` (power in Int):
  -- its relation with the corridor's nat cast is provided explicitly, then
  -- everything is linear.
  have hpow : (2 ^ c.level : Int) = ((2 ^ c.level : Nat) : Int) := by
    exact (Nat.cast_pow 2 c.level).symm
  omega

/-- **A period repeats itself** (local byte-identical copy of
    `evolve_mul_of_period`, JumpCapture L518 — this module cannot import it,
    import cycle A↔B, cf docstring of `jumpCapturedF`): if `g` has period
    `T` (in the weak sense `evolve T g = g`), then any multiple `m·T` of
    steps brings it back to itself. By induction on `m` via `evolve_add`. -/
theorem evolve_mulF_of_period {T : Nat} (g : Grid)
    (hper : evolve T g = g) (m : Nat) :
    evolve (m * T) g = g := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : (m + 1) * T = m * T + T := by ring
    rw [hsplit, evolve_add, hper, ih]

/-- **Domain bounds of a well-formed cell** (local byte-identical copy of
    `cellWf_toGrid_bounds`, JumpCapture L475 — import cycle A↔B, cf above):
    any living cell of the `toGrid` of a well-formed `MacroCell` (in the
    `cellWf` sense) of level `n` lives in the square
    `[r0, r0 + 2^n) × [c0, c0 + 2^n)`. Induction on `cellWf`: each leaf
    emits at most its corner, each node distributes its four level-`n`
    children over the offset-`0` or `2^n` quadrants, so the level-`(n+1)`
    node covers `[·, · + 2^(n+1))`. -/
theorem cellWfF_toGrid_bounds {c : MacroCell} (hc : cellWf c) (r0 c0 : Int)
    {p : Int × Int} (hp : p ∈ c.toGrid (r0, c0)) :
    r0 ≤ p.1 ∧ p.1 < r0 + (2 ^ c.level : Int) ∧
      c0 ≤ p.2 ∧ p.2 < c0 + (2 ^ c.level : Int) := by
  induction hc generalizing r0 c0 with
  | leaf b =>
    rw [mem_toGrid] at hp
    cases b with
    | true =>
      simp only [MacroCell.toCellsAux, Prod.fst, Prod.snd, List.mem_singleton] at hp
      obtain ⟨hrr, hcc⟩ : p.1 = r0 ∧ p.2 = c0 := Prod.ext_iff.mp hp
      subst hrr hcc
      simp only [MacroCell.level, pow_zero]
      omega
    | false => simp [MacroCell.toCellsAux] at hp
  | node hnw hne hsw hse hne_lvl hsw_lvl hse_lvl inw ine isw ise =>
    rename_i nw ne sw se
    simp only [mem_toGrid, MacroCell.toCellsAux, List.mem_append, or_assoc] at hp
    push_cast at hp
    have hlvl : MacroCell.level (MacroCell.node nw ne sw se) = nw.level + 1 := by
      simp only [MacroCell.level]; omega
    have hpos : (0 : Int) ≤ 2 ^ nw.level := by positivity
    rcases hp with hp | hp | hp | hp
    · have hb := inw r0 c0 (mem_toGrid.mpr hp)
      rw [hlvl, pow_succ]
      omega
    · have hb := ine r0 (c0 + (2 ^ nw.level : Int)) (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega
    · have hb := isw (r0 + (2 ^ nw.level : Int)) c0 (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega
    · have hb := ise (r0 + (2 ^ nw.level : Int)) (c0 + (2 ^ nw.level : Int))
        (mem_toGrid.mpr hp)
      simp only [← hne_lvl, ← hsw_lvl, ← hse_lvl] at hb
      rw [hlvl, pow_succ]
      omega

/-- **Interface (c) slice 3, step 3 — the periodic class `T ∣ 2^k` is
    captured.** `jumpCapturedF` version of criterion 3
    (`jumpCaptured_of_period_divides`, JumpCapture L533): any pattern of
    period `T ≥ 1` dividing the jump horizon `2^c.level`, carried by a
    well-formed cell of level `k ≥ 1`, satisfies the capture predicate.
    The jump's final generation is the pattern itself (period repeated),
    unchanged in its `padCenter2` framing — hence in the central window by
    the geometry `[3·2^(k-1), 5·2^(k-1)) ⊂ [2^k, 3·2^k)`.

    **Orthogonal complement of the corridor** (step 2,
    `jumpCapturedF_of_dilation`): the corridor requires a window absorbing
    the forward drift `2^lvl` — arithmetically closed at full level for any
    nonempty content (the `hwin` force a zero-width box). The periodic
    class drifts not at all: the exact temporal invariance `evolve T g = g`
    replaces the corridor's over-approximation. This is the hcap-reachable
    class identified by the slice-3 scoping (c.5551593604): still lifes
    (`T = 1`) and dyadic-period oscillators (`T ∣ 2^k`), the witnesses of
    the multi-cycle language. -/
theorem jumpCapturedF_of_period_divides (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level) {T : Nat} (_hT : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hdiv : T ∣ 2 ^ c.level) :
    jumpCapturedF c = true := by
  have hcw : cellWf c := cellWf_of_wf c hwf
  obtain ⟨m, hm⟩ := hdiv
  have hself : evolve (2 ^ c.level) (c.toGrid (0, 0)) = c.toGrid (0, 0) := by
    rw [hm, Nat.mul_comm]
    exact evolve_mulF_of_period _ hper m
  have hfinal : evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))
      = shift ((3 * 2 ^ (c.level - 1) : Int), (3 * 2 ^ (c.level - 1) : Int))
          (c.toGrid (0, 0)) := by
    rw [padCenter2_toGrid_shift c hlvl, ← evolve_shift, hself]
  rw [jumpCapturedF_iff]
  intro p hp
  rw [hfinal, mem_shift] at hp
  -- Bounds of the content in its own framing `[0, 2^c.level)²`…
  obtain ⟨hb1, hb2, hb3, hb4⟩ := cellWfF_toGrid_bounds hcw 0 0 hp
  dsimp only at hb1 hb2 hb3 hb4
  -- …and linear relations between the three atoms `2^(c.level-1)`,
  -- `2^c.level`, `2^(c.level+1)` — the rest is `omega`.
  have hpow : (2 ^ c.level : Int) = 2 * (2 ^ (c.level - 1) : Int) := by
    have hsplit : c.level = (c.level - 1) + 1 := by omega
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hnext : ((2 ^ (c.level + 1) : Nat) : Int)
      = (2 ^ c.level : Int) + (2 ^ c.level : Int) := by
    rw [Nat.cast_pow, pow_succ]
    ring
  have hy : (0 : Int) ≤ 2 ^ (c.level - 1) := by positivity
  omega

/-- **Still-life corollary** (`T = 1`): any still life — a pattern with
    `evolve 1 g = g`, in the strong sense a fixed point of `step` — is
    captured at any level `k ≥ 1`. This is the consumable form of the class
    for the usual Life objects (block, beehive, loaf, barrel…): the first
    L3 link for the `T = 1` class — for any `t ≤ 2^k`, `evolve t g = g` and
    the trajectory reconstruction is the cell itself. -/
theorem jumpCapturedF_of_still_life (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level)
    (hfix : evolve 1 (c.toGrid (0, 0)) = c.toGrid (0, 0)) :
    jumpCapturedF c = true :=
  jumpCapturedF_of_period_divides c hwf hlvl (T := 1) (by omega) hfix (by omega)

/-- **P4.4 L2 (sorry-stable reduction).** The frame's global equality reduces to
    the N-machine's trajectory-capture hypothesis: `hashlife_correctN` (proved)
    closes the goal as soon as `hcap` holds. The open links are L3 (lifting
    `centralCorrect c k` to `hcap`) and L4 (restricted → global equality). -/
theorem hashlife_correct_margin_of_hcap (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k)
    (hcap : ∀ t ≤ 2^k, jumpCapturedF
      (gridToMacroCellWithOffset (evolve t (c.toGrid (0, 0)))).2 = true) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correctN (2^k) (c.toGrid (0, 0)) hcap

/-! ## L3 class `T = 1` — hcap of still lifes (step 3, slice 4)

First **entirely closed** L3 link: for the class of still lifes
(`evolve 1 g = g`, a fixpoint of `step`), the L2 reduction's `hcap`
hypothesis is established end to end — the trajectory is constant, the
reconstruction is constant, and the jump is captured by
`jumpCapturedF_of_still_life`. The chain: EQUALITY round-trip of the
reconstruction for canonical grids (`Canonical.ext`, rigidity of
sorted-deduplicated lists) → transport of the fixpoint to the origin via
`toGrid_shift_grid`/`evolve_shift` → capture. -/

/-- **EQUALITY round-trip of the reconstruction (canonical grids).**
    The general form of `gridToMacroCellWithOffset`'s docstring — so far
    established only at the membership level
    (`mem_toGrid_gridToMacroCellWithOffset`, MacroCell L857) — strengthens
    to a **list equality** as soon as `g` is canonical: both grids are
    canonical (`toGrid` is a `sortDedup` image, `g` by hypothesis) and have
    the same members, hence are equal by rigidity (`Canonical.ext`). This
    is the members→equality bridge that was missing to transport fixpoint
    equivalences (`Prop` equalities) across the reconstruction. -/
theorem toGrid_gridToMacroCellWithOffset_eq (g : Grid) (hg : Canonical g) :
    (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1 = g :=
  Canonical.ext (canonical_sortDedup _) hg (fun p => mem_toGrid_gridToMacroCellWithOffset g p)

/-- **Transport of the fixpoint to the origin-rendered reconstruction.**
    If `g` is a canonical still life, then the reconstructed MacroCell
    rendered at the origin, `(gridToMacroCellWithOffset g).2.toGrid (0, 0)`,
    is itself a fixpoint of `evolve 1`: the `toGrid_shift_grid` shuttle
    brings the origin back to a shift of the framed grid, `evolve_shift`
    commutes the shift with `evolve`, `evolve_congr` transports the
    evolution to `g`'s frame (same members), and the EQUALITY round-trip
    closes the loop. This is the exact `hfix` hypothesis that
    `jumpCapturedF_of_still_life` requires on the reconstruction — now
    available for the `T = 1` class. -/
theorem still_life_fix_toGrid_zero (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) :
    evolve 1 ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = (gridToMacroCellWithOffset g).2.toGrid (0, 0) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hfix]

/-- **hcap of the `T = 1` class (still lifes) — the reconstruction's
    capture.** For any still life `g` (canonical or empty), the
    reconstructed MacroCell satisfies the jump predicate: this is the
    capture hypothesis that the L2 reduction consumes, established for the
    whole class. Nonempty case: `jumpCapturedF_of_still_life` consumes the
    three now-available hypotheses — wf (`buildFromGrid_wf`), level (the
    n-aware bound: `2 < 2^lvl` as soon as `g ≠ []`, hence `1 ≤ lvl`) and
    fixpoint (`still_life_fix_toGrid_zero`). Empty case: the
    reconstruction is a dead level-0 leaf, the padded grid is empty, and
    `List.all` on `[]` is vacuously true — decided by the kernel. -/
theorem jumpCapturedF_reconstruction_of_still_life (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · apply jumpCapturedF_of_still_life _ ?_ ?_ ?_
    · unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    · have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    · exact still_life_fix_toGrid_zero g hg hfix

/-- **hcap of still lifes, full trajectory.** For any still life `g`, at
    **every** instant `t` (a fortiori every `t ≤ 2^k`): the trajectory is
    constant (`evolve t g = g`, period 1 repeated via
    `evolve_mulF_of_period`), so the reconstruction along the trajectory
    is the constant object `gridToMacroCellWithOffset g`, whose jump is
    captured. With the assembly corollary below, this is the **first
    entirely proved L3 link** of the P4.4 decomposition: lifting a whole
    class of patterns to the N-machine's `hcap` hypothesis, with no sorry. -/
theorem hcap_of_still_life (g : Grid) (hg : Canonical g)
    (hfix : evolve 1 g = g) (t : Nat) :
    jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  have hself : evolve t g = g := by
    have hmul := evolve_mulF_of_period g hfix t
    rwa [Nat.mul_one] at hmul
  rw [hself]
  exact jumpCapturedF_reconstruction_of_still_life g hg hfix

/-- **L3 closed for the `T = 1` class: Hashlife correctness of still
    lifes.** Assembly corollary — the first case of the P4.4 decomposition
    where the L3 link (lifting a class of patterns to `hcap`) is **entirely
    proved**: for any MacroCell whose origin-rendered grid is a still life,
    the global equality `hashlife_correctN` applies at any horizon `2^k`
    under `centralCorrect`. Only L4 remains (the restricted equality
    `centralCorrect` itself), which lives in the hypothesis — exactly the
    clean seam announced by the L2 reduction. -/
theorem hashlife_correct_margin_of_still_life (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k)
    (hfix : evolve 1 (c.toGrid (0, 0)) = c.toGrid (0, 0)) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_still_life _ (canonical_sortDedup _) hfix t)

/-! ## L3 geometry — bounding-box bounds and reconstruction level (slice 3, step 5)

Scoping 3-(c) (c.5551298160) identifies the "geometry" leg of L3: at the
adaptive level, the window `[2^lvl, 3·2^lvl)` must absorb the corridor box.
Two bricks are laid here: (i) the **bounding-box bounds** of a grid whose
support is constrained — `gridRowMin` is bounded below, `gridRowMax` is
bounded above (and likewise columns); (ii) the **level bound** of the
reconstruction `gridToMacroCellWithOffset g` in terms of the box. These are
the geometric premises for capture at the adaptive level. -/

/-- **Helper: a `foldl` of `max` (via `proj`) stays strictly below `b`** if the
    seed and every element are. Direct induction on the list (invariant of
    `max`). -/
theorem foldl_proj_max_lt_of_mem_lt (ps : Grid) (proj : Int × Int → Int)
    (acc : Int) (b : Int) (hb : acc < b)
    (h₀ : ∀ q, q ∈ ps → proj q < b) :
    ps.foldl (fun m q => max m (proj q)) acc < b := by
  induction ps generalizing acc with
  | nil => simpa using hb
  | cons q qs ih =>
    have hq : proj q < b := h₀ q (by simp)
    have hb' : max acc (proj q) < b := max_lt_iff.mpr ⟨hb, hq⟩
    exact ih _ hb' (fun r hr => h₀ r (List.mem_cons_of_mem q hr))

/-- **Lower bound of `gridRowMin` from a box.** If every cell of `g` satisfies
    `a ≤ p.1`, then `a ≤ gridRowMin g`: the minimum of the rows is one of the
    rows of `g` (`foldl_proj_min_attained`), so it inherits the bound. The grid
    must be non-empty: on the empty grid, `gridRowMin` defaults to `0` and the
    bound would fail. -/
theorem gridRowMin_lower_bound (g : Grid) (a : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → a ≤ p.1) :
    a ≤ gridRowMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMin]
    rcases foldl_proj_min_attained ps (·.1) p₀.1 with hcase | ⟨p, hp, hval⟩
    · rw [hcase]
      exact h₀ p₀ (by simp)
    · rw [hval]
      exact h₀ p (List.mem_cons_of_mem p₀ hp)

/-- **Upper bound of `gridRowMax` from a box.** If every cell of `g` satisfies
    `p.1 < b`, then `gridRowMax g < b`: the maximum of the rows inherits the
    bound (invariant of the `foldl` of `max`). -/
theorem gridRowMax_upper_bound (g : Grid) (b : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → p.1 < b) :
    gridRowMax g < b := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMax]
    exact foldl_proj_max_lt_of_mem_lt ps (·.1) p₀.1 b (h₀ p₀ (by simp))
      (fun q hq => h₀ q (List.mem_cons_of_mem p₀ hq))

/-- **Lower bound of `gridColMin` from a box** (column mirror of
    `gridRowMin_lower_bound`). -/
theorem gridColMin_lower_bound (g : Grid) (a : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → a ≤ p.2) :
    a ≤ gridColMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMin]
    rcases foldl_proj_min_attained ps (·.2) p₀.2 with hcase | ⟨p, hp, hval⟩
    · rw [hcase]
      exact h₀ p₀ (by simp)
    · rw [hval]
      exact h₀ p (List.mem_cons_of_mem p₀ hp)

/-- **Upper bound of `gridColMax` from a box** (column mirror of
    `gridRowMax_upper_bound`). -/
theorem gridColMax_upper_bound (g : Grid) (b : Int) (hg : g ≠ [])
    (h₀ : ∀ p, p ∈ g → p.2 < b) :
    gridColMax g < b := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMax]
    exact foldl_proj_max_lt_of_mem_lt ps (·.2) p₀.2 b (h₀ p₀ (by simp))
      (fun q hq => h₀ q (List.mem_cons_of_mem p₀ hq))

/-- **Monotonicity of `ceilLog2`.** The log₂ ceiling is an increasing function:
    `a ≤ b ⟹ ceilLog2 a ≤ ceilLog2 b`. Follows from `Nat.log_mono_right`
    (monotonicity of `log` in its argument), after splitting on `if k ≤ 1`. -/
theorem ceilLog2_mono {a b : Nat} (hab : a ≤ b) :
    MacroCell.ceilLog2 a ≤ MacroCell.ceilLog2 b := by
  by_cases hb1 : b ≤ 1
  · have ha1 : a ≤ 1 := le_trans hab hb1
    simp only [MacroCell.ceilLog2, hb1, ha1, reduceIte]
    omega
  · by_cases ha1 : a ≤ 1
    · simp only [MacroCell.ceilLog2, ha1, reduceIte]
      exact Nat.zero_le _
    · simp only [MacroCell.ceilLog2, hb1, ha1, reduceIte]
      have hlog : Nat.log 2 (a - 1) ≤ Nat.log 2 (b - 1) :=
        Nat.log_mono_right (by omega)
      omega

/-- **Level bound of the reconstruction ("geometry" leg of L3).** If the
    support of `g` fits in the box `[a,b)` (in the sense
    `a.1 ≤ p.1 ∧ p.1 < b.1` and likewise columns), then the level of the
    reconstruction `gridToMacroCellWithOffset g` is bounded by `ceilLog2` of
    the box dimension plus the fixed padding `5` of `gridFrame`. Proof:
    `gridRowMin`/`gridColMin` are bounded below and `gridRowMax`/`gridColMax`
    bounded above by the box, so the frame height/width (`+5`) stays below the
    box dimension `+5`, and `ceilLog2` is monotone. -/
theorem gridToMacroCellWithOffset_level_le_of_box (g : Grid) (a b : Int × Int)
    (h₀ : ∀ p, p ∈ g → a.1 ≤ p.1 ∧ p.1 < b.1 ∧ a.2 ≤ p.2 ∧ p.2 < b.2) :
    (gridToMacroCellWithOffset g).2.level ≤
      MacroCell.ceilLog2 (max (b.1 - a.1 + 5).toNat (b.2 - a.2 + 5).toNat) := by
  by_cases hg : g = []
  · subst hg
    simp only [gridToMacroCellWithOffset, gridFrame]
    rw [MacroCell.level_buildFromGrid]
    exact Nat.zero_le _
  · cases g with
    | nil => exact absurd rfl hg
    | cons p₀ ps =>
      have hne : p₀ :: ps ≠ [] := List.cons_ne_nil p₀ ps
      have hrowmin : a.1 ≤ gridRowMin (p₀ :: ps) :=
        gridRowMin_lower_bound _ a.1 hne (fun p hp => (h₀ p hp).1)
      have hrowmax : gridRowMax (p₀ :: ps) < b.1 :=
        gridRowMax_upper_bound _ b.1 hne (fun p hp => (h₀ p hp).2.1)
      have hcolmin : a.2 ≤ gridColMin (p₀ :: ps) :=
        gridColMin_lower_bound _ a.2 hne (fun p hp => (h₀ p hp).2.2.1)
      have hcolmax : gridColMax (p₀ :: ps) < b.2 :=
        gridColMax_upper_bound _ b.2 hne (fun p hp => (h₀ p hp).2.2.2)
      have hside_le : max ((gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat)
          ((gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat) ≤
          max (b.1 - a.1 + 5).toNat (b.2 - a.2 + 5).toNat := by
        apply max_le_max
        · exact Int.toNat_le_toNat (by omega)
        · exact Int.toNat_le_toNat (by omega)
      simp only [gridToMacroCellWithOffset]
      rw [MacroCell.level_buildFromGrid]
      show MacroCell.ceilLog2
          (max ((gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat)
               ((gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat)) ≤ _
      exact ceilLog2_mono hside_le

/-! ## L3 periodic class `T ∣ 2^k` — hcap of oscillators (tranche 3, step 6)

Second L3 link **entirely closed**: the generalization of the `T = 1` chain
to oscillators of period `T > 1` with dyadic period. The orbit is no longer
constant — `evolve t g` cycles through the `T` phases — so the capture is
proved **phase by phase**: each phase `evolve r g` (`r < T`) is itself a
fixed point of `evolve T` (`evolve_phase_fix`), the trajectory reduces to
the residue modulo `T` (`evolve_mod_period`), and the round-trip →
transported fixed point scheme applies to each canonical phase. The
geometric premise `T ∣ 2^level` of `jumpCapturedF_of_period_divides` is
carried **explicitly**: it is a real constraint on the reconstruction level
of each phase (the level must reach `log₂ T`), not a consequence — the
upper level bound on the `gridFrame` side (step 5) is what makes it
computable. -/

/-- **Each phase is a fixed point of `evolve T`.** If `g` is `T`-periodic,
    so is every phase `evolve r g`: evolution commutes with itself
    (`evolve_add`), hence `evolve T (evolve r g) = evolve r (evolve T g)
    = evolve r g`. This is the exact `hper` hypothesis the capture requires
    at the level of each phase. -/
theorem evolve_phase_fix {T : Nat} (g : Grid)
    (hper : evolve T g = g) (r : Nat) :
    evolve T (evolve r g) = evolve r g := by
  rw [← evolve_add, Nat.add_comm T r, evolve_add, hper]

/-- **Reduction of the trajectory to the residue modulo `T`.** For a
    `T`-periodic pattern, the whole trajectory folds onto its `T` phases:
    `evolve t g = evolve (t % T) g` — the quotient `t / T` of complete
    periods vanishes by fixed point. This bounds the capture work from
    "every `t ≤ 2^k`" to "each of the `T` phases". -/
theorem evolve_mod_period {T : Nat} (g : Grid)
    (hper : evolve T g = g) (t : Nat) :
    evolve t g = evolve (t % T) g := by
  have hsplit : t = T * (t / T) + t % T := (Nat.div_add_mod t T).symm
  conv_lhs => rw [hsplit, evolve_add, Nat.mul_comm]
  exact evolve_mulF_of_period _ (evolve_phase_fix g hper _) _

/-- **Transport of the period-`T` fixed point to the reconstruction
    (returned to the origin).** The exact analogue of
    `still_life_fix_toGrid_zero` for period `T`: if `g` is canonical and
    `T`-periodic, the reconstructed MacroCell returned to the origin is
    itself a fixed point of `evolve T` — `toGrid_shift_grid` shuttle,
    `evolve_shift` commutation, EQUALITY round-trip, fixed point. -/
theorem periodic_fix_toGrid_zero (g : Grid) (hg : Canonical g) {T : Nat}
    (hper : evolve T g = g) :
    evolve T ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = (gridToMacroCellWithOffset g).2.toGrid (0, 0) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hper]

/-- **Tranche 8a — capture of oscillators with arbitrary period.** Generalization
    of `jumpCapturedF_of_period_divides`: the divisibility `T ∣ 2^c.level` was only
    used to build `hself` ("the jump of horizon `2^c.level` lands back on the
    pattern"), which de facto excludes every non-dyadic period — an oscillator of
    minimal odd period `T` never satisfies `evolve (2^ℓ) g = g`. Here the exact
    landing is replaced by the modulo fold (`evolve_mod_period`: the jump lands on
    phase `2^c.level % T`), and the only requested counterpart is **spatial**:
    every phase of the orbit fits in the starting phase's box (`hwin`, bounds
    `[0, 2^c.level)²` in origin framing — exactly what `cellWfF_toGrid_bounds`
    gives for the phase itself). The `padCenter2` geometry and the arithmetic
    tail are unchanged: a phase inside the box shifted by `3·2^(c.level-1)`
    stays in the central window `[2^c.level, 2^c.level + 2^(c.level+1))²`.
    `T = 1` (still life) and the dyadic case remain instances: `hwin` is then
    trivially the phase's own box. -/
theorem jumpCapturedF_of_period_mod (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hwin : ∀ i, i < T → ∀ p ∈ evolve i (c.toGrid (0, 0)),
      (0 : Int) ≤ p.1 ∧ p.1 < (2 ^ c.level : Int) ∧
        (0 : Int) ≤ p.2 ∧ p.2 < (2 ^ c.level : Int)) :
    jumpCapturedF c = true := by
  have hr' : 2 ^ c.level % T < T := Nat.mod_lt _ hT0
  have hmod : evolve (2 ^ c.level) (c.toGrid (0, 0))
      = evolve (2 ^ c.level % T) (c.toGrid (0, 0)) :=
    evolve_mod_period _ hper _
  have hfinal : evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))
      = shift ((3 * 2 ^ (c.level - 1) : Int), (3 * 2 ^ (c.level - 1) : Int))
          (evolve (2 ^ c.level % T) (c.toGrid (0, 0))) := by
    rw [padCenter2_toGrid_shift c hlvl, ← evolve_shift, hmod]
  rw [jumpCapturedF_iff]
  intro p hp
  rw [hfinal, mem_shift] at hp
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hwin _ hr' _ hp
  dsimp only at hb1 hb2 hb3 hb4
  have hpow : (2 ^ c.level : Int) = 2 * (2 ^ (c.level - 1) : Int) := by
    have hsplit : c.level = (c.level - 1) + 1 := by omega
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hnext : ((2 ^ (c.level + 1) : Nat) : Int)
      = (2 ^ c.level : Int) + (2 ^ c.level : Int) := by
    rw [Nat.cast_pow, pow_succ]
    ring
  have hy : (0 : Int) ≤ 2 ^ (c.level - 1) := by positivity
  omega

/-- **Capture of the reconstruction of a periodic phase.** For any
    canonical phase `g` of a `T`-periodic oscillator (`T > 1` a fortiori
    `0 < T`), whose reconstruction level divides the jump horizon
    (`T ∣ 2^level`), the reconstruction satisfies the jump predicate —
    this is `jumpCapturedF_of_period_divides` consumed at the
    reconstruction level, with the three hypotheses now available: wf
    (`buildFromGrid_wf`), level (`1 ≤ lvl` as soon as `g ≠ []`, n-aware
    bound) and period-`T` fixed point (`periodic_fix_toGrid_zero`). Empty
    case: the reconstruction is a dead level-0 leaf, decided by the kernel. -/
theorem jumpCapturedF_reconstruction_of_period (g : Grid) (hg : Canonical g)
    {T : Nat} (hT0 : 0 < T) (hper : evolve T g = g)
    (hdiv : T ∣ 2 ^ (gridToMacroCellWithOffset g).2.level) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · have hwf : ((gridToMacroCellWithOffset g).2).wf = true := by
      unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    have hlvl : 1 ≤ (gridToMacroCellWithOffset g).2.level := by
      have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    exact jumpCapturedF_of_period_divides _ hwf hlvl hT0
      (periodic_fix_toGrid_zero g hg hper) hdiv

/-- **hcap of the periodic class, whole trajectory.** For a canonical
    oscillator of period `T > 1` whose **every phase** has a reconstruction
    level divisible by `T` (in the sense `T ∣ 2^level`), every instant `t`
    (a fortiori every `t ≤ 2^k`) is captured: the trajectory reduces to the
    phase `t % T` (`evolve_mod_period`), the phase is canonical
    (`canonical_evolve_of_pos`, or `g` itself for the zero phase), a fixed
    point of `evolve T` (`evolve_phase_fix`), and its reconstruction is
    captured. The divisibility premise is finite: it bears on the `T`
    phases only, not on the infinite trajectory. -/
theorem hcap_of_period (g : Grid) (hg : Canonical g) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T g = g)
    (hdiv : ∀ i, i < T →
      T ∣ 2 ^ (gridToMacroCellWithOffset (evolve i g)).2.level) :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  intro t
  rw [evolve_mod_period g hper t]
  have hr : t % T < T := Nat.mod_lt _ hT0
  have hcan : Canonical (evolve (t % T) g) := by
    rcases Nat.eq_zero_or_pos (t % T) with h0 | hpos
    · rw [h0]
      simpa using hg
    · exact canonical_evolve_of_pos hpos _
  have hfix : evolve T (evolve (t % T) g) = evolve (t % T) g :=
    evolve_phase_fix g hper _
  exact jumpCapturedF_reconstruction_of_period _ hcan hT0 hfix (hdiv _ hr)

/-- **L3 closed for the periodic class `T ∣ 2^k`: Hashlife correctness of
    oscillators.** Assembly corollary — the second case of the P4.4
    decomposition where the L3 link is **entirely proved**: for any
    MacroCell whose grid returned to the origin is an oscillator of period
    `T > 1` (every phase of divisible level), the global equality
    `hashlife_correctN` applies at any horizon `2^k` under `centralCorrect`.
    The class covers the multi-cycle witnesses of the bestiary (blinker
    `T = 2`, toad `T = 2`, lighthouse `T = 3` as soon as `T ∣ 2^level`). -/
theorem hashlife_correct_margin_of_period (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hdiv : ∀ i, i < T →
      T ∣ 2 ^ (gridToMacroCellWithOffset (evolve i (c.toGrid (0, 0)))).2.level) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_period _ (canonical_sortDedup _) hT0 hper hdiv t)

/-! ## Tranche 8a/8b — relaxed chain for arbitrary periods

Exact mirror of the three dyadic links above, consuming
`jumpCapturedF_of_period_mod`: the divisibility `T ∣ 2^level` is everywhere
replaced by the spatial counterpart “every phase of the orbit fits inside the
reconstruction frame of the starting phase” — the absolute statement
`[o, o + 2^level)²` where `o` is the offset of the `gridToMacroCellWithOffset`
frame — which transports to the cell's origin framing via `evolve_shift` +
`mem_shift`. The starting phase automatically lies in its own frame (it is
the one built on its bounding box); the hypothesis only bears on the other
`T - 1` phases. This opens the class to non-dyadic periods (flagship witness
`T = 3`, etc.) as soon as the witness checks the containment.
-/

/-- **Tranche 8b — reconstruction capture, arbitrary periods.**
    Variant of `jumpCapturedF_reconstruction_of_period`: the divisibility
    premise is replaced by the containment of the orbit's phases inside the
    reconstruction frame of `g` (absolute coordinates). The transport to the
    cell's origin framing goes through `toGrid_shift_grid` + `evolve_shift`.
    -/
theorem jumpCapturedF_reconstruction_of_period_mod (g : Grid) (hg : Canonical g)
    {T : Nat} (hT0 : 0 < T) (hper : evolve T g = g)
    (hwin : ∀ i, i < T → ∀ p ∈ evolve i g,
      (gridToMacroCellWithOffset g).1.1 ≤ p.1 ∧
        p.1 < (gridToMacroCellWithOffset g).1.1
          + (2 ^ (gridToMacroCellWithOffset g).2.level : Int) ∧
      (gridToMacroCellWithOffset g).1.2 ≤ p.2 ∧
        p.2 < (gridToMacroCellWithOffset g).1.2
          + (2 ^ (gridToMacroCellWithOffset g).2.level : Int)) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · have hwf : ((gridToMacroCellWithOffset g).2).wf = true := by
      unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    have hlvl : 1 ≤ (gridToMacroCellWithOffset g).2.level := by
      have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
        = shift (0 - (gridToMacroCellWithOffset g).1.1,
            0 - (gridToMacroCellWithOffset g).1.2)
            ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
      toGrid_shift_grid _ 0 0 _ _
    have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
        = g := toGrid_gridToMacroCellWithOffset_eq g hg
    have hwin' : ∀ i, i < T → ∀ p ∈
        evolve i ((gridToMacroCellWithOffset g).2.toGrid (0, 0)),
      (0 : Int) ≤ p.1 ∧ p.1 < (2 ^ (gridToMacroCellWithOffset g).2.level : Int) ∧
        (0 : Int) ≤ p.2 ∧ p.2 < (2 ^ (gridToMacroCellWithOffset g).2.level : Int) := by
      intro i hi p hp
      rw [hshift, ← evolve_shift, mem_shift, hrt] at hp
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hwin i hi _ hp
      dsimp only at hb1 hb2 hb3 hb4
      omega
    exact jumpCapturedF_of_period_mod _ hwf hlvl hT0
      (periodic_fix_toGrid_zero g hg hper) hwin'

/-- **Tranche 8b — hcap of the periodic class, arbitrary periods.**
    Variant of `hcap_of_period`: each phase carries its own frame, and the
    premise asks the `T` phases to live inside the reconstruction frame of
    each one — for a real oscillator whose phases overlap, this is the same
    bounded neighbourhood, stated `T` times.
    -/
theorem hcap_of_period_mod (g : Grid) (hg : Canonical g) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T g = g)
    (hwin : ∀ r, r < T → ∀ i, i < T → ∀ p ∈ evolve i (evolve r g),
      (gridToMacroCellWithOffset (evolve r g)).1.1 ≤ p.1 ∧
        p.1 < (gridToMacroCellWithOffset (evolve r g)).1.1
          + (2 ^ (gridToMacroCellWithOffset (evolve r g)).2.level : Int) ∧
      (gridToMacroCellWithOffset (evolve r g)).1.2 ≤ p.2 ∧
        p.2 < (gridToMacroCellWithOffset (evolve r g)).1.2
          + (2 ^ (gridToMacroCellWithOffset (evolve r g)).2.level : Int)) :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  intro t
  rw [evolve_mod_period g hper t]
  have hr : t % T < T := Nat.mod_lt _ hT0
  have hcan : Canonical (evolve (t % T) g) := by
    rcases Nat.eq_zero_or_pos (t % T) with h0 | hpos
    · rw [h0]
      simpa using hg
    · exact canonical_evolve_of_pos hpos _
  have hfix : evolve T (evolve (t % T) g) = evolve (t % T) g :=
    evolve_phase_fix g hper _
  exact jumpCapturedF_reconstruction_of_period_mod _ hcan hT0 hfix (hwin _ hr)

/-- **Tranche 8b — L3 closed for the general periodic class: Hashlife
    correctness of arbitrary-period oscillators.** Mirror assembly corollary
    of `hashlife_correct_margin_of_period`: under phase containment (no more
    divisibility), the global equality holds at any horizon `2^k` under
    `centralCorrect`.
    -/
theorem hashlife_correct_margin_of_period_mod (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k) {T : Nat} (hT0 : 0 < T)
    (hper : evolve T (c.toGrid (0, 0)) = c.toGrid (0, 0))
    (hwin : ∀ r, r < T → ∀ i, i < T →
      ∀ p ∈ evolve i (evolve r (c.toGrid (0, 0))),
      (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.1 ≤ p.1 ∧
        p.1 < (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.1
          + (2 ^ (gridToMacroCellWithOffset
            (evolve r (c.toGrid (0, 0)))).2.level : Int) ∧
      (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.2 ≤ p.2 ∧
        p.2 < (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.2
          + (2 ^ (gridToMacroCellWithOffset
            (evolve r (c.toGrid (0, 0)))).2.level : Int)) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_period_mod _ (canonical_sortDedup _) hT0 hper hwin t)

/-! ### Flagship witness `T = 3`: the pulsar (tranche 8b, admission)

First **non-dyadic** witness admitted through the relaxed chain: the pulsar
(`Conway.Life.Oscillators.pulsar`, 48 cells, 13×13 box). Since 3 divides no
power of 2, the dyadic chain `T ∣ 2^level` structurally cannot admit it —
only the phase-containment relaxation reaches it. The three step equations
are proved by the **kernel** reducer (`decide` under `maxRecDepth 1000000`),
without consuming `Oscillators.pulsar_period_three` (a `native_decide`
proof, forbidden by bestiary note c.212). -/
/-- Phase 1 of the pulsar (56 cells, box `[-1, 13]²`): the only phase that
spills outside the phase-0 13×13 box. Lexicographically sorted literal. -/
def pulsarP1 : Grid :=
  [(-1, 3), (-1, 9), (0, 3), (0, 9), (1, 3), (1, 4), (1, 8), (1, 9),
  (3, -1), (3, 0), (3, 1), (3, 4), (3, 5), (3, 7), (3, 8), (3, 11),
  (3, 12), (3, 13), (4, 1), (4, 3), (4, 5), (4, 7), (4, 9), (4, 11),
  (5, 3), (5, 4), (5, 8), (5, 9), (7, 3), (7, 4), (7, 8), (7, 9),
  (8, 1), (8, 3), (8, 5), (8, 7), (8, 9), (8, 11), (9, -1), (9, 0),
  (9, 1), (9, 4), (9, 5), (9, 7), (9, 8), (9, 11), (9, 12), (9, 13),
  (11, 3), (11, 4), (11, 8), (11, 9), (12, 3), (12, 9), (13, 3), (13, 9)]
/-- Phase 2 of the pulsar (72 cells, box `[0, 12]²`). Sorted literal. -/
def pulsarP2 : Grid :=
  [(0, 2), (0, 3), (0, 9), (0, 10), (1, 3), (1, 4), (1, 8), (1, 9),
  (2, 0), (2, 3), (2, 5), (2, 7), (2, 9), (2, 12), (3, 0), (3, 1),
  (3, 2), (3, 4), (3, 5), (3, 7), (3, 8), (3, 10), (3, 11), (3, 12),
  (4, 1), (4, 3), (4, 5), (4, 7), (4, 9), (4, 11), (5, 2), (5, 3),
  (5, 4), (5, 8), (5, 9), (5, 10), (7, 2), (7, 3), (7, 4), (7, 8),
  (7, 9), (7, 10), (8, 1), (8, 3), (8, 5), (8, 7), (8, 9), (8, 11),
  (9, 0), (9, 1), (9, 2), (9, 4), (9, 5), (9, 7), (9, 8), (9, 10),
  (9, 11), (9, 12), (10, 0), (10, 3), (10, 5), (10, 7), (10, 9), (10, 12),
  (11, 3), (11, 4), (11, 8), (11, 9), (12, 2), (12, 3), (12, 9), (12, 10)]
set_option maxRecDepth 1000000 in
/-- The pulsar definition is already canonical (sorted, duplicate-free):
certified by the kernel, then converted through `canonical_sortDedup`. -/
theorem pulsar_canonical : Canonical pulsar := by
  have h : pulsar = sortDedup pulsar := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
/-- Likewise for phase 1. -/
theorem pulsarP1_canonical : Canonical pulsarP1 := by
  have h : pulsarP1 = sortDedup pulsarP1 := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
/-- Likewise for phase 2. -/
theorem pulsarP2_canonical : Canonical pulsarP2 := by
  have h : pulsarP2 = sortDedup pulsarP2 := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Step equation by the kernel reducer: phase 0 evolves into phase 1
(~4.5 min of reduction). -/
theorem pulsar_step1 : step pulsar = pulsarP1 := by decide
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Likewise, phase 1 into phase 2. -/
theorem pulsarP1_step : step pulsarP1 = pulsarP2 := by decide
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Likewise, phase 2 back to phase 0: the period-3 loop is closed. -/
theorem pulsarP2_step : step pulsarP2 = pulsar := by decide
/-- Trivial decomposition of iterates: two steps compose two unit steps
(`evolve` is the iterate of `step`). -/
theorem evolve_two (g : Grid) : evolve 2 g = evolve 1 (evolve 1 g) := rfl
/-- Likewise for three steps. -/
theorem evolve_three (g : Grid) : evolve 3 g = evolve 1 (evolve 1 (evolve 1 g)) := rfl
/-- Chain of phases under `evolve 1`: phase 0. -/
theorem pulsar_ev1 : evolve 1 pulsar = pulsarP1 := pulsar_step1
/-- Chain of phases: phase 1. -/
theorem pulsarP1_ev1 : evolve 1 pulsarP1 = pulsarP2 := pulsarP1_step
/-- Chain of phases: phase 2. -/
theorem pulsarP2_ev1 : evolve 1 pulsarP2 = pulsar := pulsarP2_step
/-- Period 3 of the pulsar proved by the **kernel**: composition of the
three step equations. The `native_decide` proof
`Oscillators.pulsar_period_three` is not consumed (note c.212). -/
theorem pulsar_period_three_kernel : evolve 3 pulsar = pulsar := by
  rw [evolve_three, pulsar_ev1, pulsarP1_ev1, pulsarP2_ev1]
set_option maxRecDepth 1000000 in
/-- Reconstruction frame of phase 0: offset `(-2, -2)` (padding 2 around
the `[0, 12]²` box). -/
theorem pulsar_frame_off : (gridToMacroCellWithOffset pulsar).1 = (-2, -2) := by decide
set_option maxRecDepth 1000000 in
/-- Level of the phase-0 frame: side 18 → level 5, frame `[-2, 30)²`. -/
theorem pulsar_frame_lvl : (gridToMacroCellWithOffset pulsar).2.level = 5 := by decide
set_option maxRecDepth 1000000 in
/-- Frame of phase 1: box `[-1, 13]²` → offset `(-3, -3)`, level 5
(frame `[-3, 29)²`). -/
theorem pulsarP1_frame_off : (gridToMacroCellWithOffset pulsarP1).1 = (-3, -3) := by decide
set_option maxRecDepth 1000000 in
/-- Level of the phase-1 frame: side 20 → level 5. -/
theorem pulsarP1_frame_lvl : (gridToMacroCellWithOffset pulsarP1).2.level = 5 := by decide
set_option maxRecDepth 1000000 in
/-- Frame of phase 2: box `[0, 12]²` → offset `(-2, -2)`. -/
theorem pulsarP2_frame_off : (gridToMacroCellWithOffset pulsarP2).1 = (-2, -2) := by decide
set_option maxRecDepth 1000000 in
/-- Level of the phase-2 frame: level 5. -/
theorem pulsarP2_frame_lvl : (gridToMacroCellWithOffset pulsarP2).2.level = 5 := by decide
set_option maxRecDepth 1000000 in
/-- Containment of the 9 phase combinations `(r, i) < 3 × 3`: every image
`evolve i (evolve r pulsar)` lives inside the reconstruction frame of
phase `r`. Phase 1 spills outside the 13×13 box, but its image stays
inside the enclosing phase-0 frame `[-2, 30)²`. -/
theorem pulsar_hwin : ∀ r, r < 3 → ∀ i, i < 3 → ∀ p ∈ evolve i (evolve r pulsar),
    (gridToMacroCellWithOffset (evolve r pulsar)).1.1 ≤ p.1 ∧
      p.1 < (gridToMacroCellWithOffset (evolve r pulsar)).1.1
        + (2 ^ (gridToMacroCellWithOffset (evolve r pulsar)).2.level : Int) ∧
    (gridToMacroCellWithOffset (evolve r pulsar)).1.2 ≤ p.2 ∧
      p.2 < (gridToMacroCellWithOffset (evolve r pulsar)).1.2
        + (2 ^ (gridToMacroCellWithOffset (evolve r pulsar)).2.level : Int) := by
  intro r hr i hi
  interval_cases r <;> interval_cases i <;>
    simp only [evolve_zero, evolve_two, pulsar_ev1, pulsarP1_ev1, pulsarP2_ev1] <;>
    first
    | (rw [pulsar_frame_off, pulsar_frame_lvl]; decide)
    | (rw [pulsarP1_frame_off, pulsarP1_frame_lvl]; decide)
    | (rw [pulsarP2_frame_off, pulsarP2_frame_lvl]; decide)
/-- Capstone: the pulsar is admitted by `hcap_of_period_mod` — the first
concrete **non-dyadic** instance. For every horizon `t`, the
reconstruction of `evolve t pulsar` is captured by Hashlife. -/
theorem pulsar_hcap_of_period_mod :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t pulsar)).2 = true :=
  hcap_of_period_mod pulsar pulsar_canonical (by decide)
    pulsar_period_three_kernel pulsar_hwin

/-! ### Dyadic witnesses `T = 2`: the blinker and the toad (tranche 12, admission)

The docstring of `hashlife_correct_margin_of_period` announces the witnesses
of its class ("blinker `T = 2`, toad `T = 2`, beacon `T = 3`"). The pulsar
(tranche 8b) covers its **non-dyadic** part; the two **dyadic** witnesses were
missing. Since `2 ∣ 2^level` as soon as `level ≥ 1`, the `hcap_of_period`
chain admits them **directly** — without the containment relaxation (`_mod`)
that period 3 required.

Both blinker phases and the toad's phase 0 are the `Conway.Life` bestiary
definitions (L206-212), reused as-is: the only new literal is the toad's
second phase. Periods are proved by the **kernel** reducer (composition of the
step equations), without consuming `blinker_period_two` or `toad_period_two`:
those bestiary lemmas yield `isOscillator g 2 = true`, a `Bool`-valued form
that does not provide the equality `evolve T g = g` required by
`hcap_of_period`. -/
/-- Second phase of the toad (6 cells, box `[0, 3] × [-1, 2]`), obtained by
applying the rule to the bestiary phase 0. Sorted literal. -/
def toadP2 : Grid :=
  [(0, 0), (0, 1), (1, 2), (2, -1), (3, 0), (3, 1)]
set_option maxRecDepth 1000000 in
/-- The toad's second phase is already canonical (sorted, duplicate-free):
certified by the kernel, then converted through `canonical_sortDedup`. -/
theorem toadP2_canonical : Canonical toadP2 := by
  have h : toadP2 = sortDedup toadP2 := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
/-- The toad's phase 0, taken from the bestiary, is canonical. -/
theorem toad_canonical : Canonical toad := by
  have h : toad = sortDedup toad := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
/-- The bestiary horizontal blinker is canonical. -/
theorem blinker_h_canonical : Canonical blinker_h := by
  have h : blinker_h = sortDedup blinker_h := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
/-- Likewise for the vertical phase. -/
theorem blinker_v_canonical : Canonical blinker_v := by
  have h : blinker_v = sortDedup blinker_v := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Step equations of the blinker, by the **kernel** reducer: the bestiary
`Bool` form (`blinker_step`) does not provide the equality. -/
theorem blinker_h_step : step blinker_h = blinker_v := by decide
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Likewise, vertical phase to horizontal phase: the period-2 loop. -/
theorem blinker_v_step : step blinker_v = blinker_h := by decide
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Step equation of the toad: phase 0 to the second phase. -/
theorem toad_step : step toad = toadP2 := by decide
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Likewise, second phase to phase 0: the period-2 loop is closed. -/
theorem toadP2_step : step toadP2 = toad := by decide
/-- Phase chain under `evolve 1`: horizontal blinker. -/
theorem blinker_ev1 : evolve 1 blinker_h = blinker_v := blinker_h_step
/-- Phase chain: vertical blinker. -/
theorem blinkerV_ev1 : evolve 1 blinker_v = blinker_h := blinker_v_step
/-- Phase chain: toad, phase 0. -/
theorem toad_ev1 : evolve 1 toad = toadP2 := toad_step
/-- Phase chain: toad, second phase. -/
theorem toadP2_ev1 : evolve 1 toadP2 = toad := toadP2_step
set_option maxRecDepth 1000000 in
/-- Reconstruction frame of the horizontal blinker: box `[0, 2] × [0, 0]`,
offset `(-2, -2)`. -/
theorem blinker_frame_off : (gridToMacroCellWithOffset blinker_h).1 = (-2, -2) := by decide
set_option maxRecDepth 1000000 in
/-- Level of the horizontal blinker's frame: side `max(2, 0) + 5 = 7` →
level 3, frame `[-2, 6)²`. -/
theorem blinker_frame_lvl : (gridToMacroCellWithOffset blinker_h).2.level = 3 := by decide
set_option maxRecDepth 1000000 in
/-- Frame of the vertical phase: box `[1, 1] × [-1, 1]`, offset `(-1, -3)`. -/
theorem blinkerV_frame_off : (gridToMacroCellWithOffset blinker_v).1 = (-1, -3) := by decide
set_option maxRecDepth 1000000 in
/-- Level of the vertical phase's frame: level 3. -/
theorem blinkerV_frame_lvl : (gridToMacroCellWithOffset blinker_v).2.level = 3 := by decide
set_option maxRecDepth 1000000 in
/-- Toad frame, phase 0: box `[0, 3] × [0, 1]`, offset `(-2, -2)`. -/
theorem toad_frame_off : (gridToMacroCellWithOffset toad).1 = (-2, -2) := by decide
set_option maxRecDepth 1000000 in
/-- Level of the toad's frame, phase 0: side `max(3, 1) + 5 = 8` → level 3. -/
theorem toad_frame_lvl : (gridToMacroCellWithOffset toad).2.level = 3 := by decide
set_option maxRecDepth 1000000 in
/-- Frame of the toad's second phase: box `[0, 3] × [-1, 2]`, offset
`(-2, -3)`. -/
theorem toadP2_frame_off : (gridToMacroCellWithOffset toadP2).1 = (-2, -3) := by decide
set_option maxRecDepth 1000000 in
/-- Level of the second phase's frame: level 3. -/
theorem toadP2_frame_lvl : (gridToMacroCellWithOffset toadP2).2.level = 3 := by decide
/-- Period 2 of the blinker proved by the **kernel**: composition of the two
step equations. -/
theorem blinker_period_two_kernel : evolve 2 blinker_h = blinker_h := by
  rw [evolve_two, blinker_ev1, blinkerV_ev1]
/-- Period 2 of the toad proved by the **kernel**. -/
theorem toad_period_two_kernel : evolve 2 toad = toad := by
  rw [evolve_two, toad_ev1, toadP2_ev1]
/-- Dyadic divisibility of the blinker: both phases have level-3 frames and
`2 ∣ 2^3`. This finite premise is what separates this class from the
pulsar's (`3 ∤ 2^level`). -/
theorem blinker_hdiv : ∀ i, i < 2 →
    2 ∣ 2 ^ (gridToMacroCellWithOffset (evolve i blinker_h)).2.level := by
  intro i hi
  interval_cases i
  · rw [evolve_zero, blinker_frame_lvl]
    decide
  · rw [blinker_ev1, blinkerV_frame_lvl]
    decide
/-- Dyadic divisibility of the toad: both phases have level-3 frames. -/
theorem toad_hdiv : ∀ i, i < 2 →
    2 ∣ 2 ^ (gridToMacroCellWithOffset (evolve i toad)).2.level := by
  intro i hi
  interval_cases i
  · rw [evolve_zero, toad_frame_lvl]
    decide
  · rw [toad_ev1, toadP2_frame_lvl]
    decide
/-- Containment of the 4 phase combinations `(r, i) < 2 × 2` of the blinker:
each image `evolve i (evolve r blinker_h)` lives in the reconstruction frame
of phase `r`. Both phases fit in a level-3 frame (side 8), which absorbs the
offset between phases. -/
theorem blinker_hwin : ∀ r, r < 2 → ∀ i, i < 2 → ∀ p ∈ evolve i (evolve r blinker_h),
    (gridToMacroCellWithOffset (evolve r blinker_h)).1.1 ≤ p.1 ∧
      p.1 < (gridToMacroCellWithOffset (evolve r blinker_h)).1.1
        + (2 ^ (gridToMacroCellWithOffset (evolve r blinker_h)).2.level : Int) ∧
    (gridToMacroCellWithOffset (evolve r blinker_h)).1.2 ≤ p.2 ∧
      p.2 < (gridToMacroCellWithOffset (evolve r blinker_h)).1.2
        + (2 ^ (gridToMacroCellWithOffset (evolve r blinker_h)).2.level : Int) := by
  intro r hr i hi
  interval_cases r <;> interval_cases i <;>
    simp only [evolve_zero, blinker_ev1, blinkerV_ev1] <;>
    first
    | (rw [blinker_frame_off, blinker_frame_lvl]; decide)
    | (rw [blinkerV_frame_off, blinkerV_frame_lvl]; decide)
/-- Containment of the 4 phase combinations `(r, i) < 2 × 2` of the toad. -/
theorem toad_hwin : ∀ r, r < 2 → ∀ i, i < 2 → ∀ p ∈ evolve i (evolve r toad),
    (gridToMacroCellWithOffset (evolve r toad)).1.1 ≤ p.1 ∧
      p.1 < (gridToMacroCellWithOffset (evolve r toad)).1.1
        + (2 ^ (gridToMacroCellWithOffset (evolve r toad)).2.level : Int) ∧
    (gridToMacroCellWithOffset (evolve r toad)).1.2 ≤ p.2 ∧
      p.2 < (gridToMacroCellWithOffset (evolve r toad)).1.2
        + (2 ^ (gridToMacroCellWithOffset (evolve r toad)).2.level : Int) := by
  intro r hr i hi
  interval_cases r <;> interval_cases i <;>
    simp only [evolve_zero, toad_ev1, toadP2_ev1] <;>
    first
    | (rw [toad_frame_off, toad_frame_lvl]; decide)
    | (rw [toadP2_frame_off, toadP2_frame_lvl]; decide)
/-- Capstone: the blinker is admitted through `hcap_of_period` — first
**dyadic** witness of the periodic class. For every horizon `t`, the
reconstruction of `evolve t blinker_h` is captured by Hashlife. -/
theorem blinker_hcap_of_period :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t blinker_h)).2 = true :=
  hcap_of_period blinker_h blinker_h_canonical (by decide)
    blinker_period_two_kernel blinker_hdiv
/-- Capstone: the toad is admitted through `hcap_of_period`. -/
theorem toad_hcap_of_period :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t toad)).2 = true :=
  hcap_of_period toad toad_canonical (by decide)
    toad_period_two_kernel toad_hdiv


/-! ## Translation invariance of the reconstruction (tranche 3, step 7, brick 1)

Step-7 scoping identifies the missing brick for the **spaceship** class
(`evolve p g = shift v g`, drift + period): the reconstruction
`gridToMacroCellWithOffset` is **invariant under translation** — translating the
grid shifts the frame offset but leaves the MacroCell (the quadtree) unchanged.
This is what reduces a spaceship trajectory to its `p` phases: every
`evolve t g` is a `shift` of some phase, and the `shift` vanishes when entering
the reconstruction. The chain: translated bounding-box bounds
(`gridRowMin_shift` etc., via attainment witnesses and `mem_shift`), then the
frame follows (`gridFrame_shift`: offset translated, level unchanged since the
spans are invariant), then the quadtree follows (`buildFromGrid_shift`, by
induction on the level via `elem`/`mem_shift`), hence the reconstructed
MacroCell is the same (`gridToMacroCellWithOffset_shift`). -/

/-- The image of a live cell is live in the translated grid: direct form
    (the ← direction of `mem_shift`), explicit witness. -/
theorem mem_shift_image (v : Int × Int) (g : Grid) (p : Int × Int) (hp : p ∈ g) :
    (p.1 + v.1, p.2 + v.2) ∈ shift v g := by
  rw [mem_shift]
  have heq : (p.1 + v.1 - v.1, p.2 + v.2 - v.2) = p := by ext <;> omega
  rw [heq]; exact hp

/-- Translation preserves non-emptiness: the image of a live cell witnesses
    that `shift v g` is not empty. -/
theorem shift_ne_nil (v : Int × Int) (g : Grid) (hg : g ≠ []) : shift v g ≠ [] := by
  obtain ⟨p, hp⟩ : ∃ p, p ∈ g := by
    cases g with
    | nil => exact absurd rfl hg
    | cons p ps => exact ⟨p, by simp⟩
  intro hnil
  have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
  rw [hnil] at himg
  exact absurd himg (by simp)

/-- **Generic helper: a `foldl` of `max` (via `proj`) is *attained*** — the
    result is either the seed `acc` or the projection of a list element.
    Twin of `foldl_proj_min_attained` (MacroCell L572) for the max, with the
    `le_total` branches swapped. -/
theorem foldl_proj_max_attained (ps : Grid) (proj : Int × Int → Int) (acc : Int) :
    ps.foldl (fun m q => max m (proj q)) acc = acc ∨
    ∃ p ∈ ps, ps.foldl (fun m q => max m (proj q)) acc = proj p := by
  induction ps generalizing acc with
  | nil => left; rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    rcases ih (max acc (proj q)) with h | ⟨p, hp, hval⟩
    · rcases le_total acc (proj q) with hle | hle
      · right; exact ⟨q, by simp, by rw [h]; omega⟩
      · left; rw [h]; omega
    · right; exact ⟨p, by simp [hp], hval⟩

/-- The row maximum of a non-empty grid is *attained* by a live cell.
    Row twin of `gridRowMax_mem`'s column siblings of `gridRowMin_mem`
    (MacroCell L590). -/
theorem gridRowMax_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.1 = gridRowMax g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridRowMax]
    rcases foldl_proj_max_attained ps (·.1) p₀.1 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- The column minimum of a non-empty grid is *attained* by a live cell.
    Column twin of `gridRowMin_mem`. -/
theorem gridColMin_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.2 = gridColMin g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMin]
    rcases foldl_proj_min_attained ps (·.2) p₀.2 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- The column maximum of a non-empty grid is *attained* by a live cell.
    Column twin of `gridRowMin_mem`. -/
theorem gridColMax_mem (g : Grid) (hg : g ≠ []) :
    ∃ p ∈ g, p.2 = gridColMax g := by
  cases g with
  | nil => exact absurd rfl hg
  | cons p₀ ps =>
    simp only [gridColMax]
    rcases foldl_proj_max_attained ps (·.2) p₀.2 with h | ⟨p, hp, hval⟩
    · exact ⟨p₀, by simp, h.symm⟩
    · exact ⟨p, by simp [hp], hval.symm⟩

/-- The bounding box follows the translation: row minimum translated by
    `v.1`. Each direction closes by the attainment witness on one side
    (`gridRowMin_mem`), the global bound on the other
    (`gridRowMin_lower_bound`, step 5). -/
theorem gridRowMin_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridRowMin (shift v g) = gridRowMin g + v.1 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · obtain ⟨p, hp, hval⟩ := gridRowMin_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := gridRowMin_le_of_mem _ _ himg
    omega
  · apply gridRowMin_lower_bound _ _ hsne
    intro r hr
    have hpre : (r.1 - v.1, r.2 - v.2) ∈ g := (mem_shift v g r).mp hr
    have := gridRowMin_le_of_mem g _ hpre
    omega

/-- The bounding box follows the translation: row maximum translated by
    `v.1`. Mirror of `gridRowMin_shift` with `gridRowMax_mem` (attainment)
    and `gridRowMax_upper_bound` (bound, step 5). -/
theorem gridRowMax_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridRowMax (shift v g) = gridRowMax g + v.1 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · have hb := gridRowMax_upper_bound (shift v g) (gridRowMax g + v.1 + 1) hsne
      (fun p hp => by
        have hpre : (p.1 - v.1, p.2 - v.2) ∈ g := (mem_shift v g p).mp hp
        have := le_gridRowMax_of_mem g _ hpre
        omega)
    omega
  · obtain ⟨p, hp, hval⟩ := gridRowMax_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := le_gridRowMax_of_mem _ _ himg
    omega

/-- The bounding box follows the translation: column minimum translated by
    `v.2`. Column mirror of `gridRowMin_shift`. -/
theorem gridColMin_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridColMin (shift v g) = gridColMin g + v.2 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · obtain ⟨p, hp, hval⟩ := gridColMin_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := gridColMin_le_of_mem _ _ himg
    omega
  · apply gridColMin_lower_bound _ _ hsne
    intro r hr
    have hpre : (r.1 - v.1, r.2 - v.2) ∈ g := (mem_shift v g r).mp hr
    have := gridColMin_le_of_mem g _ hpre
    omega

/-- The bounding box follows the translation: column maximum translated by
    `v.2`. Column mirror of `gridRowMax_shift`. -/
theorem gridColMax_shift (v : Int × Int) (g : Grid) (hg : g ≠ []) :
    gridColMax (shift v g) = gridColMax g + v.2 := by
  have hsne : shift v g ≠ [] := shift_ne_nil v g hg
  apply le_antisymm
  · have hb := gridColMax_upper_bound (shift v g) (gridColMax g + v.2 + 1) hsne
      (fun p hp => by
        have hpre : (p.1 - v.1, p.2 - v.2) ∈ g := (mem_shift v g p).mp hp
        have := le_gridColMax_of_mem g _ hpre
        omega)
    omega
  · obtain ⟨p, hp, hval⟩ := gridColMax_mem g hg
    have himg : (p.1 + v.1, p.2 + v.2) ∈ shift v g := mem_shift_image v g p hp
    have := le_gridColMax_of_mem _ _ himg
    omega

/-- The leaf test of `buildFromGrid` is translation-invariant: `elem` at the
    translated point of the translated grid equals `elem` at the original
    point of the original grid. Both directions of `mem_shift` close the
    mixed cases. -/
theorem elem_shift (v : Int × Int) (g : Grid) (r0 c0 : Int) :
    (shift v g).elem (r0 + v.1, c0 + v.2) = g.elem (r0, c0) := by
  by_cases h : (r0, c0) ∈ g
  · rw [List.elem_iff.mpr h]
    exact List.elem_iff.mpr (mem_shift_image v g _ h)
  · have hf : g.elem (r0, c0) = false := by
      cases hbool : g.elem (r0, c0) with
      | true => exact absurd (List.elem_iff.mp hbool) h
      | false => rfl
    have hf' : (shift v g).elem (r0 + v.1, c0 + v.2) = false := by
      cases hbool : (shift v g).elem (r0 + v.1, c0 + v.2) with
      | true =>
        exact absurd (List.elem_iff.mp hbool) (fun hm => h (by
          have hpre := (mem_shift v g _).mp hm
          have heq : (r0 + v.1 - v.1, c0 + v.2 - v.2) = (r0, c0) := by ext <;> omega
          rw [heq] at hpre
          exact hpre))
      | false => rfl
    rw [hf', hf]

/-- **The quadtree follows the translation**: rebuilding the translated grid
    from the translated origin gives back the original quadtree. Induction on
    the level — leaf by `elem_shift`, node by IH on the four quadrants (the
    quadrant offsets `(r0 + v.1) + 2^n` re-associate to `(r0 + 2^n) + v.1` by
    `ring` on the casts). -/
theorem buildFromGrid_shift (v : Int × Int) (g : Grid) (r0 c0 : Int) (lvl : Nat) :
    MacroCell.buildFromGrid (shift v g) (r0 + v.1) (c0 + v.2) lvl
      = MacroCell.buildFromGrid g r0 c0 lvl := by
  induction lvl generalizing r0 c0 with
  | zero =>
    simp only [MacroCell.buildFromGrid]
    rw [elem_shift]
  | succ n ih =>
    simp only [MacroCell.buildFromGrid]
    rw [show (c0 : Int) + v.2 + (2 ^ n : Nat) = c0 + (2 ^ n : Nat) + v.2 from by
        push_cast; ring,
        show (r0 : Int) + v.1 + (2 ^ n : Nat) = r0 + (2 ^ n : Nat) + v.1 from by
        push_cast; ring,
        ih r0 c0, ih r0 (c0 + (2 ^ n : Nat)),
        ih (r0 + (2 ^ n : Nat)) c0, ih (r0 + (2 ^ n : Nat)) (c0 + (2 ^ n : Nat))]

/-- **The frame follows the translation**: `gridFrame` of the translated grid
    equals the original frame with translated offset and the **same level** —
    the spans `(rMax + v) - (rMin + v)` are invariant, so height, width and
    `ceilLog2` coincide. -/
theorem gridFrame_shift (v : Int × Int) (g : Grid) (r0 c0 : Int) (lvl : Nat)
    (hframe : gridFrame g = ((r0, c0), lvl)) (hne : g ≠ []) :
    gridFrame (shift v g) = ((r0 + v.1, c0 + v.2), lvl) := by
  cases g with
  | nil => exact absurd rfl hne
  | cons p₀ ps =>
    have hne' : p₀ :: ps ≠ [] := List.cons_ne_nil p₀ ps
    have hsne : shift v (p₀ :: ps) ≠ [] := shift_ne_nil v _ hne'
    obtain ⟨q₀, qs, hq⟩ : ∃ q₀ qs, shift v (p₀ :: ps) = q₀ :: qs := by
      cases h : shift v (p₀ :: ps) with
      | nil => exact absurd h hsne
      | cons q₀ qs => exact ⟨q₀, qs, rfl⟩
    have h1 : gridRowMin (q₀ :: qs) = gridRowMin (p₀ :: ps) + v.1 := by
      rw [← hq]; exact gridRowMin_shift v _ hne'
    have h2 : gridRowMax (q₀ :: qs) = gridRowMax (p₀ :: ps) + v.1 := by
      rw [← hq]; exact gridRowMax_shift v _ hne'
    have h3 : gridColMin (q₀ :: qs) = gridColMin (p₀ :: ps) + v.2 := by
      rw [← hq]; exact gridColMin_shift v _ hne'
    have h4 : gridColMax (q₀ :: qs) = gridColMax (p₀ :: ps) + v.2 := by
      rw [← hq]; exact gridColMax_shift v _ hne'
    have hfr : gridFrame (p₀ :: ps)
        = ((gridRowMin (p₀ :: ps) - 2, gridColMin (p₀ :: ps) - 2),
           MacroCell.ceilLog2 (max (gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat
                                    (gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat)) := rfl
    rw [hfr] at hframe
    rw [Prod.mk.injEq] at hframe
    obtain ⟨hp, hlvl⟩ := hframe
    rw [Prod.mk.injEq] at hp
    obtain ⟨hr0, hc0⟩ := hp
    rw [hq]
    have hfr' : gridFrame (q₀ :: qs)
        = ((gridRowMin (q₀ :: qs) - 2, gridColMin (q₀ :: qs) - 2),
           MacroCell.ceilLog2 (max (gridRowMax (q₀ :: qs) - gridRowMin (q₀ :: qs) + 5).toNat
                                    (gridColMax (q₀ :: qs) - gridColMin (q₀ :: qs) + 5).toNat)) := rfl
    rw [hfr']
    have hrnn : gridRowMin (p₀ :: ps) ≤ gridRowMax (p₀ :: ps) :=
      gridRowMin_le_gridRowMax _ hne'
    have hcnn : gridColMin (p₀ :: ps) ≤ gridColMax (p₀ :: ps) :=
      gridColMin_le_gridColMax _ hne'
    refine Prod.ext (Prod.ext ?_ ?_) ?_
    · dsimp only; omega
    · dsimp only; omega
    · have hH : (gridRowMax (q₀ :: qs) - gridRowMin (q₀ :: qs) + 5).toNat
          = (gridRowMax (p₀ :: ps) - gridRowMin (p₀ :: ps) + 5).toNat := by omega
      have hW : (gridColMax (q₀ :: qs) - gridColMin (q₀ :: qs) + 5).toNat
          = (gridColMax (p₀ :: ps) - gridColMin (p₀ :: ps) + 5).toNat := by omega
      rw [hH, hW, hlvl]

/-- **The reconstruction is translation-invariant** (conclusion of brick 1):
    the MacroCell rebuilt from a translated grid is exactly the one of the
    original grid — only the frame offset moves. Empty case: both
    reconstructions are the dead level-0 leaf. Non-empty case:
    `gridFrame_shift` + `buildFromGrid_shift`. -/
theorem gridToMacroCellWithOffset_shift (v : Int × Int) (g : Grid) :
    (gridToMacroCellWithOffset (shift v g)).2 = (gridToMacroCellWithOffset g).2 := by
  by_cases hg : g = []
  · subst hg
    have hnil : shift v [] = [] := rfl
    rw [hnil]
  · obtain ⟨r0, c0, lvl, hframe⟩ : ∃ r0 c0 lvl, gridFrame g = ((r0, c0), lvl) :=
      ⟨(gridFrame g).1.1, (gridFrame g).1.2, (gridFrame g).2, rfl⟩
    have hframe' := gridFrame_shift v g r0 c0 lvl hframe hg
    simp only [gridToMacroCellWithOffset, hframe, hframe']
    exact buildFromGrid_shift v g r0 c0 lvl

/-! ## L3 spaceship class — hcap of spaceships (tranche 3, step 7)

Third L3 link **entirely closed**: the spaceship class
(`evolve p g = shift v g` — the `IsSpaceship p v g` API of HashlifeCorrectness
unfolds to exactly `0 < p ∧ Canonical g ∧ evolve p g = shift v g`, so these
statements apply verbatim to the bestiary spaceships: glider `p = 4`,
`v = (1, -1)`, LWSS `p = 4`, `v = (0, 2)`).

The composition that the po-2025 adjoint explicitly reserved to po-2024:
drift replaces the oscillator fixed point, so the capture combines
(i) the **reduction to the residue modulo `p` with drift** — `evolve t g` is a
`shift ((t/p)•v)` of the phase `evolve (t%p) g`; (ii) **translation invariance
of the reconstruction** (brick 1) — the `shift` vanishes inside
`gridToMacroCellWithOffset`, reducing the capture to the `p` phases only;
(iii) **the jump window absorbs the drift** — the padded content lives in
`[3·2^(k-1), 5·2^(k-1))` and `q = 2^k/p` periods drift it by `q•v`, so the
test window `[2^k, 2^k + 2^(k+1))²` contains the final generation iff
`|q·v.i| ≤ 2^(k-1)`, i.e. **`2·|v.i| ≤ p` — speed at most c/2**. LWSS
(`v = (0, 2)`, `p = 4`) attains the bound exactly; the glider (`v = (1, -1)`,
`p = 4`) satisfies it strictly. -/

/-- **Every phase of a spaceship is a spaceship.** If
    `evolve p g = shift v g`, then every phase `evolve r g` satisfies the same
    relation: evolution commutes with itself and with the shift. Exact mirror
    of `evolve_phase_fix` with the fixed point replaced by the drift
    relation. -/
theorem evolve_spaceship_phase {p : Nat} (g : Grid) (v : Int × Int)
    (hship : evolve p g = shift v g) (r : Nat) :
    evolve p (evolve r g) = shift v (evolve r g) := by
  rw [← evolve_add, Nat.add_comm p r, evolve_add, hship, evolve_shift]

/-- **`m` spaceship periods drift by `m•v`.** Adapted local copy of
    `evolve_mulF_of_period`: `evolve (m * p) g = shift (m•v) g`, by induction
    on `m` via `evolve_add`, `evolve_shift` and `shift_shift`. The base case
    requires `shift_zero` (canonical grid). -/
theorem evolve_spaceship_mulF {p : Nat} (g : Grid) (hg : Canonical g) (v : Int × Int)
    (hship : evolve p g = shift v g) (m : Nat) :
    evolve (m * p) g = shift (((m : Int) * v.1), ((m : Int) * v.2)) g := by
  induction m with
  | zero =>
    rw [Nat.zero_mul, evolve_zero, Nat.cast_zero, Int.zero_mul, Int.zero_mul]
    exact (shift_zero hg).symm
  | succ m ih =>
    have hsplit : (m + 1) * p = m * p + p := by ring
    rw [hsplit, evolve_add, hship, ← evolve_shift, ih, shift_shift]
    have h1 : v.1 + ((m : Int) * v.1) = ((m + 1 : Nat) : Int) * v.1 := by
      rw [Nat.cast_succ]; ring
    have h2 : v.2 + ((m : Int) * v.2) = ((m + 1 : Nat) : Int) * v.2 := by
      rw [Nat.cast_succ]; ring
    rw [h1, h2]

/-- **Trajectory reduction to the residue modulo `p`, with drift.** For a
    spaceship, `evolve t g = shift ((t/p)•v) (evolve (t % p) g)` — the
    quotient `t / p` of complete periods becomes a componentwise translation,
    the residue `t % p` carries the phase. Mirror of `evolve_mod_period`
    where the quotient did not vanish but became a shift. -/
theorem evolve_spaceship_mod {p : Nat} (g : Grid) (hg : Canonical g) (v : Int × Int)
    (hship : evolve p g = shift v g) (t : Nat) :
    evolve t g = shift (((t / p : Nat) : Int) * v.1, ((t / p : Nat) : Int) * v.2)
      (evolve (t % p) g) := by
  have hsplit : t = p * (t / p) + t % p := (Nat.div_add_mod t p).symm
  have hg' : Canonical (evolve (t % p) g) := by
    rcases Nat.eq_zero_or_pos (t % p) with h0 | hpos
    · rw [h0, evolve_zero]; exact hg
    · exact canonical_evolve_of_pos hpos _
  conv_lhs => rw [hsplit, evolve_add, Nat.mul_comm]
  exact evolve_spaceship_mulF _ hg' v (evolve_spaceship_phase g v hship _) _

/-- **Interface (c) tranche 3, step 7 — the spaceship class of speed ≤ c/2 is
    captured.** `jumpCapturedF` version of the spaceship criterion: any
    pattern `evolve p (c.toGrid (0,0)) = shift v (c.toGrid (0,0))` carried by
    a well-formed cell of level `k ≥ 1`, with `p ∣ 2^k` and the speed bound
    `2·|v.i| ≤ p` (both signs, each coordinate), satisfies the capture
    predicate. The final generation of the jump is the padded content drifted
    by `q•v` (`q = 2^k/p`): the content lives in
    `[3·2^(k-1), 5·2^(k-1))²` (geometry `padCenter2` + `cellWfF_toGrid_bounds`),
    the drift moves it by at most `2^(k-1)` per coordinate, so it stays inside
    the test window `[2^k, 2^k + 2^(k+1))²`. Product monotonicity
    `q·(2·v.i) ≤ q·p = 2^k` turns the speed bound into a drift bound — the
    only non-linear step, established explicitly. -/
theorem jumpCapturedF_of_spaceship (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level) {p : Nat} (v : Int × Int)
    (hship : evolve p (c.toGrid (0, 0)) = shift v (c.toGrid (0, 0)))
    (hdiv : p ∣ 2 ^ c.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    jumpCapturedF c = true := by
  obtain ⟨hspd1a, hspd1b⟩ := hspd1
  obtain ⟨hspd2a, hspd2b⟩ := hspd2
  obtain ⟨q, hq⟩ := hdiv
  have hcw : cellWf c := cellWf_of_wf c hwf
  have hcan : Canonical (c.toGrid (0, 0)) := canonical_sortDedup _
  have hmul : evolve (2 ^ c.level) (c.toGrid (0, 0))
      = shift ((q : Int) * v.1, (q : Int) * v.2) (c.toGrid (0, 0)) := by
    rw [hq, Nat.mul_comm]
    exact evolve_spaceship_mulF _ hcan v hship q
  have hfinal : evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))
      = shift ((3 * 2 ^ (c.level - 1) : Int) + (q : Int) * v.1,
               (3 * 2 ^ (c.level - 1) : Int) + (q : Int) * v.2)
          (c.toGrid (0, 0)) := by
    rw [padCenter2_toGrid_shift c hlvl, ← evolve_shift, hmul, shift_shift]
  rw [jumpCapturedF_iff]
  intro p' hp'
  rw [hfinal, mem_shift] at hp'
  obtain ⟨hb1, hb2, hb3, hb4⟩ := cellWfF_toGrid_bounds hcw 0 0 hp'
  dsimp only at hb1 hb2 hb3 hb4
  have hpow : (2 ^ c.level : Int) = 2 * (2 ^ (c.level - 1) : Int) := by
    have hsplit : c.level = (c.level - 1) + 1 := by omega
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hnext : ((2 ^ (c.level + 1) : Nat) : Int)
      = (2 ^ c.level : Int) + (2 ^ c.level : Int) := by
    rw [Nat.cast_pow, pow_succ]
    ring
  have hy : (0 : Int) ≤ 2 ^ (c.level - 1) := by positivity
  have hqnn : (0 : Int) ≤ (q : Nat) := by positivity
  have hcast : ((q : Nat) : Int) * ((p : Nat) : Int) = ((2 ^ c.level : Nat) : Int) := by
    rw [← Nat.cast_mul, Nat.mul_comm q p, hq]
  have hbridge : ((2 ^ c.level : Nat) : Int) = (2 ^ c.level : Int) :=
    (Nat.cast_pow 2 c.level).symm
  have hqA : 2 * ((q : Int) * v.1) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (2 * v.1) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left hspd1b hqnn
    have e1 : (q : Int) * (2 * v.1) = 2 * ((q : Int) * v.1) := by ring
    omega
  have hqB : 2 * (-((q : Int) * v.1)) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (-(2 * v.1)) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left (by omega) hqnn
    have e1 : (q : Int) * (-(2 * v.1)) = 2 * (-((q : Int) * v.1)) := by ring
    omega
  have hqC : 2 * ((q : Int) * v.2) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (2 * v.2) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left hspd2b hqnn
    have e1 : (q : Int) * (2 * v.2) = 2 * ((q : Int) * v.2) := by ring
    omega
  have hqD : 2 * (-((q : Int) * v.2)) ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : (q : Int) * (-(2 * v.2)) ≤ (q : Int) * ((p : Nat) : Int) :=
      mul_le_mul_of_nonneg_left (by omega) hqnn
    have e1 : (q : Int) * (-(2 * v.2)) = 2 * (-((q : Int) * v.2)) := by ring
    omega
  omega

/-- **Commutativity of translations.** Translating by `v` then by `w` equals
    translating by `w` then by `v`: both compositions land on the sum vector.
    Via `shift_shift` on each side (pairs made explicit), then componentwise
    equality of the vectors. -/
theorem shift_comm (v w : Int × Int) (g : Grid) :
    shift v (shift w g) = shift w (shift v g) := by
  obtain ⟨v1, v2⟩ := v
  obtain ⟨w1, w2⟩ := w
  have h1 : shift (v1, v2) (shift (w1, w2) g) = shift (v1 + w1, v2 + w2) g :=
    shift_shift _ _ _ _ _
  have h2 : shift (w1, w2) (shift (v1, v2) g) = shift (w1 + v1, w2 + v2) g :=
    shift_shift _ _ _ _ _
  rw [h1, h2]
  congr 1
  ext <;> ring

/-- **Transport of the spaceship relation to the reconstruction (rendered at
    the origin).** The analogue of `periodic_fix_toGrid_zero` for drift: if
    `g` is canonical and satisfies `evolve p g = shift v g`, the MacroCell
    rebuilt at the origin satisfies the same relation — `toGrid_shift_grid`
    shuttle, `evolve_shift` commutation, EQUALITY round-trip. -/
theorem spaceship_step_toGrid_zero (g : Grid) (hg : Canonical g) {p : Nat}
    (v : Int × Int) (hship : evolve p g = shift v g) :
    evolve p ((gridToMacroCellWithOffset g).2.toGrid (0, 0))
      = shift v ((gridToMacroCellWithOffset g).2.toGrid (0, 0)) := by
  have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
      = g := toGrid_gridToMacroCellWithOffset_eq g hg
  have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
      = shift (0 - (gridToMacroCellWithOffset g).1.1,
               0 - (gridToMacroCellWithOffset g).1.2)
          ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
    toGrid_shift_grid _ 0 0 _ _
  rw [hshift, ← evolve_shift, hrt, hship, shift_comm]

/-- **Capture of the reconstruction of a spaceship.** For every canonical
    phase `g` of a spaceship (`evolve p g = shift v g`), whose reconstruction
    level divides the jump horizon (`p ∣ 2^level`) and whose speed satisfies
    `2·|v.i| ≤ p`, the reconstruction satisfies the jump predicate —
    `jumpCapturedF_of_spaceship` consumed at the reconstruction level, with
    wf (`buildFromGrid_wf`), level (`1 ≤ lvl` as soon as `g ≠ []`, n-aware
    bound) and the transported drift relation
    (`spaceship_step_toGrid_zero`). Empty case: the reconstruction is a dead
    level-0 leaf, decided by the kernel. -/
theorem jumpCapturedF_reconstruction_of_spaceship (g : Grid) (hg : Canonical g)
    {p : Nat} (v : Int × Int) (hship : evolve p g = shift v g)
    (hdiv : p ∣ 2 ^ (gridToMacroCellWithOffset g).2.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · have hwf : ((gridToMacroCellWithOffset g).2).wf = true := by
      unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    have hlvl : 1 ≤ (gridToMacroCellWithOffset g).2.level := by
      have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    exact jumpCapturedF_of_spaceship _ hwf hlvl v
      (spaceship_step_toGrid_zero g hg v hship) hdiv hspd1 hspd2

/-- **hcap of the spaceship class, full trajectory.** For a canonical
    spaceship of period `p > 0`, whose **every phase** has a reconstruction
    level divisible by `p` and whose speed satisfies `2·|v.i| ≤ p`, every
    instant `t` is captured: the trajectory reduces to the phase `t % p`
    **drifted** by `(t/p)•v` (`evolve_spaceship_mod`), the translation
    vanishes in the reconstruction (`gridToMacroCellWithOffset_shift`,
    brick 1), and the phase — canonical, itself a spaceship
    (`evolve_spaceship_phase`) — is captured. The divisibility and speed
    premises are finite: they concern the `p` phases only. -/
theorem hcap_of_spaceship (g : Grid) (hg : Canonical g) {p : Nat} (hp0 : 0 < p)
    (v : Int × Int) (hship : evolve p g = shift v g)
    (hdiv : ∀ i, i < p →
      p ∣ 2 ^ (gridToMacroCellWithOffset (evolve i g)).2.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  intro t
  rw [evolve_spaceship_mod g hg v hship t, gridToMacroCellWithOffset_shift]
  have hr : t % p < p := Nat.mod_lt _ hp0
  have hcan : Canonical (evolve (t % p) g) := by
    rcases Nat.eq_zero_or_pos (t % p) with h0 | hpos
    · rw [h0]
      simpa using hg
    · exact canonical_evolve_of_pos hpos _
  exact jumpCapturedF_reconstruction_of_spaceship _ hcan v
    (evolve_spaceship_phase g v hship _) (hdiv _ hr) hspd1 hspd2

/-- **L3 closed for the spaceship class of speed ≤ c/2: Hashlife correctness
    of spaceships.** Assembly corollary — the third case of the P4.4
    decomposition where the L3 link is **fully proven**, and the composition
    that the scoping reserved to this lane: for every MacroCell whose grid
    rendered at the origin is a spaceship `p > 0` of speed `2·|v.i| ≤ p`
    (every phase of level divisible by `p`), the global equality
    `hashlife_correctN` applies at every horizon `2^k` under `centralCorrect`.
    The class covers glider (`p = 4`, `v = (1, -1)`) and LWSS (`p = 4`,
    `v = (0, 2)`, the exact bound) as soon as the level reaches `log₂ p = 2`. -/
theorem hashlife_correct_margin_of_spaceship (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k) {p : Nat} (hp0 : 0 < p) (v : Int × Int)
    (hship : evolve p (c.toGrid (0, 0)) = shift v (c.toGrid (0, 0)))
    (hdiv : ∀ i, i < p →
      p ∣ 2 ^ (gridToMacroCellWithOffset (evolve i (c.toGrid (0, 0)))).2.level)
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_spaceship _ (canonical_sortDedup _) hp0 v hship hdiv hspd1 hspd2 t)

/-! ## Slice 9 — spaceships of arbitrary period (mirror of 8a/8b)

Mirror relaxation of slices 8a/8b, applied to the spaceship class: in
`jumpCapturedF_of_spaceship`, the divisibility `p ∣ 2^level` only served to build the
exact landing `evolve (2^level) g = shift (q•v) g` — which excludes de facto every
non-dyadic spaceship (the smallest known c/3 ship lives at period 3; sir Robin,
p = 6, is not a power of 2). Here the jump folds through `evolve_spaceship_mod` —
the phase `2^level % p` carried by the quotient drift `(2^level/p)•v` — against two
counterparts: **spatial** (`hwin`: every phase of the orbit fits in the
`[0, 2^level)²` origin-framed box) and **kinematic** (speed bounds unchanged,
`2·|v.i| ≤ p`: the quotient drift stays bounded by `2^(level-1)` since
`p·(2^level/p) ≤ 2^level`). The dyadic case remains an instance. -/

/-- **Slice 9 — capture of spaceships of arbitrary period.** Generalization of
    `jumpCapturedF_of_spaceship`: the divisibility `p ∣ 2^c.level` only served to
    build the exact landing ("the horizon-`2^level` jump lands on the q•v-drifted
    pattern"), which excludes de facto every non-dyadic period. Here the fold is
    modular (`evolve_spaceship_mod`: the jump lands on phase `2^level % p` carried
    by `(2^level/p)•v`), the spatial counterpart `hwin` asks every phase of the
    orbit to fit in the starting phase's box (bounds `[0, 2^level)²` at the origin
    framing — exactly what `cellWfF_toGrid_bounds` gives for the phase itself),
    and the speed bounds `2·|v.i| ≤ p` bound the drift: monotonicity
    `Q·(2·|v.i|) ≤ Q·p ≤ 2^level` (with `Q = 2^level/p`) yields
    `|Q·v.i| ≤ 2^(level-1)`, the phase lives in the box shifted by `3·2^(level-1)`,
    hence the final generation stays in the test window
    `[2^level, 2^level + 2^(level+1))²`. -/
theorem jumpCapturedF_of_spaceship_mod (c : MacroCell) (hwf : c.wf = true)
    (hlvl : 1 ≤ c.level) {p : Nat} (hp0 : 0 < p) (v : Int × Int)
    (hship : evolve p (c.toGrid (0, 0)) = shift v (c.toGrid (0, 0)))
    (hwin : ∀ i, i < p → ∀ w ∈ evolve i (c.toGrid (0, 0)),
      (0 : Int) ≤ w.1 ∧ w.1 < (2 ^ c.level : Int) ∧
        (0 : Int) ≤ w.2 ∧ w.2 < (2 ^ c.level : Int))
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    jumpCapturedF c = true := by
  obtain ⟨hspd1a, hspd1b⟩ := hspd1
  obtain ⟨hspd2a, hspd2b⟩ := hspd2
  have hr' : 2 ^ c.level % p < p := Nat.mod_lt _ hp0
  have hcan : Canonical (c.toGrid (0, 0)) := canonical_sortDedup _
  have hmod : evolve (2 ^ c.level) (c.toGrid (0, 0))
      = shift ((((2 ^ c.level / p : Nat) : Int) * v.1),
               (((2 ^ c.level / p : Nat) : Int) * v.2))
          (evolve (2 ^ c.level % p) (c.toGrid (0, 0))) :=
    evolve_spaceship_mod _ hcan v hship _
  have hfinal : evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))
      = shift ((3 * 2 ^ (c.level - 1) : Int)
                 + (((2 ^ c.level / p : Nat) : Int) * v.1),
               (3 * 2 ^ (c.level - 1) : Int)
                 + (((2 ^ c.level / p : Nat) : Int) * v.2))
          (evolve (2 ^ c.level % p) (c.toGrid (0, 0))) := by
    rw [padCenter2_toGrid_shift c hlvl, ← evolve_shift, hmod, shift_shift]
  rw [jumpCapturedF_iff]
  intro w hw
  rw [hfinal, mem_shift] at hw
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hwin _ hr' _ hw
  dsimp only at hb1 hb2 hb3 hb4
  have hpow : (2 ^ c.level : Int) = 2 * (2 ^ (c.level - 1) : Int) := by
    have hsplit : c.level = (c.level - 1) + 1 := by omega
    conv_lhs => rw [hsplit]
    rw [pow_succ]
    ring
  have hnext : ((2 ^ (c.level + 1) : Nat) : Int)
      = (2 ^ c.level : Int) + (2 ^ c.level : Int) := by
    rw [Nat.cast_pow, pow_succ]
    ring
  have hy : (0 : Int) ≤ 2 ^ (c.level - 1) := by positivity
  have hqnn : (0 : Int) ≤ ((2 ^ c.level / p : Nat) : Int) := by positivity
  have hqple : ((2 ^ c.level / p : Nat) : Int) * (p : Int)
      ≤ (2 ^ c.level : Int) := by
    exact_mod_cast Nat.div_mul_le_self _ _
  have hqA : 2 * (((2 ^ c.level / p : Nat) : Int) * v.1)
      ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : ((2 ^ c.level / p : Nat) : Int) * (2 * v.1)
        ≤ ((2 ^ c.level / p : Nat) : Int) * (p : Int) :=
      mul_le_mul_of_nonneg_left hspd1b hqnn
    have e1 : ((2 ^ c.level / p : Nat) : Int) * (2 * v.1)
        = 2 * (((2 ^ c.level / p : Nat) : Int) * v.1) := by ring
    omega
  have hqB : 2 * (-(((2 ^ c.level / p : Nat) : Int) * v.1))
      ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : ((2 ^ c.level / p : Nat) : Int) * (-(2 * v.1))
        ≤ ((2 ^ c.level / p : Nat) : Int) * (p : Int) :=
      mul_le_mul_of_nonneg_left (by omega) hqnn
    have e1 : ((2 ^ c.level / p : Nat) : Int) * (-(2 * v.1))
        = 2 * (-(((2 ^ c.level / p : Nat) : Int) * v.1)) := by ring
    omega
  have hqC : 2 * (((2 ^ c.level / p : Nat) : Int) * v.2)
      ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : ((2 ^ c.level / p : Nat) : Int) * (2 * v.2)
        ≤ ((2 ^ c.level / p : Nat) : Int) * (p : Int) :=
      mul_le_mul_of_nonneg_left hspd2b hqnn
    have e1 : ((2 ^ c.level / p : Nat) : Int) * (2 * v.2)
        = 2 * (((2 ^ c.level / p : Nat) : Int) * v.2) := by ring
    omega
  have hqD : 2 * (-(((2 ^ c.level / p : Nat) : Int) * v.2))
      ≤ 2 * (2 ^ (c.level - 1) : Int) := by
    have e0 : ((2 ^ c.level / p : Nat) : Int) * (-(2 * v.2))
        ≤ ((2 ^ c.level / p : Nat) : Int) * (p : Int) :=
      mul_le_mul_of_nonneg_left (by omega) hqnn
    have e1 : ((2 ^ c.level / p : Nat) : Int) * (-(2 * v.2))
        = 2 * (-(((2 ^ c.level / p : Nat) : Int) * v.2)) := by ring
    omega
  omega

/-- **Slice 9 — capture of a spaceship's reconstruction, arbitrary periods.**
    Variant of `jumpCapturedF_reconstruction_of_spaceship`: the divisibility
    premise is replaced by the containment of the phases in `g`'s reconstruction
    frame (absolute coordinates). The transport to the cell's origin framing goes
    through `toGrid_shift_grid` + `evolve_shift`. -/
theorem jumpCapturedF_reconstruction_of_spaceship_mod (g : Grid) (hg : Canonical g)
    {p : Nat} (hp0 : 0 < p) (v : Int × Int) (hship : evolve p g = shift v g)
    (hwin : ∀ i, i < p → ∀ w ∈ evolve i g,
      (gridToMacroCellWithOffset g).1.1 ≤ w.1 ∧
        w.1 < (gridToMacroCellWithOffset g).1.1
          + (2 ^ (gridToMacroCellWithOffset g).2.level : Int) ∧
      (gridToMacroCellWithOffset g).1.2 ≤ w.2 ∧
        w.2 < (gridToMacroCellWithOffset g).1.2
          + (2 ^ (gridToMacroCellWithOffset g).2.level : Int))
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    jumpCapturedF (gridToMacroCellWithOffset g).2 = true := by
  by_cases hne : g = []
  · subst hne
    decide
  · have hwf : ((gridToMacroCellWithOffset g).2).wf = true := by
      unfold gridToMacroCellWithOffset
      exact buildFromGrid_wf g _ _ _
    have hlvl : 1 ≤ (gridToMacroCellWithOffset g).2.level := by
      have hN := gridToMacroCellWithOffsetN_level_gt_n 2 g hne
      rw [gridToMacroCellWithOffsetN_le_two_eq 2 g (by omega)] at hN
      cases hL : (gridToMacroCellWithOffset g).2.level with
      | zero => rw [hL] at hN; exact absurd hN (by decide)
      | succ m => omega
    have hshift : (gridToMacroCellWithOffset g).2.toGrid (0, 0)
        = shift (0 - (gridToMacroCellWithOffset g).1.1,
            0 - (gridToMacroCellWithOffset g).1.2)
            ((gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1) :=
      toGrid_shift_grid _ 0 0 _ _
    have hrt : (gridToMacroCellWithOffset g).2.toGrid (gridToMacroCellWithOffset g).1
        = g := toGrid_gridToMacroCellWithOffset_eq g hg
    have hwin' : ∀ i, i < p → ∀ w ∈
        evolve i ((gridToMacroCellWithOffset g).2.toGrid (0, 0)),
      (0 : Int) ≤ w.1 ∧ w.1 < (2 ^ (gridToMacroCellWithOffset g).2.level : Int) ∧
        (0 : Int) ≤ w.2 ∧ w.2 < (2 ^ (gridToMacroCellWithOffset g).2.level : Int) := by
      intro i hi w hw
      rw [hshift, ← evolve_shift, mem_shift, hrt] at hw
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hwin i hi _ hw
      dsimp only at hb1 hb2 hb3 hb4
      omega
    exact jumpCapturedF_of_spaceship_mod _ hwf hlvl hp0 v
      (spaceship_step_toGrid_zero g hg v hship) hwin' hspd1 hspd2

/-- **Slice 9 — hcap of the spaceship class, arbitrary periods.** Variant of
    `hcap_of_spaceship`: every phase carries its own frame, and the premise asks
    the `p` phases of **each** starting phase's orbit to live in that phase's
    reconstruction frame — for a real spaceship, this is the same bounded
    neighborhood (transported by the drift), described `p` times. -/
theorem hcap_of_spaceship_mod (g : Grid) (hg : Canonical g) {p : Nat} (hp0 : 0 < p)
    (v : Int × Int) (hship : evolve p g = shift v g)
    (hwin : ∀ r, r < p → ∀ i, i < p → ∀ w ∈ evolve i (evolve r g),
      (gridToMacroCellWithOffset (evolve r g)).1.1 ≤ w.1 ∧
        w.1 < (gridToMacroCellWithOffset (evolve r g)).1.1
          + (2 ^ (gridToMacroCellWithOffset (evolve r g)).2.level : Int) ∧
      (gridToMacroCellWithOffset (evolve r g)).1.2 ≤ w.2 ∧
        w.2 < (gridToMacroCellWithOffset (evolve r g)).1.2
          + (2 ^ (gridToMacroCellWithOffset (evolve r g)).2.level : Int))
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t g)).2 = true := by
  intro t
  rw [evolve_spaceship_mod g hg v hship t, gridToMacroCellWithOffset_shift]
  have hr : t % p < p := Nat.mod_lt _ hp0
  have hcan : Canonical (evolve (t % p) g) := by
    rcases Nat.eq_zero_or_pos (t % p) with h0 | hpos
    · rw [h0]
      simpa using hg
    · exact canonical_evolve_of_pos hpos _
  exact jumpCapturedF_reconstruction_of_spaceship_mod _ hcan hp0 v
    (evolve_spaceship_phase g v hship _) (hwin _ hr) hspd1 hspd2

/-- **Slice 9 — L3 closed for the arbitrary-period spaceship class: Hashlife
    correctness.** Assembly corollary mirroring `hashlife_correct_margin_of_spaceship`:
    under orbit-phase containment (no more divisibility), the global equality applies
    at any horizon `2^k` under `centralCorrect`. Opens the class to non-dyadic
    spaceships (c/3 and beyond) as soon as the witness checks the containment. -/
theorem hashlife_correct_margin_of_spaceship_mod (c : MacroCell) (k : Nat)
    (h_central : centralCorrect c k) {p : Nat} (hp0 : 0 < p) (v : Int × Int)
    (hship : evolve p (c.toGrid (0, 0)) = shift v (c.toGrid (0, 0)))
    (hwin : ∀ r, r < p → ∀ i, i < p →
      ∀ w ∈ evolve i (evolve r (c.toGrid (0, 0))),
      (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.1 ≤ w.1 ∧
        w.1 < (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.1
          + (2 ^ (gridToMacroCellWithOffset
            (evolve r (c.toGrid (0, 0)))).2.level : Int) ∧
      (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.2 ≤ w.2 ∧
        w.2 < (gridToMacroCellWithOffset (evolve r (c.toGrid (0, 0)))).1.2
          + (2 ^ (gridToMacroCellWithOffset
            (evolve r (c.toGrid (0, 0)))).2.level : Int))
    (hspd1 : -(p : Int) ≤ 2 * v.1 ∧ 2 * v.1 ≤ (p : Int))
    (hspd2 : -(p : Int) ≤ 2 * v.2 ∧ 2 * v.2 ≤ (p : Int)) :
    evolveHashlifeFast (2^k) (c.toGrid (0, 0)) = evolve (2^k) (c.toGrid (0, 0)) :=
  hashlife_correct_margin_of_hcap c k h_central
    (fun t _ => hcap_of_spaceship_mod _ (canonical_sortDedup _) hp0 v hship
      hwin hspd1 hspd2 t)

/-! ### Flagship c/3 witness: Hickerson's 25P3H1V0.1 (tranche 10, admission)

First **non-dyadic spaceship** admitted through the relaxed chain of
tranche 9: 25P3H1V0.1 (Dean Hickerson, August 1989), the smallest known c/3
spaceship — 25 cells in each generation, 16×5 box, period 3, drift
`(-1, 0)` per period. Since 3 divides no power of 2, the dyadic chain
`p ∣ 2^level` of `jumpCapturedF_of_spaceship` structurally cannot admit it
— only the containment relaxation of tranche 9 reaches it. The three step
equations are proved by the **kernel** reducer (`decide`), without
`native_decide` (bestiary note c.212). The pattern is transcribed from the
canonical LifeWiki RLE (`conwaylife.com/patterns/25p3h1v0.1.rle`),
re-verified in Python before transcription: 25 cells per phase,
`evolve 3 = shift (-1, 0)` (measured). -/
/-- Phase 0 of 25P3H1V0.1 (25 cells, box `[0, 4] × [0, 15]`).
Lexicographically sorted literal. -/
def hickersonC3 : Grid :=
  [(0, 7), (0, 8), (0, 10), (1, 4), (1, 5), (1, 7), 
  (1, 9), (1, 10), (1, 12), (1, 13), (1, 14), (2, 1), 
  (2, 2), (2, 3), (2, 4), (2, 7), (2, 8), (2, 15), 
  (3, 0), (3, 5), (3, 9), (3, 13), (3, 14), (4, 1), 
  (4, 2)]
/-- Phase 1 (25 cells, box `[0, 4] × [0, 15]`). Sorted literal. -/
def hickersonC3P1 : Grid :=
  [(0, 6), (0, 7), (0, 8), (0, 10), (0, 11), (0, 13), 
  (1, 2), (1, 4), (1, 5), (1, 10), (1, 11), (1, 13), 
  (1, 14), (2, 1), (2, 2), (2, 3), (2, 7), (2, 10), 
  (2, 12), (2, 15), (3, 0), (3, 4), (3, 8), (3, 14), 
  (4, 1)]
/-- Phase 2 (25 cells, box `[-1, 3] × [0, 15]`): the only phase that
spills north of the 5×16 box. Sorted literal. -/
def hickersonC3P2 : Grid :=
  [(-1, 7), (0, 5), (0, 6), (0, 7), (0, 9), (0, 10), 
  (0, 11), (0, 13), (0, 14), (1, 1), (1, 2), (1, 4), 
  (1, 5), (1, 8), (1, 13), (1, 14), (2, 1), (2, 2), 
  (2, 5), (2, 9), (2, 10), (2, 12), (2, 15), (3, 0), 
  (3, 3)]
set_option maxRecDepth 1000000 in
/-- The definition is already canonical (sorted, duplicate-free): the
kernel certifies it, then `canonical_sortDedup` converts. -/
theorem hickersonC3_canonical : Canonical hickersonC3 := by
  have h : hickersonC3 = sortDedup hickersonC3 := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
/-- Same for phase 1. -/
theorem hickersonC3P1_canonical : Canonical hickersonC3P1 := by
  have h : hickersonC3P1 = sortDedup hickersonC3P1 := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
/-- Same for phase 2. -/
theorem hickersonC3P2_canonical : Canonical hickersonC3P2 := by
  have h : hickersonC3P2 = sortDedup hickersonC3P2 := by decide
  rw [h]
  exact canonical_sortDedup _
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Step equation by the kernel reducer: phase 0 evolves into phase 1. -/
theorem hickersonC3_step1 : step hickersonC3 = hickersonC3P1 := by decide
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Same, phase 1 to phase 2. -/
theorem hickersonC3P1_step : step hickersonC3P1 = hickersonC3P2 := by decide
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- Same, phase 2 to phase 0 **drifted by `(-1, 0)`**: the period-3 loop
closes with one spaceship step. -/
theorem hickersonC3P2_step : step hickersonC3P2 = shift (-1, 0) hickersonC3 := by decide
/-- Phase chain under `evolve 1`: phase 0. -/
theorem hickersonC3_ev1 : evolve 1 hickersonC3 = hickersonC3P1 := hickersonC3_step1
/-- Phase chain: phase 1. -/
theorem hickersonC3P1_ev1 : evolve 1 hickersonC3P1 = hickersonC3P2 := hickersonC3P1_step
/-- Phase chain: phase 2, drifted return. -/
theorem hickersonC3P2_ev1 : evolve 1 hickersonC3P2 = shift (-1, 0) hickersonC3 := hickersonC3P2_step
/-- Spaceship relation proved by the **kernel**: 25P3H1V0.1 has period 3
and drift `(-1, 0)` — composition of the three step equations. -/
theorem hickersonC3_spaceship : evolve 3 hickersonC3 = shift (-1, 0) hickersonC3 := by
  rw [evolve_three, hickersonC3_ev1, hickersonC3P1_ev1, hickersonC3P2_ev1]
set_option maxRecDepth 1000000 in
/-- Reconstruction frame of phase 0: offset `(-2, -2)` (margin 2 around
the box `[0, 4] × [0, 15]`). -/
theorem hickersonC3_frame_off : (gridToMacroCellWithOffset hickersonC3).1 = (-2, -2) := by decide
set_option maxRecDepth 1000000 in
/-- Frame level of phase 0: side `max(4+5, 15+5) = 20` → level 5, frame
`[-2, 30) × [-2, 30)`. -/
theorem hickersonC3_frame_lvl : (gridToMacroCellWithOffset hickersonC3).2.level = 5 := by decide
set_option maxRecDepth 1000000 in
/-- Frame of phase 1: same box as phase 0 → offset `(-2, -2)`. -/
theorem hickersonC3P1_frame_off : (gridToMacroCellWithOffset hickersonC3P1).1 = (-2, -2) := by decide
set_option maxRecDepth 1000000 in
/-- Frame level of phase 1: level 5. -/
theorem hickersonC3P1_frame_lvl : (gridToMacroCellWithOffset hickersonC3P1).2.level = 5 := by decide
set_option maxRecDepth 1000000 in
/-- Frame of phase 2: box `[-1, 3] × [0, 15]` → offset `(-3, -2)`. -/
theorem hickersonC3P2_frame_off : (gridToMacroCellWithOffset hickersonC3P2).1 = (-3, -2) := by decide
set_option maxRecDepth 1000000 in
/-- Frame level of phase 2: level 5 (frame `[-3, 29) × [-2, 30)`). -/
theorem hickersonC3P2_frame_lvl : (gridToMacroCellWithOffset hickersonC3P2).2.level = 5 := by decide
/-- Containment of the 9 phase combinations `(r, i) < 3 × 3`: each image
`evolve i (evolve r hickersonC3)` — a phase or a drifted phase, the drift
being at most `-1` north per period — lives in the reconstruction frame of
phase `r` (side 32, margin 2 everywhere: a one-cell drift is absorbed by
the margin). -/
theorem hickersonC3_hwin : ∀ r, r < 3 → ∀ i, i < 3 → ∀ p ∈ evolve i (evolve r hickersonC3),
    (gridToMacroCellWithOffset (evolve r hickersonC3)).1.1 ≤ p.1 ∧
      p.1 < (gridToMacroCellWithOffset (evolve r hickersonC3)).1.1
        + (2 ^ (gridToMacroCellWithOffset (evolve r hickersonC3)).2.level : Int) ∧
    (gridToMacroCellWithOffset (evolve r hickersonC3)).1.2 ≤ p.2 ∧
      p.2 < (gridToMacroCellWithOffset (evolve r hickersonC3)).1.2
        + (2 ^ (gridToMacroCellWithOffset (evolve r hickersonC3)).2.level : Int) := by
  intro r hr i hi
  interval_cases r <;> interval_cases i <;>
    simp only [evolve_zero, evolve_two, ← evolve_shift,
      hickersonC3_ev1, hickersonC3P1_ev1, hickersonC3P2_ev1] <;>
    first
    | (rw [hickersonC3_frame_off, hickersonC3_frame_lvl]; decide)
    | (rw [hickersonC3P1_frame_off, hickersonC3P1_frame_lvl]; decide)
    | (rw [hickersonC3P2_frame_off, hickersonC3P2_frame_lvl]; decide)
/-- Capstone: 25P3H1V0.1 is admitted by `hcap_of_spaceship_mod` — first
concrete **non-dyadic spaceship**. The speed bound `2·|v.i| ≤ p` holds
strictly (`2·|−1| = 2 < 3`, `2·|0| = 0 < 3`): for every horizon `t`, the
reconstruction of `evolve t hickersonC3` is captured by Hashlife. -/
theorem hickersonC3_hcap_of_spaceship_mod :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t hickersonC3)).2 = true :=
  hcap_of_spaceship_mod hickersonC3 hickersonC3_canonical (by decide) (-1, 0)
    hickersonC3_spaceship hickersonC3_hwin (by norm_num) (by norm_num)

/-! ### Flagship witnesses: glider and LWSS (tranche 11, admission)

The two **spaceships** announced by the docstring of `hashlife_correct_margin_of_spaceship`
— the glider (`p = 4`, `v = (1, -1)`, "satisfies it strictly") and the LWSS (`p = 4`,
`v = (0, 2)`, "hits the bound exactly") — are admitted by the **dyadic chain**
`hcap_of_spaceship`. For `p = 4 = 2²`, the divisibility premise `4 ∣ 2^level` holds
**as soon as the level reaches `log₂ p = 2`**: it is therefore available for both
witnesses, whose frames reconstruct at levels **3** (glider, side 7) and **4** (LWSS,
side 9). Each `hdiv` is closed by the kernel over its four phases (finite computation);
the tranche 9 containment relaxation is not required for period-4 witnesses.

**Proof note.** The bestiaire's Bool witnesses (`Life.glider_spaceship`,
`PatternTour.lwss_is_spaceship`) are already certified by the **kernel** reducer (`decide`
on `isSpaceship`, a Bool); the bridge to list equality is `beq_iff_eq` — no
`native_decide`, no added axiom. -/

/-- The glider literal is canonical (sorted, duplicate-free): the kernel
    certifies it, then `canonical_sortDedup` converts. -/
theorem glider_canonical : Canonical glider := by
  have h : glider = sortDedup glider := by decide
  rw [h]
  exact canonical_sortDedup _

/-- The glider's spaceship relation as a list equality: the Bool witness
    `glider_spaceship` (already kernel-certified) lifted to `Prop`. -/
theorem glider_ship4 : evolve 4 glider = shift (1, -1) glider :=
  beq_iff_eq.mp glider_spaceship

/-- The glider's reconstruction frame: offset `(-2, -2)` (margin 2 around the
    `[0, 2]²` box). -/
theorem glider_frame_off : (gridToMacroCellWithOffset glider).1 = (-2, -2) := by decide

/-- The glider's frame level: side `max(2+5, 2+5) = 7` → level **3** — measured.
    Since `3 ≥ log₂ 4 = 2`, the divisibility `4 ∣ 2³ = 8` holds: the glider goes
    through the dyadic chain, like the LWSS. -/
theorem glider_frame_lvl : (gridToMacroCellWithOffset glider).2.level = 3 := by decide

/-- The LWSS literal is canonical. -/
theorem lwss_canonical : Canonical lwss := by
  have h : lwss = sortDedup lwss := by decide
  rw [h]
  exact canonical_sortDedup _

/-- The LWSS's spaceship relation as a list equality (Bool witness
    `lwss_is_spaceship` from `PatternTour`, kernel-certified). -/
theorem lwss_ship4 : evolve 4 lwss = shift (0, 2) lwss :=
  beq_iff_eq.mp lwss_is_spaceship

/-- The LWSS's reconstruction frame: offset `(-2, -2)` (margin 2 around the
    `[0, 3] × [0, 4]` box). -/
theorem lwss_frame_off : (gridToMacroCellWithOffset lwss).1 = (-2, -2) := by decide

/-- The LWSS's frame level: side `max(3+5, 4+5) = 9` → level 4 — the dyadic
    chain applies (`4 ∣ 2⁴`), exactly as the docstring announced. -/
theorem lwss_frame_lvl : (gridToMacroCellWithOffset lwss).2.level = 4 := by decide

/-- Divisibility of the period over the LWSS's four phases: each
    `evolve i lwss` (`i < 4`) reconstructs at level 4, hence `4 ∣ 2⁴`. The
    kernel computation is finite: 4 phases, ≤ 17 cells. -/
theorem lwss_hdiv :
    ∀ i, i < 4 → 4 ∣ 2 ^ (gridToMacroCellWithOffset (evolve i lwss)).2.level := by
  intro i hi
  interval_cases i <;> decide

set_option maxRecDepth 1000000 in
/-- Divisibility of the period over the glider's four phases: each
    `evolve i glider` (`i < 4`) reconstructs at level 3 (measured for all
    four phases), and `4 ∣ 2³`. The kernel computation is finite: 4 phases,
    5-cell grids. -/
theorem glider_hdiv :
    ∀ i, i < 4 → 4 ∣ 2 ^ (gridToMacroCellWithOffset (evolve i glider)).2.level := by
  intro i hi
  interval_cases i <;> decide

/-- Capstone: the **glider** is admitted by `hcap_of_spaceship` — the dyadic
    chain, like the LWSS (`p = 4 = 2²` divides `2^level` as soon as `level ≥ 2`;
    level-3 frame). The speed bound holds strictly (`2·|1| = 2 < 4`,
    `2·|-1| = 2 < 4`): for every horizon `t`, the reconstruction of
    `evolve t glider` is captured by Hashlife. -/
theorem glider_hcap_of_spaceship :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t glider)).2 = true :=
  hcap_of_spaceship glider glider_canonical (by decide) (1, -1) glider_ship4
    glider_hdiv (by norm_num) (by norm_num)

/-- Capstone: the **LWSS** is admitted by `hcap_of_spaceship` — the exact speed
    bound (`2·|2| = 4 ≤ 4`) and the dyadic divisibility (`4 ∣ 2⁴`, level-4
    frame) announced by the docstring. -/
theorem lwss_hcap_of_spaceship :
    ∀ t, jumpCapturedF (gridToMacroCellWithOffset (evolve t lwss)).2 = true :=
  hcap_of_spaceship lwss lwss_canonical (by decide) (0, 2) lwss_ship4
    lwss_hdiv (by norm_num) (by norm_num)

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

/-! ## Tranche 14 — compositionality: disjoint union (#13483)

The missing locality law of the program: two configurations whose supports are
separated by more than `2·t` evolve independently — the evolution of the union
is the union of the evolutions, in the membership sense (`evolve_union_mem`). This is the assembly brick
of the admitted classes (still life, oscillator, spaceship): the actual
content of Life patterns is a juxtaposition of pieces from these classes. The
capture transfer (trajectory boxes of the parts → `jumpCapturedF` of the
union's reconstruction, via the `jumpCapturedF_of_dilation` corridor) is the
next tranche: it requires the padded-render geometry, the cloison already
named by that corridor.
-/

/-- **Tranche 14, link 1(a) — local agreement of union and part.** On the
    Chebyshev-`t` box of a point `q` near `g₁` (witness `hnear`), the union
    `g₁ ++ g₂` and `g₁` alone render the same state: any live cell of `g₂` in
    the box would be at distance `≤ 2·t` from the witness (triangle),
    contradicting the **strict** separation `2·t < d` — the equality case
    (`2·t = d`) lets the box touch both supports, hence the strict bound. -/
theorem union_agrees_with_left (t : Nat) (g₁ g₂ : Grid) (q : Int × Int)
    (hnear : ∃ p, p ∈ g₁ ∧ chebDist p q ≤ t)
    (hsep : ∀ p ∈ g₁, ∀ r ∈ g₂, 2 * t < chebDist p r) :
    ∀ r, chebDist q r ≤ t → isAlive (g₁ ++ g₂) r = isAlive g₁ r := by
  intro r hqr
  obtain ⟨p, hp₁, hpq⟩ := hnear
  have hg₂r : r ∉ g₂ := by
    intro hrmem
    have hle := hsep p hp₁ r hrmem
    have htri : chebDist p r ≤ chebDist p q + chebDist q r := chebDist_triangle p r q
    omega
  cases hb : isAlive (g₁ ++ g₂) r with
  | true =>
    have hm := (isAlive_true_iff_mem _ r).mp hb
    rw [List.mem_append] at hm
    rcases hm with h | h
    · exact ((isAlive_true_iff_mem g₁ r).mpr h).symm
    · exact absurd h hg₂r
  | false =>
    cases hc : isAlive g₁ r with
    | true =>
      have hu : r ∈ g₁ := (isAlive_true_iff_mem g₁ r).mp hc
      have hcontr : isAlive (g₁ ++ g₂) r = true :=
        (isAlive_true_iff_mem _ r).mpr (List.mem_append.mpr (Or.inl hu))
      rw [hb] at hcontr
      exact Bool.noConfusion hcontr
    | false => rfl

/-- **Tranche 14, link 0 — union in the `isAlive` sense.** Purely
    set-theoretic brick (no separation required, no time step): the state
    of an append is the "or" of the states of the parts. Serves the `t = 0`
    case of the union law and the append-order bridge. -/
theorem isAlive_append_or (g₁ g₂ : Grid) (q : Int × Int) :
    isAlive (g₁ ++ g₂) q = (isAlive g₁ q || isAlive g₂ q) := by
  cases hA : isAlive g₁ q with
  | true =>
      have hm : q ∈ g₁ ++ g₂ :=
        List.mem_append.mpr (Or.inl ((isAlive_true_iff_mem g₁ q).mp hA))
      rw [(isAlive_true_iff_mem _ q).mpr hm, Bool.true_or]
  | false =>
      cases hB : isAlive g₂ q with
      | true =>
          have hm : q ∈ g₁ ++ g₂ :=
            List.mem_append.mpr (Or.inr ((isAlive_true_iff_mem g₂ q).mp hB))
          rw [(isAlive_true_iff_mem _ q).mpr hm, Bool.false_or]
      | false =>
          have hU : isAlive (g₁ ++ g₂) q = false := by
            cases hd : isAlive (g₁ ++ g₂) q with
            | false => rfl
            | true =>
                have hmem := (isAlive_true_iff_mem _ q).mp hd
                rw [List.mem_append] at hmem
                rcases hmem with h | h
                · rw [(isAlive_true_iff_mem g₁ q).mpr h] at hA
                  exact Bool.noConfusion hA
                · rw [(isAlive_true_iff_mem g₂ q).mpr h] at hB
                  exact Bool.noConfusion hB
          rw [hU, Bool.false_or]

/-- **Tranche 14, link 1(b) — the pointwise union law.** Under strict
    separation `2·t < d` of the initial supports, the state at any point
    after `t` generations of the union is the "or" of the states of the
    parts: near `g₁` the union evolves like `g₁` alone (local agreement) and
    `g₂` is dead there (cone + triangle); outside both cones, everything is
    dead. -/
theorem evolve_union (t : Nat) (g₁ g₂ : Grid)
    (hsep : ∀ p ∈ g₁, ∀ r ∈ g₂, 2 * t < chebDist p r) (q : Int × Int) :
    isAlive (evolve t (g₁ ++ g₂)) q =
      (isAlive (evolve t g₁) q || isAlive (evolve t g₂) q) := by
  by_cases hn₁ : ∃ p, p ∈ g₁ ∧ chebDist p q ≤ t
  · have hagree : ∀ r, chebDist q r ≤ t → isAlive (g₁ ++ g₂) r = isAlive g₁ r :=
      union_agrees_with_left t g₁ g₂ q hn₁ hsep
    have hbow : isAlive (evolve t (g₁ ++ g₂)) q = isAlive (evolve t g₁) q :=
      evolve_box_agree t (g₁ ++ g₂) g₁ q hagree
    have hdead : isAlive (evolve t g₂) q = false := by
      cases hd : isAlive (evolve t g₂) q with
      | false => rfl
      | true =>
        obtain ⟨r, hr₂, hrq⟩ := evolve_reach_chebyshev t g₂ q hd
        obtain ⟨p, hp₁, hpq⟩ := hn₁
        have hle := hsep p hp₁ r ((isAlive_true_iff_mem g₂ r).mp hr₂)
        have htri : chebDist p r ≤ chebDist p q + chebDist q r :=
          chebDist_triangle p r q
        have hcomm : chebDist q r = chebDist r q := chebDist_comm q r
        omega
    rw [hbow, hdead, Bool.or_false]
  · by_cases hn₂ : ∃ p, p ∈ g₂ ∧ chebDist p q ≤ t
    · have hseps : ∀ p ∈ g₂, ∀ r ∈ g₁, 2 * t < chebDist p r := by
        intro p hp r hr
        have hle := hsep r hr p hp
        rw [chebDist_comm]
        exact hle
      have hagree : ∀ r, chebDist q r ≤ t → isAlive (g₂ ++ g₁) r = isAlive g₂ r :=
        union_agrees_with_left t g₂ g₁ q hn₂ hseps
      have hbow : isAlive (evolve t (g₂ ++ g₁)) q = isAlive (evolve t g₂) q :=
        evolve_box_agree t (g₂ ++ g₁) g₂ q hagree
      have hdead : isAlive (evolve t g₁) q = false := by
        cases hd : isAlive (evolve t g₁) q with
        | false => rfl
        | true =>
          obtain ⟨r, hr₁, hrq⟩ := evolve_reach_chebyshev t g₁ q hd
          obtain ⟨p, hp₂, hpq⟩ := hn₂
          have hle := hseps p hp₂ r ((isAlive_true_iff_mem g₁ r).mp hr₁)
          have htri : chebDist p r ≤ chebDist p q + chebDist q r :=
            chebDist_triangle p r q
          have hcomm : chebDist q r = chebDist r q := chebDist_comm q r
          omega
      have hswap : isAlive (evolve t (g₁ ++ g₂)) q = isAlive (evolve t (g₂ ++ g₁)) q := by
        cases t with
        | zero =>
            show isAlive (g₁ ++ g₂) q = isAlive (g₂ ++ g₁) q
            rw [isAlive_append_or g₁ g₂ q, isAlive_append_or g₂ g₁ q]
            cases isAlive g₁ q <;> cases isAlive g₂ q <;> rfl
        | succ n =>
            exact congrArg (isAlive · q) (evolve_congr (fun p =>
              List.mem_append.trans (or_comm.trans List.mem_append.symm))
              (Nat.succ_le_succ (Nat.zero_le n)))
      rw [hswap, hbow, hdead, Bool.false_or]
    · have hdead₁ : isAlive (evolve t g₁) q = false := by
        cases hd : isAlive (evolve t g₁) q with
        | false => rfl
        | true =>
          obtain ⟨p, hp₁, hpq⟩ := evolve_reach_chebyshev t g₁ q hd
          exact absurd ⟨p, (isAlive_true_iff_mem g₁ p).mp hp₁, hpq⟩ hn₁
      have hdead₂ : isAlive (evolve t g₂) q = false := by
        cases hd : isAlive (evolve t g₂) q with
        | false => rfl
        | true =>
          obtain ⟨p, hp₂, hpq⟩ := evolve_reach_chebyshev t g₂ q hd
          exact absurd ⟨p, (isAlive_true_iff_mem g₂ p).mp hp₂, hpq⟩ hn₂
      have hdeadU : isAlive (evolve t (g₁ ++ g₂)) q = false := by
        cases hd : isAlive (evolve t (g₁ ++ g₂)) q with
        | false => rfl
        | true =>
          obtain ⟨p, hpU, hpq⟩ := evolve_reach_chebyshev t (g₁ ++ g₂) q hd
          have hmemU : p ∈ g₁ ++ g₂ := (isAlive_true_iff_mem _ p).mp hpU
          rw [List.mem_append] at hmemU
          rcases hmemU with h | h
          · exact absurd ⟨p, h, hpq⟩ hn₁
          · exact absurd ⟨p, h, hpq⟩ hn₂
      rw [hdeadU, hdead₁, hdead₂, Bool.false_or]

/-- **Tranche 14, link 1(c) — trajectory of the union, membership form.**
    Under strict separation `2·t < d` of the initial supports, the membership
    of the evolution of the union is the union of the memberships of the
    evolutions. The "literal list" form `evolve t (g₁ ++ g₂) = evolve t g₁ ++
    evolve t g₂` is false for `t ≥ 1`: the canonical enumeration of `evolve`
    (lexicographic order, `canonical_evolve_of_pos`) interleaves points of
    separated parts sharing a column, where the append keeps them blocked —
    order is not preserved, only the support is. This is the compositionality
    brick that the capture transfer (tranche 14b) will consume: trajectory
    boxes of the parts → box of the union, membership reasoning. -/
theorem evolve_union_mem (t : Nat) (g₁ g₂ : Grid)
    (hsep : ∀ p ∈ g₁, ∀ r ∈ g₂, 2 * t < chebDist p r) (q : Int × Int) :
    q ∈ evolve t (g₁ ++ g₂) ↔ (q ∈ evolve t g₁ ∨ q ∈ evolve t g₂) := by
  simp only [← isAlive_true_iff_mem]
  rw [evolve_union t g₁ g₂ hsep q, Bool.or_eq_true]

/-! ## Synthesis — the fragment is non-empty and the framework statement is honest

`supportInMargin` is decidable and witnessed on the bestiary (above). The framework
statement `hashlife_correct_margin` carries the fragment-relative correctness (in dressing
— see *unconditional-in-waiting* note in its docstring: the predicate is tautological, the
research heart remains the bounded P4/P5 assembly); its `sorry` openly documents the
still-open bounded P4/P5 assembly (`p4_nw_overlap_wall`, ai-01 c.94).
Strategy for the rest of #6724: the bounded NE/SW/SE walls are CLOSED and
`p5_large_n_jumpN` is proved (b3') — the L2 reduction above is in place, leaving the L3
link (the `centralCorrect → hcap` bridge, the bounded assembly proper) and L4 (restricted
→ global equality), which will discharge the `sorry` of `hashlife_correct_margin`.
**First closed L3 link** (step 3, slice 4): the `T = 1` class of still lifes is
entirely lifted to `hcap` (`hcap_of_still_life` →
`hashlife_correct_margin_of_still_life`), with no sorry — generalizing to the
other periodic classes `T ∣ 2^k` will follow the same pattern (canonical
round-trip → transported fixpoint → capture).
-/

end Life_en
end Conway_en
