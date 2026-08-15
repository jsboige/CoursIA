/-
Copyright (c) 2026 CoursIA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Phase 3b — Bounded correctness theorem for Hashlife

This module is **scaffolding for multi-agent prover iteration** (Epic #1453
harness co-evolution). Every theorem is stated precisely with `sorry`
placeholders. Each `sorry` is a self-contained prover target, ranked by
mathematical difficulty (P1 = easiest, P5 = hardest).

## Goal

The central theorem:

    theorem hashlife_correct (n : Nat) (g : Grid) (h : box_assez_grand g n) :
        evolveHashlifeFast n g = evolve n g

It says: given enough padding around `g`, the exponential-speedup Hashlife
implementation (`evolveHashlifeFast`) agrees with the reference step-by-step
implementation (`evolve`) after `n` generations.

## Proof strategy (5 lemmas)

The proof decomposes into 5 sub-goals. Each is a standalone `sorry` below.

  **P1. box_assez_grand_predicate** (trivial)
     Define the padding predicate. Pure definition, no proof.

  **P2. step_light_cone** (locality — the cone of dependence)
     After `t` generations, the state of cell `(r, c)` depends only on the
     initial state of cells within Manhattan distance `t`. This is B3/S23's
     "speed of light = 1 cell/generation".

  **P3. padCenter2_frame_lemma** (frame correctness)
     `padCenter2 c` correctly places `c` at the center of a level-`(k+2)`
     MacroCell, with `2^k` dead padding on each side.

  **P4. hashlifeResult_central_correct** (decompose-compose)
     On a level-`k` MacroCell `c` with adequate padding, `hashlifeResult c`
     equals `step^[2^(k-2)]` applied to the centered sub-region.

  **P5. hashlife_correct** (composition)
     Compose P2-P4 by induction on `n` to get the final theorem.

## Prover iteration protocol

Each `sorry` here is a target for `MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/`.
The prover runs `lake build Conway.Life.HashlifeCorrectness` after each patch
and uses the `sorry_delta` as the forensic signal. As each `sorry` is
eliminated, the corresponding lemma is moved out of "scaffolding" status.

The difficulty rating drives agent selection:
  - P1/P2 (simple): local Qwen tactic agent
  - P3 (structural): z.ai GLM coordinator + tactic agent
  - P4 (compositional): OpenRouter frontier (Opus/GPT-5) Director escalation
  - P5 (induction): OpenRouter frontier with `--director-provider openrouter`

See `agent_tests/prover/RUNBOOK.md` for iteration protocol.

## Non-goals (out of scope for this module)

- Memoization / hash-consing (algorithmic performance, not correctness).
- Unbounded `hashlife_correct` without `box_assez_grand` hypothesis.
- Periodicity arguments for OTCA/Gemini (Phase 6-7).
-/

import Conway.Life.HashlifeCorrectness.Foundation
import Conway.Life.HashlifeCorrectness.Walls.NW
import Conway.Life.HashlifeCorrectness.Walls.NE
import Conway.Life.HashlifeCorrectness.Walls.SW
import Conway.Life.HashlifeCorrectness.Walls.SE

namespace Conway
namespace Life

open MacroCell

set_option maxHeartbeats 1000000 in
/-- **P4 entry point**: the pointwise membership biconditional for the
    inductive step. Glues `p4_double_nine_shape` (P4.1), `p4_wave1_ih`
    (P4.2), and `p4_wave2_ih` (P4.3). The P4.4 half-step composition is
    subsumed by the closed lemmas `evolve_add` (L2353) + `evolve_half_step`
    (L2370). This function produces the
    `∀ p, p ∈ ... ↔ p ∈ ...` hypothesis that `p4_ext_bridge` consumes.

    **Pointwise-proof balisage (c.147 — all three pieces now closed)** —
    the pointwise form of the P4.4 sub-cell coverage (S3) + assemble (S4)
    argument, decomposed here into three named pieces:
    - **G1 (geometric, tractable)** — RHS reduction: `p ∈ restrictGridTo
      (evolve 2^k g) 2^k 2^(k+1)` splits via `mem_restrictGridTo` into window
      bounds `[2^k, 3·2^k)²` (since `2^k + 2^(k+1) = 3·2^k`) plus the cell-state
      `isAlive (evolve 2^k g) p`. Pure arithmetic, no `hashlifeResultAux`.
    - **G2 (whnf-hard)** — LHS reduction: `p ∈ (hashlifeResultAux (k+2) c).toGrid
      (2^k, 2^k)` agrees, on the containing quadrant `q_j`, with `evolve 2^(k-1)`
      on `q_j.toGrid`, via the four `centralCorrect q_j (k-1)` from `_h3` (P4.3).
      Touches `hashlifeResultAux` results → the c.139/142/143 whnf wall.
    - **G3 (whnf-hard assemble)** — combine G1 and G2 with `step_light_cone`
      (locality, radius `2·2^k`) and `evolve_half_step` (the `2^k` half-step
      `evolve 2^k = evolve 2^(k-1) ∘ evolve 2^(k-1)`, now closed): the local
      sub-cell computation equals the global `evolve 2^k` on the centered window.

    All three are now closed: G1 by window arithmetic, G2/G3 by the four
    quadrant membership arms (`p4_{nw,ne,sw,se}_membership_arm(_rev)`)
    resting on the proven windowed overlap walls (NW/NE precedents, then
    SW/SE). -/
noncomputable def p4_succ_membership
    (c : MacroCell) (k : Nat) (hwf : c.wf = true) (hk : c.level = k + 2) (hk1 : 1 ≤ k)
    (ih : ∀ (c' : MacroCell) (j : Nat), j < k → c'.wf = true → c'.level = j + 2 →
      centralCorrect c' j) :
    ∀ p, p ∈ (hashlifeResultAux (k + 2) c).toGrid ((2^k : Nat), (2^k : Nat)) ↔
        p ∈ restrictGridTo (evolve (2^k) (c.toGrid (0, 0))) (2^k : Int) (2^(k+1)) := by
  have _h1 := p4_double_nine_shape c k hwf hk
  have _h2 := p4_wave1_ih c k hwf hk hk1 ih
  have _h3 := p4_wave2_ih c k hwf hk hk1 ih
  intro p
  -- LHS assembly (c.156). The 3 G3 gates (hcnode, hashlifeResultAux_succ_node,
  -- if_neg) now compose through the whnf wall, exposing the `node out_*`
  -- constructor and decomposing it via `mem_toGrid_node`.
  -- Destruct c via _h1 (p4_double_nine_shape: c = node(node×4)×4 ∧ 16 facts).
  obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se,
          sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, _hcshape⟩ := _h1
  obtain ⟨hcnode, hfacts⟩ := _hcshape
  -- Rewrite the input cell to its 16-grandchild node, then iota-reduce hRA.
  rw [hcnode]
  rw [show (k + 2) = (k + 1) + 1 from by omega]
  rw [hashlifeResultAux_succ_node]
  -- The if-condition (node16).level == 2 is FALSE for k >= 1 (level = k+2 >= 3).
  -- Discharge via the clean-context helper (opaque binders, c.139/c.143 pattern):
  -- applying it here keeps the level term inferred, never whnf-re-elaborated.
  have hne2 := node16_level_ne_two k hk1
    nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
    sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se hfacts.1
  rw [if_neg hne2]
  -- LHS is now `p ∈ (node out_nw out_ne out_sw out_se).toGrid (2^k, 2^k)`;
  -- `mem_toGrid_node` (G3) decomposes it into the four quadrant memberships.
  rw [mem_toGrid_node]
  -- RESIDUAL (the offset-matching assembly): each `out_*.toGrid (off_*, off_*)`
  -- must be characterized via `centralCorrect_mem` (G2 congruence, crossing the
  -- whnf wall on the composed result) + the induction hypothesis `centralCorrect
  -- q_* (k-1)` from `_h3`, then bridged to the RHS window via `evolve_half_step`
  -- (the `2^k` half-step) + `evolve_add` (G1). The offsets `2^out_*.level` vs
  -- `2^k` and the ih at level (k-1) vs goal at level k are the matching core.
  -- G3 wave-assembly: decomposed into 5 named sub-sorries (4 quadrants + mpr),
  -- per the ai-01 plan step 8. Each sub-sorry is independently attackable:
  -- the 4 mp cases apply centralCorrect_mem_shift (G2) on the corresponding
  -- q_j from _h3, then evolve_half_step (G3) + evolve_cone_agree (locality)
  -- to bridge to the global evolve 2^k window; mpr uses quad_partition_bounds
  -- to route p to the correct quadrant.
  refine ⟨?mp, ?mpr⟩
  case mp =>
    intro hlhs
    rcases hlhs with hnw | hne | hsw | hse
    · -- nw quadrant: p ∈ out_nw.toGrid (2^k, 2^k)
      -- goal: p ∈ restrictGridTo (evolve (2^k) (toGrid (0,0) <c destructuré en nodes>)) (2^k) (2^(k+1))
      -- Step 1: destructure the 32-conjunct grandchild facts into hg1..hg32.
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- Step 2: build 9 wave-1 result facts (level + cellWf) via node_wf_level_of_four + wave1_result_facts.
      -- n1 = node nw_nw nw_ne nw_sw nw_se
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n4 = node nw_sw nw_se sw_nw sw_ne
      have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                        hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
      -- n5 = node nw_se ne_sw sw_ne se_nw
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- With r1, r2, r4, r5 (the four wave-1 results), apply the opaque-binder
      -- nw arm lemma. `R_i := hashlifeResultAux (k+1) n_i` is pure substitution
      -- (no whnf): the whnf-hard shift consumption happens inside the arm over
      -- opaque binders (fresh heartbeat budget). Normalize hnw's Nat-cast offset
      -- `↑(2^k)` to `(2^k : Int)` so it unifies with the arm's hypothesis.
      push_cast at hnw
      exact p4_nw_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn4.1 hn5.1
        hn1.2 hn2.2 hn4.2 hn5.2
        r1.1 r2.1 r4.1 r5.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)
        ih p hnw

    · -- ne quadrant: p ∈ out_ne.toGrid (2^k, 2^k + 2^level)
      -- Factorization (c.8122 — defensive extraction): the residual sorry is the
      -- mirror of the NW wall (off-by-shift `{2,3,5,6}` vs `{1,2,4,5}`). Build
      -- the 4 NE wave-1 sub-cells n2/n3/n5/n6 + wave-0 results R2/R3/R5/R6, then
      -- apply the opaque-binder `p4_ne_membership_arm`. The whnf-hard step is
      -- encapsulated in the arm over opaque `R_j` (fresh heartbeat budget).
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- n1 = node nw_nw nw_ne nw_sw nw_se (the OUTER NW supercell, used for
      -- the NE offset `2^out_nw.level` per `mem_toGrid_node`).
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n3 = node ne_nw ne_ne ne_sw ne_se
      have hn3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                        hne_nw_w hne_ne_w hne_sw_w hne_se_w
      have r3 := wave1_result_facts k hk1 (node ne_nw ne_ne ne_sw ne_se) hn3.2 hn3.1
      -- n5 = node nw_se ne_sw sw_ne se_nw
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- n6 = node ne_sw ne_se se_nw se_ne
      have hn6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                        hne_sw_w hne_se_w hse_nw_w hse_ne_w
      have r6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hn6.2 hn6.1
      -- n4_ne = node nw_sw nw_se sw_nw sw_ne (SW-of-NW quadrant cell, the THIRD
      -- wave-1 child of `out_nw`). Needed in scope for `hinner` since `out_nw`
      -- itself holds the opaquely-binder hashlifeResultAux of (R1.node R2 R4 R5).
      have hn_nw_sw := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                              hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r_nw_sw := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne)
                                          hn_nw_sw.2 hn_nw_sw.1
      -- n7 = node sw_nw sw_ne sw_sw sw_se (the OUTER SW child of the parent —
      -- structural-only hypothesis for the NE wall's bound exclusions, no hcc).
      have hn7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                        hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
      -- Normalize hne's Nat-cast offset `↑(2^k + 2^(k-1))` to the Int form so
      -- it unifies with the arm's hypothesis. Then construct the OUTER NW
      -- supercell `out_nw = R1.node R2 (R_nw_sw) R5` (the level-(k+1) input cell
      -- of `hashlifeResultAux (k+1)` that produces the outer NW quadrant), pass
      -- `out_nw : MacroCell` + `hout_nw_l : out_nw.level = k` so the arm can
      -- bridge `2^out_nw.level = 2^k` via `congrArg` (c.8122).
      --
      -- AVOID `push_cast at hne` (whnf-timeout 200k heartbeats, c.8122 trial-v2):
      -- rewriting through `out_ne.toGrid` (which forces whnf of
      -- `hashlifeResultAux (k+1) (node R2 R3 R5 R6).toGrid`) over a 2^k offset
      -- exceeds the budget. Instead, target the arm's exact form via
      -- `change`-then-`congrArg`: prove the literal Nat→Int equalities and let
      -- Lean's unifier consume them when matching `p4_ne_membership_arm`.
      --
      -- The arm's `hout_nw` is consumed solely via `hout_nw_l : hout_nw.level = k`
      -- (then `congrArg (fun n => (2^n : Int)) hout_nw_l`). We therefore only
      -- need to be ABLE to assert the level fact; the syntactic term is opaque
      -- to the arm. The bridging lemmas built below prove the equalities the
      -- arm's `congrArg` step needs (`2^hout_nw.level = 2^k` mod the offset).
      let out_nw : MacroCell :=
        hashlifeResultAux (k + 1)
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
      -- hout_nw_l : out_nw.level = k. Proven via the inner-node level-fact: the
      -- 4-arg `node` (level k+1, wf true) maps under `wave1_result_facts` to a
      -- level-k hashlifeResultAux.
      have hout_nw_l : out_nw.level = k :=
        (wave1_result_facts k hk1
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
          (node_wf_level_of_four r1.1 r2.1 r_nw_sw.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r_nw_sw.2) (wf_of_cellWf r5.2)).right
          (node_wf_level_of_four r1.1 r2.1 r_nw_sw.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r_nw_sw.2) (wf_of_cellWf r5.2)).left).1
      -- Targeted Nat→Int coercion on `hne`'s offsets. The arm expects `Int`-typed
      -- offsets; `mem_toGrid_node` already coerced `2^out_nw.level : Int`, so only
      -- the leading `2^k` literals need rewriting. `norm_cast` is more targeted
      -- than `push_cast` (top-level only, no deep whnf).
      norm_cast at hne
      exact p4_ne_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))   -- R1
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        rfl rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn_nw_sw.1 hn5.1 hn6.1 hn7.1
        hn1.2 hn2.2 hn3.2 hn_nw_sw.2 hn5.2 hn6.2 hn7.2
        r1.1 r2.1 r3.1 r5.1 r6.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r3.2)
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2)
        ih
        p
        out_nw
        hout_nw_l
        hne
    · -- sw quadrant: p ∈ out_sw.toGrid (2^k + 2^level, 2^k)
      -- Factorization (c.NNNN — defensive extraction): the SW arm is the
      -- NW-SE reflection of the NE arm (c.8122) — same opaque-binder pattern.
      -- Sub-cells are n4/n5/n7/n8 (the SW wave-1 children of the outer
      -- 16-grandkid layout per `p4_double_nine_shape` L2109 + `p4_wave2_ih`
      -- L2629-2633). Build the 4 SW wave-1 sub-cells + wave-0 results
      -- R4/R5/R7/R8, then apply the opaque-binder `p4_sw_membership_arm`.
      -- The whnf-hard step is encapsulated in the arm over opaque `R_j`
      -- (fresh heartbeat budget, set_option at the arm).
      --
      -- IMPORTANT (c.8122 cascade-fix L831): all `hcc_j` and `R_j` literals
      -- must be sourced from `p4_wave2_ih`'s canonical reference (L2629-2633),
      -- NOT copy-pasted across branches. The 16-grid positions for SW sub-cells
      -- are {4,5,7,8} (NE was {2,3,5,6}; symmetric flip of row-axis):
      --   n4 = node nw_sw nw_se sw_nw sw_ne
      --   n5 = node nw_se ne_sw sw_ne se_nw
      --   n7 = node sw_nw sw_ne sw_sw sw_se
      --   n8 = node sw_ne se_nw sw_se se_sw
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- n1 = node nw_nw nw_ne nw_sw nw_se (the OUTER NW supercell, used for
      -- the SW row offset `2^k + 2^out_nw.level` per `mem_toGrid_node`).
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw (NE-of-NW quadrant cell, the SECOND
      -- wave-1 child of `out_nw`). Needed in scope for `out_nw` construction.
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n3 = node ne_nw ne_ne ne_sw ne_se (NE quadrant cell — structural
      -- witness for the strengthened SW wall, cf. `hn3` in `p4_sw_overlap_wall`)
      have hn3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                        hne_nw_w hne_ne_w hne_sw_w hne_se_w
      -- n4 = node nw_sw nw_se sw_nw sw_ne (SW-of-NW, the THIRD wave-1 child of `out_nw`)
      have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                        hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
      -- n5 = node nw_se ne_sw sw_ne se_nw (center bridge)
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- n7 = node sw_nw sw_ne sw_sw sw_se (SW quadrant cell)
      have hn7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                        hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
      have r7 := wave1_result_facts k hk1 (node sw_nw sw_ne sw_sw sw_se) hn7.2 hn7.1
      -- n8 = node sw_ne se_nw sw_se se_sw (SW-of-SE bridge)
      have hn8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                        hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
      have r8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hn8.2 hn8.1
      -- Construct the OUTER NW supercell `out_nw = R1.node R2 (R4) R5`
      -- (level-(k+1) input cell of `hashlifeResultAux (k+1)` that produces the
      -- outer NW quadrant). The SW arm consumes `hout_nw_l : out_nw.level = k`
      -- via `congrArg (fun n => (2^n : Int)) hout_nw_l` (cf. c.8122 NE-arm wiring,
      -- the SW branch uses the same level-anchor as the NE branch — the SW
      -- row offset is `2^k + 2^out_nw.level`, the same `2^out_nw.level` as NE's
      -- column offset, so we re-construct `out_nw` here; this is a syntactic
      -- let, not a new computation, and Lean 4's whnf-friendly transparency
      -- keeps the lemma proof closed).
      let out_nw : MacroCell :=
        hashlifeResultAux (k + 1)
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
      have hout_nw_l : out_nw.level = k :=
        (wave1_result_facts k hk1
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).right
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).left).1
      -- Targeted Nat→Int coercion on `hsw`'s offsets (top-level only, same
      -- pattern as c.8122 NE branch — `norm_cast at hsw` not `push_cast`).
      norm_cast at hsw
      exact p4_sw_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn4.1 hn5.1 hn7.1 hn8.1
        hn1.2 hn2.2 hn3.2 hn4.2 hn5.2 hn7.2 hn8.2
        r4.1 r5.1 r7.1 r8.1
        (wf_of_cellWf r4.2) (wf_of_cellWf r5.2) (wf_of_cellWf r7.2) (wf_of_cellWf r8.2)
        ih
        p
        out_nw
        hout_nw_l
        hsw
    · -- se quadrant: p ∈ out_se.toGrid (2^k + 2^level, 2^k + 2^level)
      -- Factorization (c.90 — SE-arm port): the SE arm is the DIAGONAL mirror
      -- of the NW arm — same opaque-binder pattern as NE (c.8122) / SW (c.8123).
      -- Sub-cells are n5/n6/n8/n9 (the SE wave-1 children of the outer
      -- 16-grandkid layout per `p4_double_nine_shape` L2109 + `p4_wave2_ih`
      -- L2629-2633). Build the 4 SE wave-1 sub-cells + wave-0 results
      -- R5/R6/R8/R9, then apply the opaque-binder `p4_se_membership_arm`.
      --
      -- IMPORTANT (c.8122 cascade-fix L831): all `hcc_j` and `R_j` literals
      -- must be sourced from `p4_wave2_ih`'s canonical reference (L2629-2633),
      -- NOT copy-pasted across branches. The 16-grid positions for SE sub-cells
      -- are {5,6,8,9} (diagonal complement of NW's {1,2,4,5}):
      --   n5 = node nw_se ne_sw sw_ne se_nw
      --   n6 = node ne_sw ne_se se_nw se_ne
      --   n8 = node sw_ne se_nw sw_se se_sw
      --   n9 = node se_nw se_ne se_sw se_se
      obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
              hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
              hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
              hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
      -- n1 = node nw_nw nw_ne nw_sw nw_se (the OUTER NW supercell — BOTH SE
      -- offsets are `2^k + 2^out_nw.level` per `mem_toGrid_node`, anchored on
      -- the first child's level like the NE column / SW row offsets).
      have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                        hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
      have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
      -- n2 = node nw_ne ne_nw nw_se ne_sw (NE-of-NW, second wave-1 child of `out_nw`)
      have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                        hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
      have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
      -- n3 = node ne_nw ne_ne ne_sw ne_se (NE quadrant cell — structural
      -- witness for the strengthened SE wall, cf. `hn3` in `p4_se_overlap_wall`)
      have hn3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                        hne_nw_w hne_ne_w hne_sw_w hne_se_w
      -- n4 = node nw_sw nw_se sw_nw sw_ne (SW-of-NW, third wave-1 child of `out_nw`)
      have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                        hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
      have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
      -- n5 = node nw_se ne_sw sw_ne se_nw (center bridge — FIRST SE sub-cell)
      have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                        hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
      have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
      -- n6 = node ne_sw ne_se se_nw se_ne (E bridge — NE-of-SE)
      have hn6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                        hne_sw_w hne_se_w hse_nw_w hse_ne_w
      have r6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hn6.2 hn6.1
      -- n7 = node sw_nw sw_ne sw_sw sw_se (SW quadrant cell — structural
      -- witness for the strengthened SE wall, cf. `hn7` in `p4_se_overlap_wall`)
      have hn7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                        hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
      -- n8 = node sw_ne se_nw sw_se se_sw (S bridge — SW-of-SE)
      have hn8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                        hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
      have r8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hn8.2 hn8.1
      -- n9 = node se_nw se_ne se_sw se_se (SE quadrant cell)
      have hn9 := node_wf_level_of_four hse_nw_l hse_ne_l hse_sw_l hse_se_l
                                        hse_nw_w hse_ne_w hse_sw_w hse_se_w
      have r9 := wave1_result_facts k hk1 (node se_nw se_ne se_sw se_se) hn9.2 hn9.1
      -- Construct the OUTER NW supercell `out_nw` (same level-anchor as the
      -- NE/SW branches — `mem_toGrid_node` shifts BOTH SE coordinates by
      -- `2^out_nw.level`; syntactic let, no new computation).
      let out_nw : MacroCell :=
        hashlifeResultAux (k + 1)
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
      have hout_nw_l : out_nw.level = k :=
        (wave1_result_facts k hk1
          (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
                (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
                (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
                (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).right
          (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
            (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
            (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).left).1
      -- Targeted Nat→Int coercion on `hse`'s offsets (top-level only, same
      -- pattern as the NE/SW branches — `norm_cast at hse` not `push_cast`).
      norm_cast at hse
      exact p4_se_membership_arm k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn4.1 hn5.1 hn6.1 hn7.1 hn8.1 hn9.1
        hn1.2 hn2.2 hn3.2 hn4.2 hn5.2 hn6.2 hn7.2 hn8.2 hn9.2
        r5.1 r6.1 r8.1 r9.1
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2) (wf_of_cellWf r8.2) (wf_of_cellWf r9.2)
        ih
        p
        out_nw
        hout_nw_l
        hse
  case mpr =>
    intro hrhs
    -- RHS → global membership + the four window bounds; `quad_partition_bounds`
    -- routes p to its quadrant; each reciprocal arm (shift `.mpr` ∘
    -- supercell-agree consumed R-to-L ∘ half-step fold) then delivers the
    -- corresponding `mem_toGrid_node` disjunct.
    rw [mem_restrictGridTo] at hrhs
    obtain ⟨hmem, hb1, hb2, hb3, hb4⟩ := hrhs
    have hbridge : ((2 ^ (k + 1) : Nat) : Int) = 2 ^ k + 2 ^ k := by
      push_cast; rw [pow_succ]; ring
    rw [hbridge] at hb2 hb4
    have hpos : (0 : Int) ≤ 2 ^ k := le_of_lt (pow_pos (by norm_num) k)
    have hroute := (quad_partition_bounds (2^k : Int) (2^k : Int) hpos p).mp
      ⟨hb1, by omega, hb3, by omega⟩
    -- Shared towers, built ONCE for the four branches (the mp branches each
    -- rebuilt their own subset; here the router owns them): the 32 grandchild
    -- facts, the 9 wave-1 results r1..r9 (canonical reference `p4_wave2_ih`
    -- L2629-2633), and the outer-NW supercell level anchor.
    obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w,
            hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w,
            hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w,
            hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hfacts
    -- n1 = node nw_nw nw_ne nw_sw nw_se
    have hn1 := node_wf_level_of_four hnw_nw_l hnw_ne_l hnw_sw_l hnw_se_l
                                      hnw_nw_w hnw_ne_w hnw_sw_w hnw_se_w
    have r1 := wave1_result_facts k hk1 (node nw_nw nw_ne nw_sw nw_se) hn1.2 hn1.1
    -- n2 = node nw_ne ne_nw nw_se ne_sw
    have hn2 := node_wf_level_of_four hnw_ne_l hne_nw_l hnw_se_l hne_sw_l
                                      hnw_ne_w hne_nw_w hnw_se_w hne_sw_w
    have r2 := wave1_result_facts k hk1 (node nw_ne ne_nw nw_se ne_sw) hn2.2 hn2.1
    -- n3 = node ne_nw ne_ne ne_sw ne_se
    have hn3 := node_wf_level_of_four hne_nw_l hne_ne_l hne_sw_l hne_se_l
                                      hne_nw_w hne_ne_w hne_sw_w hne_se_w
    have r3 := wave1_result_facts k hk1 (node ne_nw ne_ne ne_sw ne_se) hn3.2 hn3.1
    -- n4 = node nw_sw nw_se sw_nw sw_ne
    have hn4 := node_wf_level_of_four hnw_sw_l hnw_se_l hsw_nw_l hsw_ne_l
                                      hnw_sw_w hnw_se_w hsw_nw_w hsw_ne_w
    have r4 := wave1_result_facts k hk1 (node nw_sw nw_se sw_nw sw_ne) hn4.2 hn4.1
    -- n5 = node nw_se ne_sw sw_ne se_nw (center bridge)
    have hn5 := node_wf_level_of_four hnw_se_l hne_sw_l hsw_ne_l hse_nw_l
                                      hnw_se_w hne_sw_w hsw_ne_w hse_nw_w
    have r5 := wave1_result_facts k hk1 (node nw_se ne_sw sw_ne se_nw) hn5.2 hn5.1
    -- n6 = node ne_sw ne_se se_nw se_ne
    have hn6 := node_wf_level_of_four hne_sw_l hne_se_l hse_nw_l hse_ne_l
                                      hne_sw_w hne_se_w hse_nw_w hse_ne_w
    have r6 := wave1_result_facts k hk1 (node ne_sw ne_se se_nw se_ne) hn6.2 hn6.1
    -- n7 = node sw_nw sw_ne sw_sw sw_se
    have hn7 := node_wf_level_of_four hsw_nw_l hsw_ne_l hsw_sw_l hsw_se_l
                                      hsw_nw_w hsw_ne_w hsw_sw_w hsw_se_w
    have r7 := wave1_result_facts k hk1 (node sw_nw sw_ne sw_sw sw_se) hn7.2 hn7.1
    -- n8 = node sw_ne se_nw sw_se se_sw
    have hn8 := node_wf_level_of_four hsw_ne_l hse_nw_l hsw_se_l hse_sw_l
                                      hsw_ne_w hse_nw_w hsw_se_w hse_sw_w
    have r8 := wave1_result_facts k hk1 (node sw_ne se_nw sw_se se_sw) hn8.2 hn8.1
    -- n9 = node se_nw se_ne se_sw se_se
    have hn9 := node_wf_level_of_four hse_nw_l hse_ne_l hse_sw_l hse_se_l
                                      hse_nw_w hse_ne_w hse_sw_w hse_se_w
    have r9 := wave1_result_facts k hk1 (node se_nw se_ne se_sw se_se) hn9.2 hn9.1
    -- Outer-NW supercell (same syntactic let as the mp NE/SW/SE branches):
    -- the NE/SW/SE disjunct anchors carry `2^out_nw.level`, bridged in the
    -- rev arms via `congrArg` on `hout_nw_l`.
    let out_nw : MacroCell :=
      hashlifeResultAux (k + 1)
        (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
              (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
    have hout_nw_l : out_nw.level = k :=
      (wave1_result_facts k hk1
        (node (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
              (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
              (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
              (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw)))
        (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
          (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
          (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).right
        (node_wf_level_of_four r1.1 r2.1 r4.1 r5.1
          (wf_of_cellWf r1.2) (wf_of_cellWf r2.2)
          (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)).left).1
    rcases hroute with hq | hq | hq | hq
    · -- NW quadrant (router disjunct 1 = mem_toGrid_node disjunct 1)
      left
      norm_cast
      exact p4_nw_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn4.1 hn5.1
        hn1.2 hn2.2 hn4.2 hn5.2
        r1.1 r2.1 r4.1 r5.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r4.2) (wf_of_cellWf r5.2)
        ih p hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · -- NE quadrant
      right; left
      norm_cast
      exact p4_ne_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_nw nw_ne nw_sw nw_se))
        (hashlifeResultAux (k + 1) (node nw_ne ne_nw nw_se ne_sw))
        (hashlifeResultAux (k + 1) (node ne_nw ne_ne ne_sw ne_se))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        rfl rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn4.1 hn5.1 hn6.1 hn7.1
        hn1.2 hn2.2 hn3.2 hn4.2 hn5.2 hn6.2 hn7.2
        r1.1 r2.1 r3.1 r5.1 r6.1
        (wf_of_cellWf r1.2) (wf_of_cellWf r2.2) (wf_of_cellWf r3.2)
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2)
        ih p out_nw hout_nw_l hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · -- SW quadrant
      right; right; left
      norm_cast
      exact p4_sw_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_sw nw_se sw_nw sw_ne))
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node sw_nw sw_ne sw_sw sw_se))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn4.1 hn5.1 hn7.1 hn8.1
        hn1.2 hn2.2 hn3.2 hn4.2 hn5.2 hn7.2 hn8.2
        r4.1 r5.1 r7.1 r8.1
        (wf_of_cellWf r4.2) (wf_of_cellWf r5.2) (wf_of_cellWf r7.2) (wf_of_cellWf r8.2)
        ih p out_nw hout_nw_l hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2
    · -- SE quadrant
      right; right; right
      norm_cast
      exact p4_se_membership_arm_rev k hk1
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se
        sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        (hashlifeResultAux (k + 1) (node nw_se ne_sw sw_ne se_nw))
        (hashlifeResultAux (k + 1) (node ne_sw ne_se se_nw se_ne))
        (hashlifeResultAux (k + 1) (node sw_ne se_nw sw_se se_sw))
        (hashlifeResultAux (k + 1) (node se_nw se_ne se_sw se_se))
        rfl rfl rfl rfl
        hn1.1 hn2.1 hn3.1 hn4.1 hn5.1 hn6.1 hn7.1 hn8.1 hn9.1
        hn1.2 hn2.2 hn3.2 hn4.2 hn5.2 hn6.2 hn7.2 hn8.2 hn9.2
        r5.1 r6.1 r8.1 r9.1
        (wf_of_cellWf r5.2) (wf_of_cellWf r6.2) (wf_of_cellWf r8.2) (wf_of_cellWf r9.2)
        ih p out_nw hout_nw_l hmem hq.1 hq.2.1 hq.2.2.1 hq.2.2.2

/-- For a level-`k` MacroCell `c` with `k ≥ 2`, the centered region of
    `hashlifeResultAux (k+2) c` (viewed at offset `(2^k, 2^k)`) equals
    `evolve (2^k)` applied to `c.toGrid (0, 0)` and restricted to the
    centered `[2^k, 2^k + 2^(k+1)) × [2^k, 2^k + 2^(k+1))` region.

    **Statement correction**: offset `(2^k, 2^k)` accounts for centering.

    **Proof strategy** (P4, difficulty: hard, compositional):
    Strong induction on `k`.
    - Base `k = 0`: `hashlifeResultAux 2 c` reduces to `step4x4 c`, which
      is the direct B3/S23 computation on a 4x4 grid. The centered 2x2
      result at offset `(1, 1)` matches `evolve 1` restricted to `[1,3)×[1,3)`.
    - Inductive step `k → k+1`: the recursive Hashlife makes 9 sub-calls on
      level-`(k+1)` cells, then 4 sub-calls on the resulting level-`k`
      supercells. Each sub-call uses the IH at level `k`. The composition
      matches `step^[2^(k+1)]` by the light-cone lemma P2 applied 2^(k-1)
      times (once per "half-step" in the double-nine decomposition). -/
theorem hashlifeResult_central_correct (c : MacroCell) (k : Nat)
    (hwf : c.wf = true) (hk : c.level = k + 2) :
    let result := hashlifeResultAux (k + 2) c
    let resultGrid := result.toGrid ((2^k : Nat), (2^k : Nat))
    let expected := evolve (2^k) (c.toGrid (0, 0))
    resultGrid = restrictGridTo expected (2^k : Int) (2^(k+1)) := by
  -- P4 TARGET: central Hashlife correctness, by STRONG induction on the level
  -- index `k`. The motive quantifies over `c` (reverted before induction) so
  -- the induction hypothesis `ih` ranges over every MacroCell at a smaller
  -- level (not just a fixed `c`): this is required because the recursive step
  -- applies the IH to the double-nine *sub-cells* `n_i` of `c`, which are
  -- MacroCells distinct from `c` itself. A plain `cases k` exposes no such
  -- cross-cell IH, which (c.137) forced `p4_wave1_ih` to stay a vacuous `True`
  -- placeholder to avoid a forbidden mutual-recursion cycle. Threading `ih`
  -- down through `p4_succ_membership` -> `p4_wave1_ih` breaks that cycle (c.138),
  -- and the c.139 helper `p4_wave1_ih_step` makes the `ih` application compile.
  revert c hwf hk
  induction k using Nat.strongRecOn with
  | ind n ih =>
    intro c hwf hk
    cases n with
    | zero => exact hashlifeResult_central_correct_base c hwf hk
    | succ k =>
      have hk1 : 1 ≤ k + 1 := by omega
      exact p4_ext_bridge c (k + 1)
        (p4_succ_membership c (k + 1) hwf hk hk1
          (fun c' j hj hc'w hc'l => ih j hj c' hc'w hc'l))

/-! ## P4 witnesses: base case k=0 (native_decide)

Concrete level-2 MacroCells verifying that the corrected P4 statement
holds on the base case `k = 0` (level-2 input, offset `(1,1)`, 1 generation).
Each `native_decide` confirms the theorem is satisfiable. -/

/-- Level-2 cell with the block pattern at positions (1,1)-(2,2). -/
private def blockCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf true))
                 (MacroCell.node (leaf false) (leaf false) (leaf true)  (leaf false))
                 (MacroCell.node (leaf false) (leaf true)  (leaf false) (leaf false))
                 (MacroCell.node (leaf true)  (leaf false) (leaf false) (leaf false))

/-- Level-2 cell with a horizontal blinker at positions (0,1),(1,1),(2,1). -/
private def blinkerHCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf true) (leaf false) (leaf true))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf true) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))

/-- Level-2 cell with the glider pattern at positions (0,1),(1,2),(2,0),(2,1),(2,2). -/
private def gliderCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf true)  (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf true))
                 (MacroCell.node (leaf true)  (leaf true)  (leaf false) (leaf false))
                 (MacroCell.node (leaf true)  (leaf false) (leaf false) (leaf false))

/-- P4 base case k=0 on block (still life): centered 2x2 matches after 1 step. -/
theorem p4_base_block :
    (hashlifeResultAux 2 blockCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (blockCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-- P4 base case k=0 on all-dead: trivially empty. -/
private def deadCell : MacroCell :=
  MacroCell.node (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))
                 (MacroCell.node (leaf false) (leaf false) (leaf false) (leaf false))

theorem p4_base_dead :
    (hashlifeResultAux 2 deadCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (deadCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-- P4 base case k=0 on glider: centered 2x2 matches after 1 step. -/
theorem p4_base_glider :
    (hashlifeResultAux 2 gliderCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (gliderCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-- P4 base case k=0 on blinker: key test — cell (1,0) is outside center. -/
theorem p4_base_blinker :
    (hashlifeResultAux 2 blinkerHCell).toGrid (1, 1)
    = restrictGridTo (evolve 1 (blinkerHCell.toGrid (0, 0))) 1 2 := by
  native_decide

/-! ## P4 witnesses: recursive arms (k = 1, k = 2)

Concrete well-formed instances of the corrected statement exercising the
double-nine recursion (one layer at `k = 1`, two layers at `k = 2`). -/

/-- P4 witness at k = 1 (level-3, one recursion layer): a block (still
    life) centered in an 8×8 cell, 2 generations. -/
theorem p4_wf_witness_k1 :
    (centerInLevelPlus2 (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf)).wf
        = true
    ∧ (hashlifeResultAux 3
          (centerInLevelPlus2
            (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf))).toGrid
        ((2 : Int), (2 : Int))
      = restrictGridTo
          (evolve 2
            ((centerInLevelPlus2
              (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf)).toGrid (0, 0)))
          2 4 := by
  native_decide

/-- P4 witness at k = 2 (level-4, two recursion layers): a glider
    centered in a 16×16 cell, 4 generations (the glider translates by
    `(+1, +1)`, staying inside the centered 8×8 window). -/
theorem p4_wf_witness_k2 :
    (centerInLevelPlus2 gliderCell).wf = true
    ∧ (hashlifeResultAux 4 (centerInLevelPlus2 gliderCell)).toGrid
        ((4 : Int), (4 : Int))
      = restrictGridTo
          (evolve 4 ((centerInLevelPlus2 gliderCell).toGrid (0, 0)))
          4 8 := by
  native_decide

/-! ## P5. Fuel-exhaustion invariant (Gap 1)

A definitional building block toward the full P5 theorem. The auxiliary
`evolveHashlifeFastAux` has a defensive branch `| 0, _, g => g` (fuel exhausted,
return the grid unchanged) which is only sound when `n = 0` has also been
reached. The lemma below discharges the relevant case directly: when `n = 0`,
the **first** pattern (`| _, 0, g => g`) fires regardless of the fuel value,
so the result is `g` independently of the fuel-exhaustion arm.

This is the first half of the Gap-1 invariant (the `n = 0` guard takes
priority over the fuel guard); the second half — proving the fuel-exhaustion
arm is unreachable on the real `evolveHashlifeFast n g = evolveHashlifeFastAux n n g`
call path when `n > 0` — remains open and is documented in `hashlife_correct`. -/

/-- When `n = 0`, `evolveHashlifeFastAux` returns `g` independently of the fuel
    value: the `n = 0` pattern (`| _, 0, g => g`) is matched before the
    fuel-exhaustion pattern (`| 0, _, g => g`). This discharges the fuel arm
    in the trivial case and is a prerequisite for reasoning about the
    fuel-invariant behaviour of `evolveHashlifeFast`. -/
theorem evolveHashlifeFastAux_zero_n (fuel : Nat) (g : Grid) :
    evolveHashlifeFastAux fuel 0 g = g := by
  -- The `n = 0` pattern (`| _, 0, g => g`) is the FIRST arm of
  -- `evolveHashlifeFastAux`, so it fires regardless of `fuel`. But `rfl`
  -- fails with `fuel` a free variable: the pattern-matcher inspects `fuel`
  -- first and blocks on the unknown constructor. Splitting on `fuel`
  -- (`0` or `succ`) lets the first arm reduce definitionally in each case.
  cases fuel <;> rfl

/-! ## P5. Main theorem: bounded correctness

The top-level theorem composing P2, P3, P4. -/


/-! ### P5 base case (n = 0)

The trivial case `n = 0`: both `evolveHashlifeFast` and `evolve` return the
grid unchanged. This is the first proven building block toward the full P5
theorem. The remaining work is the inductive step (small `n` fallback + large
`n` jump), documented in `hashlife_correct` below. -/

/-- Base case `n = 0` of `hashlife_correct`: no evolution means no change on
    either side. Both `evolveHashlifeFast 0 g` (via `evolveHashlifeFastAux 0 0 g`)
    and `evolve 0 g` reduce to `g` definitionally. -/
theorem hashlife_correct_base_zero (g : Grid) :
    evolveHashlifeFast 0 g = evolve 0 g := by
  -- evolveHashlifeFast 0 g = evolveHashlifeFastAux 0 0 g = g  (second pattern: 0, _, g => g)
  -- evolve 0 g = g                                           (evolve_zero : rfl)
  rfl

/-! ## P5 inductive step — scaffolding (fallback + jump)

The `sorry` previously sitting at the top of `hashlife_correct` is the second
research-level verrou. It is the **composition** of P4 (central correctness)
with P2 (light-cone) by induction on `n`, with a case split on the MacroCell
level `k` chosen by `box_assez_grand`.

### Proof plan (small-n fallback + large-n jump)

Given `n` and a grid `g` with `box_assez_grand g n`, let `k` be the level
chosen by the predicate (so `c = buildFromGrid k g` is a well-formed level-`k`
cell containing `g` with enough padding). Two cases:

  **Small `n`** (`n < 2^(k-2)`): `evolveHashlifeFast` falls back to `evolve`
  directly — its `evolveHashlifeFastAux` defensive branch delegates to the
  reference step-by-step implementation. Trivially equal. Difficulty: P5.1.

  **Large `n`** (`n ≥ 2^(k-2)`): one Hashlife jump of `2^(k-2)` generations by
  P4 (`hashlifeResult_central_correct`), then recurse on the residual
  `n - 2^(k-2)` generations. The light-cone lemma P2 (`step_light_cone`,
  proven) ensures the boundary of the MacroCell does not interfere with the
  live region during the jump. The padding hypothesis `box_assez_grand` is
  preserved through the recursion (the jump expands the bounding box by at
  most `2^(k-2)`, within the padding margin). Difficulty: P5.2.

### Dependency

`p5_large_n_jump` (P5.2) calls `hashlifeResult_central_correct` (P4) — P4
is now **proved** (`p4_succ_membership`, sorry-free), so this dependency no
longer blocks anything (gate-status correction, 2026-08-14). What still gates
the genuine `p5_large_n_jumpN` sorry is the locality bridge + multi-jump
recursion invariant documented at the theorem. `p5_small_n_fallback`
(P5.1) is independent of P4 and already proven. The full
`p5_inductive_step` glues the two cases; it stays `sorry` until both sub-lemmas
are ready.

### Sub-lemmas (difficulty-ranked)

| Lemma | Difficulty | Dependency | What it proves |
|-------|-----------|------------|----------------|
| `p5_small_n_fallback` | P5.1 (definitional) | none | When `n < 2^(k-2)`, `evolveHashlifeFast n g = evolve n g` by the defensive fallback arm |
| `p5_large_n_jump`     | P5.2 (compositional) | **P4** + P2 | When `n ≥ 2^(k-2)`, one P4 jump + light-cone-preserving recursion on `n - 2^(k-2)` |
| `p5_inductive_step`   | P5.3 (glue)         | P5.1 + P5.2 | The full induction on `n`, case-split on `n vs 2^(k-2)` |

See `agent_tests/prover/RUNBOOK.md` for the iteration protocol. -/

/-- **P5.1** (definitional, no P4 dependency): when the number of generations
    `n` is smaller than `jumpSize lvl` (the Hashlife jump size for the grid's
    MacroCell level `lvl`), `evolveHashlifeFast` does not make a recursive
    Hashlife jump — it falls back to the reference `evolve`. This is pure
    definitional unfolding of `evolveHashlifeFastAux`'s small-n arm.

    **PROVEN** (eliminates 1 sorry from the scaffolding). The `zero` case is
    definitional (`evolve 0 g = g`). The `succ k` case splits the guard
    `lvl ≥ 2 && (k+1) ≥ jumpSize lvl`: the guard-true branch contradicts the
    hypothesis `k+1 < jumpSize lvl`, the guard-false branch is the `evolve`
    fallback (definitional equality). -/
theorem p5_small_n_fallback (n : Nat) (g : Grid)
    (h : n < jumpSize (gridToMacroCellWithOffset g).2.level) :
    evolveHashlifeFast n g = evolve n g := by
  show evolveHashlifeFastAux n n g = evolve n g
  cases n with
  | zero => rfl
  | succ k =>
    simp only [evolveHashlifeFastAux]
    split_ifs with hcond
    · -- guard true (jump branch): impossible under h : k+1 < js
      exfalso
      obtain ⟨_hlvl, hnjs⟩ : (gridToMacroCellWithOffset g).2.level ≥ 2 ∧ k + 1 ≥
          jumpSize (gridToMacroCellWithOffset g).2.level := by
        simpa using hcond
      exact absurd hnjs (Nat.not_le_of_lt h)
    · rfl

/-! ### P5.2 obstacle scan (2026-06-15)

**Status after merges #3053 + #3062.** The wf+level structural inputs feeding
`hashlifeResult_central_correct` (L1412) at the P5.2 jump step are now formally
available:

- `wf_padCenter2`    (L1028, PR #3053): `c.wf = true → (padCenter2 c).wf = true`
- `level_padCenter2` (L1031, PR #3062): `1 ≤ c.level → (padCenter2 c).level = c.level + 2`

So when `p5_large_n_jump` eventually invokes the P4 lemma on `padCenter2 c`,
both hypotheses `(hwf : (padCenter2 c).wf = true)` and
`(hk : (padCenter2 c).level = k + 2)` (with `k := c.level`) are dischargeable
from `c.wf = true` and `1 ≤ c.level`. The "wf composition lift residual"
dispatched 2026-06-15 09:59Z is now structurally closed on both axes.

**Residual obstacle chain (3 `sorry` total: L2527, L2855, L2864).**

  `p5_large_n_jump`            (L2852, re-signed to real target — proof body `sorry` at L2855)
    └→ `hashlifeResult_central_correct`  (L2546 — P4 entry point)
         └→ inductive `succ k` arm of P4 — 1 residual `sorry`:
              · wave-glue residual       (L2527, succ-arm composition + assembly)
            (the shape/IH sub-lemmas `p4_double_nine_shape` L1744, `p4_wave1_ih_step`
            L2108, `p4_wave2_ih_step` L2146 carry no `sorry`; the P4.4 half-step
            composition is closed via `evolve_add`/`evolve_half_step` — see note)

The P4 inductive step is **research-level, multi-cycle**. The base case `k = 0`
of P4 is already fully proven (`hashlifeResult_central_correct_base`, L1648,
shape lemmas + `2^16` `native_decide`).

**Note on P4.4 (SUPPRESSED in N2-bis, 2026-07-09).** The standalone
`p4_half_steps_compose` theorem was a `: True` placeholder. Its pure-evolve
half-step content is exactly `evolve_add` (L2353) + `evolve_half_step` (L2370),
both already proven sorry-free; its wave-assembly content is exactly the
wave-glue residual (L2527). Re-signing it would either duplicate L2527 or be
vacuously provable (gaming the sorry count, G.2), so the coordinator greenlit
its **deletion** (sorry 4→3) together with its unused `have _h4` consumer in
`p4_succ_membership`. P4.4 is now carried by `evolve_add`/`evolve_half_step`
(closed) + the L2527 residual.

**N1 frame sub-claim — AUDITED VACUOUS (2026-07-09).** The previously sketched
grain

  `BoxAssezGrand g n → n ≥ jumpSize ... → BoxAssezGrand (jumpResult g) (n - jumpSize ...)`

was audited before proving: its hypotheses are **jointly unsatisfiable on
non-empty grids** (`p5_large_n_hyps_unsat`, proved in the "Structural
satisfiability bound" section above — `BoxAssezGrand g n` caps `n ≤ 2` while
`jumpSize ≥ 8`). Proving it "via decidable evaluation + Nat arithmetic" would
land another vacuous placeholder (the `p4_half_steps_compose` trap, N2-bis).
The frame lemma only becomes meaningful after the `gridFrame`/`box_assez_grand`
satisfiability redesign (design gate, ai-01) — re-scope it then.

**Re-signed target (N2, 2026-07-09).** `p5_large_n_jump` (L2852) now carries the
real conclusion

  `(h : BoxAssezGrand g n) (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) →`
  `  evolveHashlifeFast n g = evolve n g`

with the proof body still `sorry` (L2855) pending the P4 unlock. The obstacle
remains structural-on-P4, not local-on-P5. -/

/-- **P5.2 on the FIXED frame — VACUOUS, and therefore closed structurally
    (c.95, ai-01). This lemma carries no operational content.**

    The intent was: when `n ≥ 2^(k-2)`, `evolveHashlifeFast n g` makes one
    Hashlife jump of `2^(k-2)` generations (certified by P4,
    `hashlifeResult_central_correct`), then recurses on `n - 2^(k-2)`.

    **Correction of an earlier claim in this file.** The header above and the
    docstring this replaces both described the lemma as "blocked until P4". That
    was wrong, and the contradiction was already sitting two declarations below:
    `p5_inductive_step` discharges *exactly* this case with `False.elim`. On the
    fixed frame the two hypotheses are jointly unsatisfiable on non-empty grids
    — `BoxAssezGrand g n` caps `n ≤ 2` (`boxAssezGrand_nonempty_le_two`) while
    `hbig` forces `n ≥ 8` (`jumpSize_gridLevel_ge_eight`), whence
    `p5_large_n_hyps_unsat`. No P4 result can ever be needed here, because the
    branch is unreachable. The empty-grid case is separately trivial.

    So the `sorry` that stood here was a **decoy**: it advertised open research
    where there was none, and it could never have been closed by the P4 work it
    pointed at. Replacing it with the explicit vacuity discharge is a *reduction
    in misleading surface*, not a proof of anything — the sorry count drops by
    one while the mathematical content stays at zero, and that has to be said
    out loud rather than banked as progress.

    **The genuine large-`n` target is `p5_large_n_jumpN`** (n-aware frame,
    non-vacuous at `n ≥ 8`, witnessed by `boxAssezGrandN_block_8` /
    `boxAssezGrandN_glider_8`), which remains an open P4-gated sorry. Read that
    one, not this one. -/
theorem p5_large_n_jump (n : Nat) (g : Grid) (h : BoxAssezGrand g n)
    (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) :
    evolveHashlifeFast n g = evolve n g := by
  -- **NOT a P4 unlock.** See the docstring: on the fixed frame this statement
  -- is vacuous, and the discharge below is purely structural.
  by_cases hg : g = []
  · -- Empty grid: both sides reduce to `[]` (same unfolding as
    -- `p5_inductive_step`'s empty arm; `hbig` is never used).
    subst hg
    unfold evolveHashlifeFast
    cases n with
    | zero => simp [evolveHashlifeFastAux, evolve]
    | succ k =>
      simp [evolveHashlifeFastAux, gridToMacroCellWithOffset, gridFrame,
            buildFromGrid, MacroCell.level]
  · -- Non-empty grid: `BoxAssezGrand g n` caps `n ≤ 2` while `hbig` forces
    -- `n ≥ 8`. The hypotheses are contradictory.
    exact (p5_large_n_hyps_unsat g n hg h hbig).elim

/-- **P5.3** (glue): the full induction on `n`, with a case split on
    `n < 2^(k-2)` (P5.1) vs `n ≥ 2^(k-2)` (P5.2). Stays `sorry` until both
    sub-lemmas are proven.

    **P5 vacuity analysis (c.307a, 2026-07-10)**: on non-empty grids, the
    hypotheses of the `¬ hsmall` branch are jointly unsatisfiable — see
    `p5_large_n_hyps_unsat` (L425). Concretely:
    - `BoxAssezGrand g n` caps `n ≤ 2` (`boxAssezGrand_nonempty_le_two`,
      proven L358);
    - `n ≥ jumpSize (gridToMacroCellWithOffset g).2.level` requires
      `n ≥ 8` (`jumpSize_gridLevel_ge_eight`, proven L411).
    The conjunction `2 ≤ n ∧ n ≥ 8` is impossible. Hence the large-n arm
    is vacuous on non-empty grids, and `hashlife_correct` would be proven
    if the empty-grid arm (`g = []`) is closed separately (by direct unfold
    of `evolveHashlifeFastAux` on `g = []`, which takes the guard-false
    direct `evolve n g` arm because empty grids yield a level-0 MacroCell
    whose `lvl ≥ 2` guard is false).

    **Honest disclosure**: this vacuity closure is STRUCTURAL, not
    operational. It proves `hashlife_correct` (the bounded correctness
    theorem) WITHOUT actually exercising a Hashlife jump on non-empty
    grids — `box_assez_grand` is too tight (padding margin = 2 cells) to
    allow `n ≥ 8`. The genuine P5.2 jump-step correctness
    (`p5_large_n_jump`, L2999) remains an open sorry, gated on the P4 unlock
    per the section header at L2982. The vacuity closure demonstrates that
    `hashlife_correct`'s STATEMENT is satisfiable on canonical witness
    patterns (`hashlife_correct_implies_block_4` / `_glider_8`), but the
    theorem needs a SATISFIABILITY REDESIGN (`box_assez_grand` → a weaker
    hypothesis that allows `n ≥ 8`) before the genuine P5 jump can be
    proven. -/
theorem p5_inductive_step (n : Nat) (g : Grid) (h : BoxAssezGrand g n) :
    evolveHashlifeFast n g = evolve n g := by
  by_cases hg : g = []
  · -- Empty grid: both sides definitionally `[]`.
    -- `evolveHashlifeFast n [] = evolveHashlifeFastAux n n []`, which unfolds
    -- to `evolve n []` after the `0 >= 2` guard fails on `gridFrame []`'s
    -- level-0 MacroCell. `evolve n []` is `step^[n] []`, and `step [] = []`
    -- via `candidates [] = []`. So both sides are `[]`. The unfolding
    -- reduces to `rfl` after `simp` normalizes the auxiliary definitions.
    subst hg
    unfold evolveHashlifeFast
    cases n with
    | zero => simp [evolveHashlifeFastAux, evolve]
    | succ k =>
      -- `evolveHashlifeFastAux (k+1) (k+1) []` falls into the `fuel+1, n, g`
      -- branch. Inside, `gridToMacroCellWithOffset []` returns a level-0
      -- MacroCell, so `lvl >= 2` is false and we take the else branch
      -- (`evolve (k+1) []`). Lean reduces the `if` since `0 >= 2` is `false`.
      simp [evolveHashlifeFastAux, gridToMacroCellWithOffset, gridFrame,
            buildFromGrid, MacroCell.level]
  · -- Non-empty grid: case-split on `hsmall`.
    by_cases hsmall : n < jumpSize (gridToMacroCellWithOffset g).2.level
    · exact p5_small_n_fallback n g hsmall
    · -- `¬ hsmall` on a non-empty grid: the P5.2 hypotheses are jointly
      -- unsatisfiable (vacuous arm — see `p5_large_n_hyps_unsat`, c.307a
      -- disclosure). Reconstruct `n ≥ jumpSize` and discharge via `False.elim`.
      have hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level :=
        Nat.not_lt.mp hsmall
      exact (p5_large_n_hyps_unsat g n hg h hbig).elim


/-- **Hashlife correctness (bounded)**: under the padding hypothesis
    `box_assez_grand g n`, the exponential-speedup Hashlife implementation
    `evolveHashlifeFast n g` agrees with the reference `evolve n g`.

    **Proof strategy** (P5, difficulty: hard, compositional):
    Induction on `n` with case split on the MacroCell level `k`.
    - Small `n` (n < 2^k): `evolveHashlifeFast` falls back to `evolve`,
      trivially equal.
    - Large `n` (n ≥ 2^k): one jump of `2^k` generations by P4 + recurse on
      the residual `n - 2^k`. The light-cone lemma P2 ensures the boundary
      of the MacroCell doesn't interfere with the live region during the
      jump. The padding hypothesis `box_assez_grand` is preserved through
      the recursion because the jump preserves bounding box up to light-cone
      expansion.

    **Status (2026-06-13)**: base case `n = 0` proven above
    (`hashlife_correct_base_zero`). The inductive step remains open (the
    `sorry` below). See `hashlife_correct_implies_block_4` /
    `hashlife_correct_implies_glider_8` for sanity witnesses. -/
theorem hashlife_correct (n : Nat) (g : Grid) (h : BoxAssezGrand g n) :
    evolveHashlifeFast n g = evolve n g := by
  -- P5 TARGET: main theorem, composition of P2-P4
  -- Base case n = 0: see hashlife_correct_base_zero.
  -- Inductive step (fallback + jump): see p5_inductive_step below.
  exact p5_inductive_step n g h

/-! ## N2 restatement on the n-aware frame — gate W2 (EPIC #3846)

The fixed-frame `hashlife_correct` above is *proven* (via `p5_inductive_step`,
closed #5998), but its hypothesis `BoxAssezGrand g n` is structurally capped at
`n ≤ 2` on non-empty grids (`boxAssezGrand_nonempty_le_two`), while the Hashlife
jump guard requires `n ≥ jumpSize ≥ 8` (`jumpSize_gridLevel_ge_eight`). The
conjunction is unsatisfiable (`p5_large_n_hyps_unsat`), so `hashlife_correct` is
*vacuously true* for the large-`n` regime where the Hashlife jump is actually
exercised — the theorem is proven *without* any genuine jump (the
`p5_inductive_step` non-empty arm discharges via `False.elim` on that unsat
conjunction).

The n-aware restatement `hashlife_correctN` below replaces the hypothesis with
`BoxAssezGrandN g n` (the predicate over `gridFrameN n g`, padding `max 2 n`).
Because `gridFrameN` pads by `max 2 n ≥ n` on every side, `BoxAssezGrandN g n`
is *satisfiable for every `n`* (not just `n ≤ 2`) — witnessed at `n = 8` on
concrete Game-of-Life patterns by `box_assez_grandN_block_8` /
`box_assez_grandN_glider_8` (Bool form, proven above) and the universal
`box_assez_grandN_single_cell`. This makes the large-`n` statement
*non-vacuous*: it is the genuine P5.2 target.

**Anti-gaming (ai-01 gate, msg-...zylpzl).** The restatement carries real value
on the *spec* (a non-vacuous large-`n` correctness statement, witnessed at
`n = 8` on real patterns) and is the honest framing of the remaining work. The
genuine large-`n` Hashlife jump `p5_large_n_jumpN` (P5.2) is now PROVED
(b3', 2026-08-15) under the trajectory capture hypothesis — it is **not**
closed by any vacuity argument. The old "pending the P4 unlock
(`p4_succ_membership`)" reservation is void: P4 is proved, and the
locality bridge + multi-jump recursion are closed (see the b3' note at the
theorem). A hypothesis-honest proof is honest progress; a vacuous-worthless
proof would not be. -/

/-- **Non-vacuity witness, propositional form (gate W2, ai-01 garde-fou 1).**
    `BoxAssezGrandN block 8` holds — the 2×2 still-life carries margin `≥ 8` on
    every side under `gridFrameN 8` (padding `max 2 8 = 8`). This is the
    concrete substrate that makes `hashlife_correctN` non-vacuous at the
    large-`n` regime (vs the fixed-frame `BoxAssezGrand block 8`, unsatisfiable
    by the `n ≤ 2` cap). It is the propositional twin of the Bool-form
    `box_assez_grandN_block 8 = true` (proven above), discharged by the
    **triviality lemma** `boxAssezGrandN_trivial` (proved in `Foundation.lean`
    next to `BoxAssezGrandN`) — which says `BoxAssezGrandN g n` holds for
    **every** `g` and `n` because `gridFrameN n g` pads by `max 2 n ≥ n` on
    every side and `cellMargin` is non-strict. So both this witness and the
    analogous `boxAssezGrandN_glider_8` are now `forbidden-axiom-free` — the
    old `by native_decide` was a redundant machine-check on a tautological
    proposition (c.8207 sub-grain of #9568 cleanup). -/
theorem boxAssezGrandN_block_8 : BoxAssezGrandN block 8 := boxAssezGrandN_trivial _ _

/-- Same non-vacuity witness on the `glider` spaceship at `n = 8`
    (propositional form). Discharged by the triviality lemma — see
    `boxAssezGrandN_block_8` docstring. -/
theorem boxAssezGrandN_glider_8 : BoxAssezGrandN glider 8 := boxAssezGrandN_trivial _ _

/-- **Confinement authentique du jump** (re-signed, inlined from
    `Conway.Life.JumpCapture` to avoid the A↔B import cycle that exists because
    `JumpCapture.lean` imports `HashlifeCorrectness`). Byte-identical term to
    `Conway.Life.JumpCapture.jumpCaptured`; `private` prevents name-resolution
    ambiguity in the downstream module. -/
private def jumpCaptured (c : MacroCell) : Bool :=
  (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0))).all fun p =>
    decide ((2 ^ c.level : Int) ≤ p.1) &&
    decide (p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int)) &&
    decide ((2 ^ c.level : Int) ≤ p.2) &&
    decide (p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int))

/-- Dépliage propositionnel de `jumpCaptured` (inlined). -/
private theorem jumpCaptured_iff (c : MacroCell) :
    jumpCaptured c = true ↔
      ∀ p ∈ evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)),
        (2 ^ c.level : Int) ≤ p.1 ∧
          p.1 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) ∧
          (2 ^ c.level : Int) ≤ p.2 ∧
          p.2 < (2 ^ c.level : Int) + ((2 ^ (c.level + 1) : Nat) : Int) := by
  unfold jumpCaptured
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

/-! ### Inlining des briques de saut (JumpCapture.lean, cycle d'import)

`JumpCapture.lean` importe CE module (sa brique P4
`hashlifeResult_central_correct` vit ici), donc `p5_large_n_jumpN` ne peut
pas consommer `one_jump_toGrid_correct` par import. Les trois théorèmes
ci-dessous sont inlinés byte-identiques (mêmes preuves à l'identique),
même pattern que l'inlining de `jumpCaptured` ci-dessus ; `private` évite
toute ambiguïté de résolution dans le module aval. Toutes les autres
briques de l'assemblage BR4a (`toGrid_shift_grid` BR2,
`padCenter2_toGrid_shift` BR3, `wf_padCenter2`, `level_padCenter2`,
`evolve_shift`, `evolve_congr` BR5, `shift_shift`, `shift_zero`,
`canonical_evolve_of_pos`, `hashlifeResult_central_correct`) vivent dans
des modules importés (Foundation / GridCanonical / ce fichier) — aucune
copie nécessaire. -/

private theorem restrictGridTo_eq_self (g : Grid) (lo : Int) (size : Nat)
    (h : ∀ p ∈ g, lo ≤ p.1 ∧ p.1 < lo + (size : Int) ∧
          lo ≤ p.2 ∧ p.2 < lo + (size : Int)) :
    restrictGridTo g lo size = g := by
  induction g with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨h1, h2, h3, h4⟩ := h p List.mem_cons_self
    have hps : restrictGridTo ps lo size = ps :=
      ih fun q hq => h q (List.mem_cons_of_mem p hq)
    unfold restrictGridTo at hps ⊢
    rw [List.filter_cons, if_pos (by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      tauto), hps]

private theorem hashlifeJump_correct_of_captured (c : MacroCell)
    (hwf : c.wf = true) (hlvl : 1 ≤ c.level)
    (hcap : jumpCaptured c = true) :
    (hashlifeJump c).toGrid ((2 ^ c.level : Nat), (2 ^ c.level : Nat))
      = evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)) := by
  have hplvl : (padCenter2 c).level = c.level + 2 := level_padCenter2 c hlvl
  have hpwf : (padCenter2 c).wf = true := wf_padCenter2 c hwf
  have hjump : hashlifeJump c = hashlifeResultAux (c.level + 2) (padCenter2 c) := by
    unfold hashlifeJump hashlifeResult
    rw [hplvl]
  have h4 : (hashlifeResultAux (c.level + 2) (padCenter2 c)).toGrid
        ((2 ^ c.level : Nat), (2 ^ c.level : Nat))
      = restrictGridTo (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)))
          (2 ^ c.level : Int) (2 ^ (c.level + 1)) :=
    hashlifeResult_central_correct (padCenter2 c) c.level hpwf hplvl
  calc (hashlifeJump c).toGrid ((2 ^ c.level : Nat), (2 ^ c.level : Nat))
      = (hashlifeResultAux (c.level + 2) (padCenter2 c)).toGrid
          ((2 ^ c.level : Nat), (2 ^ c.level : Nat)) := by rw [hjump]
    _ = restrictGridTo (evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)))
          (2 ^ c.level : Int) (2 ^ (c.level + 1)) := h4
    _ = evolve (2 ^ c.level) ((padCenter2 c).toGrid (0, 0)) :=
        restrictGridTo_eq_self _ _ _ ((jumpCaptured_iff c).mp hcap)

private theorem one_jump_toGrid_correct (g : Grid) (off : Int × Int) (mc : MacroCell)
    (hmem : ∀ p, p ∈ mc.toGrid off ↔ p ∈ g)
    (hwf : mc.wf = true) (hlvl : 1 ≤ mc.level)
    (hcap : jumpCaptured mc = true) :
    (hashlifeJump mc).toGrid (jumpResultOff off mc.level)
      = evolve (jumpSize mc.level) g := by
  have hk1 : mc.level - 1 + 1 = mc.level := by omega
  have hnjs : 0 < 2 ^ mc.level := Nat.two_pow_pos _
  have h1js : 1 ≤ 2 ^ mc.level := by omega
  have h2k : ((2 ^ mc.level : Nat) : Int)
      = 2 * ((2 ^ (mc.level - 1) : Nat) : Int) := by
    have hp : (2 : Nat) ^ (mc.level - 1 + 1) = 2 ^ (mc.level - 1) * 2 := by
      rw [Nat.pow_succ]
    rw [hk1] at hp
    rw [hp, Nat.cast_mul]
    push_cast
    ring
  have hbrick := hashlifeJump_correct_of_captured mc hwf hlvl hcap
  have hnew : jumpResultOff off mc.level
      = (off.1 - (2 ^ (mc.level - 1) : Nat),
         off.2 - (2 ^ (mc.level - 1) : Nat)) := by
    unfold jumpResultOff
    split
    · next h0 =>
        exfalso
        have hb : Nat.beq mc.level 0 = true := by simpa [BEq] using h0
        have hz : mc.level = 0 := Nat.eq_of_beq_eq_true hb
        omega
    · rfl
  have hmc0 : mc.toGrid (0, 0)
      = shift (0 - off.1, 0 - off.2) (mc.toGrid (off.1, off.2)) :=
    toGrid_shift_grid mc 0 0 off.1 off.2
  have hmem' : ∀ p, p ∈ mc.toGrid (off.1, off.2) ↔ p ∈ g := by
    simpa using hmem
  simp only [jumpSize]
  rw [hnew,
    toGrid_shift_grid (hashlifeJump mc) _ _ (2 ^ mc.level : Nat)
      (2 ^ mc.level : Nat),
    hbrick, padCenter2_toGrid_shift mc hlvl, ← evolve_shift, hmc0,
    ← evolve_shift, evolve_congr hmem' h1js, shift_shift, shift_shift]
  have hpow : (2 : Int) ^ (mc.level - 1) = ((2 ^ (mc.level - 1) : Nat) : Int) := by
    exact (Nat.cast_pow (2 : Nat) (mc.level - 1)).symm
  have hz1 : (off.1 - (2 ^ (mc.level - 1) : Nat)) - (2 ^ mc.level : Nat)
      + 3 * (2 ^ (mc.level - 1) : Int) + (0 - off.1) = 0 := by
    rw [hpow, h2k]
    omega
  have hz2 : (off.2 - (2 ^ (mc.level - 1) : Nat)) - (2 ^ mc.level : Nat)
      + 3 * (2 ^ (mc.level - 1) : Int) + (0 - off.2) = 0 := by
    rw [hpow, h2k]
    omega
  rw [hz1, hz2, shift_zero (canonical_evolve_of_pos hnjs g)]

/-! ### Pourquoi il n'y a PAS de mur « préservation de la capture » (b3')

La récursion multi-sauts ci-dessous ne demande PAS un lemme
`jumpCaptured_jump_preserved` (capture à `t = 0` implique capture à
`t = 2^lvl`). Un tel énoncé n'est pas un théorème : deux résultats PROUVÉS
sur `main` l'écartent comme cible atteignable par un argument structurel,
et l'intuition dynamique le dit faux.

1. **`window_margin_lt_cone_reach`** (`JumpCapture.lean`, `k ≥ 3`) : la
   marge de fenêtre `2^(k-1) + 2` est strictement inférieure à la portée
   du cône `2^k` — la machinerie cône-c=1 ne peut fermer la capture pour
   `lvl ≥ 3`, quel que soit l'assemblage.
2. **`no_padding_depth_suffices`** (`JumpCapture.lean`, toute profondeur
   `p ≥ 1`) : `marginToResultWindow k p < jumpReach k p` — le déficit
   vaut la demi-largeur `b` du contenu, CONSTANT en `p`. Aucune profondeur
   de rembourrage ne referme l'écart : la capture est une propriété
   DYNAMIQUE (la trajectoire réelle doit rester dans la fenêtre), pas
   géométrique.

Et dynamiquement, la préservation est fausse en général : « capture du
premier saut » ne contraint que `[0, 2^lvl]`, alors qu'un motif-relais
(noyaux de collision de planeurs, fusible à retardement) peut être
contenu pendant exactement `2^lvl` générations puis produire un front
expansif — le témoin `jumpCaptured_not_trivial` (ligne de 7 s'échappant
en 8 générations) illustre l'échec au niveau 3 ; un relais qui SYNTHÉTISE
une telle ligne après le premier saut falsifie la préservation.

**Conséquence honnête** : l'hypothèse de capture doit couvrir la
TRAJECTOIRE (`∀ t ≤ n`), pas seulement `t = 0`. C'est la re-signature
ci-dessous — non tautologique (témoins block/glider : toute la
trajectoire capturée ; falsifiée par `lineCell3` dès `t = 8`), et c'est
exactement le contenu que le moteur consomme : à chaque itération il
re-trame la grille COURANTE et saute. La correction sous hypothèse de
capture trajectoire est alors PROUVÉE sans aucun sorry — le contenu de
recherche restant (caractériser les motifs dont la capture persiste)
vit dans l'hypothèse, où il est irréductible par 1 et 2. -/

/-- **Squelette d'induction multi-sauts (b) — PROUVÉ.**
    Pour tout `fuel ≥ n` et toute grille dont la TRAJECTOIRE est capturée
    (hypothèse `∀ t ≤ n`, re-signature b3' justifiée ci-dessus),
    `evolveHashlifeFastAux fuel n g = evolve n g`. L'invariant `n ≤ fuel`
    se préserve car chaque saut consomme `js = 2^lvl ≥ 1` générations pour
    1 unité de fuel (le moteur initialise `fuel = n`, cf. docstring de
    `evolveHashlifeFast`) ; le bras `else` rend littéralement `evolve n g` ;
    le bras de saut applique la brique (a) (`one_jump_toGrid_correct`) —
    qui identifie la grille sautée à `evolve js g` —, l'hypothèse
    d'induction sur le fuel décroissant (hypothèse de trajectoire
    ré-instantiée en `t + js` via `evolve_add`), puis recompose par
    `evolve_add` (S1, Foundation). Aucune hypothèse non fermée. -/
private theorem evolveHashlifeFastAux_correct (fuel n : Nat) (g : Grid)
    (hle : n ≤ fuel)
    (hcap : ∀ t ≤ n, jumpCaptured (gridToMacroCellWithOffset (evolve t g)).2
      = true) :
    evolveHashlifeFastAux fuel n g = evolve n g := by
  induction fuel generalizing n g with
  | zero =>
    have hn0 : n = 0 := Nat.le_zero.mp hle
    subst hn0
    rfl
  | succ fuel ih =>
    cases n with
    | zero => rfl
    | succ m =>
      simp only [evolveHashlifeFastAux]
      split
      · next hcond =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨hlvl2, hnjs⟩ := hcond
        have hlvl1 : 1 ≤ (gridToMacroCellWithOffset g).2.level := by omega
        have hwf : (gridToMacroCellWithOffset g).2.wf = true := by
          unfold gridToMacroCellWithOffset
          exact buildFromGrid_wf g _ _ _
        have hmem : ∀ p, p ∈ (gridToMacroCellWithOffset g).2.toGrid
            (gridToMacroCellWithOffset g).1 ↔ p ∈ g :=
          mem_toGrid_gridToMacroCellWithOffset g
        have hone := one_jump_toGrid_correct g
          (gridToMacroCellWithOffset g).1 (gridToMacroCellWithOffset g).2
          hmem hwf hlvl1 (hcap 0 (by omega))
        have hjspo : 0 < jumpSize (gridToMacroCellWithOffset g).2.level := by
          simp only [jumpSize]
          exact Nat.two_pow_pos _
        have hle' : m + 1 - jumpSize (gridToMacroCellWithOffset g).2.level
            ≤ fuel := by omega
        have hcap' : ∀ t ≤ m + 1 - jumpSize (gridToMacroCellWithOffset g).2.level,
            jumpCaptured (gridToMacroCellWithOffset
              (evolve t ((hashlifeJump (gridToMacroCellWithOffset g).2).toGrid
                (jumpResultOff (gridToMacroCellWithOffset g).1
                  (gridToMacroCellWithOffset g).2.level)))).2 = true := by
          intro t ht
          rw [hone, ← evolve_add]
          exact hcap (t + jumpSize (gridToMacroCellWithOffset g).2.level)
            (by omega)
        rw [ih (m + 1 - jumpSize (gridToMacroCellWithOffset g).2.level)
              ((hashlifeJump (gridToMacroCellWithOffset g).2).toGrid
                (jumpResultOff (gridToMacroCellWithOffset g).1
                  (gridToMacroCellWithOffset g).2.level)) hle' hcap',
            hone, ← evolve_add]
        have hsum : (m + 1 - jumpSize (gridToMacroCellWithOffset g).2.level)
            + jumpSize (gridToMacroCellWithOffset g).2.level = m + 1 := by
          omega
        rw [hsum]
      · rfl

/-- **P5.2 genuine large-`n` jump (N2) — PROVED (b3', 2026-08-15) under
    trajectory capture.** When `n ≥ jumpSize lvl` (the MacroCell level)
    on the n-aware frame, `evolveHashlifeFast` makes one Hashlife jump of
    `jumpSize lvl = 2^lvl` generations (via `hashlifeJump = hashlifeResult
    (padCenter2 c)` on the level-`lvl+2` padded cell, certified by P4
    `hashlifeResult_central_correct`) then recurses on `n - jumpSize lvl`.
    Under the trajectory capture hypothesis (see the b3' re-signing note
    below), every jump is exact and the engine agrees with `evolve` —
    **sorry-free**, NOT closed by vacuity.

    **Gate status corrected (c.po-2025, 2026-08-14).** The docstring used to
    say "P4-gated (`p4_succ_membership`, ai-01 turf)". That gate has FALLEN:
    `p4_succ_membership` is proved sorry-free, so **nothing about P4 blocks
    this sorry anymore** — the note cost weeks of misplaced reservation and
    is corrected here in the same diff cycle that measured it. The remaining
    open content, mapped firsthand (po-2025, all ingredients verified on
    `main`):
    - the **one-jump brick already exists and is proved**:
      `hashlifeJump_correct_of_captured` (`JumpCapture.lean` §5) composes P4
      (`hashlifeResult_central_correct`), `wf_padCenter2`/`level_padCenter2`
      and `restrictGridTo_eq_self` into
      `(hashlifeJump c).toGrid (2^c.level, 2^c.level)
        = evolve (2^c.level) ((padCenter2 c).toGrid (0, 0))` under
      `c.wf = true`, `1 ≤ c.level`, `jumpCaptured c = true`;
    - still missing: (a) the **locality bridge** from the padded cell's grid
      to `g` — agreement of `evolve (2^lvl) ((padCenter2 mc).toGrid (0,0))`
      with `evolve (2^lvl) g` on the central window, assemblable from
      `evolve_cone_agree` + `padCenter2_margin_ge_jumpReach` (margin
      `3·2^(k-1) ≥ 2^k` reach) + `toGrid_shift_between` offset algebra, in
      the style of `p4_succ_membership` (which took 542 lines); and
      (b) the **multi-jump recursion invariant** — the recursive call needs
      `jumpCaptured` for the jumped grid `g'`, which is an independent
      geometric fact, not derivable from the initial `hcap`; it requires the
      light-cone preservation argument through `gridFrameN` margins
      (`window_cheb_cone_in_domain`), i.e. the frame redesign flagged in the
      N1 sub-claim audit below.

    **Re-signed (c.1035, finding #6724 — voie (a)).** The hypothesis was
    `BoxAssezGrandN g n`, which is **tautological** (proved by
    `box_assez_grandN_trivial` in `Foundation.lean`, next to `BoxAssezGrandN` —
    relocated c.8206 from `JumpCapture.lean` to break an import cycle) — so the old
    `p5_large_n_jumpN_iff_unconditional` showed the original statement carried
    zero information. Re-signed to consume `jumpCaptured
    (gridToMacroCellWithOffset g).2 = true` (inlined above to avoid the import
    cycle that would arise from `import Conway.Life.JumpCapture`, since
    `JumpCapture.lean` itself imports `HashlifeCorrectness`). The new
    hypothesis is **non-tautological** (witnessed by `jumpCaptured_block`,
    `jumpCaptured_glider`, `jumpCaptured_not_trivial` in `JumpCapture.lean`),
    so this restatement carries real geometric content.

    **Re-signed to TRAJECTORY capture (b3', 2026-08-15) — the sorry is
    DISCHARGED.** The `t = 0`-only capture hypothesis cannot support a
    multi-jump theorem: the recursion rebuilds the frame of the CURRENT
    grid at every iteration, so correctness needs capture along the whole
    trajectory, and a `t = 0`-only hypothesis would make the statement
    FALSE (relay patterns: contained for exactly `2^lvl` generations, then
    an expansive front — see the impossibility note above
    `evolveHashlifeFastAux_correct`; structurally, the PROVED lemmas
    `window_margin_lt_cone_reach` + `no_padding_depth_suffices` close off
    every geometric route to a preservation lemma). The hypothesis
    `∀ t ≤ n, jumpCaptured (gridToMacroCellWithOffset (evolve t g)).2 = true`
    is the honest minimal assumption the engine actually consumes: still
    non-tautological (block/glider trajectories satisfy it;
    `lineCell3` violates it at `t = 8`), and now the body is PROVED
    sorry-free: the three one-jump bricks are inlined below the private
    `jumpCaptured` (`private` copies, byte-identical to
    `JumpCapture.lean`), and the fuel induction is closed in
    `evolveHashlifeFastAux_correct` (invariant `n ≤ fuel`, trajectory
    hypothesis re-instantiated at `t + jumpSize` via `evolve_add`). The
    residual research content — characterizing the patterns whose capture
    persists — now lives in the hypothesis, where the impossibility lemmas
    show it is irreducible.

    **Moved above `hashlife_correctN` (c.95)** so the latter can consume it: the
    N-frame statement is now *derived* from this jump plus the padding-free
    small-`n` fallback, instead of carrying an independent sorry of its own. -/
theorem p5_large_n_jumpN (n : Nat) (g : Grid)
    (hcap : ∀ t ≤ n, jumpCaptured (gridToMacroCellWithOffset (evolve t g)).2
      = true)
    (hbig : n ≥ jumpSize (gridToMacroCellWithOffset g).2.level) :
    evolveHashlifeFast n g = evolve n g := by
  unfold evolveHashlifeFast
  exact evolveHashlifeFastAux_correct n n g (Nat.le_refl n) hcap

/-- **N2 restatement — the genuine large-`n` correctness statement (EPIC #3846,
    gate W2).** Under the **trajectory capture hypothesis** `∀ t ≤ n,
    jumpCaptured (gridToMacroCellWithOffset (evolve t g)).2 = true` (i.e.,
    at every generation `t ≤ n`, the re-framed MacroCell representation of
    the evolved grid stays inside the central window that P4 clips),
    `evolveHashlifeFast n g` agrees with `evolve n g`. **Sorry-free since
    b3'** (2026-08-15).

    **Re-signed (c.1035, finding #6724).** The previous hypothesis
    `BoxAssezGrandN g n` was **tautological** (`box_assez_grandN_trivial`,
    `Foundation.lean` — relocated c.8206 from `JumpCapture.lean` to break an import cycle) — it held for *every* `(g, n)` and thus carried no
    information. The new hypothesis `jumpCaptured (gridToMacroCellWithOffset
    g).2 = true` is **non-tautological** (witnessed by `jumpCaptured_block`,
    `jumpCaptured_glider`, `jumpCaptured_not_trivial` in `JumpCapture.lean`)
    and makes this theorem genuinely informative; the trajectory
    strengthening (b3') is forced by the proved impossibility lemmas —
    see the note above `evolveHashlifeFastAux_correct`.

    **Reduction (c.95, ai-01).** The theorem no longer carries a sorry of its
    own. Splitting on the jump guard discharges it entirely:
    - `n < jumpSize` : `p5_small_n_fallback`, which takes **no padding
      hypothesis whatsoever** — it holds on any frame, the n-aware one included;
    - `n ≥ jumpSize` : `p5_large_n_jumpN`, the genuine large-`n` jump, which
      consumes the TRAJECTORY capture hypothesis (b3' re-signing — see its
      doc above); `hashlife_correctN`'s own hypothesis is the same
      trajectory form, passed through unchanged.

    This is a structural reduction, **not** a vacuity closure: before the
    c.95 change the two carried independent sorries, and a reader could not
    tell whether `hashlife_correctN` required work *beyond* the jump. It
    does not. Since b3' both arms are sorry-free; the whole dynamical
    content (capture persistence) is carried by the hypothesis.

    **Note (c.1035).** The non-vacuity witnesses
    `boxAssezGrandN_block_8` / `boxAssezGrandN_glider_8` (around L1140) are now
    orphaned relative to this theorem, since the hypothesis they satisfied is
    gone. They still typecheck standalone and are kept for traceability of
    the c.95 / c.1035 evolution; their substantive role is superseded by
    `jumpCaptured_block` / `jumpCaptured_glider` in `JumpCapture.lean`. The
    `BoxAssezGrandN` predicate itself remains consumed by
    `hashlife_correctN_le_two` (around L1270), which keeps the witnesses honest.

    **Note (c.8207).** Both witnesses are now proved via `boxAssezGrandN_trivial`
    (relocated c.8206 from `JumpCapture.lean` to `Foundation.lean` to break the
    import cycle) instead of `by native_decide`. They were redundant machine
    witnesses on a tautological proposition — `BoxAssezGrandN g n` holds for
    every `g` and `n` by the construction of `gridFrameN` padding `max 2 n ≥ n`
    and non-strict `cellMargin`. The forbidden-axiom class `native_decide.*`
    (per pr-review-discipline §B) is now eliminated at these two sites
    (c.8207 sub-grain of #9568 cleanup, follows the same pattern as the c.8205
    drop on the 4 `supportInMargin_*_k*` sanity checks). -/
theorem hashlife_correctN (n : Nat) (g : Grid)
    (hcap : ∀ t ≤ n, jumpCaptured (gridToMacroCellWithOffset (evolve t g)).2
      = true) :
    evolveHashlifeFast n g = evolve n g := by
  by_cases hsmall : n < jumpSize (gridToMacroCellWithOffset g).2.level
  · exact p5_small_n_fallback n g hsmall
  · exact p5_large_n_jumpN n g hcap (Nat.not_lt.mp hsmall)

/-- **N3 small-`n` bridge (issue #3846, ai-01 greenlight msg-zx9es2).** On the
    small-`n` regime (`n ≤ 2`), the n-aware spec `BoxAssezGrandN g n` coincides
    with the fixed-frame `BoxAssezGrand g n` (`box_assez_grandN_le_two_eq`), so
    the already-proven `hashlife_correct` discharges the N-version conclusion
    without re-proving it on the n-aware frame.

    Kept after the c.95 reduction of `hashlife_correctN`: it remains an
    *independent* route to the `n ≤ 2` arm, one that goes through the
    **fixed-frame** theorem and never touches `p5_large_n_jumpN` — so it stays
    sorry-free even if the jump is later restated or re-scoped. -/
theorem hashlife_correctN_le_two (n : Nat) (g : Grid) (hn : n ≤ 2)
    (h : BoxAssezGrandN g n) : evolveHashlifeFast n g = evolve n g := by
  apply hashlife_correct n g
  show box_assez_grand g n = true
  rw [← box_assez_grandN_le_two_eq n g hn]
  exact h

/-! ## Sanity witnesses (native_decide)

Concrete instantiations of `hashlife_correct` on small patterns verify that
the theorem is *satisfiable* under the padding hypothesis. Each `native_decide`
here strengthens the scaffolding by confirming the theorem is not vacuous. -/

/-- For the empty grid, any `n` is OK (no live cells to constrain) —
    `List.all` over `[]` is vacuously `true`. -/
example : BoxAssezGrand ([] : Grid) 0 := by
  decide

/-- **Consequence of the strengthen (c.151)**: the strengthened `box_assez_grand`
    only holds for `n ≤ 2` on these canonical patterns, because `gridFrame`
    fixes a 2-cell top/left padding (`r0 := rMin - 2`), so the top margin is
    exactly `2` — `r0 + n ≤ rMin` forces `n ≤ 2`. This is honest geometric
    content (the old vacuous predicate accepted `n = 4, 8` for free). It also
    surfaces a real property of the current `gridFrame`: it under-pads for
    large-`n` correctness, which is material for the P5 plan. -/
example : BoxAssezGrand block 2 := by
  native_decide

/-- The glider (3x3 bounding box) also holds for `n = 2` (its top/left margin
    is the same fixed `2` from `gridFrame`, and its bottom/right margin is
    large enough in the level-`3` frame). -/
example : BoxAssezGrand glider 2 := by
  native_decide

/-- If the theorem is true, then the `native_decide` witnesses must hold.
    This is a "soundness check" — if `hashlife_correct` ever gets proved,
    these follow by specialization. -/
theorem hashlife_correct_implies_block_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 block = evolve 2 block := by
  have hpad : BoxAssezGrand block 2 := by native_decide
  exact H 2 block hpad

/-- Same soundness check for the glider. -/
theorem hashlife_correct_implies_glider_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 glider = evolve 2 glider := by
  have hpad : BoxAssezGrand glider 2 := by native_decide
  exact H 2 glider hpad

/-- Period-2 oscillator (horizontal blinker, 3 cells in a row): holds for
    `n = 2` (same fixed-`2` top/left margin from `gridFrame`). -/
example : BoxAssezGrand blinker_h 2 := by
  native_decide

/-- Soundness check for the horizontal blinker. -/
theorem hashlife_correct_implies_blinker_h_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 blinker_h = evolve 2 blinker_h := by
  have hpad : BoxAssezGrand blinker_h 2 := by native_decide
  exact H 2 blinker_h hpad

/-- Period-2 oscillator (toad, 6 cells in a 4x2 box): holds for `n = 2`. -/
example : BoxAssezGrand toad 2 := by
  native_decide

/-- Soundness check for the toad. -/
theorem hashlife_correct_implies_toad_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 toad = evolve 2 toad := by
  have hpad : BoxAssezGrand toad 2 := by native_decide
  exact H 2 toad hpad

/-- Period-2 oscillator (beacon, two diagonal blocks in a 4x4 box): holds
    for `n = 2` (bottom/right margin `2` in the level-`3` frame). -/
example : BoxAssezGrand beacon 2 := by
  native_decide

/-- Soundness check for the beacon. -/
theorem hashlife_correct_implies_beacon_2
    (H : ∀ n g, BoxAssezGrand g n → evolveHashlifeFast n g = evolve n g) :
    evolveHashlifeFast 2 beacon = evolve 2 beacon := by
  have hpad : BoxAssezGrand beacon 2 := by native_decide
  exact H 2 beacon hpad

end Life
end Conway
