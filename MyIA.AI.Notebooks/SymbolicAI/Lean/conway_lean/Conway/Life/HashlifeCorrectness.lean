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

/-! ### P4-At : socle du moteur décorrélaté (grain 3, #11161)

La brique de base du saut décorrélaté `hashlifeResultAt j` (Hashlife.lean,
section « Saut à portée découplée ») : au niveau terminal `j + 2` de sa
récursion, le moteur At délègue au moteur plein `hashlifeResultAux` avec
le fuel saturé — exactement la forme du P4 prouvé
(`hashlifeResult_central_correct`). La correction centrale se transfère
donc TELLE QUELLE, sans hypothèse de capture. C'est le socle de la
décharge de `OneJumpAtCorrect` (grain 2 du re-cadrage Gosper, #11161) ;
le contenu restant du grain 3 est le pas inductif `M > j + 2` (assemblage
mono-ronde en sous-quadrants) puis le pont de localité (`evolve_box_agree`,
LightCone) avec l'invariant du cadre (grain 1). -/

/-- **P4-At cas de base (grain 3, #11161).** Pour toute cellule bien
    formée de niveau exactement `j + 2` (le niveau terminal de la récursion
    At), `hashlifeResultAt j c` est le moteur plein à fuel saturé et rend
    la fenêtre centrale de `evolve (2^j)` — l'énoncé P4 transféré
    littéralement au moteur décorrélaté, SANS hypothèse de capture.

    L'inversion `wf` passe par le prédicat OPAQUE `cellWf` (pont
    `cellWf_of_wf`) : le `Bool` transparent `MacroCell.wf` diverge en whnf
    sur les `node` en defeq (Foundation, note c.142). -/
theorem hashlifeResultAt_base_central (c : MacroCell) (j : Nat)
    (hwf : c.wf = true) (hklvl : c.level = j + 2) :
    (hashlifeResultAt j c).toGrid ((2^j : Nat), (2^j : Nat))
      = restrictGridTo (evolve (2^j) (c.toGrid (0, 0))) (2^j : Int) (2^(j+1)) := by
  have hshape : ∀ (x : MacroCell) (n : Nat), x.level = n + 1 →
      ∃ nw ne sw se, x = MacroCell.node nw ne sw se ∧ nw.level = n := by
    intro x n hx
    cases x with
    | leaf _ => simp only [MacroCell.level] at hx; omega
    | node nw ne sw se =>
        exact ⟨nw, ne, sw, se, rfl, by simp only [MacroCell.level] at hx; omega⟩
  have hnode : ∀ (q : MacroCell) (hq : q.level ≥ 1),
      ∃ p1 p2 p3 p4, q = MacroCell.node p1 p2 p3 p4 := by
    intro q hq
    cases q with
    | leaf _ => simp only [MacroCell.level] at hq; omega
    | node p1 p2 p3 p4 => exact ⟨p1, p2, p3, p4, rfl⟩
  have hwrap : hashlifeResultAt j c = hashlifeResultAux (j + 2) c := by
    unfold hashlifeResultAt
    rw [hklvl]
    obtain ⟨a, b, d, e, rfl, ha⟩ := hshape c (j + 1) hklvl
    obtain ⟨_, _, _, _, hlb, hld, hle⟩ := cellWf_of_wf _ hwf
    have hbl : b.level = j + 1 := by omega
    have hdl : d.level = j + 1 := by omega
    have hel : e.level = j + 1 := by omega
    obtain ⟨a1, a2, a3, a4, rfl⟩ := hnode a (by omega)
    obtain ⟨b1, b2, b3, b4, rfl⟩ := hnode b (by omega)
    obtain ⟨d1, d2, d3, d4, rfl⟩ := hnode d (by omega)
    obtain ⟨e1, e2, e3, e4, rfl⟩ := hnode e (by omega)
    simp only [MacroCell.level] at ha
    show hashlifeResultAtAux (j + 1 + 1) j _
      = hashlifeResultAux (j + 2) _
    simp only [hashlifeResultAtAux, MacroCell.level, ha, beq_iff_eq]
    split
    · rfl
    · exfalso; omega
  rw [hwrap]
  exact hashlifeResult_central_correct c j hwf hklvl

/-- Témoin P4-At k = 1 : même cellule que `p4_wf_witness_k1` (bloc encore
    de vie centré, niveau 3 = j+2 pour j = 1), lue au moteur décorrélaté —
    au niveau terminal il rend exactement le moteur plein. -/
theorem p4at_witness_k1 :
    (hashlifeResultAt 1
      (centerInLevelPlus2 (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf))).toGrid
        ((2 : Int), (2 : Int))
      = restrictGridTo
          (evolve 2
            ((centerInLevelPlus2
              (node aliveLeaf aliveLeaf aliveLeaf aliveLeaf)).toGrid (0, 0)))
          2 4 := by
  native_decide

/-- Témoin P4-At k = 2 : même cellule que `p4_wf_witness_k2` (glider centré
    de niveau 4 = j+2 pour j = 2, avance 4 générations). -/
theorem p4at_witness_k2 :
    (hashlifeResultAt 2 (centerInLevelPlus2 gliderCell)).toGrid
        ((4 : Int), (4 : Int))
      = restrictGridTo
          (evolve 4 ((centerInLevelPlus2 gliderCell).toGrid (0, 0)))
          4 8 := by
  native_decide

/-! ### P4-At pas mono-ronde : socle geometrique (grain 3b, #11161)

Le pas inductif `M > j + 2` du moteur At assemble la fenetre de sortie en
SOUS-QUADRANTS des `r_i = hashlifeResultAt j n_i` (recursion mono-ronde,
Hashlife.lean section « Saut a portee decouplee »). Ce bloc pose le socle
geometrique de l'assemblage, sans toucher a `evolve` :

* `mem_toGrid_extent` : la grille d'une cellule bien formee ne sort jamais
  de son etendue `[a, a + 2^level)²` — l'ingredient d'elimination des
  disjonctes impossibles de `mem_toGrid_node` ;
* `subSE/subSW/subNE/subNW_toGrid_mem` : lire un sous-quadrant d'un `r_i`
  dans le repere local de `r_i` — `p ∈ (subXX r).toGrid (a, b)` equivaut a
  un point translate dans `r.toGrid (0, 0)`, avec la contrainte de region
  (le quadrant ou `p` tombe dans la fenetre) ;
* `hashlifeResultAtAux_succ_node_at` : le moteur At au cran successeur se
  reduit (rfl) au noeud explicite de sous-quadrants — l'unlock du LHS du
  pas, miroir de `hashlifeResultAux_succ_node` pour le moteur plein ;
* `p4at_ext_bridge` : l'egalite de grille du pas se reduit a la
  biconditionnelle point par point.

Les briques de localite (`evolve_box_agree_local`, accord `n_i` vs `c`) et
les quatre bras d'assemblage consomment ce socle au grain 3b part 2. -/

private theorem pow_two_succ_le_int (n : Nat) : (2 ^ n : Int) ≤ (2 ^ (n + 1) : Int) := by
  have hN : 2 ^ n ≤ 2 ^ (n + 1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by positivity)
  exact_mod_cast hN

private theorem pow_two_succ_eq_int (n : Nat) : (2 ^ (n + 1) : Int) = 2 * (2 ^ n : Int) := by
  push_cast
  rw [pow_succ]
  ring

/-- **Borne d'etendue de `toGrid`.** L'appartenance a la grille d'une
    cellule bien formee placee en `(a, b)` implique que le point est dans
    la region couverte `[a, a + 2^level)²` : la grille n'emet jamais hors
    de l'etendue de la cellule. Par induction structurelle sur `c` — les
    feuilles emettent exactement leur coin, un `node` ecarte ses quatre
    enfants (de niveau egal, `wf`) sur ses quadrants. -/
theorem mem_toGrid_extent (c : MacroCell) (a b : Int) (p : Int × Int)
    (hwf : c.wf = true) (h : p ∈ c.toGrid (a, b)) :
    a ≤ p.1 ∧ p.1 < a + (2^c.level : Int) ∧ b ≤ p.2 ∧ p.2 < b + (2^c.level : Int) := by
  rw [mem_toGrid] at h
  induction c generalizing a b with
  | leaf lf =>
      cases lf with
      | false => simp [MacroCell.toCellsAux] at h
      | true =>
          simp only [MacroCell.toCellsAux, List.mem_singleton] at h
          subst p
          simp [MacroCell.level]
  | node nw ne sw se ihnw ihne ihsw ihse =>
      obtain ⟨_hnw_lvl, hne_lvl, hsw_lvl, hse_lvl, hw_nw, hw_ne, hw_sw, hw_se⟩ :=
        wf_node_quad_level (n := nw.level)
          (by show 1 + nw.level = nw.level + 1; omega) hwf
      have hor : p ∈ nw.toCellsAux a b ∨
          p ∈ ne.toCellsAux a (b + (2 ^ nw.level : Int)) ∨
          p ∈ sw.toCellsAux (a + (2 ^ nw.level : Int)) b ∨
          p ∈ se.toCellsAux (a + (2 ^ nw.level : Int)) (b + (2 ^ nw.level : Int)) := by
        simpa [MacroCell.toCellsAux, List.mem_append] using h
      simp only [MacroCell.level]
      rcases hor with h | h | h | h
      · have hb := ihnw a b hw_nw h
        rw [show 1 + nw.level = nw.level + 1 from by omega]
        omega
      · have hb := ihne a (b + (2 ^ nw.level : Int)) hw_ne h
        rw [show 1 + nw.level = nw.level + 1 from by omega]
        have hp1 : p.1 < a + (2 ^ (nw.level + 1) : Int) := by
          have hb2 := hb.2.1
          rw [hne_lvl] at hb2
          have hup := pow_two_succ_le_int nw.level
          omega
        have hp2 : p.2 < b + (2 ^ (nw.level + 1) : Int) := by
          have hb2 := hb.2.2.2
          rw [hne_lvl] at hb2
          rw [pow_two_succ_eq_int nw.level]
          omega
        omega
      · have hb := ihsw (a + (2 ^ nw.level : Int)) b hw_sw h
        rw [show 1 + nw.level = nw.level + 1 from by omega]
        have hp1 : p.1 < a + (2 ^ (nw.level + 1) : Int) := by
          have hb2 := hb.2.1
          rw [hsw_lvl] at hb2
          rw [pow_two_succ_eq_int nw.level]
          omega
        have hp2 : p.2 < b + (2 ^ (nw.level + 1) : Int) := by
          have hb2 := hb.2.2.2
          rw [hsw_lvl] at hb2
          have hup := pow_two_succ_le_int nw.level
          omega
        omega
      · have hb := ihse (a + (2 ^ nw.level : Int)) (b + (2 ^ nw.level : Int)) hw_se h
        rw [show 1 + nw.level = nw.level + 1 from by omega]
        have hp1 : p.1 < a + (2 ^ (nw.level + 1) : Int) := by
          have hb2 := hb.2.1
          rw [hse_lvl] at hb2
          rw [pow_two_succ_eq_int nw.level]
          omega
        have hp2 : p.2 < b + (2 ^ (nw.level + 1) : Int) := by
          have hb2 := hb.2.2.2
          rw [hse_lvl] at hb2
          rw [pow_two_succ_eq_int nw.level]
          omega
        omega

/-- **Appartenance au sous-quadrant SE.** `p` dans la grille du sous-quadrant
    SE de `r` place en `(a, b)` (region `[a, a+s') × [b, b+s')`,
    `s' = 2^(r.level-1)`) equivaut au point translate
    `(p.1 - a + s', p.2 - b + s')` dans la grille de `r` au repere local —
    la lecture de l'assemblage mono-ronde depuis le repere local de chaque
    `r_i`. L'elimination des trois disjonctes impossibles de
    `mem_toGrid_node` passe par `mem_toGrid_extent`. -/
theorem subSE_toGrid_mem (r : MacroCell) (a b : Int) (p : Int × Int)
    (hr : 1 ≤ r.level) (hwf : r.wf = true)
    (hbox : a ≤ p.1 ∧ p.1 < a + (2^(r.level - 1) : Int) ∧
            b ≤ p.2 ∧ p.2 < b + (2^(r.level - 1) : Int)) :
    p ∈ (subSE r).toGrid (a, b) ↔
      (p.1 - a + (2^(r.level - 1) : Int), p.2 - b + (2^(r.level - 1) : Int)) ∈ r.toGrid (0, 0) := by
  obtain ⟨r1, r2, r3, r4, hnode⟩ : ∃ r1 r2 r3 r4, r = node r1 r2 r3 r4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hr; omega
    | node r1 r2 r3 r4 => exact ⟨r1, r2, r3, r4, rfl⟩
  subst r
  have hnodelevel : (MacroCell.node r1 r2 r3 r4).level = r1.level + 1 := by
    show 1 + r1.level = r1.level + 1
    omega
  rw [hnodelevel] at hbox ⊢
  simp only [Nat.add_sub_cancel] at hbox ⊢
  obtain ⟨_hr1eq, hr2eq, hr3eq, hr4eq, hw1, hw2, hw3, hw4⟩ :=
    wf_node_quad_level (n := r1.level) hnodelevel hwf
  constructor
  · intro hmem
    have hmem' : (p.1 - a, p.2 - b) ∈ r4.toGrid (0, 0) := by
      exact (mem_toGrid_shift (c := r4) (r0 := a) (c0 := b) (p := p)).mp hmem
    have hq4 : (p.1 - a + (2 ^ r1.level : Int), p.2 - b + (2 ^ r1.level : Int)) ∈
        r4.toGrid ((2 ^ r1.level : Int), (2 ^ r1.level : Int)) := by
      refine (mem_toGrid_shift (c := r4) (r0 := (2 ^ r1.level : Int))
        (c0 := (2 ^ r1.level : Int))
        (p := (p.1 - a + (2 ^ r1.level : Int), p.2 - b + (2 ^ r1.level : Int)))).mpr ?_
      have hpp : ((p.1 - a + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int),
                  (p.2 - b + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int)) = (p.1 - a, p.2 - b) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hpp]
      exact hmem'
    rw [mem_toGrid_node]
    simp only [Int.zero_add, Int.add_zero]
    right; right; right
    exact hq4
  · intro hq
    rw [mem_toGrid_node] at hq
    simp only [Int.zero_add, Int.add_zero] at hq
    rcases hq with h1 | h2 | h3 | h4
    · have he1 := mem_toGrid_extent r1 0 0 (p.1 - a + (2 ^ r1.level : Int), p.2 - b + (2 ^ r1.level : Int)) hw1 h1
      have hle : (2 ^ r1.level : Int) ≤ p.1 - a + (2 ^ r1.level : Int) := by omega
      omega
    · have he2 := mem_toGrid_extent r2 0 (2 ^ r1.level : Int) (p.1 - a + (2 ^ r1.level : Int), p.2 - b + (2 ^ r1.level : Int)) hw2 h2
      have hle : (2 ^ r1.level : Int) ≤ p.1 - a + (2 ^ r1.level : Int) := by omega
      rw [hr2eq] at he2
      omega
    · have he3 := mem_toGrid_extent r3 (2 ^ r1.level : Int) 0 (p.1 - a + (2 ^ r1.level : Int), p.2 - b + (2 ^ r1.level : Int)) hw3 h3
      have hle : (2 ^ r1.level : Int) ≤ p.2 - b + (2 ^ r1.level : Int) := by omega
      rw [hr3eq] at he3
      omega
    · have h4s : (p.1 - a, p.2 - b) ∈ r4.toGrid (0, 0) := by
        have h4s' := (mem_toGrid_shift (c := r4) (r0 := (2 ^ r1.level : Int))
          (c0 := (2 ^ r1.level : Int))
          (p := (p.1 - a + (2 ^ r1.level : Int), p.2 - b + (2 ^ r1.level : Int)))).mp h4
        have hpp : ((p.1 - a + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int),
                    (p.2 - b + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int)) = (p.1 - a, p.2 - b) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hpp] at h4s'
        exact h4s'
      exact (mem_toGrid_shift (c := r4) (r0 := a) (c0 := b) (p := p)).mpr h4s

/-- **Appartenance au sous-quadrant SW.** Miroir de `subSE_toGrid_mem` pour
    le sous-quadrant SW de `r` (region `[a, a+s') × [b, b+s')`, le point
    translate est `(p.1 - a + s', p.2 - b)`). -/
theorem subSW_toGrid_mem (r : MacroCell) (a b : Int) (p : Int × Int)
    (hr : 1 ≤ r.level) (hwf : r.wf = true)
    (hbox : a ≤ p.1 ∧ p.1 < a + (2^(r.level - 1) : Int) ∧
            b ≤ p.2 ∧ p.2 < b + (2^(r.level - 1) : Int)) :
    p ∈ (subSW r).toGrid (a, b) ↔
      (p.1 - a + (2^(r.level - 1) : Int), p.2 - b) ∈ r.toGrid (0, 0) := by
  obtain ⟨r1, r2, r3, r4, hnode⟩ : ∃ r1 r2 r3 r4, r = node r1 r2 r3 r4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hr; omega
    | node r1 r2 r3 r4 => exact ⟨r1, r2, r3, r4, rfl⟩
  subst r
  have hnodelevel : (MacroCell.node r1 r2 r3 r4).level = r1.level + 1 := by
    show 1 + r1.level = r1.level + 1
    omega
  rw [hnodelevel] at hbox ⊢
  simp only [Nat.add_sub_cancel] at hbox ⊢
  obtain ⟨_hr1eq, hr2eq, hr3eq, hr4eq, hw1, hw2, hw3, hw4⟩ :=
    wf_node_quad_level (n := r1.level) hnodelevel hwf
  constructor
  · intro hmem
    have hmem' : (p.1 - a, p.2 - b) ∈ r3.toGrid (0, 0) := by
      exact (mem_toGrid_shift (c := r3) (r0 := a) (c0 := b) (p := p)).mp hmem
    have hq3 : (p.1 - a + (2 ^ r1.level : Int), p.2 - b) ∈
        r3.toGrid ((2 ^ r1.level : Int), 0) := by
      refine (mem_toGrid_shift (c := r3) (r0 := (2 ^ r1.level : Int)) (c0 := 0)
        (p := (p.1 - a + (2 ^ r1.level : Int), p.2 - b))).mpr ?_
      have hpp : ((p.1 - a + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int),
                  (p.2 - b) - 0) = (p.1 - a, p.2 - b) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hpp]
      exact hmem'
    rw [mem_toGrid_node]
    simp only [Int.zero_add, Int.add_zero]
    right; right; left
    exact hq3
  · intro hq
    rw [mem_toGrid_node] at hq
    simp only [Int.zero_add, Int.add_zero] at hq
    rcases hq with h1 | h2 | h3 | h4
    · have he1 := mem_toGrid_extent r1 0 0 (p.1 - a + (2 ^ r1.level : Int), p.2 - b) hw1 h1
      have hle : (2 ^ r1.level : Int) ≤ p.1 - a + (2 ^ r1.level : Int) := by omega
      omega
    · have he2 := mem_toGrid_extent r2 0 (2 ^ r1.level : Int) (p.1 - a + (2 ^ r1.level : Int), p.2 - b) hw2 h2
      have hle : (2 ^ r1.level : Int) ≤ p.1 - a + (2 ^ r1.level : Int) := by omega
      rw [hr2eq] at he2
      omega
    · have h3s : (p.1 - a, p.2 - b) ∈ r3.toGrid (0, 0) := by
        have h3s' := (mem_toGrid_shift (c := r3) (r0 := (2 ^ r1.level : Int)) (c0 := 0)
          (p := (p.1 - a + (2 ^ r1.level : Int), p.2 - b))).mp h3
        have hpp : ((p.1 - a + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int),
                    (p.2 - b) - 0) = (p.1 - a, p.2 - b) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hpp] at h3s'
        exact h3s'
      exact (mem_toGrid_shift (c := r3) (r0 := a) (c0 := b) (p := p)).mpr h3s
    · have he4 := mem_toGrid_extent r4 (2 ^ r1.level : Int) (2 ^ r1.level : Int) (p.1 - a + (2 ^ r1.level : Int), p.2 - b) hw4 h4
      have hlt : p.2 - b < (2 ^ r1.level : Int) := by omega
      omega

/-- **Appartenance au sous-quadrant NE.** Miroir de `subSE_toGrid_mem` pour
    le sous-quadrant NE de `r` (region `[a, a+s') × [b, b+s')`, le point
    translate est `(p.1 - a, p.2 - b + s')`). -/
theorem subNE_toGrid_mem (r : MacroCell) (a b : Int) (p : Int × Int)
    (hr : 1 ≤ r.level) (hwf : r.wf = true)
    (hbox : a ≤ p.1 ∧ p.1 < a + (2^(r.level - 1) : Int) ∧
            b ≤ p.2 ∧ p.2 < b + (2^(r.level - 1) : Int)) :
    p ∈ (subNE r).toGrid (a, b) ↔
      (p.1 - a, p.2 - b + (2^(r.level - 1) : Int)) ∈ r.toGrid (0, 0) := by
  obtain ⟨r1, r2, r3, r4, hnode⟩ : ∃ r1 r2 r3 r4, r = node r1 r2 r3 r4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hr; omega
    | node r1 r2 r3 r4 => exact ⟨r1, r2, r3, r4, rfl⟩
  subst r
  have hnodelevel : (MacroCell.node r1 r2 r3 r4).level = r1.level + 1 := by
    show 1 + r1.level = r1.level + 1
    omega
  rw [hnodelevel] at hbox ⊢
  simp only [Nat.add_sub_cancel] at hbox ⊢
  obtain ⟨_hr1eq, hr2eq, hr3eq, hr4eq, hw1, hw2, hw3, hw4⟩ :=
    wf_node_quad_level (n := r1.level) hnodelevel hwf
  constructor
  · intro hmem
    have hmem' : (p.1 - a, p.2 - b) ∈ r2.toGrid (0, 0) := by
      exact (mem_toGrid_shift (c := r2) (r0 := a) (c0 := b) (p := p)).mp hmem
    have hq2 : (p.1 - a, p.2 - b + (2 ^ r1.level : Int)) ∈
        r2.toGrid (0, (2 ^ r1.level : Int)) := by
      refine (mem_toGrid_shift (c := r2) (r0 := 0) (c0 := (2 ^ r1.level : Int))
        (p := (p.1 - a, p.2 - b + (2 ^ r1.level : Int)))).mpr ?_
      have hpp : ((p.1 - a) - 0,
                  (p.2 - b + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int)) = (p.1 - a, p.2 - b) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hpp]
      exact hmem'
    rw [mem_toGrid_node]
    simp only [Int.zero_add, Int.add_zero]
    right; left
    exact hq2
  · intro hq
    rw [mem_toGrid_node] at hq
    simp only [Int.zero_add, Int.add_zero] at hq
    rcases hq with h1 | h2 | h3 | h4
    · have he1 := mem_toGrid_extent r1 0 0 (p.1 - a, p.2 - b + (2 ^ r1.level : Int)) hw1 h1
      have hle : (2 ^ r1.level : Int) ≤ p.2 - b + (2 ^ r1.level : Int) := by omega
      omega
    · have h2s : (p.1 - a, p.2 - b) ∈ r2.toGrid (0, 0) := by
        have h2s' := (mem_toGrid_shift (c := r2) (r0 := 0) (c0 := (2 ^ r1.level : Int))
          (p := (p.1 - a, p.2 - b + (2 ^ r1.level : Int)))).mp h2
        have hpp : ((p.1 - a) - 0,
                    (p.2 - b + (2 ^ r1.level : Int)) - (2 ^ r1.level : Int)) = (p.1 - a, p.2 - b) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hpp] at h2s'
        exact h2s'
      exact (mem_toGrid_shift (c := r2) (r0 := a) (c0 := b) (p := p)).mpr h2s
    · have he3 := mem_toGrid_extent r3 (2 ^ r1.level : Int) 0 (p.1 - a, p.2 - b + (2 ^ r1.level : Int)) hw3 h3
      have hle : (2 ^ r1.level : Int) ≤ p.2 - b + (2 ^ r1.level : Int) := by omega
      omega
    · have he4 := mem_toGrid_extent r4 (2 ^ r1.level : Int) (2 ^ r1.level : Int) (p.1 - a, p.2 - b + (2 ^ r1.level : Int)) hw4 h4
      have hlt : p.1 - a < (2 ^ r1.level : Int) := by omega
      omega

/-- **Appartenance au sous-quadrant NW.** Miroir de `subSE_toGrid_mem` pour
    le sous-quadrant NW de `r` (region `[a, a+s') × [b, b+s')`, le point
    translate est `(p.1 - a, p.2 - b)`). -/
theorem subNW_toGrid_mem (r : MacroCell) (a b : Int) (p : Int × Int)
    (hr : 1 ≤ r.level) (hwf : r.wf = true)
    (hbox : a ≤ p.1 ∧ p.1 < a + (2^(r.level - 1) : Int) ∧
            b ≤ p.2 ∧ p.2 < b + (2^(r.level - 1) : Int)) :
    p ∈ (subNW r).toGrid (a, b) ↔
      (p.1 - a, p.2 - b) ∈ r.toGrid (0, 0) := by
  obtain ⟨r1, r2, r3, r4, hnode⟩ : ∃ r1 r2 r3 r4, r = node r1 r2 r3 r4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hr; omega
    | node r1 r2 r3 r4 => exact ⟨r1, r2, r3, r4, rfl⟩
  subst r
  have hnodelevel : (MacroCell.node r1 r2 r3 r4).level = r1.level + 1 := by
    show 1 + r1.level = r1.level + 1
    omega
  rw [hnodelevel] at hbox
  simp only [Nat.add_sub_cancel] at hbox
  obtain ⟨_hr1eq, hr2eq, hr3eq, hr4eq, hw1, hw2, hw3, hw4⟩ :=
    wf_node_quad_level (n := r1.level) hnodelevel hwf
  constructor
  · intro hmem
    have hmem' : (p.1 - a, p.2 - b) ∈ r1.toGrid (0, 0) := by
      exact (mem_toGrid_shift (c := r1) (r0 := a) (c0 := b) (p := p)).mp hmem
    rw [mem_toGrid_node]
    left
    exact hmem'
  · intro hq
    rw [mem_toGrid_node] at hq
    simp only [Int.zero_add, Int.add_zero] at hq
    rcases hq with h1 | h2 | h3 | h4
    · have h1s : (p.1 - a, p.2 - b) ∈ r1.toGrid (0, 0) := h1
      exact (mem_toGrid_shift (c := r1) (r0 := a) (c0 := b) (p := p)).mpr h1s
    · have he2 := mem_toGrid_extent r2 0 (2 ^ r1.level : Int) (p.1 - a, p.2 - b) hw2 h2
      have hlt : p.2 - b < (2 ^ r1.level : Int) := by omega
      omega
    · have he3 := mem_toGrid_extent r3 (2 ^ r1.level : Int) 0 (p.1 - a, p.2 - b) hw3 h3
      have hlt : p.1 - a < (2 ^ r1.level : Int) := by omega
      omega
    · have he4 := mem_toGrid_extent r4 (2 ^ r1.level : Int) (2 ^ r1.level : Int) (p.1 - a, p.2 - b) hw4 h4
      have hlt : p.1 - a < (2 ^ r1.level : Int) := by omega
      omega

/-! ### P4-At pas mono-ronde : unlock du LHS et pont d'extensionnalite (grain 3b)

L'egalite de grille du pas se prouve point par point (`p4at_ext_bridge`),
et le LHS `hashlifeResultAt j c` se reduit, au cran successeur, au noeud
explicite de sous-quadrants (`hashlifeResultAtAux_succ_node_at`, rfl) —
le miroir de `hashlifeResultAux_succ_node` (Foundation) pour le moteur At.
L'assemblage mono-ronde consomme ensuite `mem_toGrid_node` deux fois (les
quadrants de la fenetre, puis leurs sous-quadrants) et les lemmes
sous-quadrants ci-dessus pour lire chaque sous-quadrant dans le repere
local du `r_i` correspondant. -/

/-- **Unfold du moteur At au cran successeur.** Le LHS du pas est
    `p ∈ (hashlifeResultAt j c).toGrid ...` avec `c.level = M > j + 2` ; ce
    lemme (vrai par rfl — iota + zeta, comme son miroir P4) reduit
    `hashlifeResultAtAux (fuel + 1) j c` au noeud explicite dont les quatre
    enfants sont eux-memes des noeuds de sous-quadrants des `r_i`, rendant
    le LHS accessible a `mem_toGrid_node`. -/
theorem hashlifeResultAtAux_succ_node_at (fuel j : Nat)
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell) :
    hashlifeResultAtAux (fuel + 1) j
      (MacroCell.node (MacroCell.node a1 a2 a3 a4) (MacroCell.node b1 b2 b3 b4)
            (MacroCell.node c1 c2 c3 c4) (MacroCell.node d1 d2 d3 d4)) =
    if (MacroCell.node (MacroCell.node a1 a2 a3 a4) (MacroCell.node b1 b2 b3 b4)
             (MacroCell.node c1 c2 c3 c4) (MacroCell.node d1 d2 d3 d4)).level == j + 2 then
      hashlifeResultAux (fuel + 1)
        (MacroCell.node (MacroCell.node a1 a2 a3 a4) (MacroCell.node b1 b2 b3 b4)
             (MacroCell.node c1 c2 c3 c4) (MacroCell.node d1 d2 d3 d4))
    else
      node
        (node (subSE (hashlifeResultAtAux fuel j (MacroCell.node a1 a2 a3 a4)))
              (subSW (hashlifeResultAtAux fuel j (MacroCell.node a2 b1 a4 b3)))
              (subNE (hashlifeResultAtAux fuel j (MacroCell.node a3 a4 c1 c2)))
              (subNW (hashlifeResultAtAux fuel j (MacroCell.node a4 b3 c2 d1))))
        (node (subSE (hashlifeResultAtAux fuel j (MacroCell.node a2 b1 a4 b3)))
              (subSW (hashlifeResultAtAux fuel j (MacroCell.node b1 b2 b3 b4)))
              (subNE (hashlifeResultAtAux fuel j (MacroCell.node a4 b3 c2 d1)))
              (subNW (hashlifeResultAtAux fuel j (MacroCell.node b3 b4 d1 d2))))
        (node (subSE (hashlifeResultAtAux fuel j (MacroCell.node a3 a4 c1 c2)))
              (subSW (hashlifeResultAtAux fuel j (MacroCell.node a4 b3 c2 d1)))
              (subNE (hashlifeResultAtAux fuel j (MacroCell.node c1 c2 c3 c4)))
              (subNW (hashlifeResultAtAux fuel j (MacroCell.node c2 d1 c4 d3))))
        (node (subSE (hashlifeResultAtAux fuel j (MacroCell.node a4 b3 c2 d1)))
              (subSW (hashlifeResultAtAux fuel j (MacroCell.node b3 b4 d1 d2)))
              (subNE (hashlifeResultAtAux fuel j (MacroCell.node c2 d1 c4 d3)))
              (subNW (hashlifeResultAtAux fuel j (MacroCell.node d1 d2 d3 d4)))) := by
  rfl

/-- **Pont d'extensionnalite P4-At.** L'egalite de grille de
    `hashlifeResultAt_central_correct` (et de son pas) se reduit a la
    biconditionnelle point par point — miroir de `p4_ext_bridge` (Foundation)
    pour le moteur decorrele. -/
theorem p4at_ext_bridge (c : MacroCell) (j M : Nat)
    (h : ∀ p, p ∈ (hashlifeResultAt j c).toGrid ((2^(M-2) : Nat), (2^(M-2) : Nat)) ↔
        p ∈ restrictGridTo (evolve (2^j) (c.toGrid (0, 0))) (2^(M-2) : Int) (2^(M-1))) :
    (hashlifeResultAt j c).toGrid ((2^(M-2) : Nat), (2^(M-2) : Nat))
      = restrictGridTo (evolve (2^j) (c.toGrid (0, 0))) (2^(M-2) : Int) (2^(M-1)) := by
  apply Canonical.ext (canonical_toGrid _ _) _ h
  unfold restrictGridTo
  exact (canonical_evolve_of_pos (Nat.two_pow_pos j) _).filter _

/-! ### P4-At : invariant niveau/wf du moteur At (grain 3b, partie 3)

Miroir de `hashlifeResultAux_level_cellWf` (Foundation, c.142) pour le
moteur decorrele. Comptage du fuel verifie sur la definition
(Hashlife.lean, `hashlifeResultAtAux`) : le wrapper pose fuel = niveau,
et la recursion mono-ronde descend le niveau ET le fuel de 1 chacune
(les neuf `n_i` sont des noeuds de quatre petits-enfants, donc de
niveau `M - 1`) — l'invariant fuel = niveau est preserve, et le cas
terminal delegue au moteur plein avec exactement le fuel de la brique
Foundation. -/

/-- Preservation niveau + `cellWf` de l'accesseur `subNW` sur une
    cellule de niveau `m + 1` bien formee : le quadrant nord-ouest est de
    niveau `m` et bien forme. Les conclusions portent le predicat
    OPAQUE `cellWf` (pont `cellWf_of_wf`) : dans les bras d'assemblage
    du moteur At, les `r_i` sont des termes bloques — la version
    transparente `.wf` y divergerait en whnf (c.140). -/
theorem subNW_level_cellWf {m : Nat} {r : MacroCell}
    (hwf : cellWf r) (hlevel : r.level = m + 1) :
    (subNW r).level = m ∧ cellWf (subNW r) := by
  have hw := wf_of_cellWf hwf
  obtain ⟨q1, q2, q3, q4, rfl⟩ :
      ∃ q1 q2 q3 q4, r = MacroCell.node q1 q2 q3 q4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hlevel; omega
    | node q1 q2 q3 q4 => exact ⟨q1, q2, q3, q4, rfl⟩
  obtain ⟨h1, _, _, _, h1w, _, _, _⟩ := wf_node_quad_level (n := m) hlevel hw
  exact ⟨h1, cellWf_of_wf _ h1w⟩

/-- Preservation niveau + `cellWf` de l'accesseur `subNE` sur une
    cellule de niveau `m + 1` bien formee : le quadrant nord-est est de
    niveau `m` et bien forme. Les conclusions portent le predicat
    OPAQUE `cellWf` (pont `cellWf_of_wf`) : dans les bras d'assemblage
    du moteur At, les `r_i` sont des termes bloques — la version
    transparente `.wf` y divergerait en whnf (c.140). -/
theorem subNE_level_cellWf {m : Nat} {r : MacroCell}
    (hwf : cellWf r) (hlevel : r.level = m + 1) :
    (subNE r).level = m ∧ cellWf (subNE r) := by
  have hw := wf_of_cellWf hwf
  obtain ⟨q1, q2, q3, q4, rfl⟩ :
      ∃ q1 q2 q3 q4, r = MacroCell.node q1 q2 q3 q4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hlevel; omega
    | node q1 q2 q3 q4 => exact ⟨q1, q2, q3, q4, rfl⟩
  obtain ⟨_, h2, _, _, _, h2w, _, _⟩ := wf_node_quad_level (n := m) hlevel hw
  exact ⟨h2, cellWf_of_wf _ h2w⟩

/-- Preservation niveau + `cellWf` de l'accesseur `subSW` sur une
    cellule de niveau `m + 1` bien formee : le quadrant sud-ouest est de
    niveau `m` et bien forme. Les conclusions portent le predicat
    OPAQUE `cellWf` (pont `cellWf_of_wf`) : dans les bras d'assemblage
    du moteur At, les `r_i` sont des termes bloques — la version
    transparente `.wf` y divergerait en whnf (c.140). -/
theorem subSW_level_cellWf {m : Nat} {r : MacroCell}
    (hwf : cellWf r) (hlevel : r.level = m + 1) :
    (subSW r).level = m ∧ cellWf (subSW r) := by
  have hw := wf_of_cellWf hwf
  obtain ⟨q1, q2, q3, q4, rfl⟩ :
      ∃ q1 q2 q3 q4, r = MacroCell.node q1 q2 q3 q4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hlevel; omega
    | node q1 q2 q3 q4 => exact ⟨q1, q2, q3, q4, rfl⟩
  obtain ⟨_, _, h3, _, _, _, h3w, _⟩ := wf_node_quad_level (n := m) hlevel hw
  exact ⟨h3, cellWf_of_wf _ h3w⟩

/-- Preservation niveau + `cellWf` de l'accesseur `subSE` sur une
    cellule de niveau `m + 1` bien formee : le quadrant sud-est est de
    niveau `m` et bien forme. Les conclusions portent le predicat
    OPAQUE `cellWf` (pont `cellWf_of_wf`) : dans les bras d'assemblage
    du moteur At, les `r_i` sont des termes bloques — la version
    transparente `.wf` y divergerait en whnf (c.140). -/
theorem subSE_level_cellWf {m : Nat} {r : MacroCell}
    (hwf : cellWf r) (hlevel : r.level = m + 1) :
    (subSE r).level = m ∧ cellWf (subSE r) := by
  have hw := wf_of_cellWf hwf
  obtain ⟨q1, q2, q3, q4, rfl⟩ :
      ∃ q1 q2 q3 q4, r = MacroCell.node q1 q2 q3 q4 := by
    cases r with
    | leaf _ => simp only [MacroCell.level] at hlevel; omega
    | node q1 q2 q3 q4 => exact ⟨q1, q2, q3, q4, rfl⟩
  obtain ⟨_, _, _, h4, _, _, _, h4w⟩ := wf_node_quad_level (n := m) hlevel hw
  exact ⟨h4, cellWf_of_wf _ h4w⟩

/-- Conjunct-closer pour un noeud de quatre cellules de meme niveau `m`
    bien formees : niveau `m + 1` et `cellWf`. Version publique et
    parametree en niveau ABSOLU du helper prive
    `node_level_cellWf_conjuncts` (Foundation, c.142, en `n - 2`), pour
    l'assemblage mono-ronde du moteur At : les sous-quadrants `subX r_i`
    sont de niveau `F - 2` et les quadrants de la fenetre de niveau
    `F - 1`. -/
theorem node4_level_cellWf {a b c d : MacroCell} {m : Nat}
    (ha : a.level = m) (hb : b.level = m) (hc : c.level = m) (hd : d.level = m)
    (hwa : cellWf a) (hwb : cellWf b) (hwc : cellWf c) (hwd : cellWf d) :
    (MacroCell.node a b c d).level = m + 1 ∧ cellWf (MacroCell.node a b c d) := by
  refine ⟨?_, ?_⟩
  · show 1 + a.level = m + 1
    omega
  · exact cellWf.node hwa hwb hwc hwd (by omega) (by omega) (by omega)

set_option maxHeartbeats 4000000 in
/-- **Pas mono-ronde de l'invariant du moteur At** (grain 3b,
    partie 3). Corps lourd de `hashlifeResultAtAux_level_cellWf`
    isole dans sa propre commande (budget heartbeats frais,
    miroir du helper prive `hashlifeResultAux_level_cellWf_step`,
    Foundation c.142).

    **Discipline omega** (mesuree sur la divergence v1-v3, probes
    scratch) : chaque `omega` POST-obtain re-scanne les 32 faits de
    petits-enfants — le preprocessing grind normalise chaque
    hypothese lineaire (~100k heartbeats par appel). Toute
    l'arithmetique est donc pre-prouvee AVANT l'obtain en lemmes
    parametriques (`key*`, contexte minimal), et le corps
    post-obtain n'utilise que des APPLICATIONS DE TERMES
    (`Eq.trans`/`symm`, `keyL`, `keyS`, `keyT`). L'unfold passe par
    l'equation rfl `hashlifeResultAtAux_succ_node_at` + `hlev` +
    `if_neg` — jamais de `simp` sur le terme 16-petits-enfants
    (divergence c.138-c.140). -/
private theorem hashlifeResultAtAux_level_cellWf_mono (fuel j : Nat)
    (hle : j + 2 ≤ fuel)
    (nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se : MacroCell)
    (hgrands : nw_nw.level = fuel - 1 ∧ nw_nw.wf = true ∧ nw_ne.level = fuel - 1 ∧ nw_ne.wf = true ∧ nw_sw.level = fuel - 1 ∧ nw_sw.wf = true ∧ nw_se.level = fuel - 1 ∧ nw_se.wf = true ∧ ne_nw.level = fuel - 1 ∧ ne_nw.wf = true ∧ ne_ne.level = fuel - 1 ∧ ne_ne.wf = true ∧ ne_sw.level = fuel - 1 ∧ ne_sw.wf = true ∧ ne_se.level = fuel - 1 ∧ ne_se.wf = true ∧ sw_nw.level = fuel - 1 ∧ sw_nw.wf = true ∧ sw_ne.level = fuel - 1 ∧ sw_ne.wf = true ∧ sw_sw.level = fuel - 1 ∧ sw_sw.wf = true ∧ sw_se.level = fuel - 1 ∧ sw_se.wf = true ∧ se_nw.level = fuel - 1 ∧ se_nw.wf = true ∧ se_ne.level = fuel - 1 ∧ se_ne.wf = true ∧ se_sw.level = fuel - 1 ∧ se_sw.wf = true ∧ se_se.level = fuel - 1 ∧ se_se.wf = true)
    (hne : ¬ (fuel + 1 = j + 2))
    (ih : ∀ (j : Nat) (c' : MacroCell), cellWf c' → c'.level = fuel → j + 2 ≤ fuel →
      ((hashlifeResultAtAux fuel j c').level = fuel - 1 ∧ cellWf (hashlifeResultAtAux fuel j c'))) :
    ((hashlifeResultAtAux (fuel + 1) j (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se))).level = fuel + 1 - 1 ∧
     cellWf (hashlifeResultAtAux (fuel + 1) j (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)))) := by
  -- Arithmetique pre-prouvee : chaque omega ci-dessous travaille sur
  -- un contexte MINIMAL (hgrands est UNE hypothese, pas 32).
  have hfuel : 1 ≤ fuel := by omega
  have hf2 : 2 ≤ fuel := by omega
  have keyL : ∀ x : Nat, x = fuel - 1 → 1 + x = fuel := by
    intro x hx; omega
  have keyLev2 : ∀ x : Nat, x = fuel - 1 → 1 + (1 + x) = fuel + 1 := by
    intro x hx; omega
  have keyS : ∀ x : Nat, x = fuel - 1 → x = (fuel - 2) + 1 := by
    intro x hx; omega
  have keyT : ∀ x : Nat, x = (fuel - 2) + 1 → x = fuel - 1 := by
    intro x hx; omega
  have keyFin : (fuel - 1) + 1 = fuel + 1 - 1 := by omega
  obtain ⟨hnw_nw_l, hnw_nw_w, hnw_ne_l, hnw_ne_w, hnw_sw_l, hnw_sw_w, hnw_se_l, hnw_se_w, hne_nw_l, hne_nw_w, hne_ne_l, hne_ne_w, hne_sw_l, hne_sw_w, hne_se_l, hne_se_w, hsw_nw_l, hsw_nw_w, hsw_ne_l, hsw_ne_w, hsw_sw_l, hsw_sw_w, hsw_se_l, hsw_se_w, hse_nw_l, hse_nw_w, hse_ne_l, hse_ne_w, hse_sw_l, hse_sw_w, hse_se_l, hse_se_w⟩ := hgrands
  have hlev : (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)).level = fuel + 1 := by
    show 1 + (1 + nw_nw.level) = fuel + 1
    exact keyLev2 _ hnw_nw_l
  have hn1l : (node nw_nw nw_ne nw_sw nw_se).level = fuel := by
    show 1 + nw_nw.level = fuel
    exact keyL _ hnw_nw_l
  have hn1w : cellWf (node nw_nw nw_ne nw_sw nw_se) :=
    cellWf.node (cellWf_of_wf _ hnw_nw_w) (cellWf_of_wf _ hnw_ne_w)
      (cellWf_of_wf _ hnw_sw_w) (cellWf_of_wf _ hnw_se_w)
      (hnw_nw_l.trans hnw_ne_l.symm) (hnw_nw_l.trans hnw_sw_l.symm) (hnw_nw_l.trans hnw_se_l.symm)
  have hn2l : (node nw_ne ne_nw nw_se ne_sw).level = fuel := by
    show 1 + nw_ne.level = fuel
    exact keyL _ hnw_ne_l
  have hn2w : cellWf (node nw_ne ne_nw nw_se ne_sw) :=
    cellWf.node (cellWf_of_wf _ hnw_ne_w) (cellWf_of_wf _ hne_nw_w)
      (cellWf_of_wf _ hnw_se_w) (cellWf_of_wf _ hne_sw_w)
      (hnw_ne_l.trans hne_nw_l.symm) (hnw_ne_l.trans hnw_se_l.symm) (hnw_ne_l.trans hne_sw_l.symm)
  have hn3l : (node ne_nw ne_ne ne_sw ne_se).level = fuel := by
    show 1 + ne_nw.level = fuel
    exact keyL _ hne_nw_l
  have hn3w : cellWf (node ne_nw ne_ne ne_sw ne_se) :=
    cellWf.node (cellWf_of_wf _ hne_nw_w) (cellWf_of_wf _ hne_ne_w)
      (cellWf_of_wf _ hne_sw_w) (cellWf_of_wf _ hne_se_w)
      (hne_nw_l.trans hne_ne_l.symm) (hne_nw_l.trans hne_sw_l.symm) (hne_nw_l.trans hne_se_l.symm)
  have hn4l : (node nw_sw nw_se sw_nw sw_ne).level = fuel := by
    show 1 + nw_sw.level = fuel
    exact keyL _ hnw_sw_l
  have hn4w : cellWf (node nw_sw nw_se sw_nw sw_ne) :=
    cellWf.node (cellWf_of_wf _ hnw_sw_w) (cellWf_of_wf _ hnw_se_w)
      (cellWf_of_wf _ hsw_nw_w) (cellWf_of_wf _ hsw_ne_w)
      (hnw_sw_l.trans hnw_se_l.symm) (hnw_sw_l.trans hsw_nw_l.symm) (hnw_sw_l.trans hsw_ne_l.symm)
  have hn5l : (node nw_se ne_sw sw_ne se_nw).level = fuel := by
    show 1 + nw_se.level = fuel
    exact keyL _ hnw_se_l
  have hn5w : cellWf (node nw_se ne_sw sw_ne se_nw) :=
    cellWf.node (cellWf_of_wf _ hnw_se_w) (cellWf_of_wf _ hne_sw_w)
      (cellWf_of_wf _ hsw_ne_w) (cellWf_of_wf _ hse_nw_w)
      (hnw_se_l.trans hne_sw_l.symm) (hnw_se_l.trans hsw_ne_l.symm) (hnw_se_l.trans hse_nw_l.symm)
  have hn6l : (node ne_sw ne_se se_nw se_ne).level = fuel := by
    show 1 + ne_sw.level = fuel
    exact keyL _ hne_sw_l
  have hn6w : cellWf (node ne_sw ne_se se_nw se_ne) :=
    cellWf.node (cellWf_of_wf _ hne_sw_w) (cellWf_of_wf _ hne_se_w)
      (cellWf_of_wf _ hse_nw_w) (cellWf_of_wf _ hse_ne_w)
      (hne_sw_l.trans hne_se_l.symm) (hne_sw_l.trans hse_nw_l.symm) (hne_sw_l.trans hse_ne_l.symm)
  have hn7l : (node sw_nw sw_ne sw_sw sw_se).level = fuel := by
    show 1 + sw_nw.level = fuel
    exact keyL _ hsw_nw_l
  have hn7w : cellWf (node sw_nw sw_ne sw_sw sw_se) :=
    cellWf.node (cellWf_of_wf _ hsw_nw_w) (cellWf_of_wf _ hsw_ne_w)
      (cellWf_of_wf _ hsw_sw_w) (cellWf_of_wf _ hsw_se_w)
      (hsw_nw_l.trans hsw_ne_l.symm) (hsw_nw_l.trans hsw_sw_l.symm) (hsw_nw_l.trans hsw_se_l.symm)
  have hn8l : (node sw_ne se_nw sw_se se_sw).level = fuel := by
    show 1 + sw_ne.level = fuel
    exact keyL _ hsw_ne_l
  have hn8w : cellWf (node sw_ne se_nw sw_se se_sw) :=
    cellWf.node (cellWf_of_wf _ hsw_ne_w) (cellWf_of_wf _ hse_nw_w)
      (cellWf_of_wf _ hsw_se_w) (cellWf_of_wf _ hse_sw_w)
      (hsw_ne_l.trans hse_nw_l.symm) (hsw_ne_l.trans hsw_se_l.symm) (hsw_ne_l.trans hse_sw_l.symm)
  have hn9l : (node se_nw se_ne se_sw se_se).level = fuel := by
    show 1 + se_nw.level = fuel
    exact keyL _ hse_nw_l
  have hn9w : cellWf (node se_nw se_ne se_sw se_se) :=
    cellWf.node (cellWf_of_wf _ hse_nw_w) (cellWf_of_wf _ hse_ne_w)
      (cellWf_of_wf _ hse_sw_w) (cellWf_of_wf _ hse_se_w)
      (hse_nw_l.trans hse_ne_l.symm) (hse_nw_l.trans hse_sw_l.symm) (hse_nw_l.trans hse_se_l.symm)
  obtain ⟨hr1l, hr1w⟩ := ih j (node nw_nw nw_ne nw_sw nw_se) hn1w hn1l hle
  obtain ⟨hr2l, hr2w⟩ := ih j (node nw_ne ne_nw nw_se ne_sw) hn2w hn2l hle
  obtain ⟨hr3l, hr3w⟩ := ih j (node ne_nw ne_ne ne_sw ne_se) hn3w hn3l hle
  obtain ⟨hr4l, hr4w⟩ := ih j (node nw_sw nw_se sw_nw sw_ne) hn4w hn4l hle
  obtain ⟨hr5l, hr5w⟩ := ih j (node nw_se ne_sw sw_ne se_nw) hn5w hn5l hle
  obtain ⟨hr6l, hr6w⟩ := ih j (node ne_sw ne_se se_nw se_ne) hn6w hn6l hle
  obtain ⟨hr7l, hr7w⟩ := ih j (node sw_nw sw_ne sw_sw sw_se) hn7w hn7l hle
  obtain ⟨hr8l, hr8w⟩ := ih j (node sw_ne se_nw sw_se se_sw) hn8w hn8l hle
  obtain ⟨hr9l, hr9w⟩ := ih j (node se_nw se_ne se_sw se_se) hn9w hn9l hle
  have hSE1 := subSE_level_cellWf (m := fuel - 2) hr1w (keyS _ hr1l)
  have hSW2 := subSW_level_cellWf (m := fuel - 2) hr2w (keyS _ hr2l)
  have hNE4 := subNE_level_cellWf (m := fuel - 2) hr4w (keyS _ hr4l)
  have hNW5 := subNW_level_cellWf (m := fuel - 2) hr5w (keyS _ hr5l)
  have hSE2 := subSE_level_cellWf (m := fuel - 2) hr2w (keyS _ hr2l)
  have hSW3 := subSW_level_cellWf (m := fuel - 2) hr3w (keyS _ hr3l)
  have hNE5 := subNE_level_cellWf (m := fuel - 2) hr5w (keyS _ hr5l)
  have hNW6 := subNW_level_cellWf (m := fuel - 2) hr6w (keyS _ hr6l)
  have hSE4 := subSE_level_cellWf (m := fuel - 2) hr4w (keyS _ hr4l)
  have hSW5 := subSW_level_cellWf (m := fuel - 2) hr5w (keyS _ hr5l)
  have hNE7 := subNE_level_cellWf (m := fuel - 2) hr7w (keyS _ hr7l)
  have hNW8 := subNW_level_cellWf (m := fuel - 2) hr8w (keyS _ hr8l)
  have hSE5 := subSE_level_cellWf (m := fuel - 2) hr5w (keyS _ hr5l)
  have hSW6 := subSW_level_cellWf (m := fuel - 2) hr6w (keyS _ hr6l)
  have hNE8 := subNE_level_cellWf (m := fuel - 2) hr8w (keyS _ hr8l)
  have hNW9 := subNW_level_cellWf (m := fuel - 2) hr9w (keyS _ hr9l)
  obtain ⟨hI1l, hI1w⟩ := node4_level_cellWf hSE1.1 hSW2.1 hNE4.1 hNW5.1 hSE1.2 hSW2.2 hNE4.2 hNW5.2
  obtain ⟨hI2l, hI2w⟩ := node4_level_cellWf hSE2.1 hSW3.1 hNE5.1 hNW6.1 hSE2.2 hSW3.2 hNE5.2 hNW6.2
  obtain ⟨hI3l, hI3w⟩ := node4_level_cellWf hSE4.1 hSW5.1 hNE7.1 hNW8.1 hSE4.2 hSW5.2 hNE7.2 hNW8.2
  obtain ⟨hI4l, hI4w⟩ := node4_level_cellWf hSE5.1 hSW6.1 hNE8.1 hNW9.1 hSE5.2 hSW6.2 hNE8.2 hNW9.2
  obtain ⟨hOl, hOw⟩ := node4_level_cellWf (m := fuel - 1)
    (hwa := hI1w) (hwb := hI2w) (hwc := hI3w) (hwd := hI4w)
    (ha := keyT _ hI1l) (hb := keyT _ hI2l) (hc := keyT _ hI3l) (hd := keyT _ hI4l)
  -- Unfold en FIN de preuve (le but reste le terme NEUTRE pendant
  -- l'etablissement des faits) puis arithmetique terminale en
  -- termes (keyFin), sans omega.
  rw [hashlifeResultAtAux_succ_node_at, hlev]
  rw [if_neg (by simp only [beq_iff_eq]; exact hne)]
  refine ⟨?_, hOw⟩
  rw [hOl]
  exact keyFin

set_option maxHeartbeats 4000000 in
/-- **Invariant niveau/wf du moteur At (grain 3b, partie 3).** Miroir de
    `hashlifeResultAux_level_cellWf` (Foundation, c.142) pour le moteur
    decorrele : pour une cellule bien formee de niveau `F >= j + 2`,
    sous l'invariant du wrapper `hashlifeResultAt` — le fuel EGAL le
    niveau, preserve par la recursion mono-ronde (chaque ronde descend
    le niveau ET le fuel de 1, les neuf `n_i` etant des noeuds de quatre
    petits-enfants, donc de niveau `M - 1`) — le resultat est de niveau
    `F - 1` et bien forme.

    Architecture (celle de la brique Foundation) : le corps lourd du pas
    mono-ronde vit dans le helper prive `hashlifeResultAtAux_level_cellWf_mono`
    (budget heartbeats propre) ; la commande publique ne fait qu'aiguiller.
    Le cas terminal appelle la brique de preservation Foundation sur la
    cellule OPAQUE AVANT tout destructure (isolation whnf c.139 : appeler
    la brique sur le 16-petits-enfants epelle fait diverger le whnf de la
    conclusion, cf `wave1_result_facts`), puis destructure uniquement pour
    declencher l'unfold `hashlifeResultAtAux` (la definition matche la
    structure de la cellule) et conclut par `exact` syntaxique. -/
theorem hashlifeResultAtAux_level_cellWf :
    ∀ (F : Nat) (j : Nat) (c : MacroCell), cellWf c → c.level = F → j + 2 ≤ F →
      ((hashlifeResultAtAux F j c).level = F - 1 ∧ cellWf (hashlifeResultAtAux F j c)) := by

  intro F
  induction F with
  | zero => intro j c _hwf _hc hj2; exact absurd hj2 (by omega)
  | succ fuel ih =>
    intro j c hwf hc hj2
    by_cases heq : c.level == j + 2
    · -- terminal : fuel + 1 = j + 2, delegation au moteur plein.
      -- Brique Foundation sur la cellule OPAQUE d'abord (isolation
      -- whnf c.139), destructure ensuite pour l'unfold seul.
      rw [hc] at heq
      simp only [beq_iff_eq] at heq
      have hres := hashlifeResultAux_level_cellWf (fuel + 1) c hwf hc (by omega)
      have hk : c.level = (fuel - 1) + 2 := by omega
      obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se, sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
        p4_double_nine_shape c (fuel - 1) (wf_of_cellWf hwf) hk
      obtain ⟨hnw_nw_l, _⟩ := hgrands
      have hdef : hashlifeResultAtAux (fuel + 1) j
          (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)) =
          hashlifeResultAux (fuel + 1) (node (node nw_nw nw_ne nw_sw nw_se) (node ne_nw ne_ne ne_sw ne_se)
          (node sw_nw sw_ne sw_sw sw_se) (node se_nw se_ne se_sw se_se)) := by
        simp only [hashlifeResultAtAux, MacroCell.level, hnw_nw_l, beq_iff_eq]
        split
        · rfl
        · exfalso; omega
      rw [hdef]
      exact hres
    · -- mono-ronde : fuel + 1 ≥ j + 3, helper prive (budget propre).
      rw [hc] at heq
      simp only [beq_iff_eq] at heq
      have hle : j + 2 ≤ fuel := by omega
      have hk : c.level = (fuel - 1) + 2 := by omega
      obtain ⟨nw_nw, nw_ne, nw_sw, nw_se, ne_nw, ne_ne, ne_sw, ne_se, sw_nw, sw_ne, sw_sw, sw_se, se_nw, se_ne, se_sw, se_se, rfl, hgrands⟩ :=
        p4_double_nine_shape c (fuel - 1) (wf_of_cellWf hwf) hk
      exact hashlifeResultAtAux_level_cellWf_mono fuel j hle
        nw_nw nw_ne nw_sw nw_se ne_nw ne_ne ne_sw ne_se sw_nw sw_ne sw_sw sw_se se_nw se_ne se_sw se_se
        hgrands heq ih

/-- Enveloppe `hashlifeResultAt` : l'invariant du moteur At se
    specialise au fuel = niveau pose par le wrapper. C'est la forme
    consommee par le pas inductif de `hashlifeResultAt_central_correct`
    (l'ih sur les `n_i` exige leur niveau ET leur `cellWf`). -/
theorem hashlifeResultAt_level_cellWf (j : Nat) (c : MacroCell)
    (hwf : cellWf c) (hj : j + 2 ≤ c.level) :
    (hashlifeResultAt j c).level = c.level - 1 ∧ cellWf (hashlifeResultAt j c) := by
  have h := hashlifeResultAtAux_level_cellWf c.level j c hwf rfl hj
  unfold hashlifeResultAt
  exact h

/-! ## Grain 3b partie 2 — accords de grille n_i vs c (briques de localite)

Le pas inductif de `hashlifeResultAt_central_correct` (niveau `M > j + 2`)
decompose le resultat mono-ronde en 16 sous-quadrants des `r_i`. Chaque bras
relie l'evolution de la sous-cellule `n_i` a celle de `c` : apres `2^j` pas,
l'etat d'un point de la fenetre certifiee de `n_i` ne depend que de la boite
Chebyshev de rayon `2^j` autour de lui, boite contenue dans la region de
`n_i` (marge `2^k >= 2^j` avec `k = M - 2`). Les lemmes ci-dessous etablissent
l'accord BRUT des grilles initiales : sur sa region, la grille de `n_i`
(ramenee au repere de `c`) coincide avec celle de `c`, petit-enfant par
petit-enfant. La consommation (`evolve_box_agree_local` + `evolve_shift`)
se fait dans les bras de l'assemblage. -/

/-- Depuis `c.wf` et le niveau d'un seul petit-enfant, les 16 niveaux et les
    16 `wf` des petits-enfants d'une cellule 16-petits-enfants. -/
theorem node16_grandchild_facts {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) :
    a2.level = k ∧ a3.level = k ∧ a4.level = k ∧
    b1.level = k ∧ b2.level = k ∧ b3.level = k ∧ b4.level = k ∧
    c1.level = k ∧ c2.level = k ∧ c3.level = k ∧ c4.level = k ∧
    d1.level = k ∧ d2.level = k ∧ d3.level = k ∧ d4.level = k ∧
    a1.wf = true ∧ a2.wf = true ∧ a3.wf = true ∧ a4.wf = true ∧
    b1.wf = true ∧ b2.wf = true ∧ b3.wf = true ∧ b4.wf = true ∧
    c1.wf = true ∧ c2.wf = true ∧ c3.wf = true ∧ c4.wf = true ∧
    d1.wf = true ∧ d2.wf = true ∧ d3.wf = true ∧ d4.wf = true := by
  have hclvl : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
                 (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level = k + 2 := by
    show 1 + (1 + a1.level) = k + 2
    rw [ha1l]
    omega
  obtain ⟨hq1e, hq2e, hq3e, hq4e, hqw1, hqw2, hqw3, hqw4⟩ :=
    wf_node_quad_level (n := k + 1) hclvl hwf
  obtain ⟨_ha1e, ha2e, ha3e, ha4e, ha1w, ha2w, ha3w, ha4w⟩ :=
    wf_node_quad_level (n := k) hq1e hqw1
  obtain ⟨hb1e, hb2e, hb3e, hb4e, hb1w, hb2w, hb3w, hb4w⟩ :=
    wf_node_quad_level (n := k) hq2e hqw2
  obtain ⟨hc1e, hc2e, hc3e, hc4e, hc1w, hc2w, hc3w, hc4w⟩ :=
    wf_node_quad_level (n := k) hq3e hqw3
  obtain ⟨hd1e, hd2e, hd3e, hd4e, hd1w, hd2w, hd3w, hd4w⟩ :=
    wf_node_quad_level (n := k) hq4e hqw4
  exact ⟨ha2e, ha3e, ha4e, hb1e, hb2e, hb3e, hb4e, hc1e, hc2e, hc3e, hc4e,
    hd1e, hd2e, hd3e, hd4e,
    ha1w, ha2w, ha3w, ha4w, hb1w, hb2w, hb3w, hb4w,
    hc1w, hc2w, hc3w, hc4w, hd1w, hd2w, hd3w, hd4w⟩

/-- Etendue d'un petit-enfant de niveau `k` place en `(i, j)` : appartenance
    implique la boite `[i, i + 2^k) x [j, j + 2^k)`. Consommme par `omega`
    dans les tuels des accords `n_i`. -/
theorem grandchild_extent' {k : Nat} (g : MacroCell) (i j : Int) (q : Int × Int)
    (hgl : g.level = k) (hwf : g.wf = true) (h : q ∈ g.toGrid (i, j)) :
    i ≤ q.1 ∧ q.1 < i + (2^k : Int) ∧ j ≤ q.2 ∧ q.2 < j + (2^k : Int) := by
  have he := mem_toGrid_extent g i j q hwf h
  rwa [hgl] at he

-- Navette origin<->place : `(p.1 - r0, p.2 - c0) in g.toGrid (0, 0)` ssi
-- `p in g.toGrid (r0, c0)` (specialisation symetrique de `mem_toGrid_shift`).
theorem toGrid_origin_iff_placed {g : MacroCell} {r0 c0 : Int} {p : Int × Int} :
    (p.1 - r0, p.2 - c0) ∈ g.toGrid (0, 0) ↔ p ∈ g.toGrid (r0, c0) :=
  (mem_toGrid_shift (c := g) (r0 := r0) (c0 := c0) (p := p)).symm

-- Pont Bool : une biconditionnelle d'appartenances donne l'egalite des
-- `isAlive`. Consomme les accords `n_i` dans les bras de l'assemblage,
-- face a `evolve_box_agree_local` (qui parle en `isAlive`).
theorem isAlive_eq_of_mem_iff {g1 g2 : Grid} {p1 p2 : Int × Int}
    (h : p1 ∈ g1 ↔ p2 ∈ g2) : isAlive g1 p1 = isAlive g2 p2 := by
  by_cases h1 : p1 ∈ g1
  · have h2 : p2 ∈ g2 := h.mp h1
    simp [isAlive, h1, h2]
  · have h2 : ¬ (p2 ∈ g2) := fun hc => h1 (h.mpr hc)
    simp [isAlive, h1, h2]

/-- Decomposition 16-voies de la grille d'une cellule 16-petits-enfants :
    chaque petit-enfant occupe son bloc `u x u` (`u = 2^k`) sur la grille
    `4u x 4u`, groupe par quadrant. Preuve deterministe en deux niveaux :
    `mem_toGrid_node` sur `c` (quadrants, offsets `2^(k+1) = 2*(2^k)` via
    `pow_two_succ_eq_int`), puis `mem_toGrid_node` + navettes
    `mem_toGrid_shift` / `toGrid_origin_iff_placed` par quadrant, avec pont
    arithmetique `2*(2^k) + 2^k = 3*(2^k)` (ring). -/
theorem toGrid_node16_mem {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int) :
    q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) ↔
      q ∈ a1.toGrid (0, 0) ∨
      q ∈ a2.toGrid (0, (2^k : Int)) ∨
      q ∈ a3.toGrid ((2^k : Int), 0) ∨
      q ∈ a4.toGrid ((2^k : Int), (2^k : Int)) ∨
      q ∈ b1.toGrid (0, (2*(2^k : Int))) ∨
      q ∈ b2.toGrid (0, (3*(2^k : Int))) ∨
      q ∈ b3.toGrid ((2^k : Int), (2*(2^k : Int))) ∨
      q ∈ b4.toGrid ((2^k : Int), (3*(2^k : Int))) ∨
      q ∈ c1.toGrid ((2*(2^k : Int)), 0) ∨
      q ∈ c2.toGrid ((2*(2^k : Int)), (2^k : Int)) ∨
      q ∈ c3.toGrid ((3*(2^k : Int)), 0) ∨
      q ∈ c4.toGrid ((3*(2^k : Int)), (2^k : Int)) ∨
      q ∈ d1.toGrid ((2*(2^k : Int)), (2*(2^k : Int))) ∨
      q ∈ d2.toGrid ((2*(2^k : Int)), (3*(2^k : Int))) ∨
      q ∈ d3.toGrid ((3*(2^k : Int)), (2*(2^k : Int))) ∨
      q ∈ d4.toGrid ((3*(2^k : Int)), (3*(2^k : Int))) := by
  obtain ⟨_ha2l, _ha3l, _ha4l, hb1l, _hb2l, _hb3l, _hb4l, hc1l, _hc2l, _hc3l, _hc4l, hd1l, _hd2l, _hd3l, _hd4l, _ha1w, _ha2w, _ha3w, _ha4w, _hb1w, _hb2w, _hb3w, _hb4w, _hc1w, _hc2w, _hc3w, _hc4w, _hd1w, _hd2w, _hd3w, _hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  have hq1l : (node a1 a2 a3 a4).level = k + 1 := by
    show 1 + a1.level = k + 1
    rw [ha1l]
    omega
  have hq2l : (node b1 b2 b3 b4).level = k + 1 := by
    show 1 + b1.level = k + 1
    rw [hb1l]
    omega
  have hq3l : (node c1 c2 c3 c4).level = k + 1 := by
    show 1 + c1.level = k + 1
    rw [hc1l]
    omega
  have hq4l : (node d1 d2 d3 d4).level = k + 1 := by
    show 1 + d1.level = k + 1
    rw [hd1l]
    omega
  rw [mem_toGrid_node, hq1l, pow_two_succ_eq_int]
  simp only [Int.zero_add, Int.add_zero]
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · rw [mem_toGrid_node] at h1
      rw [ha1l] at h1
      simp only [Int.zero_add, Int.add_zero] at h1
      rcases h1 with (e1 | e2 | e3 | e4)
      · exact Or.inl e1
      · exact Or.inr (Or.inl e2)
      · exact Or.inr (Or.inr (Or.inl e3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
    · have hs : (q.1 - 0, q.2 - (2*(2^k : Int))) ∈ (node b1 b2 b3 b4).toGrid (0, 0) :=
        (mem_toGrid_shift (c := node b1 b2 b3 b4) (r0 := 0) (c0 := (2*(2^k : Int))) (p := q)).mp h2
      rw [mem_toGrid_node] at hs
      rw [hb1l] at hs
      simp only [Int.zero_add, Int.add_zero] at hs
      rcases hs with (e1 | e2 | e3 | e4)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := b1) (r0 := 0) (c0 := (2*(2^k : Int))) (p := q)).mpr e1)))))
      · have hss := (mem_toGrid_shift (c := b2) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mp e2
        have hp : ((q.1 - 0) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - 0, q.2 - (3*(2^k : Int))) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b2) (r0 := 0) (c0 := (3*(2^k : Int))) (p := q)).mp hss))))))
      · have hss := (mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mp e3
        have hp : ((q.1 - 0) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp hss)))))))
      · have hss := (mem_toGrid_shift (c := b4) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mp e4
        have hp : ((q.1 - 0) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (3*(2^k : Int))) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b4) (r0 := (2^k : Int)) (c0 := (3*(2^k : Int))) (p := q)).mp hss))))))))
    · have hs : (q.1 - (2*(2^k : Int)), q.2 - 0) ∈ (node c1 c2 c3 c4).toGrid (0, 0) :=
        (mem_toGrid_shift (c := node c1 c2 c3 c4) (r0 := (2*(2^k : Int))) (c0 := 0) (p := q)).mp h3
      rw [mem_toGrid_node] at hs
      rw [hc1l] at hs
      simp only [Int.zero_add, Int.add_zero] at hs
      rcases hs with (e1 | e2 | e3 | e4)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := c1) (r0 := (2*(2^k : Int))) (c0 := 0) (p := q)).mpr e1)))))))))
      · have hss := (mem_toGrid_shift (c := c2) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mp e2
        have hp : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - 0) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp hss))))))))))
      · have hss := (mem_toGrid_shift (c := c3) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mp e3
        have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - 0) - 0) = (q.1 - (3*(2^k : Int)), q.2 - 0) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c3) (r0 := (3*(2^k : Int))) (c0 := 0) (p := q)).mp hss)))))))))))
      · have hss := (mem_toGrid_shift (c := c4) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mp e4
        have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - 0) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (2^k : Int)) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c4) (r0 := (3*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp hss))))))))))))
    · have hs : (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) ∈ (node d1 d2 d3 d4).toGrid (0, 0) :=
        (mem_toGrid_shift (c := node d1 d2 d3 d4) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp h4
      rw [mem_toGrid_node] at hs
      rw [hd1l] at hs
      simp only [Int.zero_add, Int.add_zero] at hs
      rcases hs with (e1 | e2 | e3 | e4)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mpr e1)))))))))))))
      · have hss := (mem_toGrid_shift (c := d2) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mp e2
        have hp : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d2) (r0 := (2*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp hss))))))))))))))
      · have hss := (mem_toGrid_shift (c := d3) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mp e3
        have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (3*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d3) (r0 := (3*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp hss)))))))))))))))
      · have hss := (mem_toGrid_shift (c := d4) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mp e4
        have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
          simp only [Prod.mk.injEq]
          constructor <;> omega
        rw [hp] at hss
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (((toGrid_origin_iff_placed (g := d4) (r0 := (3*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp hss))))))))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · have hq : q ∈ (node a1 a2 a3 a4).toGrid (0, 0) := by
        rw [mem_toGrid_node, ha1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inl h1
      exact Or.inl hq
    · have hq : q ∈ (node a1 a2 a3 a4).toGrid (0, 0) := by
        rw [mem_toGrid_node, ha1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inr (Or.inl h2)
      exact Or.inl hq
    · have hq : q ∈ (node a1 a2 a3 a4).toGrid (0, 0) := by
        rw [mem_toGrid_node, ha1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inr (Or.inr (Or.inl h3))
      exact Or.inl hq
    · have hq : q ∈ (node a1 a2 a3 a4).toGrid (0, 0) := by
        rw [mem_toGrid_node, ha1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inr (Or.inr (Or.inr (h4)))
      exact Or.inl hq
    · have hq : q ∈ (node b1 b2 b3 b4).toGrid (0, (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hb1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inl h5
      exact Or.inr (Or.inl hq)
    · have hq : q ∈ (node b1 b2 b3 b4).toGrid (0, (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hb1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        rw [show (2*(2^k : Int)) + (2^k : Int) = 3*(2^k : Int) from by ring]
        exact Or.inr (Or.inl h6)
      exact Or.inr (Or.inl hq)
    · have hq : q ∈ (node b1 b2 b3 b4).toGrid (0, (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hb1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inr (Or.inr (Or.inl h7))
      exact Or.inr (Or.inl hq)
    · have hq : q ∈ (node b1 b2 b3 b4).toGrid (0, (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hb1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        rw [show (2*(2^k : Int)) + (2^k : Int) = 3*(2^k : Int) from by ring]
        exact Or.inr (Or.inr (Or.inr (h8)))
      exact Or.inr (Or.inl hq)
    · have hq : q ∈ (node c1 c2 c3 c4).toGrid ((2*(2^k : Int)), 0) := by
        rw [mem_toGrid_node, hc1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inl h9
      exact Or.inr (Or.inr (Or.inl hq))
    · have hq : q ∈ (node c1 c2 c3 c4).toGrid ((2*(2^k : Int)), 0) := by
        rw [mem_toGrid_node, hc1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inr (Or.inl h10)
      exact Or.inr (Or.inr (Or.inl hq))
    · have hq : q ∈ (node c1 c2 c3 c4).toGrid ((2*(2^k : Int)), 0) := by
        rw [mem_toGrid_node, hc1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        rw [show (2*(2^k : Int)) + (2^k : Int) = 3*(2^k : Int) from by ring]
        exact Or.inr (Or.inr (Or.inl h11))
      exact Or.inr (Or.inr (Or.inl hq))
    · have hq : q ∈ (node c1 c2 c3 c4).toGrid ((2*(2^k : Int)), 0) := by
        rw [mem_toGrid_node, hc1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        rw [show (2*(2^k : Int)) + (2^k : Int) = 3*(2^k : Int) from by ring]
        exact Or.inr (Or.inr (Or.inr (h12)))
      exact Or.inr (Or.inr (Or.inl hq))
    · have hq : q ∈ (node d1 d2 d3 d4).toGrid ((2*(2^k : Int)), (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hd1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        exact Or.inl h13
      exact Or.inr (Or.inr (Or.inr (hq)))
    · have hq : q ∈ (node d1 d2 d3 d4).toGrid ((2*(2^k : Int)), (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hd1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        rw [show (2*(2^k : Int)) + (2^k : Int) = 3*(2^k : Int) from by ring]
        exact Or.inr (Or.inl h14)
      exact Or.inr (Or.inr (Or.inr (hq)))
    · have hq : q ∈ (node d1 d2 d3 d4).toGrid ((2*(2^k : Int)), (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hd1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        rw [show (2*(2^k : Int)) + (2^k : Int) = 3*(2^k : Int) from by ring]
        exact Or.inr (Or.inr (Or.inl h15))
      exact Or.inr (Or.inr (Or.inr (hq)))
    · have hq : q ∈ (node d1 d2 d3 d4).toGrid ((2*(2^k : Int)), (2*(2^k : Int))) := by
        rw [mem_toGrid_node, hd1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        rw [show (2*(2^k : Int)) + (2^k : Int) = 3*(2^k : Int) from by ring]
        exact Or.inr (Or.inr (Or.inr (h16)))
      exact Or.inr (Or.inr (Or.inr (hq)))

/-! ### Accords n_i vs c : 9 instances

Chaque `n_i` est un bloc 2×2 de petits-enfants de `c`. Sur sa region
(blocs couverts, en unites de `u = 2^k`), la grille de `n_i` au repere de
`c` coincide avec celle de `c` : biconditionnelle d'appartenance, preuve
par decomposition 16-voies + tuels d'etendue (`grandchild_extent'` + `omega`).
Regions (`[r1, r2) x [c1, c2)` en unites u) :
n1 [0,2)², n2 [0,2)×[1,3), n3 [0,2)×[2,4), n4 [1,3)×[0,2), n5 [1,3)²,
n6 [1,3)×[2,4), n7 [2,4)×[0,2), n8 [2,4)×[1,3), n9 [2,4)². -/

/-- Accord n1 (origine (0, 0) en unites u = 2^k). -/
theorem n1_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : 0 ≤ q.1 ∧ q.1 < (2*(2^k : Int)) ∧ 0 ≤ q.2 ∧ q.2 < (2*(2^k : Int))) :
    (q.1 - 0, q.2 - 0) ∈ (node a1 a2 a3 a4).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨_ha2l, _ha3l, _ha4l, hb1l, hb2l, hb3l, hb4l, hc1l, hc2l, hc3l, hc4l, hd1l, hd2l, hd3l, hd4l, _ha1w, _ha2w, _ha3w, _ha4w, hb1w, hb2w, hb3w, hb4w, hc1w, hc2w, hc3w, hc4w, hd1w, hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, ha1l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- a1 : n1-frame (0,0) -> c-frame (0, 0)
      exact Or.inl ((toGrid_origin_iff_placed (g := a1) (r0 := 0) (c0 := 0) (p := q)).mp h1)
    · -- a2 : n1-frame (0, (2^k : Int)) -> c-frame (0, (2^k : Int))
      have hs := (mem_toGrid_shift (c := a2) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - 0))).mp h2
      have hp : ((q.1 - 0) - 0, (q.2 - 0) - (2^k : Int)) = (q.1 - 0, q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a2) (r0 := 0) (c0 := (2^k : Int)) (p := q)).mp hs))
    · -- a3 : n1-frame ((2^k : Int), 0) -> c-frame ((2^k : Int), 0)
      have hs := (mem_toGrid_shift (c := a3) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - 0, q.2 - 0))).mp h3
      have hp : ((q.1 - 0) - (2^k : Int), (q.2 - 0) - 0) = (q.1 - (2^k : Int), q.2 - 0) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a3) (r0 := (2^k : Int)) (c0 := 0) (p := q)).mp hs)))
    · -- a4 : n1-frame ((2^k : Int), (2^k : Int)) -> c-frame ((2^k : Int), (2^k : Int))
      have hs := (mem_toGrid_shift (c := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - 0))).mp h4
      have hp : ((q.1 - 0) - (2^k : Int), (q.2 - 0) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mp hs))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · -- a1 : keep (n1 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := a1) (r0 := 0) (c0 := 0) (p := q)).mpr h1)
    · -- a2 : keep (n1 pos 2)
      have h0 : (q.1 - 0, q.2 - (2^k : Int)) ∈ a2.toGrid (0, 0) :=
        (mem_toGrid_shift (c := a2) (r0 := 0) (c0 := (2^k : Int)) (p := q)).mp h2
      have hp' : ((q.1 - 0) - 0, (q.2 - 0) - (2^k : Int)) = (q.1 - 0, q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := a2) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - 0, q.2 - 0))).mpr h0))
    · -- a3 : keep (n1 pos 3)
      have h0 : (q.1 - (2^k : Int), q.2 - 0) ∈ a3.toGrid (0, 0) :=
        (mem_toGrid_shift (c := a3) (r0 := (2^k : Int)) (c0 := 0) (p := q)).mp h3
      have hp' : ((q.1 - 0) - (2^k : Int), (q.2 - 0) - 0) = (q.1 - (2^k : Int), q.2 - 0) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := a3) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - 0, q.2 - 0))).mpr h0)))
    · -- a4 : keep (n1 pos 4)
      have h0 : (q.1 - (2^k : Int), q.2 - (2^k : Int)) ∈ a4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mp h4
      have hp' : ((q.1 - 0) - (2^k : Int), (q.2 - 0) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - 0, q.2 - 0))).mpr h0))))
    · exact absurd (grandchild_extent' b1 0 (2*(2^k : Int)) q hb1l hb1w h5) (by omega)
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · exact absurd (grandchild_extent' b3 (2^k : Int) (2*(2^k : Int)) q hb3l hb3w h7) (by omega)
    · exact absurd (grandchild_extent' b4 (2^k : Int) (3*(2^k : Int)) q hb4l hb4w h8) (by omega)
    · exact absurd (grandchild_extent' c1 (2*(2^k : Int)) 0 q hc1l hc1w h9) (by omega)
    · exact absurd (grandchild_extent' c2 (2*(2^k : Int)) (2^k : Int) q hc2l hc2w h10) (by omega)
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · exact absurd (grandchild_extent' c4 (3*(2^k : Int)) (2^k : Int) q hc4l hc4w h12) (by omega)
    · exact absurd (grandchild_extent' d1 (2*(2^k : Int)) (2*(2^k : Int)) q hd1l hd1w h13) (by omega)
    · exact absurd (grandchild_extent' d2 (2*(2^k : Int)) (3*(2^k : Int)) q hd2l hd2w h14) (by omega)
    · exact absurd (grandchild_extent' d3 (3*(2^k : Int)) (2*(2^k : Int)) q hd3l hd3w h15) (by omega)
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n2 (origine (0, (2^k : Int)) en unites u = 2^k). -/
theorem n2_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : 0 ≤ q.1 ∧ q.1 < (2*(2^k : Int)) ∧ (2^k : Int) ≤ q.2 ∧ q.2 < (3*(2^k : Int))) :
    (q.1 - 0, q.2 - (2^k : Int)) ∈ (node a2 b1 a4 b3).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, _ha4l, _hb1l, hb2l, _hb3l, hb4l, hc1l, hc2l, hc3l, hc4l, hd1l, hd2l, hd3l, hd4l, ha1w, _ha2w, ha3w, _ha4w, _hb1w, hb2w, _hb3w, hb4w, hc1w, hc2w, hc3w, hc4w, hd1w, hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, ha2l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- a2 : n2-frame (0,0) -> c-frame (0, (2^k : Int))
      exact Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a2) (r0 := 0) (c0 := (2^k : Int)) (p := q)).mp h1))
    · -- b1 : n2-frame (0, (2^k : Int)) -> c-frame (0, (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := b1) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - (2^k : Int)))).mp h2
      have hp : ((q.1 - 0) - 0, (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - 0, q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b1) (r0 := 0) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))
    · -- a4 : n2-frame ((2^k : Int), 0) -> c-frame ((2^k : Int), (2^k : Int))
      have hs := (mem_toGrid_shift (c := a4) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - 0, q.2 - (2^k : Int)))).mp h3
      have hp : ((q.1 - 0) - (2^k : Int), (q.2 - (2^k : Int)) - 0) = (q.1 - (2^k : Int), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mp hs))))
    · -- b3 : n2-frame ((2^k : Int), (2^k : Int)) -> c-frame ((2^k : Int), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - (2^k : Int)))).mp h4
      have hp : ((q.1 - 0) - (2^k : Int), (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · -- a2 : keep (n2 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := a2) (r0 := 0) (c0 := (2^k : Int)) (p := q)).mpr h2)
    · exact absurd (grandchild_extent' a3 (2^k : Int) 0 q ha3l ha3w h3) (by omega)
    · -- a4 : keep (n2 pos 3)
      have h0 : (q.1 - (2^k : Int), q.2 - (2^k : Int)) ∈ a4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mp h4
      have hp' : ((q.1 - 0) - (2^k : Int), (q.2 - (2^k : Int)) - 0) = (q.1 - (2^k : Int), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := a4) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - 0, q.2 - (2^k : Int)))).mpr h0)))
    · -- b1 : keep (n2 pos 2)
      have h0 : (q.1 - 0, q.2 - (2*(2^k : Int))) ∈ b1.toGrid (0, 0) :=
        (mem_toGrid_shift (c := b1) (r0 := 0) (c0 := (2*(2^k : Int))) (p := q)).mp h5
      have hp' : ((q.1 - 0) - 0, (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - 0, q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := b1) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - 0, q.2 - (2^k : Int)))).mpr h0))
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · -- b3 : keep (n2 pos 4)
      have h0 : (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) ∈ b3.toGrid (0, 0) :=
        (mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp h7
      have hp' : ((q.1 - 0) - (2^k : Int), (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - 0, q.2 - (2^k : Int)))).mpr h0))))
    · exact absurd (grandchild_extent' b4 (2^k : Int) (3*(2^k : Int)) q hb4l hb4w h8) (by omega)
    · exact absurd (grandchild_extent' c1 (2*(2^k : Int)) 0 q hc1l hc1w h9) (by omega)
    · exact absurd (grandchild_extent' c2 (2*(2^k : Int)) (2^k : Int) q hc2l hc2w h10) (by omega)
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · exact absurd (grandchild_extent' c4 (3*(2^k : Int)) (2^k : Int) q hc4l hc4w h12) (by omega)
    · exact absurd (grandchild_extent' d1 (2*(2^k : Int)) (2*(2^k : Int)) q hd1l hd1w h13) (by omega)
    · exact absurd (grandchild_extent' d2 (2*(2^k : Int)) (3*(2^k : Int)) q hd2l hd2w h14) (by omega)
    · exact absurd (grandchild_extent' d3 (3*(2^k : Int)) (2*(2^k : Int)) q hd3l hd3w h15) (by omega)
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n3 (origine (0, (2*(2^k : Int))) en unites u = 2^k). -/
theorem n3_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : 0 ≤ q.1 ∧ q.1 < (2*(2^k : Int)) ∧ (2*(2^k : Int)) ≤ q.2 ∧ q.2 < (4*(2^k : Int))) :
    (q.1 - 0, q.2 - (2*(2^k : Int))) ∈ (node b1 b2 b3 b4).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, ha4l, hb1l, _hb2l, _hb3l, _hb4l, hc1l, hc2l, hc3l, hc4l, hd1l, hd2l, hd3l, hd4l, ha1w, ha2w, ha3w, ha4w, _hb1w, _hb2w, _hb3w, _hb4w, hc1w, hc2w, hc3w, hc4w, hd1w, hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, hb1l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- b1 : n3-frame (0,0) -> c-frame (0, (2*(2^k : Int)))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b1) (r0 := 0) (c0 := (2*(2^k : Int))) (p := q)).mp h1)))))
    · -- b2 : n3-frame (0, (2^k : Int)) -> c-frame (0, (3*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := b2) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mp h2
      have hp : ((q.1 - 0) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - 0, q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b2) (r0 := 0) (c0 := (3*(2^k : Int))) (p := q)).mp hs))))))
    · -- b3 : n3-frame ((2^k : Int), 0) -> c-frame ((2^k : Int), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mp h3
      have hp : ((q.1 - 0) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))
    · -- b4 : n3-frame ((2^k : Int), (2^k : Int)) -> c-frame ((2^k : Int), (3*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := b4) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mp h4
      have hp : ((q.1 - 0) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b4) (r0 := (2^k : Int)) (c0 := (3*(2^k : Int))) (p := q)).mp hs))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · exact absurd (grandchild_extent' a2 0 (2^k : Int) q ha2l ha2w h2) (by omega)
    · exact absurd (grandchild_extent' a3 (2^k : Int) 0 q ha3l ha3w h3) (by omega)
    · exact absurd (grandchild_extent' a4 (2^k : Int) (2^k : Int) q ha4l ha4w h4) (by omega)
    · -- b1 : keep (n3 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := b1) (r0 := 0) (c0 := (2*(2^k : Int))) (p := q)).mpr h5)
    · -- b2 : keep (n3 pos 2)
      have h0 : (q.1 - 0, q.2 - (3*(2^k : Int))) ∈ b2.toGrid (0, 0) :=
        (mem_toGrid_shift (c := b2) (r0 := 0) (c0 := (3*(2^k : Int))) (p := q)).mp h6
      have hp' : ((q.1 - 0) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - 0, q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := b2) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mpr h0))
    · -- b3 : keep (n3 pos 3)
      have h0 : (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) ∈ b3.toGrid (0, 0) :=
        (mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp h7
      have hp' : ((q.1 - 0) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mpr h0)))
    · -- b4 : keep (n3 pos 4)
      have h0 : (q.1 - (2^k : Int), q.2 - (3*(2^k : Int))) ∈ b4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := b4) (r0 := (2^k : Int)) (c0 := (3*(2^k : Int))) (p := q)).mp h8
      have hp' : ((q.1 - 0) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := b4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - 0, q.2 - (2*(2^k : Int))))).mpr h0))))
    · exact absurd (grandchild_extent' c1 (2*(2^k : Int)) 0 q hc1l hc1w h9) (by omega)
    · exact absurd (grandchild_extent' c2 (2*(2^k : Int)) (2^k : Int) q hc2l hc2w h10) (by omega)
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · exact absurd (grandchild_extent' c4 (3*(2^k : Int)) (2^k : Int) q hc4l hc4w h12) (by omega)
    · exact absurd (grandchild_extent' d1 (2*(2^k : Int)) (2*(2^k : Int)) q hd1l hd1w h13) (by omega)
    · exact absurd (grandchild_extent' d2 (2*(2^k : Int)) (3*(2^k : Int)) q hd2l hd2w h14) (by omega)
    · exact absurd (grandchild_extent' d3 (3*(2^k : Int)) (2*(2^k : Int)) q hd3l hd3w h15) (by omega)
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n4 (origine ((2^k : Int), 0) en unites u = 2^k). -/
theorem n4_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : (2^k : Int) ≤ q.1 ∧ q.1 < (3*(2^k : Int)) ∧ 0 ≤ q.2 ∧ q.2 < (2*(2^k : Int))) :
    (q.1 - (2^k : Int), q.2 - 0) ∈ (node a3 a4 c1 c2).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, _ha4l, hb1l, hb2l, hb3l, hb4l, _hc1l, _hc2l, hc3l, hc4l, hd1l, hd2l, hd3l, hd4l, ha1w, ha2w, _ha3w, _ha4w, hb1w, hb2w, hb3w, hb4w, _hc1w, _hc2w, hc3w, hc4w, hd1w, hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, ha3l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- a3 : n4-frame (0,0) -> c-frame ((2^k : Int), 0)
      exact Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a3) (r0 := (2^k : Int)) (c0 := 0) (p := q)).mp h1)))
    · -- a4 : n4-frame (0, (2^k : Int)) -> c-frame ((2^k : Int), (2^k : Int))
      have hs := (mem_toGrid_shift (c := a4) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2^k : Int), q.2 - 0))).mp h2
      have hp : ((q.1 - (2^k : Int)) - 0, (q.2 - 0) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mp hs))))
    · -- c1 : n4-frame ((2^k : Int), 0) -> c-frame ((2*(2^k : Int)), 0)
      have hs := (mem_toGrid_shift (c := c1) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2^k : Int), q.2 - 0))).mp h3
      have hp : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - 0) - 0) = (q.1 - (2*(2^k : Int)), q.2 - 0) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c1) (r0 := (2*(2^k : Int))) (c0 := 0) (p := q)).mp hs)))))))))
    · -- c2 : n4-frame ((2^k : Int), (2^k : Int)) -> c-frame ((2*(2^k : Int)), (2^k : Int))
      have hs := (mem_toGrid_shift (c := c2) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2^k : Int), q.2 - 0))).mp h4
      have hp : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - 0) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp hs))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · exact absurd (grandchild_extent' a2 0 (2^k : Int) q ha2l ha2w h2) (by omega)
    · -- a3 : keep (n4 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := a3) (r0 := (2^k : Int)) (c0 := 0) (p := q)).mpr h3)
    · -- a4 : keep (n4 pos 2)
      have h0 : (q.1 - (2^k : Int), q.2 - (2^k : Int)) ∈ a4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mp h4
      have hp' : ((q.1 - (2^k : Int)) - 0, (q.2 - 0) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := a4) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - (2^k : Int), q.2 - 0))).mpr h0))
    · exact absurd (grandchild_extent' b1 0 (2*(2^k : Int)) q hb1l hb1w h5) (by omega)
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · exact absurd (grandchild_extent' b3 (2^k : Int) (2*(2^k : Int)) q hb3l hb3w h7) (by omega)
    · exact absurd (grandchild_extent' b4 (2^k : Int) (3*(2^k : Int)) q hb4l hb4w h8) (by omega)
    · -- c1 : keep (n4 pos 3)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - 0) ∈ c1.toGrid (0, 0) :=
        (mem_toGrid_shift (c := c1) (r0 := (2*(2^k : Int))) (c0 := 0) (p := q)).mp h9
      have hp' : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - 0) - 0) = (q.1 - (2*(2^k : Int)), q.2 - 0) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := c1) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - (2^k : Int), q.2 - 0))).mpr h0)))
    · -- c2 : keep (n4 pos 4)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) ∈ c2.toGrid (0, 0) :=
        (mem_toGrid_shift (c := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp h10
      have hp' : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - 0) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := c2) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - (2^k : Int), q.2 - 0))).mpr h0))))
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · exact absurd (grandchild_extent' c4 (3*(2^k : Int)) (2^k : Int) q hc4l hc4w h12) (by omega)
    · exact absurd (grandchild_extent' d1 (2*(2^k : Int)) (2*(2^k : Int)) q hd1l hd1w h13) (by omega)
    · exact absurd (grandchild_extent' d2 (2*(2^k : Int)) (3*(2^k : Int)) q hd2l hd2w h14) (by omega)
    · exact absurd (grandchild_extent' d3 (3*(2^k : Int)) (2*(2^k : Int)) q hd3l hd3w h15) (by omega)
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n5 (origine ((2^k : Int), (2^k : Int)) en unites u = 2^k). -/
theorem n5_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : (2^k : Int) ≤ q.1 ∧ q.1 < (3*(2^k : Int)) ∧ (2^k : Int) ≤ q.2 ∧ q.2 < (3*(2^k : Int))) :
    (q.1 - (2^k : Int), q.2 - (2^k : Int)) ∈ (node a4 b3 c2 d1).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, ha4l, hb1l, hb2l, _hb3l, hb4l, hc1l, _hc2l, hc3l, hc4l, _hd1l, hd2l, hd3l, hd4l, ha1w, ha2w, ha3w, _ha4w, hb1w, hb2w, _hb3w, hb4w, hc1w, _hc2w, hc3w, hc4w, _hd1w, hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, ha4l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- a4 : n5-frame (0,0) -> c-frame ((2^k : Int), (2^k : Int))
      exact Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mp h1))))
    · -- b3 : n5-frame (0, (2^k : Int)) -> c-frame ((2^k : Int), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := b3) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2^k : Int), q.2 - (2^k : Int)))).mp h2
      have hp : ((q.1 - (2^k : Int)) - 0, (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))
    · -- c2 : n5-frame ((2^k : Int), 0) -> c-frame ((2*(2^k : Int)), (2^k : Int))
      have hs := (mem_toGrid_shift (c := c2) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2^k : Int), q.2 - (2^k : Int)))).mp h3
      have hp : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2^k : Int)) - 0) = (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp hs))))))))))
    · -- d1 : n5-frame ((2^k : Int), (2^k : Int)) -> c-frame ((2*(2^k : Int)), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d1) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2^k : Int), q.2 - (2^k : Int)))).mp h4
      have hp : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · exact absurd (grandchild_extent' a2 0 (2^k : Int) q ha2l ha2w h2) (by omega)
    · exact absurd (grandchild_extent' a3 (2^k : Int) 0 q ha3l ha3w h3) (by omega)
    · -- a4 : keep (n5 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := a4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := q)).mpr h4)
    · exact absurd (grandchild_extent' b1 0 (2*(2^k : Int)) q hb1l hb1w h5) (by omega)
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · -- b3 : keep (n5 pos 2)
      have h0 : (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) ∈ b3.toGrid (0, 0) :=
        (mem_toGrid_shift (c := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp h7
      have hp' : ((q.1 - (2^k : Int)) - 0, (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := b3) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - (2^k : Int), q.2 - (2^k : Int)))).mpr h0))
    · exact absurd (grandchild_extent' b4 (2^k : Int) (3*(2^k : Int)) q hb4l hb4w h8) (by omega)
    · exact absurd (grandchild_extent' c1 (2*(2^k : Int)) 0 q hc1l hc1w h9) (by omega)
    · -- c2 : keep (n5 pos 3)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) ∈ c2.toGrid (0, 0) :=
        (mem_toGrid_shift (c := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp h10
      have hp' : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2^k : Int)) - 0) = (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := c2) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - (2^k : Int), q.2 - (2^k : Int)))).mpr h0)))
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · exact absurd (grandchild_extent' c4 (3*(2^k : Int)) (2^k : Int) q hc4l hc4w h12) (by omega)
    · -- d1 : keep (n5 pos 4)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) ∈ d1.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp h13
      have hp' : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := d1) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - (2^k : Int), q.2 - (2^k : Int)))).mpr h0))))
    · exact absurd (grandchild_extent' d2 (2*(2^k : Int)) (3*(2^k : Int)) q hd2l hd2w h14) (by omega)
    · exact absurd (grandchild_extent' d3 (3*(2^k : Int)) (2*(2^k : Int)) q hd3l hd3w h15) (by omega)
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n6 (origine ((2^k : Int), (2*(2^k : Int))) en unites u = 2^k). -/
theorem n6_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : (2^k : Int) ≤ q.1 ∧ q.1 < (3*(2^k : Int)) ∧ (2*(2^k : Int)) ≤ q.2 ∧ q.2 < (4*(2^k : Int))) :
    (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))) ∈ (node b3 b4 d1 d2).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, ha4l, hb1l, hb2l, hb3l, _hb4l, hc1l, hc2l, hc3l, hc4l, _hd1l, _hd2l, hd3l, hd4l, ha1w, ha2w, ha3w, ha4w, hb1w, hb2w, _hb3w, _hb4w, hc1w, hc2w, hc3w, hc4w, _hd1w, _hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, hb3l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- b3 : n6-frame (0,0) -> c-frame ((2^k : Int), (2*(2^k : Int)))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mp h1)))))))
    · -- b4 : n6-frame (0, (2^k : Int)) -> c-frame ((2^k : Int), (3*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := b4) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))))).mp h2
      have hp : ((q.1 - (2^k : Int)) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := b4) (r0 := (2^k : Int)) (c0 := (3*(2^k : Int))) (p := q)).mp hs))))))))
    · -- d1 : n6-frame ((2^k : Int), 0) -> c-frame ((2*(2^k : Int)), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d1) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))))).mp h3
      have hp : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))))))))
    · -- d2 : n6-frame ((2^k : Int), (2^k : Int)) -> c-frame ((2*(2^k : Int)), (3*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d2) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))))).mp h4
      have hp : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d2) (r0 := (2*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp hs))))))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · exact absurd (grandchild_extent' a2 0 (2^k : Int) q ha2l ha2w h2) (by omega)
    · exact absurd (grandchild_extent' a3 (2^k : Int) 0 q ha3l ha3w h3) (by omega)
    · exact absurd (grandchild_extent' a4 (2^k : Int) (2^k : Int) q ha4l ha4w h4) (by omega)
    · exact absurd (grandchild_extent' b1 0 (2*(2^k : Int)) q hb1l hb1w h5) (by omega)
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · -- b3 : keep (n6 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := b3) (r0 := (2^k : Int)) (c0 := (2*(2^k : Int))) (p := q)).mpr h7)
    · -- b4 : keep (n6 pos 2)
      have h0 : (q.1 - (2^k : Int), q.2 - (3*(2^k : Int))) ∈ b4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := b4) (r0 := (2^k : Int)) (c0 := (3*(2^k : Int))) (p := q)).mp h8
      have hp' : ((q.1 - (2^k : Int)) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2^k : Int), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := b4) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))))).mpr h0))
    · exact absurd (grandchild_extent' c1 (2*(2^k : Int)) 0 q hc1l hc1w h9) (by omega)
    · exact absurd (grandchild_extent' c2 (2*(2^k : Int)) (2^k : Int) q hc2l hc2w h10) (by omega)
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · exact absurd (grandchild_extent' c4 (3*(2^k : Int)) (2^k : Int) q hc4l hc4w h12) (by omega)
    · -- d1 : keep (n6 pos 3)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) ∈ d1.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp h13
      have hp' : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := d1) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))))).mpr h0)))
    · -- d2 : keep (n6 pos 4)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (3*(2^k : Int))) ∈ d2.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d2) (r0 := (2*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp h14
      have hp' : ((q.1 - (2^k : Int)) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := d2) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - (2^k : Int), q.2 - (2*(2^k : Int))))).mpr h0))))
    · exact absurd (grandchild_extent' d3 (3*(2^k : Int)) (2*(2^k : Int)) q hd3l hd3w h15) (by omega)
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n7 (origine ((2*(2^k : Int)), 0) en unites u = 2^k). -/
theorem n7_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : (2*(2^k : Int)) ≤ q.1 ∧ q.1 < (4*(2^k : Int)) ∧ 0 ≤ q.2 ∧ q.2 < (2*(2^k : Int))) :
    (q.1 - (2*(2^k : Int)), q.2 - 0) ∈ (node c1 c2 c3 c4).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, ha4l, hb1l, hb2l, hb3l, hb4l, hc1l, _hc2l, _hc3l, _hc4l, hd1l, hd2l, hd3l, hd4l, ha1w, ha2w, ha3w, ha4w, hb1w, hb2w, hb3w, hb4w, _hc1w, _hc2w, _hc3w, _hc4w, hd1w, hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, hc1l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- c1 : n7-frame (0,0) -> c-frame ((2*(2^k : Int)), 0)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c1) (r0 := (2*(2^k : Int))) (c0 := 0) (p := q)).mp h1)))))))))
    · -- c2 : n7-frame (0, (2^k : Int)) -> c-frame ((2*(2^k : Int)), (2^k : Int))
      have hs := (mem_toGrid_shift (c := c2) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mp h2
      have hp : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - 0) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp hs))))))))))
    · -- c3 : n7-frame ((2^k : Int), 0) -> c-frame ((3*(2^k : Int)), 0)
      have hs := (mem_toGrid_shift (c := c3) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mp h3
      have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - 0) - 0) = (q.1 - (3*(2^k : Int)), q.2 - 0) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c3) (r0 := (3*(2^k : Int))) (c0 := 0) (p := q)).mp hs)))))))))))
    · -- c4 : n7-frame ((2^k : Int), (2^k : Int)) -> c-frame ((3*(2^k : Int)), (2^k : Int))
      have hs := (mem_toGrid_shift (c := c4) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mp h4
      have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - 0) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c4) (r0 := (3*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp hs))))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · exact absurd (grandchild_extent' a2 0 (2^k : Int) q ha2l ha2w h2) (by omega)
    · exact absurd (grandchild_extent' a3 (2^k : Int) 0 q ha3l ha3w h3) (by omega)
    · exact absurd (grandchild_extent' a4 (2^k : Int) (2^k : Int) q ha4l ha4w h4) (by omega)
    · exact absurd (grandchild_extent' b1 0 (2*(2^k : Int)) q hb1l hb1w h5) (by omega)
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · exact absurd (grandchild_extent' b3 (2^k : Int) (2*(2^k : Int)) q hb3l hb3w h7) (by omega)
    · exact absurd (grandchild_extent' b4 (2^k : Int) (3*(2^k : Int)) q hb4l hb4w h8) (by omega)
    · -- c1 : keep (n7 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := c1) (r0 := (2*(2^k : Int))) (c0 := 0) (p := q)).mpr h9)
    · -- c2 : keep (n7 pos 2)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) ∈ c2.toGrid (0, 0) :=
        (mem_toGrid_shift (c := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp h10
      have hp' : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - 0) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := c2) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mpr h0))
    · -- c3 : keep (n7 pos 3)
      have h0 : (q.1 - (3*(2^k : Int)), q.2 - 0) ∈ c3.toGrid (0, 0) :=
        (mem_toGrid_shift (c := c3) (r0 := (3*(2^k : Int))) (c0 := 0) (p := q)).mp h11
      have hp' : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - 0) - 0) = (q.1 - (3*(2^k : Int)), q.2 - 0) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := c3) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mpr h0)))
    · -- c4 : keep (n7 pos 4)
      have h0 : (q.1 - (3*(2^k : Int)), q.2 - (2^k : Int)) ∈ c4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := c4) (r0 := (3*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp h12
      have hp' : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - 0) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := c4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - (2*(2^k : Int)), q.2 - 0))).mpr h0))))
    · exact absurd (grandchild_extent' d1 (2*(2^k : Int)) (2*(2^k : Int)) q hd1l hd1w h13) (by omega)
    · exact absurd (grandchild_extent' d2 (2*(2^k : Int)) (3*(2^k : Int)) q hd2l hd2w h14) (by omega)
    · exact absurd (grandchild_extent' d3 (3*(2^k : Int)) (2*(2^k : Int)) q hd3l hd3w h15) (by omega)
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n8 (origine ((2*(2^k : Int)), (2^k : Int)) en unites u = 2^k). -/
theorem n8_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : (2*(2^k : Int)) ≤ q.1 ∧ q.1 < (4*(2^k : Int)) ∧ (2^k : Int) ≤ q.2 ∧ q.2 < (3*(2^k : Int))) :
    (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)) ∈ (node c2 d1 c4 d3).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, ha4l, hb1l, hb2l, hb3l, hb4l, hc1l, hc2l, hc3l, _hc4l, _hd1l, hd2l, _hd3l, hd4l, ha1w, ha2w, ha3w, ha4w, hb1w, hb2w, hb3w, hb4w, hc1w, _hc2w, hc3w, _hc4w, _hd1w, hd2w, _hd3w, hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, hc2l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- c2 : n8-frame (0,0) -> c-frame ((2*(2^k : Int)), (2^k : Int))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp h1))))))))))
    · -- d1 : n8-frame (0, (2^k : Int)) -> c-frame ((2*(2^k : Int)), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d1) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)))).mp h2
      have hp : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))))))))
    · -- c4 : n8-frame ((2^k : Int), 0) -> c-frame ((3*(2^k : Int)), (2^k : Int))
      have hs := (mem_toGrid_shift (c := c4) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)))).mp h3
      have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2^k : Int)) - 0) = (q.1 - (3*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := c4) (r0 := (3*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp hs))))))))))))
    · -- d3 : n8-frame ((2^k : Int), (2^k : Int)) -> c-frame ((3*(2^k : Int)), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d3) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)))).mp h4
      have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d3) (r0 := (3*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · exact absurd (grandchild_extent' a2 0 (2^k : Int) q ha2l ha2w h2) (by omega)
    · exact absurd (grandchild_extent' a3 (2^k : Int) 0 q ha3l ha3w h3) (by omega)
    · exact absurd (grandchild_extent' a4 (2^k : Int) (2^k : Int) q ha4l ha4w h4) (by omega)
    · exact absurd (grandchild_extent' b1 0 (2*(2^k : Int)) q hb1l hb1w h5) (by omega)
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · exact absurd (grandchild_extent' b3 (2^k : Int) (2*(2^k : Int)) q hb3l hb3w h7) (by omega)
    · exact absurd (grandchild_extent' b4 (2^k : Int) (3*(2^k : Int)) q hb4l hb4w h8) (by omega)
    · exact absurd (grandchild_extent' c1 (2*(2^k : Int)) 0 q hc1l hc1w h9) (by omega)
    · -- c2 : keep (n8 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := c2) (r0 := (2*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mpr h10)
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · -- c4 : keep (n8 pos 3)
      have h0 : (q.1 - (3*(2^k : Int)), q.2 - (2^k : Int)) ∈ c4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := c4) (r0 := (3*(2^k : Int))) (c0 := (2^k : Int)) (p := q)).mp h12
      have hp' : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2^k : Int)) - 0) = (q.1 - (3*(2^k : Int)), q.2 - (2^k : Int)) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := c4) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)))).mpr h0)))
    · -- d1 : keep (n8 pos 2)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) ∈ d1.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp h13
      have hp' : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := d1) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)))).mpr h0))
    · exact absurd (grandchild_extent' d2 (2*(2^k : Int)) (3*(2^k : Int)) q hd2l hd2w h14) (by omega)
    · -- d3 : keep (n8 pos 4)
      have h0 : (q.1 - (3*(2^k : Int)), q.2 - (2*(2^k : Int))) ∈ d3.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d3) (r0 := (3*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp h15
      have hp' : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2^k : Int)) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := d3) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - (2*(2^k : Int)), q.2 - (2^k : Int)))).mpr h0))))
    · exact absurd (grandchild_extent' d4 (3*(2^k : Int)) (3*(2^k : Int)) q hd4l hd4w h16) (by omega)

/-- Accord n9 (origine ((2*(2^k : Int)), (2*(2^k : Int))) en unites u = 2^k). -/
theorem n9_grid_agree {k : Nat}
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = k) (q : Int × Int)
    (hq : (2*(2^k : Int)) ≤ q.1 ∧ q.1 < (4*(2^k : Int)) ∧ (2*(2^k : Int)) ≤ q.2 ∧ q.2 < (4*(2^k : Int))) :
    (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))) ∈ (node d1 d2 d3 d4).toGrid (0, 0) ↔
      q ∈ (node (node a1 a2 a3 a4) (node b1 b2 b3 b4) (node c1 c2 c3 c4) (node d1 d2 d3 d4)).toGrid (0, 0) := by
  obtain ⟨ha2l, ha3l, ha4l, hb1l, hb2l, hb3l, hb4l, hc1l, hc2l, hc3l, hc4l, hd1l, _hd2l, _hd3l, _hd4l, ha1w, ha2w, ha3w, ha4w, hb1w, hb2w, hb3w, hb4w, hc1w, hc2w, hc3w, hc4w, _hd1w, _hd2w, _hd3w, _hd4w⟩ :=
    node16_grandchild_facts a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l
  rw [mem_toGrid_node, hd1l]
  simp only [Int.zero_add, Int.add_zero]
  rw [toGrid_node16_mem a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 hwf ha1l q]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (h1 | h2 | h3 | h4)
    · -- d1 : n9-frame (0,0) -> c-frame ((2*(2^k : Int)), (2*(2^k : Int)))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp h1)))))))))))))
    · -- d2 : n9-frame (0, (2^k : Int)) -> c-frame ((2*(2^k : Int)), (3*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d2) (r0 := 0) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mp h2
      have hp : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d2) (r0 := (2*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp hs))))))))))))))
    · -- d3 : n9-frame ((2^k : Int), 0) -> c-frame ((3*(2^k : Int)), (2*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d3) (r0 := (2^k : Int)) (c0 := 0)
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mp h3
      have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (3*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((toGrid_origin_iff_placed (g := d3) (r0 := (3*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp hs)))))))))))))))
    · -- d4 : n9-frame ((2^k : Int), (2^k : Int)) -> c-frame ((3*(2^k : Int)), (3*(2^k : Int)))
      have hs := (mem_toGrid_shift (c := d4) (r0 := (2^k : Int)) (c0 := (2^k : Int))
        (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mp h4
      have hp : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [hp] at hs
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (((toGrid_origin_iff_placed (g := d4) (r0 := (3*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp hs))))))))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · exact absurd (grandchild_extent' a1 0 0 q ha1l ha1w h1) (by omega)
    · exact absurd (grandchild_extent' a2 0 (2^k : Int) q ha2l ha2w h2) (by omega)
    · exact absurd (grandchild_extent' a3 (2^k : Int) 0 q ha3l ha3w h3) (by omega)
    · exact absurd (grandchild_extent' a4 (2^k : Int) (2^k : Int) q ha4l ha4w h4) (by omega)
    · exact absurd (grandchild_extent' b1 0 (2*(2^k : Int)) q hb1l hb1w h5) (by omega)
    · exact absurd (grandchild_extent' b2 0 (3*(2^k : Int)) q hb2l hb2w h6) (by omega)
    · exact absurd (grandchild_extent' b3 (2^k : Int) (2*(2^k : Int)) q hb3l hb3w h7) (by omega)
    · exact absurd (grandchild_extent' b4 (2^k : Int) (3*(2^k : Int)) q hb4l hb4w h8) (by omega)
    · exact absurd (grandchild_extent' c1 (2*(2^k : Int)) 0 q hc1l hc1w h9) (by omega)
    · exact absurd (grandchild_extent' c2 (2*(2^k : Int)) (2^k : Int) q hc2l hc2w h10) (by omega)
    · exact absurd (grandchild_extent' c3 (3*(2^k : Int)) 0 q hc3l hc3w h11) (by omega)
    · exact absurd (grandchild_extent' c4 (3*(2^k : Int)) (2^k : Int) q hc4l hc4w h12) (by omega)
    · -- d1 : keep (n9 pos 1)
      exact Or.inl ((toGrid_origin_iff_placed (g := d1) (r0 := (2*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mpr h13)
    · -- d2 : keep (n9 pos 2)
      have h0 : (q.1 - (2*(2^k : Int)), q.2 - (3*(2^k : Int))) ∈ d2.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d2) (r0 := (2*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp h14
      have hp' : ((q.1 - (2*(2^k : Int))) - 0, (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (2*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inl ((mem_toGrid_shift (c := d2) (r0 := 0) (c0 := (2^k : Int)) (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mpr h0))
    · -- d3 : keep (n9 pos 3)
      have h0 : (q.1 - (3*(2^k : Int)), q.2 - (2*(2^k : Int))) ∈ d3.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d3) (r0 := (3*(2^k : Int))) (c0 := (2*(2^k : Int))) (p := q)).mp h15
      have hp' : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2*(2^k : Int))) - 0) = (q.1 - (3*(2^k : Int)), q.2 - (2*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inl ((mem_toGrid_shift (c := d3) (r0 := (2^k : Int)) (c0 := 0) (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mpr h0)))
    · -- d4 : keep (n9 pos 4)
      have h0 : (q.1 - (3*(2^k : Int)), q.2 - (3*(2^k : Int))) ∈ d4.toGrid (0, 0) :=
        (mem_toGrid_shift (c := d4) (r0 := (3*(2^k : Int))) (c0 := (3*(2^k : Int))) (p := q)).mp h16
      have hp' : ((q.1 - (2*(2^k : Int))) - (2^k : Int), (q.2 - (2*(2^k : Int))) - (2^k : Int)) = (q.1 - (3*(2^k : Int)), q.2 - (3*(2^k : Int))) := by
        simp only [Prod.mk.injEq]
        constructor <;> omega
      rw [← hp'] at h0
      exact Or.inr (Or.inr (Or.inr (((mem_toGrid_shift (c := d4) (r0 := (2^k : Int)) (c0 := (2^k : Int)) (p := (q.1 - (2*(2^k : Int)), q.2 - (2*(2^k : Int))))).mpr h0))))

/-! ### P4-At sortie mono-ronde : decomposition 16-voies (grain 3b, partie 4)

Preparation du LHS du pas inductif de `hashlifeResultAt_central_correct` :
la fenetre certifiee `[2^(M-2), 2^(M-2) + 2^(M-1))^2` (cf `p4at_ext_bridge`,
`restrictGridTo` prend lo et SIZE) couvre la sortie ENTIÈRE du moteur At
lue a l'ancre `(2^(M-2), 2^(M-2))`. Les seize sous-cellules `subX r_i`
(niveau `k`, cote `2^k`) pavent ce carre en grille 4x4 ; `r5` (centre)
y figure quatre fois. Decomposition par deux niveaux de
`mem_toGrid_node` + normalisation des offsets (`2*2^k + 2^k = 3*2^k`),
sans navettes : les seize disjonctes sont deja les `subX r_i`. Les faits
de niveau des sous-cellules viennent de `subX_level_cellWf` (partie 3,
premier consommateur). -/

theorem out16_toGrid_mem {k : Nat}
    (r1 r2 r3 r4 r5 r6 r7 r8 r9 : MacroCell)
    (hr1w : r1.wf = true) (hr1l : r1.level = k + 1)
    (hr2w : r2.wf = true) (hr2l : r2.level = k + 1)
    (hr3w : r3.wf = true) (hr3l : r3.level = k + 1)
    (hr4w : r4.wf = true) (hr4l : r4.level = k + 1)
    (hr5w : r5.wf = true) (hr5l : r5.level = k + 1)
    (hr6w : r6.wf = true) (hr6l : r6.level = k + 1)
    (hr7w : r7.wf = true) (hr7l : r7.level = k + 1)
    (hr8w : r8.wf = true) (hr8l : r8.level = k + 1)
    (hr9w : r9.wf = true) (hr9l : r9.level = k + 1)
    (a b : Int) (q : Int × Int) :
    q ∈ (node (node (subSE r1) (subSW r2) (subNE r4) (subNW r5))
             (node (subSE r2) (subSW r3) (subNE r5) (subNW r6))
             (node (subSE r4) (subSW r5) (subNE r7) (subNW r8))
             (node (subSE r5) (subSW r6) (subNE r8) (subNW r9))).toGrid (a, b) ↔
      q ∈ (subSE r1).toGrid (a, b) ∨
      q ∈ (subSW r2).toGrid (a, (b + (2^k : Int))) ∨
      q ∈ (subNE r4).toGrid ((a + (2^k : Int)), b) ∨
      q ∈ (subNW r5).toGrid ((a + (2^k : Int)), (b + (2^k : Int))) ∨
      q ∈ (subSE r2).toGrid (a, (b + (2*(2^k : Int)))) ∨
      q ∈ (subSW r3).toGrid (a, (b + (3*(2^k : Int)))) ∨
      q ∈ (subNE r5).toGrid ((a + (2^k : Int)), (b + (2*(2^k : Int)))) ∨
      q ∈ (subNW r6).toGrid ((a + (2^k : Int)), (b + (3*(2^k : Int)))) ∨
      q ∈ (subSE r4).toGrid ((a + (2*(2^k : Int))), b) ∨
      q ∈ (subSW r5).toGrid ((a + (2*(2^k : Int))), (b + (2^k : Int))) ∨
      q ∈ (subNE r7).toGrid ((a + (3*(2^k : Int))), b) ∨
      q ∈ (subNW r8).toGrid ((a + (3*(2^k : Int))), (b + (2^k : Int))) ∨
      q ∈ (subSE r5).toGrid ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) ∨
      q ∈ (subSW r6).toGrid ((a + (2*(2^k : Int))), (b + (3*(2^k : Int)))) ∨
      q ∈ (subNE r8).toGrid ((a + (3*(2^k : Int))), (b + (2*(2^k : Int)))) ∨
      q ∈ (subNW r9).toGrid ((a + (3*(2^k : Int))), (b + (3*(2^k : Int)))) := by
  have hSE1l : (subSE r1).level = k :=
    (subSE_level_cellWf (m := k) (cellWf_of_wf _ hr1w) hr1l).1
  have hSW2l : (subSW r2).level = k :=
    (subSW_level_cellWf (m := k) (cellWf_of_wf _ hr2w) hr2l).1
  have hNE4l : (subNE r4).level = k :=
    (subNE_level_cellWf (m := k) (cellWf_of_wf _ hr4w) hr4l).1
  have hNW5l : (subNW r5).level = k :=
    (subNW_level_cellWf (m := k) (cellWf_of_wf _ hr5w) hr5l).1
  have hSE2l : (subSE r2).level = k :=
    (subSE_level_cellWf (m := k) (cellWf_of_wf _ hr2w) hr2l).1
  have hSW3l : (subSW r3).level = k :=
    (subSW_level_cellWf (m := k) (cellWf_of_wf _ hr3w) hr3l).1
  have hNE5l : (subNE r5).level = k :=
    (subNE_level_cellWf (m := k) (cellWf_of_wf _ hr5w) hr5l).1
  have hNW6l : (subNW r6).level = k :=
    (subNW_level_cellWf (m := k) (cellWf_of_wf _ hr6w) hr6l).1
  have hSE4l : (subSE r4).level = k :=
    (subSE_level_cellWf (m := k) (cellWf_of_wf _ hr4w) hr4l).1
  have hSW5l : (subSW r5).level = k :=
    (subSW_level_cellWf (m := k) (cellWf_of_wf _ hr5w) hr5l).1
  have hNE7l : (subNE r7).level = k :=
    (subNE_level_cellWf (m := k) (cellWf_of_wf _ hr7w) hr7l).1
  have hNW8l : (subNW r8).level = k :=
    (subNW_level_cellWf (m := k) (cellWf_of_wf _ hr8w) hr8l).1
  have hSE5l : (subSE r5).level = k :=
    (subSE_level_cellWf (m := k) (cellWf_of_wf _ hr5w) hr5l).1
  have hSW6l : (subSW r6).level = k :=
    (subSW_level_cellWf (m := k) (cellWf_of_wf _ hr6w) hr6l).1
  have hNE8l : (subNE r8).level = k :=
    (subNE_level_cellWf (m := k) (cellWf_of_wf _ hr8w) hr8l).1
  have hNW9l : (subNW r9).level = k :=
    (subNW_level_cellWf (m := k) (cellWf_of_wf _ hr9w) hr9l).1
  have hQ1l : (node (subSE r1) (subSW r2) (subNE r4) (subNW r5)).level = k + 1 := by
    show 1 + (subSE r1).level = k + 1
    omega
  rw [mem_toGrid_node, hQ1l, pow_two_succ_eq_int]
  first | simp only [Int.zero_add, Int.add_zero] | skip
  constructor
  · rintro (hQ1 | hQ2 | hQ3 | hQ4)
    · rw [mem_toGrid_node, hSE1l] at hQ1
      first | simp only [Int.zero_add, Int.add_zero] at hQ1 | skip
      rcases hQ1 with (e1 | e2 | e3 | e4)
      · have hp : (a, b) = (a, b) := by
          congr 1 <;> ring
        rw [hp] at e1
        exact Or.inl e1
      · have hp : (a, (b + (2^k : Int))) = (a, (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp] at e2
        exact Or.inr (Or.inl e2)
      · have hp : ((a + (2^k : Int)), b) = ((a + (2^k : Int)), b) := by
          congr 1 <;> ring
        rw [hp] at e3
        exact Or.inr (Or.inr (Or.inl e3))
      · have hp : ((a + (2^k : Int)), (b + (2^k : Int))) = ((a + (2^k : Int)), (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp] at e4
        exact Or.inr (Or.inr (Or.inr (Or.inl e4)))
    · rw [mem_toGrid_node, hSE2l] at hQ2
      first | simp only [Int.zero_add, Int.add_zero] at hQ2 | skip
      rcases hQ2 with (e1 | e2 | e3 | e4)
      · have hp : (a, (b + (2*(2^k : Int)))) = (a, (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e1
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e1))))
      · have hp : (a, ((b + (2*(2^k : Int))) + (2^k : Int))) = (a, (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e2)))))
      · have hp : ((a + (2^k : Int)), (b + (2*(2^k : Int)))) = ((a + (2^k : Int)), (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3))))))
      · have hp : ((a + (2^k : Int)), ((b + (2*(2^k : Int))) + (2^k : Int))) = ((a + (2^k : Int)), (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e4
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e4)))))))
    · rw [mem_toGrid_node, hSE4l] at hQ3
      first | simp only [Int.zero_add, Int.add_zero] at hQ3 | skip
      rcases hQ3 with (e1 | e2 | e3 | e4)
      · have hp : ((a + (2*(2^k : Int))), b) = ((a + (2*(2^k : Int))), b) := by
          congr 1 <;> ring
        rw [hp] at e1
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e1))))))))
      · have hp : ((a + (2*(2^k : Int))), (b + (2^k : Int))) = ((a + (2*(2^k : Int))), (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp] at e2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e2)))))))))
      · have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), b) = ((a + (3*(2^k : Int))), b) := by
          congr 1 <;> ring
        rw [hp] at e3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3))))))))))
      · have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), (b + (2^k : Int))) = ((a + (3*(2^k : Int))), (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp] at e4
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e4)))))))))))
    · rw [mem_toGrid_node, hSE5l] at hQ4
      first | simp only [Int.zero_add, Int.add_zero] at hQ4 | skip
      rcases hQ4 with (e1 | e2 | e3 | e4)
      · have hp : ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) = ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e1
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e1))))))))))))
      · have hp : ((a + (2*(2^k : Int))), ((b + (2*(2^k : Int))) + (2^k : Int))) = ((a + (2*(2^k : Int))), (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e2)))))))))))))
      · have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), (b + (2*(2^k : Int)))) = ((a + (3*(2^k : Int))), (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e3))))))))))))))
      · have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), ((b + (2*(2^k : Int))) + (2^k : Int))) = ((a + (3*(2^k : Int))), (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp] at e4
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e4)))))))))))))))
  · rintro (h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16)
    · have hQ1 : q ∈ (node (subSE r1) (subSW r2) (subNE r4) (subNW r5)).toGrid (a, b) := by
        rw [mem_toGrid_node, hSE1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (a, b) = (a, b) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inl h1
      exact Or.inl hQ1
    · have hQ1 : q ∈ (node (subSE r1) (subSW r2) (subNE r4) (subNW r5)).toGrid (a, b) := by
        rw [mem_toGrid_node, hSE1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (a, (b + (2^k : Int))) = (a, (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inl h2)
      exact Or.inl hQ1
    · have hQ1 : q ∈ (node (subSE r1) (subSW r2) (subNE r4) (subNW r5)).toGrid (a, b) := by
        rw [mem_toGrid_node, hSE1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2^k : Int)), b) = ((a + (2^k : Int)), b) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inl h3))
      exact Or.inl hQ1
    · have hQ1 : q ∈ (node (subSE r1) (subSW r2) (subNE r4) (subNW r5)).toGrid (a, b) := by
        rw [mem_toGrid_node, hSE1l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2^k : Int)), (b + (2^k : Int))) = ((a + (2^k : Int)), (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inr (h4)))
      exact Or.inl hQ1
    · have hQ2 : q ∈ (node (subSE r2) (subSW r3) (subNE r5) (subNW r6)).toGrid (a, (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE2l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (a, (b + (2*(2^k : Int)))) = (a, (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inl h5
      exact Or.inr (Or.inl hQ2)
    · have hQ2 : q ∈ (node (subSE r2) (subSW r3) (subNE r5) (subNW r6)).toGrid (a, (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE2l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (a, ((b + (2*(2^k : Int))) + (2^k : Int))) = (a, (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inl h6)
      exact Or.inr (Or.inl hQ2)
    · have hQ2 : q ∈ (node (subSE r2) (subSW r3) (subNE r5) (subNW r6)).toGrid (a, (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE2l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2^k : Int)), (b + (2*(2^k : Int)))) = ((a + (2^k : Int)), (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inl h7))
      exact Or.inr (Or.inl hQ2)
    · have hQ2 : q ∈ (node (subSE r2) (subSW r3) (subNE r5) (subNW r6)).toGrid (a, (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE2l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2^k : Int)), ((b + (2*(2^k : Int))) + (2^k : Int))) = ((a + (2^k : Int)), (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inr (h8)))
      exact Or.inr (Or.inl hQ2)
    · have hQ3 : q ∈ (node (subSE r4) (subSW r5) (subNE r7) (subNW r8)).toGrid ((a + (2*(2^k : Int))), b) := by
        rw [mem_toGrid_node, hSE4l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2*(2^k : Int))), b) = ((a + (2*(2^k : Int))), b) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inl h9
      exact Or.inr (Or.inr (Or.inl hQ3))
    · have hQ3 : q ∈ (node (subSE r4) (subSW r5) (subNE r7) (subNW r8)).toGrid ((a + (2*(2^k : Int))), b) := by
        rw [mem_toGrid_node, hSE4l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2*(2^k : Int))), (b + (2^k : Int))) = ((a + (2*(2^k : Int))), (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inl h10)
      exact Or.inr (Or.inr (Or.inl hQ3))
    · have hQ3 : q ∈ (node (subSE r4) (subSW r5) (subNE r7) (subNW r8)).toGrid ((a + (2*(2^k : Int))), b) := by
        rw [mem_toGrid_node, hSE4l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), b) = ((a + (3*(2^k : Int))), b) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inl h11))
      exact Or.inr (Or.inr (Or.inl hQ3))
    · have hQ3 : q ∈ (node (subSE r4) (subSW r5) (subNE r7) (subNW r8)).toGrid ((a + (2*(2^k : Int))), b) := by
        rw [mem_toGrid_node, hSE4l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), (b + (2^k : Int))) = ((a + (3*(2^k : Int))), (b + (2^k : Int))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inr (h12)))
      exact Or.inr (Or.inr (Or.inl hQ3))
    · have hQ4 : q ∈ (node (subSE r5) (subSW r6) (subNE r8) (subNW r9)).toGrid ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE5l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) = ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inl h13
      exact Or.inr (Or.inr (Or.inr (hQ4)))
    · have hQ4 : q ∈ (node (subSE r5) (subSW r6) (subNE r8) (subNW r9)).toGrid ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE5l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : ((a + (2*(2^k : Int))), ((b + (2*(2^k : Int))) + (2^k : Int))) = ((a + (2*(2^k : Int))), (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inl h14)
      exact Or.inr (Or.inr (Or.inr (hQ4)))
    · have hQ4 : q ∈ (node (subSE r5) (subSW r6) (subNE r8) (subNW r9)).toGrid ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE5l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), (b + (2*(2^k : Int)))) = ((a + (3*(2^k : Int))), (b + (2*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inl h15))
      exact Or.inr (Or.inr (Or.inr (hQ4)))
    · have hQ4 : q ∈ (node (subSE r5) (subSW r6) (subNE r8) (subNW r9)).toGrid ((a + (2*(2^k : Int))), (b + (2*(2^k : Int)))) := by
        rw [mem_toGrid_node, hSE5l]
        first | simp only [Int.zero_add, Int.add_zero] | skip
        have hp : (((a + (2*(2^k : Int))) + (2^k : Int)), ((b + (2*(2^k : Int))) + (2^k : Int))) = ((a + (3*(2^k : Int))), (b + (3*(2^k : Int)))) := by
          congr 1 <;> ring
        rw [hp]
        exact Or.inr (Or.inr (Or.inr (h16)))
      exact Or.inr (Or.inr (Or.inr (hQ4)))

/-! ### P5-At pas inductif (a) : reduction de la fenetre LHS (grain 3b, partie 5a)

Premiere brique du pas inductif de `hashlifeResultAt_central_correct` :
la fenetre certifiee `[2^(M-1), 2^M)^2` de la sortie mono-ronde du moteur
At (lue a l'ancre `(2^(M-1), 2^(M-1))`, cf la geometrie de la partie 4)
coincide avec le quadrant nord-ouest `Q1` de l'assemblage, c'est-a-dire la
grille du noeud des quatre sous-quadrants `subX r_i` des briques centrales.
Preuve : decomposition 16-voies (partie 4, `k = M - 2`), elimination des
douze placements hors fenetre par bornes inferieures d'etendue
(`grandchild_extent'`) contre des cles de contradiction pre-prouvees
(discipline omega de la partie 3 : aucun omega post-obtention),
conservation des quatre placements de Q1 par `mem_toGrid_node`, pont
d'extensionnalite `Canonical.ext` (miroir de `p4at_ext_bridge`). Les
ascriptions de type ferment l'ecart de coersion `↑(2^(M-1) : Nat)` vs
`(2^(M-1) : Int)` (definitionnellement egaux, verifie par `rfl`). -/

set_option maxHeartbeats 4000000 in
theorem hashlifeResultAt_step_window_nw {M j : Nat} (hj : j + 2 ≤ M)
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : MacroCell)
    (hwf : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).wf = true)
    (ha1l : a1.level = M - 1) :
    restrictGridTo ((hashlifeResultAt j (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4))).toGrid ((2^(M-1) : Nat), (2^(M-1) : Nat)))
        (2^(M-1) : Int) (2^(M-1))
      = (node (subSE (hashlifeResultAt j (node a1 a2 a3 a4)))
              (subSW (hashlifeResultAt j (node a2 b1 a4 b3)))
              (subNE (hashlifeResultAt j (node a3 a4 c1 c2)))
              (subNW (hashlifeResultAt j (node a4 b3 c2 d1)))).toGrid ((2^(M-1) : Nat), (2^(M-1) : Nat)) := by
  have hM2 : 2 ≤ M := by omega
  have keyL : ∀ x : Nat, x = M - 1 → 1 + x = M := by intro x hx; omega
  have keyS : ∀ x : Nat, x = M - 1 → x = (M - 2) + 1 := by intro x hx; omega
  have keyT : ∀ x : Nat, x = (M - 2) + 1 → x = M - 1 := by intro x hx; omega
  have keyLev2 : ∀ x : Nat, x = M - 1 → 1 + (1 + x) = M + 1 := by
    intro x hx; omega
  have hrel : (2^(M-1) : Int) = 2 * (2^(M-2) : Int) := by
    have hM' : M - 1 = (M - 2) + 1 := by omega
    rw [hM', pow_two_succ_eq_int]
  have hB : 0 < (2^(M-2) : Int) := by
    exact_mod_cast (pow_pos (by norm_num : (0 : Nat) < 2) (M - 2))
  have hne : ¬ (M + 1 = j + 2) := by omega
  have keyR2 : ∀ pr : Int, (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ pr →
      pr < (2^(M-1) : Int) + (2^(M-1) : Nat) → False := by
    intro pr hlo hup
    have hup' : pr < (2^(M-1) : Int) + (2^(M-1) : Int) := hup
    omega
  have keyR3 : ∀ pr : Int, (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ pr →
      pr < (2^(M-1) : Int) + (2^(M-1) : Nat) → False := by
    intro pr hlo hup
    have hup' : pr < (2^(M-1) : Int) + (2^(M-1) : Int) := hup
    omega
  have keyC2 : ∀ pc : Int, (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ pc →
      pc < (2^(M-1) : Int) + (2^(M-1) : Nat) → False := by
    intro pc hlo hup
    have hup' : pc < (2^(M-1) : Int) + (2^(M-1) : Int) := hup
    omega
  have keyC3 : ∀ pc : Int, (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ pc →
      pc < (2^(M-1) : Int) + (2^(M-1) : Nat) → False := by
    intro pc hlo hup
    have hup' : pc < (2^(M-1) : Int) + (2^(M-1) : Int) := hup
    omega
  obtain ⟨ha2l, ha3l, ha4l, hb1l, hb2l, hb3l, hb4l, hc1l, hc2l, hc3l, hc4l, hd1l, hd2l, hd3l, hd4l,
          ha1w, ha2w, ha3w, ha4w, hb1w, hb2w, hb3w, hb4w, hc1w, hc2w, hc3w, hc4w, hd1w, hd2w, hd3w, hd4w⟩ :=
    node16_grandchild_facts (k := M - 1) a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4
      d1 d2 d3 d4 hwf ha1l
  have hn1l : ((node a1 a2 a3 a4)).level = M := by
    show 1 + a1.level = M
    exact keyL _ ha1l
  have hn1w : cellWf ((node a1 a2 a3 a4)) :=
    cellWf.node (cellWf_of_wf _ ha1w) (cellWf_of_wf _ ha2w)
      (cellWf_of_wf _ ha3w) (cellWf_of_wf _ ha4w)
      (ha1l.trans ha2l.symm) (ha1l.trans ha3l.symm) (ha1l.trans ha4l.symm)
  have hjn1 : j + 2 ≤ ((node a1 a2 a3 a4)).level := by rw [hn1l]; exact hj
  have hn2l : ((node a2 b1 a4 b3)).level = M := by
    show 1 + a2.level = M
    exact keyL _ ha2l
  have hn2w : cellWf ((node a2 b1 a4 b3)) :=
    cellWf.node (cellWf_of_wf _ ha2w) (cellWf_of_wf _ hb1w)
      (cellWf_of_wf _ ha4w) (cellWf_of_wf _ hb3w)
      (ha2l.trans hb1l.symm) (ha2l.trans ha4l.symm) (ha2l.trans hb3l.symm)
  have hjn2 : j + 2 ≤ ((node a2 b1 a4 b3)).level := by rw [hn2l]; exact hj
  have hn3l : ((node b1 b2 b3 b4)).level = M := by
    show 1 + b1.level = M
    exact keyL _ hb1l
  have hn3w : cellWf ((node b1 b2 b3 b4)) :=
    cellWf.node (cellWf_of_wf _ hb1w) (cellWf_of_wf _ hb2w)
      (cellWf_of_wf _ hb3w) (cellWf_of_wf _ hb4w)
      (hb1l.trans hb2l.symm) (hb1l.trans hb3l.symm) (hb1l.trans hb4l.symm)
  have hjn3 : j + 2 ≤ ((node b1 b2 b3 b4)).level := by rw [hn3l]; exact hj
  have hn4l : ((node a3 a4 c1 c2)).level = M := by
    show 1 + a3.level = M
    exact keyL _ ha3l
  have hn4w : cellWf ((node a3 a4 c1 c2)) :=
    cellWf.node (cellWf_of_wf _ ha3w) (cellWf_of_wf _ ha4w)
      (cellWf_of_wf _ hc1w) (cellWf_of_wf _ hc2w)
      (ha3l.trans ha4l.symm) (ha3l.trans hc1l.symm) (ha3l.trans hc2l.symm)
  have hjn4 : j + 2 ≤ ((node a3 a4 c1 c2)).level := by rw [hn4l]; exact hj
  have hn5l : ((node a4 b3 c2 d1)).level = M := by
    show 1 + a4.level = M
    exact keyL _ ha4l
  have hn5w : cellWf ((node a4 b3 c2 d1)) :=
    cellWf.node (cellWf_of_wf _ ha4w) (cellWf_of_wf _ hb3w)
      (cellWf_of_wf _ hc2w) (cellWf_of_wf _ hd1w)
      (ha4l.trans hb3l.symm) (ha4l.trans hc2l.symm) (ha4l.trans hd1l.symm)
  have hjn5 : j + 2 ≤ ((node a4 b3 c2 d1)).level := by rw [hn5l]; exact hj
  have hn6l : ((node b3 b4 d1 d2)).level = M := by
    show 1 + b3.level = M
    exact keyL _ hb3l
  have hn6w : cellWf ((node b3 b4 d1 d2)) :=
    cellWf.node (cellWf_of_wf _ hb3w) (cellWf_of_wf _ hb4w)
      (cellWf_of_wf _ hd1w) (cellWf_of_wf _ hd2w)
      (hb3l.trans hb4l.symm) (hb3l.trans hd1l.symm) (hb3l.trans hd2l.symm)
  have hjn6 : j + 2 ≤ ((node b3 b4 d1 d2)).level := by rw [hn6l]; exact hj
  have hn7l : ((node c1 c2 c3 c4)).level = M := by
    show 1 + c1.level = M
    exact keyL _ hc1l
  have hn7w : cellWf ((node c1 c2 c3 c4)) :=
    cellWf.node (cellWf_of_wf _ hc1w) (cellWf_of_wf _ hc2w)
      (cellWf_of_wf _ hc3w) (cellWf_of_wf _ hc4w)
      (hc1l.trans hc2l.symm) (hc1l.trans hc3l.symm) (hc1l.trans hc4l.symm)
  have hjn7 : j + 2 ≤ ((node c1 c2 c3 c4)).level := by rw [hn7l]; exact hj
  have hn8l : ((node c2 d1 c4 d3)).level = M := by
    show 1 + c2.level = M
    exact keyL _ hc2l
  have hn8w : cellWf ((node c2 d1 c4 d3)) :=
    cellWf.node (cellWf_of_wf _ hc2w) (cellWf_of_wf _ hd1w)
      (cellWf_of_wf _ hc4w) (cellWf_of_wf _ hd3w)
      (hc2l.trans hd1l.symm) (hc2l.trans hc4l.symm) (hc2l.trans hd3l.symm)
  have hjn8 : j + 2 ≤ ((node c2 d1 c4 d3)).level := by rw [hn8l]; exact hj
  have hn9l : ((node d1 d2 d3 d4)).level = M := by
    show 1 + d1.level = M
    exact keyL _ hd1l
  have hn9w : cellWf ((node d1 d2 d3 d4)) :=
    cellWf.node (cellWf_of_wf _ hd1w) (cellWf_of_wf _ hd2w)
      (cellWf_of_wf _ hd3w) (cellWf_of_wf _ hd4w)
      (hd1l.trans hd2l.symm) (hd1l.trans hd3l.symm) (hd1l.trans hd4l.symm)
  have hjn9 : j + 2 ≤ ((node d1 d2 d3 d4)).level := by rw [hn9l]; exact hj
  obtain ⟨hres1l, hres1w⟩ := hashlifeResultAt_level_cellWf j ((node a1 a2 a3 a4)) hn1w hjn1
  rw [hn1l] at hres1l
  obtain ⟨hres2l, hres2w⟩ := hashlifeResultAt_level_cellWf j ((node a2 b1 a4 b3)) hn2w hjn2
  rw [hn2l] at hres2l
  obtain ⟨hres3l, hres3w⟩ := hashlifeResultAt_level_cellWf j ((node b1 b2 b3 b4)) hn3w hjn3
  rw [hn3l] at hres3l
  obtain ⟨hres4l, hres4w⟩ := hashlifeResultAt_level_cellWf j ((node a3 a4 c1 c2)) hn4w hjn4
  rw [hn4l] at hres4l
  obtain ⟨hres5l, hres5w⟩ := hashlifeResultAt_level_cellWf j ((node a4 b3 c2 d1)) hn5w hjn5
  rw [hn5l] at hres5l
  obtain ⟨hres6l, hres6w⟩ := hashlifeResultAt_level_cellWf j ((node b3 b4 d1 d2)) hn6w hjn6
  rw [hn6l] at hres6l
  obtain ⟨hres7l, hres7w⟩ := hashlifeResultAt_level_cellWf j ((node c1 c2 c3 c4)) hn7w hjn7
  rw [hn7l] at hres7l
  obtain ⟨hres8l, hres8w⟩ := hashlifeResultAt_level_cellWf j ((node c2 d1 c4 d3)) hn8w hjn8
  rw [hn8l] at hres8l
  obtain ⟨hres9l, hres9w⟩ := hashlifeResultAt_level_cellWf j ((node d1 d2 d3 d4)) hn9w hjn9
  rw [hn9l] at hres9l
  have hSE1 := subSE_level_cellWf (m := M - 2) hres1w (keyS _ hres1l)
  have hSW2 := subSW_level_cellWf (m := M - 2) hres2w (keyS _ hres2l)
  have hNE4 := subNE_level_cellWf (m := M - 2) hres4w (keyS _ hres4l)
  have hNW5 := subNW_level_cellWf (m := M - 2) hres5w (keyS _ hres5l)
  have hSE2 := subSE_level_cellWf (m := M - 2) hres2w (keyS _ hres2l)
  have hSW3 := subSW_level_cellWf (m := M - 2) hres3w (keyS _ hres3l)
  have hNE5 := subNE_level_cellWf (m := M - 2) hres5w (keyS _ hres5l)
  have hNW6 := subNW_level_cellWf (m := M - 2) hres6w (keyS _ hres6l)
  have hSE4 := subSE_level_cellWf (m := M - 2) hres4w (keyS _ hres4l)
  have hSW5 := subSW_level_cellWf (m := M - 2) hres5w (keyS _ hres5l)
  have hNE7 := subNE_level_cellWf (m := M - 2) hres7w (keyS _ hres7l)
  have hNW8 := subNW_level_cellWf (m := M - 2) hres8w (keyS _ hres8l)
  have hSE5 := subSE_level_cellWf (m := M - 2) hres5w (keyS _ hres5l)
  have hSW6 := subSW_level_cellWf (m := M - 2) hres6w (keyS _ hres6l)
  have hNE8 := subNE_level_cellWf (m := M - 2) hres8w (keyS _ hres8l)
  have hNW9 := subNW_level_cellWf (m := M - 2) hres9w (keyS _ hres9l)
  obtain ⟨hQ1l', hQ1w⟩ := node4_level_cellWf hSE1.1 hSW2.1 hNE4.1 hNW5.1
    hSE1.2 hSW2.2 hNE4.2 hNW5.2
  have hQ1l : (node (subSE (hashlifeResultAt j (node a1 a2 a3 a4)))
              (subSW (hashlifeResultAt j (node a2 b1 a4 b3)))
              (subNE (hashlifeResultAt j (node a3 a4 c1 c2)))
              (subNW (hashlifeResultAt j (node a4 b3 c2 d1)))).level = M - 1 := keyT _ hQ1l'
  have hrw1 : hashlifeResultAtAux M j ((node a1 a2 a3 a4)) = hashlifeResultAt j ((node a1 a2 a3 a4)) := by
    unfold hashlifeResultAt
    rw [hn1l]
  have hrw2 : hashlifeResultAtAux M j ((node a2 b1 a4 b3)) = hashlifeResultAt j ((node a2 b1 a4 b3)) := by
    unfold hashlifeResultAt
    rw [hn2l]
  have hrw3 : hashlifeResultAtAux M j ((node b1 b2 b3 b4)) = hashlifeResultAt j ((node b1 b2 b3 b4)) := by
    unfold hashlifeResultAt
    rw [hn3l]
  have hrw4 : hashlifeResultAtAux M j ((node a3 a4 c1 c2)) = hashlifeResultAt j ((node a3 a4 c1 c2)) := by
    unfold hashlifeResultAt
    rw [hn4l]
  have hrw5 : hashlifeResultAtAux M j ((node a4 b3 c2 d1)) = hashlifeResultAt j ((node a4 b3 c2 d1)) := by
    unfold hashlifeResultAt
    rw [hn5l]
  have hrw6 : hashlifeResultAtAux M j ((node b3 b4 d1 d2)) = hashlifeResultAt j ((node b3 b4 d1 d2)) := by
    unfold hashlifeResultAt
    rw [hn6l]
  have hrw7 : hashlifeResultAtAux M j ((node c1 c2 c3 c4)) = hashlifeResultAt j ((node c1 c2 c3 c4)) := by
    unfold hashlifeResultAt
    rw [hn7l]
  have hrw8 : hashlifeResultAtAux M j ((node c2 d1 c4 d3)) = hashlifeResultAt j ((node c2 d1 c4 d3)) := by
    unfold hashlifeResultAt
    rw [hn8l]
  have hrw9 : hashlifeResultAtAux M j ((node d1 d2 d3 d4)) = hashlifeResultAt j ((node d1 d2 d3 d4)) := by
    unfold hashlifeResultAt
    rw [hn9l]
  have hlev : (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)).level = M + 1 :=
    keyLev2 _ ha1l
  have hunf : hashlifeResultAt j (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)) =
      hashlifeResultAtAux (M + 1) j (node (node a1 a2 a3 a4) (node b1 b2 b3 b4)
             (node c1 c2 c3 c4) (node d1 d2 d3 d4)) := by
    unfold hashlifeResultAt
    rw [hlev]
  rw [hunf, hashlifeResultAtAux_succ_node_at, hlev]
  rw [if_neg (by simp only [beq_iff_eq]; exact hne)]
  rw [hrw1, hrw2, hrw3, hrw4, hrw5, hrw6, hrw7, hrw8, hrw9]
  refine Canonical.ext ?_ (canonical_toGrid _ _) ?_
  · unfold restrictGridTo
    exact (canonical_toGrid _ _).filter _
  · intro p
    constructor
    · intro hpw
      obtain ⟨hout, hlo1, hup1, hlo2, hup2⟩ := mem_restrictGridTo.mp hpw
      rcases (out16_toGrid_mem (k := M - 2)
          (hashlifeResultAt j (node a1 a2 a3 a4))
          (hashlifeResultAt j (node a2 b1 a4 b3))
          (hashlifeResultAt j (node b1 b2 b3 b4))
          (hashlifeResultAt j (node a3 a4 c1 c2))
          (hashlifeResultAt j (node a4 b3 c2 d1))
          (hashlifeResultAt j (node b3 b4 d1 d2))
          (hashlifeResultAt j (node c1 c2 c3 c4))
          (hashlifeResultAt j (node c2 d1 c4 d3))
          (hashlifeResultAt j (node d1 d2 d3 d4))
          (wf_of_cellWf hres1w) (keyS _ hres1l)
          (wf_of_cellWf hres2w) (keyS _ hres2l)
          (wf_of_cellWf hres3w) (keyS _ hres3l)
          (wf_of_cellWf hres4w) (keyS _ hres4l)
          (wf_of_cellWf hres5w) (keyS _ hres5l)
          (wf_of_cellWf hres6w) (keyS _ hres6l)
          (wf_of_cellWf hres7w) (keyS _ hres7l)
          (wf_of_cellWf hres8w) (keyS _ hres8l)
          (wf_of_cellWf hres9w) (keyS _ hres9l)
          (2^(M-1) : Nat) (2^(M-1) : Nat) p).mp hout with
        (e1 | e2 | e3 | e4 | e5 | e6 | e7 | e8 | e9 | e10 | e11 | e12 | e13 | e14 | e15 | e16)
      ·
        rw [mem_toGrid_node, hSE1.1]
        exact Or.inl e1
      ·
        rw [mem_toGrid_node, hSE1.1]
        exact Or.inr (Or.inl e2)
      ·
        rw [mem_toGrid_node, hSE1.1]
        exact Or.inr (Or.inr (Or.inl e3))
      ·
        rw [mem_toGrid_node, hSE1.1]
        exact Or.inr (Or.inr (Or.inr (e4)))
      ·
        have hx := grandchild_extent' (subSE (hashlifeResultAt j (node a2 b1 a4 b3))) (2^(M-1) : Nat) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) p hSE2.1
          (wf_of_cellWf hSE2.2) e5
        exact (keyC2 p.2 (hx.2.2.1 : (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ p.2) hup2).elim
      ·
        have hx := grandchild_extent' (subSW (hashlifeResultAt j (node b1 b2 b3 b4))) (2^(M-1) : Nat) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) p hSW3.1
          (wf_of_cellWf hSW3.2) e6
        exact (keyC3 p.2 (hx.2.2.1 : (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ p.2) hup2).elim
      ·
        have hx := grandchild_extent' (subNE (hashlifeResultAt j (node a4 b3 c2 d1))) ((2^(M-1) : Nat) + (2^(M-2) : Int)) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) p hNE5.1
          (wf_of_cellWf hNE5.2) e7
        exact (keyC2 p.2 (hx.2.2.1 : (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ p.2) hup2).elim
      ·
        have hx := grandchild_extent' (subNW (hashlifeResultAt j (node b3 b4 d1 d2))) ((2^(M-1) : Nat) + (2^(M-2) : Int)) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) p hNW6.1
          (wf_of_cellWf hNW6.2) e8
        exact (keyC3 p.2 (hx.2.2.1 : (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ p.2) hup2).elim
      ·
        have hx := grandchild_extent' (subSE (hashlifeResultAt j (node a3 a4 c1 c2))) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) (2^(M-1) : Nat) p hSE4.1
          (wf_of_cellWf hSE4.2) e9
        exact (keyR2 p.1 (hx.1 : (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ p.1) hup1).elim
      ·
        have hx := grandchild_extent' (subSW (hashlifeResultAt j (node a4 b3 c2 d1))) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) ((2^(M-1) : Nat) + (2^(M-2) : Int)) p hSW5.1
          (wf_of_cellWf hSW5.2) e10
        exact (keyR2 p.1 (hx.1 : (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ p.1) hup1).elim
      ·
        have hx := grandchild_extent' (subNE (hashlifeResultAt j (node c1 c2 c3 c4))) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) (2^(M-1) : Nat) p hNE7.1
          (wf_of_cellWf hNE7.2) e11
        exact (keyR3 p.1 (hx.1 : (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ p.1) hup1).elim
      ·
        have hx := grandchild_extent' (subNW (hashlifeResultAt j (node c2 d1 c4 d3))) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) ((2^(M-1) : Nat) + (2^(M-2) : Int)) p hNW8.1
          (wf_of_cellWf hNW8.2) e12
        exact (keyR3 p.1 (hx.1 : (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ p.1) hup1).elim
      ·
        have hx := grandchild_extent' (subSE (hashlifeResultAt j (node a4 b3 c2 d1))) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) p hSE5.1
          (wf_of_cellWf hSE5.2) e13
        exact (keyR2 p.1 (hx.1 : (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ p.1) hup1).elim
      ·
        have hx := grandchild_extent' (subSW (hashlifeResultAt j (node b3 b4 d1 d2))) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) p hSW6.1
          (wf_of_cellWf hSW6.2) e14
        exact (keyR2 p.1 (hx.1 : (2^(M-1) : Int) + 2 * (2^(M-2) : Int) ≤ p.1) hup1).elim
      ·
        have hx := grandchild_extent' (subNE (hashlifeResultAt j (node c2 d1 c4 d3))) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) ((2^(M-1) : Nat) + (2*(2^(M-2) : Int))) p hNE8.1
          (wf_of_cellWf hNE8.2) e15
        exact (keyR3 p.1 (hx.1 : (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ p.1) hup1).elim
      ·
        have hx := grandchild_extent' (subNW (hashlifeResultAt j (node d1 d2 d3 d4))) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) ((2^(M-1) : Nat) + (3*(2^(M-2) : Int))) p hNW9.1
          (wf_of_cellWf hNW9.2) e16
        exact (keyR3 p.1 (hx.1 : (2^(M-1) : Int) + 3 * (2^(M-2) : Int) ≤ p.1) hup1).elim
    · intro hpq1
      have hext := mem_toGrid_extent (node (subSE (hashlifeResultAt j (node a1 a2 a3 a4)))
              (subSW (hashlifeResultAt j (node a2 b1 a4 b3)))
              (subNE (hashlifeResultAt j (node a3 a4 c1 c2)))
              (subNW (hashlifeResultAt j (node a4 b3 c2 d1)))) (2^(M-1) : Nat) (2^(M-1) : Nat) p
        (wf_of_cellWf hQ1w) hpq1
      rw [hQ1l] at hext
      have hout : p ∈ (node (node (subSE (hashlifeResultAt j (node a1 a2 a3 a4)))
              (subSW (hashlifeResultAt j (node a2 b1 a4 b3)))
              (subNE (hashlifeResultAt j (node a3 a4 c1 c2)))
              (subNW (hashlifeResultAt j (node a4 b3 c2 d1))))
        (node (subSE (hashlifeResultAt j (node a2 b1 a4 b3)))
              (subSW (hashlifeResultAt j (node b1 b2 b3 b4)))
              (subNE (hashlifeResultAt j (node a4 b3 c2 d1)))
              (subNW (hashlifeResultAt j (node b3 b4 d1 d2))))
        (node (subSE (hashlifeResultAt j (node a3 a4 c1 c2)))
              (subSW (hashlifeResultAt j (node a4 b3 c2 d1)))
              (subNE (hashlifeResultAt j (node c1 c2 c3 c4)))
              (subNW (hashlifeResultAt j (node c2 d1 c4 d3))))
        (node (subSE (hashlifeResultAt j (node a4 b3 c2 d1)))
              (subSW (hashlifeResultAt j (node b3 b4 d1 d2)))
              (subNE (hashlifeResultAt j (node c2 d1 c4 d3)))
              (subNW (hashlifeResultAt j (node d1 d2 d3 d4))))).toGrid ((2^(M-1) : Nat), (2^(M-1) : Nat)) := by
        rw [mem_toGrid_node]
        exact Or.inl hpq1
      exact mem_restrictGridTo.mpr ⟨hout,
        (hext.1 : (2^(M-1) : Int) ≤ p.1),
        hext.2.1.trans_eq (Int.add_comm _ _),
        (hext.2.2.1 : (2^(M-1) : Int) ≤ p.2),
        hext.2.2.2.trans_eq (Int.add_comm _ _)⟩

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

/-! ## N3 decorrelated-reach engine: fuel skeleton (#11161, grain 2)

Adaptation du squelette P5.1 (`evolveHashlifeFastAux_correct`) au moteur
a portee decorrele `evolveHashlifeFastAtAuxN` (Hashlife.lean). Deux
differences structurelles : l'hypothese de capture TRAJECTOIRE
disparait (la brique un-saut `OneJumpAtCorrect` est universellement
quantifiee, la re-instantiation en `t + js` est gratuite), et le garde
decorrele est VIABLE (temoins ci-dessous). Le contenu ouvert restant est la
correction P4-At de `hashlifeResultAt` (recursion mono-ronde) — portee
par l'hypothese, a decharger au grain 3 (voir #11161). -/

/-- **Hypothese P4-At (brique un-saut a portee decorrelee, grain 2 #11161).**
    Pour tout re-cadrage conscient de n dont le niveau est au moins 2
    (i.e. tout etat ou le garde de saut de `evolveHashlifeFastAtAuxN`
    tire), le saut decorrele calcule exactement `evolve (jumpSizeAt lvl) g`
    sur la grille, avec la comptabilite de decalage `jumpResultOff`. C'est
    l'analogique At de la brique un-saut `one_jump_toGrid_correct` (P5.1),
    avec une difference structurelle : PLUS d'hypothese de capture —
    `jumpAt_capture_centered` rend la capture corollaire de l'invariant du
    cadre (grain 1, #11161). Le contenu encore ouvert est la correction
    P4-At de `hashlifeResultAt` elle-meme (recursion mono-ronde ; note
    d'honnetete du meme nom dans Hashlife.lean) — portee ici par
    l'hypothese, a decharger au grain 3. -/
def OneJumpAtCorrect : Prop :=
  ∀ (n : Nat) (g : Grid),
    2 ≤ (gridToMacroCellWithOffsetN n g).2.level →
      (hashlifeJumpAt ((gridToMacroCellWithOffsetN n g).2.level - 2)
          (gridToMacroCellWithOffsetN n g).2).toGrid
        (jumpResultOff (gridToMacroCellWithOffsetN n g).1
          (gridToMacroCellWithOffsetN n g).2.level)
        = evolve (jumpSizeAt (gridToMacroCellWithOffsetN n g).2.level) g

/-- **Grain 2 (#11161) : squelette d'induction fuel du moteur decorrele.**
    Sous la brique un-saut `OneJumpAtCorrect`, pour tout `fuel >= n`,
    `evolveHashlifeFastAtAuxN fuel n g = evolve n g`. L'induction est
    l'adaptation de `evolveHashlifeFastAux_correct` (P5.1) avec deux
    simplifications structurelles : (1) l'hypothese de capture
    TRAJECTOIRE disparaît — `OneJumpAtCorrect` est universellement
    quantifiee, donc la re-instantiation de l'hypothese en `t + js` est
    gratuite ; (2) l'invariant `n <= fuel` se preserve car le saut
    consomme `js = 2^(lvl-2) >= 1` generations pour 1 unite de fuel. Le
    bras `else` rend litteralement `evolve n g`. Aucun sorry. -/
theorem evolveHashlifeFastAtAuxN_correct (hbr : OneJumpAtCorrect)
    (fuel n : Nat) (g : Grid) (hle : n ≤ fuel) :
    evolveHashlifeFastAtAuxN fuel n g = evolve n g := by
  induction fuel generalizing n g with
  | zero =>
    have hn0 : n = 0 := Nat.le_zero.mp hle
    subst hn0
    rfl
  | succ fuel ih =>
    cases n with
    | zero => rfl
    | succ m =>
      simp only [evolveHashlifeFastAtAuxN]
      split
      · next hcond =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        obtain ⟨hlvl2, hnjs⟩ := hcond
        have hjspo : 0 < jumpSizeAt
            (gridToMacroCellWithOffsetN (m + 1) g).2.level :=
          Nat.two_pow_pos _
        have hle' : m + 1 - jumpSizeAt (gridToMacroCellWithOffsetN (m + 1) g).2.level
            ≤ fuel := by omega
        rw [hbr (m + 1) g hlvl2,
            ih (m + 1 - jumpSizeAt (gridToMacroCellWithOffsetN (m + 1) g).2.level)
              (evolve (jumpSizeAt (gridToMacroCellWithOffsetN (m + 1) g).2.level) g)
              hle',
            ← evolve_add]
        have hsum : (m + 1 - jumpSizeAt (gridToMacroCellWithOffsetN (m + 1) g).2.level)
            + jumpSizeAt (gridToMacroCellWithOffsetN (m + 1) g).2.level = m + 1 := by
          omega
        rw [hsum]
      · rfl

/-- **Grain 2 (#11161) : correction conditionnelle de l'API publique.**
    Sous la meme unique hypothese, `evolveHashlifeFastAtN n g = evolve n g`
    pour TOUT n et TOUTE grille — la portee du theoreme n'est plus bornee
    par une hypothese de capture. Dechargee au grain 3 : `OneJumpAtCorrect`
    suit de l'invariant du cadre (grain 1) + la correction P4-At de
    `hashlifeResultAt`. -/
theorem evolveHashlifeFastAtN_correct (hbr : OneJumpAtCorrect)
    (n : Nat) (g : Grid) :
    evolveHashlifeFastAtN n g = evolve n g :=
  evolveHashlifeFastAtAuxN_correct hbr n n g (Nat.le_refl n)

/-- Témoin d'échappement : ligne de 7 cellules (grille de `lineCell3`,
    `jumpCaptured_not_trivial` en JumpCapture) — son burst transitoire
    atteint le bord de toute fenêtre FIXE à la génération 8. Sur le moteur
    décorrélé n-aware, la même grille est capturée (rembourrage
    `max 2 n`). -/
def line7 : Grid := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6)]

-- Témoin 1 (acceptance #11161) : glider à n = 8 — le garde décorrélé tire
-- (guardAt_viable_glider), un saut de jumpSizeAt 5 = 8.
#eval evolveHashlifeFastAtN 8 glider == evolve 8 glider

-- Témoin 2 : blinker à n = 8 — oscillateur période 2, un saut.
#eval evolveHashlifeFastAtN 8 blinker_h == evolve 8 blinker_h

-- Témoin 3 (acceptance #11161) : la ligne de 7 qui falsifiait le moteur
-- plein doit PASSER sur le moteur décorrélé (re-cadrage n-aware).
#eval evolveHashlifeFastAtN 8 line7 == evolve 8 line7

-- Témoin 4 : glider à n = 12 — DEUX sauts décorrélés (js = 8, reste 4,
-- nouveau cadre lvl 4 → js' = 4), exercice du bras récursif multi-sauts.
#eval evolveHashlifeFastAtN 12 glider == evolve 12 glider

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
