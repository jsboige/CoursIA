# KB v5 Recommendations — Prover Forensic Consolidation (Cycle 77)

**Date:** 2026-05-20
**Author:** po-2026 (from ai-01 dispatch msg-20260519T201323-061d3z)
**Baseline:** KB v4 (`proof_knowledge.json` version 3, `proven_successful_tactics` + `wall_clock_burn_patterns`)

## Forensic Summary (Cycles 74-77)

### What works (validated in production)
- **F12 Director force-invocation** (workflow.py:108-124): Guarantees Director call at iter 4. Multi-agent prover with Sonnet Coordinator calls Director naturally at ~809s, validating F12 architecture.
- **B2a absent-identifier injection**: Director flags dead-end identifiers → TacticAgent gets WARNING block. Reduced hallucinated attempts from 3-5/session to 0-1.
- **B2c cumulative fail counter**: Never resets on decomposition, forces Director re-escalade at threshold 5. Prevents infinite decomposition loops.
- **B3 constructive existential heuristic**: `try_constructive_existential()` regex-parses ∃ goals, scans for constructors. Wired into CoordinatorAgent fallback chain.
- **`proven_successful_tactics` injection**: KB v4 winning tactic chains injected into all agent instructions via `augment_instructions()`.

### What doesn't work (validated failures)
- **GLM-5.1 Coordinator timeout**: Systematic 12+ min on complex Lean contexts (Lattice.lean L324). Issue #1289 open for replacement.
- **L324 INTRACTABLE**: Cross-pair stability constraints involving unknown men (μ⁻¹(w₂)/ν⁻¹(w₁)) block local contradiction. Requires rural hospitals / global decomposition lemma. Confirmed across Sprint C+D (5+ sessions).
- **SearchAgent reasoning burn**: Qwen3.6 consumes 80-100% output budget in `reasoning_content` before producing visible text. 16384 max_tokens bump insufficient for tool-call tasks. Non-reasoning variant recommended.

## v5 Recommendations

### R1: Add Lemmas.lean winning tactics to KB (PATCH — no code change)
**Priority:** HIGH | **Effort:** 15 min | **Impact:** Enriches Director/Coordinator context

Add 3 new entries to `proven_successful_tactics` in `proof_knowledge.json`:
- `gsFinalMatching`: partial→total matching conversion (pigeonhole + Finset.card_biUnion)
- `gsAllWomenMatched`: all women matched in terminated state (Fintype.card + Finset.sum_card_inter)
- `gsNoBlockingPairs`: 6-step contradiction chain (stable → blocking pair → absurd)

These were proved in PR #1194 (2026-05-16) but never added to KB.

### R2: SearchAgent model downgrade (PATCH — config.py)
**Priority:** MEDIUM | **Effort:** 30 min | **Impact:** Prevents reasoning-content burn

Add `"fast"` model key for SearchAgent using a non-reasoning Qwen variant:
```python
# In config.py MODEL_CONFIGS:
"zai": {
    ...
    "fast": os.getenv("LOCAL_FAST_MODEL_ID", "qwen3-35b"),  # non-reasoning for tool calls
}
# In agents.py: SearchAgent uses model_key="fast"
```

### R3: Director wall-clock trigger (ALREADY IMPLEMENTED — F8)
**Status:** Implemented in workflow.py via VerifyExecutor. B2c + F8 + F12 provide triple escalation. No additional work needed.

### R4: Coordinator model replacement (DEPENDS ON ISSUE #1289)
**Priority:** HIGH | **Effort:** External decision | **Impact:** Prevents systematic timeout

GLM-5.1 is insufficient for complex Lean contexts. Options:
- Sonnet 4.6 (2x faster per ai-01 forensic, but costly)
- GPT-5.5 via OpenRouter (already available, untested as Coordinator)
- Await Claude Haiku 4.5 (fast + cheap, if Lean-capable)

Decision belongs to user/ai-01 per Issue #1289.

### R5: Proof targets — INTRACTABLE classification

| File | Line | Target | Blocker | Classification |
|------|------|--------|---------|----------------|
| Basic.lean | L308 | hCore (G.Core.Nonempty) | Hyperplane separation for proper cones | INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION |
| GaleShapley.lean | L97 | gale_shapley_man_optimal | Man-optimal witness from GS algorithm | INTRACTABLE_UNTIL_RURAL_HOSPITALS |
| GaleShapley.lean | L125 | gale_shapley_woman_pessimal | Knuth 1976 lattice duality | INTRACTABLE_UNTIL_RURAL_HOSPITALS |
| Lattice.lean | L324 | meetSpouse "different women" | Rural hospitals for n≥3 | INTRACTABLE_UNTIL_RURAL_HOSPITALS |
| Lattice.lean | L387 | meetSpouse symmetric cross-case | Same as L324 | INTRACTABLE_UNTIL_RURAL_HOSPITALS |
| Lattice.lean | L727 | doctor_optimal_eq_top | GS algorithm witness | INTRACTABLE_UNTIL_RURAL_HOSPITALS |

### R6: Proof targets — ACTIONABLE (next prover sessions)

These are not INTRACTABLE and should be attempted:
1. **Basic.lean hP_nonempty + hK_empty** (PR #1161 OPEN): already proved, needs rebase + merge
2. **Lattice.lean join_inverse_anti** (proved in Sprint D, PR #1292 MERGED)
3. **Any new targets from Mathlib/Conway expansion** (see below)

## Conway Tribute — CGT Targets

### Current state (VERIFIED)
- `GameTheory/conway_lean/` exists with 3 "noix" COMPLETE (0 sorry):
  - Doomsday.lean: Conway's day-of-week algorithm
  - LookAndSay.lean: Look-and-say sequence + Conway's constant
  - Fractran.lean: FRACTRAN universal machine
- Issue #1151 CLOSED (original spec had Penney's game + Conway's Soldiers; implementation pivoted)

### Next CGT targets (ordered by feasibility)
1. **Penney's game / Conway's leading number** (medium, 3-5 days): Expected toss count for pattern matching. Probabilistic, uses Fin n coin flips. Issue #1151 Noix 2 originally.
2. **Sprague-Grundy theorem** (hard, 1-2 weeks): Every impartial game ≈ nimber. Foundation of CGT. Requires `PGame` or `SimpleGame` type.
3. **Surreal numbers** (very hard, 2-4 weeks): Conway construction via left/right set pairs. Partially in Mathlib (`Mathlib.SetTheory.Surreal`).
4. **Conway's Soldiers** (legendary, 2+ weeks): Impossibility of reaching line 5 via golden ratio Lyapunov function. Issue #1151 Noix 3 originally.

## Mathlib Beta — Complementary Theorems

### Relevant Mathlib modules (NOT in beta releases, but stable)
1. `Mathlib.Analysis.Convex.Cone.Dual` — `ProperCone.hyperplane_separation` (for Bondareva hCore)
2. `Mathlib.Combinatorics.SimpleGraph.Matching` — `IsPerfectMatching` (for Knuth lattice infrastructure)
3. `Mathlib.Combinatorics.Hall.Basic` — Hall's marriage theorem (for GS termination)
4. `Mathlib.Combinatorics.SimpleGraph.Tutte` — Tutte's theorem (generalizes Hall)
5. `Mathlib.Data.Set.Lattice` — Birkhoff representation (for Knuth lattice duality)

### External repos (Lean 4, actively maintained)
1. **`mmaaz-git/stable-marriage-lean`**: Full GS formalization with incomplete preferences. May contain proof strategies for our remaining sorrys.
2. **`DominikPeters/SocialChoiceLean`**: Comprehensive voting theory (Gibbard-Satterthwaite, Duggan-Schwartz, Split Cycle). Extends beyond our Arrow/Sen/Voting.

### No new beta content for our domain
v4.29.1 → v4.30.0-rc2 diff touches zero files in Combinatorics, Convex, Cone, or Matching modules.
