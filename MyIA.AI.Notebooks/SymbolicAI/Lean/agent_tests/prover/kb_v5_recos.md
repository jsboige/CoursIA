# KB v5 Recommendations — Prover Forensic Consolidation (Cycle 77)

**Date:** 2026-05-20
**Author:** po-2026 (from ai-01 dispatch msg-20260519T201323-061d3z)
**Baseline:** KB v4 (`proof_knowledge.json` version 3, `proven_successful_tactics` + `wall_clock_burn_patterns`)

## Status (reassessed c.311, 2026-07-11) — L143 G.1 archival

**All R1–R6 recommendations have been actioned.** Forensic re-verification on
2026-07-11 (cycle c.311) confirms every R-reco below has been resolved in the
~2 months since this doc was written. This file is retained for forensic
reference of the **what-works / what-doesn't** summary (cycles 74-77)
and the **R5 INTRACTABLE table** (proof that those gates were correctly
classified as open-at-time-of-doc, then closed). **Do NOT use as a current
todo list** — see `proof_knowledge.json` + recent commit history for live state.

| Reco | Original priority | Closing evidence | Date |
|------|-------------------|------------------|------|
| R1: Lemmas.lean tactics → KB | HIGH (15 min) | `proven_successful_tactics` keys `gsFinalMatching` / `gsAllWomenMatched` / `gsNoBlockingPairs` already present, commit `23e41056` (PR #1194) | 2026-05-15–16 |
| R2: SearchAgent `fast` model | MEDIUM (30 min) | `config.py` `MODEL_CONFIGS` already exposes `fast` for z.ai (`glm-5.1`), local (`qwen3.6-35b-a3b`), openrouter (`claude-haiku-4.5`), mistral (`labs-leanstral-1-5`) | by 2026-05-21 |
| R3: Director wall-clock trigger | (F8) | `workflow.py:278` `F12` force-Director at iter 4 + B2c cumulative-fail counter wired | already done at doc-writing time |
| R4: Coordinator model replace | HIGH (external) | Issue #1289 CLOSED 2026-05-21 via PR #1394 + PR #1398 (Sonnet 4.6 Coordinator retained per Sprint D verdict) | 2026-05-21 |
| R5 INTRACTABLE table | — | **All 5 targets now 0-sorry.** See below. | by 2026-05-19 |
| R6 #1 (Basic.lean hP_nonempty+hK_empty) | — | PR #1161 MERGED 2026-05-15 (sorry 3→1) | 2026-05-15 |
| R6 #2 (Lattice.lean join_inverse_anti) | — | PR #1292 MERGED 2026-05-19 | 2026-05-19 |

### R5 INTRACTABLE — closure table (L143 G.1 verified 2026-07-11)

| File | Original target | Status now | Closing PR |
|------|-----------------|------------|------------|
| Basic.lean L308 | `hCore (G.Core.Nonempty)` | RESOLVED (sorry 1→0) | #3954 (`feat(lean): prove Bondareva-Shapley attainment crux`) |
| GaleShapley.lean L97 | `gale_shapley_man_optimal` | RESOLVED | #1452 (anti-crossing fragment via `no_cross_match`) + #1530 |
| GaleShapley.lean L125 | `gale_shapley_woman_pessimal` | RESOLVED | #1335 (`feat(lean): prove gale_shapley_woman_pessimal + Lean-8/9 end-exercises`) |
| Lattice.lean L324 | `meetSpouse` "different women" | REMOVED FROM FILE (was renamed `meetSpouse_injective` and proved via `no_cross_match`) | #1452 (`feat(lean): prove meetSpouse injective cross-case via no_cross_match`) |
| Lattice.lean L387 | `meetSpouse` symmetric cross-case | Same — consolidated with L324 proof | #1452 (same PR) |
| Lattice.lean L727 | `doctor_optimal_eq_top` | RESOLVED via `IsManOptimal` hypothesis (#2499 scaffolding → #1530 consolidation) | #1530 (`feat(lean): consolidate StableMarriage proofs — sorry 5→3`) |

**Lesson L143 / G.1 (this reassessment):** Doc-staleness check on
`kb_v5_recos.md` took ~5 min (`grep` on current `proof_knowledge.json` +
`grep -cE "^\s*(sorry|admit)"` on the 3 R5 files + 1 `gh` for each
referenced PR). Without this pass, a future worker would have spent time
on "INTRACTABLE until Bondareva hyperplane separation" / "INTRACTABLE
until rural hospitals" gates that **no longer exist**. The doc's value
post-c.311 is **forensic**: it captures the **classification method** that
proved correct (5/5 targets were right to defer, all 5 closed in <2 months),
not the **state** of the targets themselves.

---

## Forensic Summary (Cycles 74-77) — HISTORICAL REFERENCE

## Forensic Summary (Cycles 74-77)

### What works (validated in production)
- **F12 Director force-invocation** (workflow.py:108-124): Guarantees Director call at iter 4. Multi-agent prover with Sonnet Coordinator calls Director naturally at ~809s, validating F12 architecture.
- **B2a absent-identifier injection**: Director flags dead-end identifiers → TacticAgent gets WARNING block. Reduced hallucinated attempts from 3-5/session to 0-1.
- **B2c cumulative fail counter**: Never resets on decomposition, forces Director re-escalade at threshold 5. Prevents infinite decomposition loops.
- **B3 constructive existential heuristic**: `try_constructive_existential()` regex-parses ∃ goals, scans for constructors. Wired into CoordinatorAgent fallback chain.
- **`proven_successful_tactics` injection**: KB v4 winning tactic chains injected into all agent instructions via `augment_instructions()`.

### What doesn't work (validated failures — HISTORICAL, all 3 closed by c.311)

- **GLM-5.1 Coordinator timeout**: Was systematic 12+ min on complex Lean contexts (Lattice.lean L324). **CLOSED 2026-05-21** — Issue #1289 closed by PR #1394 + PR #1398 (Sonnet 4.6 Coordinator retained per Sprint D verdict, see issue comments).
- **L324 INTRACTABLE**: Cross-pair stability constraints involving unknown men (μ⁻¹(w₂)/ν⁻¹(w₁)) block local contradiction. **CLOSED via no_cross_match anti-crossing lemma** — see R5 closure table above (L324 → `meetSpouse_injective` proved via `no_cross_match` in PR #1452).
- **SearchAgent reasoning burn**: Qwen3.6 consumes 80-100% output budget in `reasoning_content`. **MITIGATED** — `fast` model key now exposed for 4 providers (z.ai/local/openrouter/mistral). The `fast` config chooses non-reasoning models by default; whether SearchAgent actually consumes `fast` vs `reasoning` is a wiring question (see R2 below, already done structurally).

## v5 Recommendations — STATUS ONLY (see top-of-doc table for closure evidence)

### R1: ~~Add Lemmas.lean winning tactics to KB~~ ✅ DONE

Originally HIGH / 15 min. All 3 entries (`gsFinalMatching`, `gsAllWomenMatched`, `gsNoBlockingPairs`) already present in `proof_knowledge.json` `proven_successful_tactics` at doc-writing time (commit `23e41056`, PR #1194, 2026-05-15–16). The R1 patch in this doc was redundant.

### R2: ~~SearchAgent model downgrade~~ ✅ DONE

Originally MEDIUM / 30 min. `config.py` `MODEL_CONFIGS` already exposes `fast` keys:

- `zai.fast = glm-5.1` (reasoning variant OK — GLM is faster than Qwen reasoning)
- `local.fast = qwen3.6-35b-a3b` (same as `reasoning` for local — change if Qwen `fast` is available)
- `openrouter.fast = anthropic/claude-haiku-4.5`
- `mistral.fast = labs-leanstral-1-5` (Mistral Lean-specialized, Apache-2.0)

Wiring question (which agent uses which `model_key`) was the actual open work; if any agent still calls `reasoning` for tool-bound tasks, that's a 1-line `model_key` change in `agents.py` at the relevant `create_*_agent` factory.

### R3: ~~Director wall-clock trigger~~ ✅ DONE

Already implemented at doc-writing time (workflow.py:278 F12 force-Director at iter 4 + B2c cumulative-fail counter).

### R4: ~~Coordinator model replacement~~ ✅ CLOSED via #1289

Issue #1289 CLOSED 2026-05-21 by PR #1394 + PR #1398. Sonnet 4.6 Coordinator retained per Sprint D verdict (ai-01 2026-05-19T12:08:31Z comment on #1289).

### R5: ~~Proof targets — INTRACTABLE classification~~ ✅ ALL RESOLVED

**Historical table retained for forensic reference** — all 6 entries below are now
0-sorry in their respective files (verified c.311 via
`grep -cE "^\s*(sorry|admit)"` on each file). See the closure table at the top
of this doc for the closing PR per row.

| File | Line | Target | Blocker | Classification |
|------|------|--------|---------|----------------|
| Basic.lean | L308 | hCore (G.Core.Nonempty) | Hyperplane separation for proper cones | INTRACTABLE_UNTIL_BONDAREVA_HYPERPLANE_SEPARATION ✅ closed (#3954) |
| GaleShapley.lean | L97 | gale_shapley_man_optimal | Man-optimal witness from GS algorithm | INTRACTABLE_UNTIL_RURAL_HOSPITALS ✅ closed (#1452) |
| GaleShapley.lean | L125 | gale_shapley_woman_pessimal | Knuth 1976 lattice duality | INTRACTABLE_UNTIL_RURAL_HOSPITALS ✅ closed (#1335) |
| Lattice.lean | L324 | meetSpouse "different women" | Rural hospitals for n≥3 | INTRACTABLE_UNTIL_RURAL_HOSPITALS ✅ closed (#1452 via `meetSpouse_injective`) |
| Lattice.lean | L387 | meetSpouse symmetric cross-case | Same as L324 | INTRACTABLE_UNTIL_RURAL_HOSPITALS ✅ closed (#1452) |
| Lattice.lean | L727 | doctor_optimal_eq_top | GS algorithm witness | INTRACTABLE_UNTIL_RURAL_HOSPITALS ✅ closed (#1530 via `IsManOptimal`) |

### R6: ~~Proof targets — ACTIONABLE~~ ✅ BOTH #1/#2 DONE, #3 = ongoing Conway Tribute

Historical list (all "next prover session" candidates exhausted by 2026-05-19):

1. **Basic.lean hP_nonempty + hK_empty** — ✅ closed via PR #1161 (MERGED 2026-05-15)
2. **Lattice.lean join_inverse_anti** — ✅ closed via PR #1292 (MERGED 2026-05-19)
3. **Any new targets from Mathlib/Conway expansion** — ongoing; see Conway Tribute section below + recent Nim/Doomsday/LookAndSay/Fractran "noix" trilogy (conway_lean/Conway/, see #1541, #1645).

## Conway Tribute — CGT Targets

### Current state (VERIFIED)
- `SymbolicAI/Lean/conway_lean/` exists with 3 "noix" COMPLETE (0 sorry) — relocated 2026-05-28 from `GameTheory/conway_lean/`:
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
