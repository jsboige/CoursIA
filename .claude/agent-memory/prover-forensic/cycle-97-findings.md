---
name: cycle-97-findings
description: Forensic analysis of 53 prover traces, 44.8h wall-clock, stagnation pathology, ROI-ranked improvements
metadata:
  type: project
---

# Prover Forensic Analysis -- Cycle 97 (2026-05-26)

## Macro Signal (VERIFIED)

| Metric | Value |
|--------|-------|
| Total runs | 53 |
| Progress (sorry_delta < 0) | 30 (57%) |
| No progress (sorry_delta = 0) | 23 (43%) |
| Total sorry reduced | -55 |
| Total wall-clock | 44.8h (161,424s) |
| Total iterations | 375 |

### By Mode

| Mode | Runs | Progress | Rate | Avg wall-clock |
|------|------|----------|------|---------------|
| autonomous | 29 | 22 | **76%** | 3,947s |
| multi | 24 | 8 | **33%** | 1,957s |

**VERIFIED**: Autonomous mode has 2.3x higher progress rate than multi mode.

### Top Delta0 Burners (wall-clock wasted with zero sorry reduction)

| Target | Wall-clock | Iterations | Mode |
|--------|-----------|------------|------|
| custom_Basic_L308 | 21,084s (5.9h) | 10 | autonomous |
| LATTICE_MEET_STABLE_CASE1 | 13,454s (3.7h) | 10 | autonomous |
| LATTICE_DOCTOR_OPTIMAL_TOP | 9,689s (2.7h) | 10 | autonomous |
| custom_GaleShapley_L97 | 9,081s (2.5h) | 15 | multi |
| custom_Basic_L237 | 7,892s (2.2h) | 15 | multi |

**Top 5 burners alone = 61.2h wall-clock for zero sorry reduction.**

---

## Finding 1: compile_probe_goal Cache Invalidation Too Aggressive (HIGH ROI)

**Evidence**: Basic_L308 trace has 20 probes all targeting the SAME sorry_line. Conway_LAS_ROUND_TRIP has 29 probes on the same line. The cache key is `(content_hash, sorry_line)` (tools.py:1476). Every file edit changes content_hash, invalidating ALL cached probes -- even if the sorry at the target line is untouched.

**Measured waste**: 19/20 probes in L308 were re-probes (the sorry text never changed between most edits). At ~5-10s per Lean server invocation per probe, this is ~100-200s per session wasted on probes alone.

**Root cause**: `tools.py:1474-1476` -- content_hash is a full-file MD5. A `file_replace_lines` edit on line 50 invalidates the probe cache for sorry at line 300 even though the goal at 300 is unchanged.

**Proposed fix**: Use `(sorry_line, surrounding_context_hash)` where `surrounding_context_hash` hashes only lines [sorry_line-10, sorry_line+10] instead of the entire file. ROI: saves ~100-200s per 10-iteration session on probe-heavy targets.

**File:line**: `tools.py:1474-1493`

---

## Finding 2: 43% of Runs Are Delta0 (Zero Sorry Progress) Despite Stagnation Guards (HIGH ROI)

**Evidence**: 23/53 runs have sorry_delta=0. The DELTA0_STAGNATION_HARDCAP=6 (workflow.py:72) and stagnation_threshold=3 (tools.py:577) exist but the top burners still ran full iteration budgets (10-15 iters).

**Root cause (VERIFIED from code)**: The stagnation guard in `workflow.py:222-236` reads `state.consecutive_delta0_compiles` which is mirrored from `tools.py:1574`. However, the compile tool must be explicitly called by the agent for the counter to increment. In autonomous mode, the agent controls its own tool calls. If the agent avoids calling `compile()` and instead uses `file_replace_lines` + `file_replace_sorry` (which have their own build_check), the `consecutive_delta0` counter never increments because it lives in the `compile()` method only (tools.py:1552-1560).

**Measured impact**: Basic_L308 had 5 explicit `compile()` calls but 75 `replace` calls (42 file_replace_lines + 33 file_replace_sorry). Each replace does its own `_build_check_or_revert` (tools.py:1147) which does NOT update `_consecutive_delta0`. The stagnation guard is bypassed.

**Proposed fix**: Move delta0 tracking to `_build_check_or_revert` (tools.py:873) so every build-check (including those from file_replace_lines/sorry) updates the consecutive_delta0 counter. ROI: would terminate the top 5 burners 2-5 iterations early, saving ~20-30h cumulative wall-clock.

**File:line**: `tools.py:873-993` (_build_check_or_revert) needs delta0 tracking like `tools.py:1552-1560` (compile method).

---

## Finding 3: Multi-Mode 33% Success Rate -- Escalation Path Failure (MEDIUM ROI)

**Evidence**: Multi-mode achieves only 33% progress rate (8/24) vs 76% for autonomous (22/29). The top multi-mode burners (L237: 15 iters, L97: 15 iters) suggest the multi-agent routing fails to escalate effectively.

**Root cause (from code analysis)**: The `VerifyExecutor._consecutive_build_fails` counter (workflow.py:640) resets on decomposition (workflow.py:858). The `_cumulative_fails` counter (workflow.py:658) was added to fix this, but its threshold=5 (workflow.py:659) combined with the director budget of 3 calls means the escalation fires late and may exhaust budget on the first invocation without useful guidance.

**Measured impact**: Multi-mode burns avg 1,957s per run with 67% zero-progress. The Director force-invocation at iter 4 (workflow.py:244) should help, but for runs that never reach iter 4 (2-iter runs on VOTING/LATTICE_JOIN_BIJECTIVE), the routing fails earlier.

**Proposed fix**: Lower `_cumulative_fails_threshold` from 5 to 3 for multi-mode sessions. The threshold was calibrated before the Director was wired; with a competent Director (GPT-5.5), earlier escalation is more cost-effective than iteration burn.

**File:line**: `workflow.py:659`

---

## Finding 4: Conway Calibration Success Pattern -- Rapid Prove on Simple Targets (LOW ROI, confirmation)

**Evidence**: All 11 Conway calibration targets (24/05) proved successfully in 5-8 iterations with sorry_delta=-1 or -2. Nash calibration targets also proved (sd=-1 to -5). These are "simple" targets where the autonomous agent finds the proof in 1-2 iterations then burns remaining iterations on secondary sorrys.

**Pattern**: Successful runs show chat_count proportional to proof difficulty. Conway targets: 30-60 chats in 30-50s. Complex targets: 200+ chats in 2000+s. The overhead is dominated by LLM latency, not tool execution.

**No action needed** -- this confirms the harness works well on tractable targets.

---

## Non-Verified (Flagged)

1. **LLM latency vs tool latency split**: Spans don't capture per-tool duration in a way that separates LLM think-time from Lean build-time. The `duration_ms` on chat spans includes full LLM round-trip but tool spans show 0ms (likely a tracing gap). Cannot distinguish "agent is thinking" from "agent is waiting for build" without fixing the span instrumentation.

2. **Autonomous vs multi performance gap causality**: The 76% vs 33% gap could be caused by (a) target difficulty (autonomous gets calibration targets, multi gets GS/Lattice), (b) routing inefficiency, or (c) provider differences. The target distribution confounds the analysis -- this is NOT verified as a harness bug.

3. **LOST_PROGRESS revert veto effectiveness**: The `_build_check_or_revert` LOST_PROGRESS guard (tools.py:931-963) was added in PR #1518 but no trace in this corpus exercises it (all recent traces predate that merge). Its effectiveness is UNVERIFIED against real runs.

---

## Priority Summary

| Priority | Finding | ROI | Estimated Savings | Code Location |
|----------|---------|-----|-------------------|---------------|
| **P1** | Delta0 tracking in _build_check_or_revert | HIGH | ~20-30h cumulative | tools.py:873 |
| **P2** | Probe cache invalidation granularity | HIGH | ~100-200s/session | tools.py:1474 |
| **P3** | Lower cumulative_fails_threshold for multi | MEDIUM | Earlier Director escalation | workflow.py:659 |
