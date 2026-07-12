# Forensic Analysis: Multi-Agent Lean Prover Traces (Epic #1453)

**Date**: 2026-05-23
**Data source**: 90 JSONL trace files, 23,375 spans total
**Targets analyzed**: 39 distinct proof targets across LATTICE, Basic, Voting, GaleShapley, and smoke tests
**Modes**: `auto` (25 files, 14,325 spans) and `multi` (65 files, 9,050 spans)

---

## 1. Error Rate Analysis by Target

| Target | Spans | Errors | Error% |
|--------|------:|-------:|-------:|
| LATTICE_MEET_STABLE_CASE2 | 256 | 40 | **15.6%** |
| LATTICE_MEET_STABLE_CASE1 | 1,535 | 136 | **8.9%** |
| MEN_MATCHED_PROPOSED_STEPWITH | 228 | 18 | 7.9% |
| LATTICE_DOCTOR_OPTIMAL_TOP | 2,527 | 198 | **7.8%** |
| LATTICE_MEET_BIJECTIVE | 1,705 | 132 | **7.7%** |
| LATTICE_MEET_ANTI_COMPL | 2,411 | 154 | 6.4% |
| LATTICE_MEET_ANTI_COMPL_PRIME | 2,360 | 140 | 5.9% |
| LATTICE_JOIN_BIJECTIVE | 3,635 | 197 | **5.4%** |
| custom_Basic_L252 | 226 | 4 | 1.8% |
| VOTING_MEDIAN_COUNTING_LT | 761 | 12 | 1.6% |
| All others | — | — | <1.5% |

**Finding**: LATTICE targets have 5.4-15.6% error rates. All other targets are below 1.8%. The LATTICE targets are exclusively `auto` mode runs with glm-5.1, which is the root cause (see Section 7).

**Root cause**: 87.7% of all errors (940/1,071) are **glm-5.1 rate limit (HTTP 429)**. The remaining errors are timeouts (28) and other transient issues. The high error rates on LATTICE targets are entirely explained by the auto-mode glm-5.1 429 cascade.

---

## 2. Duration Analysis

### 2.1 Per-Agent Duration Stats

| Span Type | Count | Median | P95 | Max |
|-----------|------:|-------:|----:|----:|
| proof_session.auto-zai | 21 | 9,867s (2.7h) | 17,613s (4.9h) | **21,071s (5.9h)** |
| proof_session.multi | 47 | 637s (10.6min) | 6,016s (1.7h) | 9,018s (2.5h) |
| invoke_agent TacticAgent | 78 | 443s (7.4min) | 2,114s (35min) | 2,427s (40min) |
| invoke_agent CoordinatorAgent | 66 | 111s (1.8min) | 1,446s (24min) | 2,438s (41min) |
| invoke_agent AutonomousProver | 547 | 59s | 1,498s (25min) | 4,815s (80min) |
| invoke_agent SearchAgent | 48 | 82s | 363s (6min) | 1,307s (22min) |
| invoke_agent DirectorAgent | 13 | 10.5s | 25.3s | 25.3s |

### 2.2 Chat Model Latency

| Model | Count | Median | P95 | Max |
|-------|------:|-------:|----:|----:|
| glm-5.1 | 6,545 | 7.1s | **244s** | **1,209s** |
| gpt-5.5 | 523 | 4.9s | 20.9s | 51.3s |
| qwen3.6-35b-a3b | 345 | 3.9s | 151s | 492s |
| claude-sonnet-4-6 | 101 | 4.9s | 63s | 92s |

**Finding**: glm-5.1 has extreme tail latency (P95 = 244s, max = 1,209s). The P95 for auto-mode glm-5.1 is **248s** vs 131s for multi-mode, suggesting the long sessions themselves contribute to degradation (possibly rate-limit-induced retry backoff). gpt-5.5 is 12x faster at P95.

### 2.3 Tool Execution

| Tool | Count | Median | P95 | Max |
|------|------:|-------:|----:|----:|
| compile_probe_goal | 626 | 12.7s | 61.5s | 77.8s |
| file_replace_sorry | 692 | 9.7s | 14.6s | 40.0s |
| file_replace_lines | 611 | 10.1s | 14.1s | 39.7s |
| compile | 260 | 5.0s | 15.5s | 30.3s |
| verify_sorry_replacement | 57 | 13.2s | 17.5s | 22.2s |
| file_read_lines | 3,584 | 0ms | 1ms | 16ms |

**Finding**: `compile_probe_goal` at 12.7s median is the most expensive tool per call. With 626 invocations, it accounts for ~2.2 hours of wall-clock time. Each `file_replace` followed by `compile_probe_goal` costs ~22s median.

---

## 3. Loop Detection

### 3.1 Exact Loops (identical consecutive tool calls)

**170 instances** of 3+ consecutive identical tool_name + tool_args calls detected.

| Tool | Loop count |
|------|----------:|
| file_read_lines | 78 |
| compile_probe_goal | 54 |
| search_mathlib_lemmas | 13 |
| AutoProver.file_read_lines | 9 |
| add_discovered_lemma | 9 |
| AutoProver.compile_probe_goal | 7 |

**Worst files** (all auto-mode LATTICE):
- `auto_LATTICE_DOCTOR_OPTIMAL_TOP_zai_1778959909.spans.jsonl`: **31 loops**
- `auto_LATTICE_DOCTOR_OPTIMAL_TOP_zai_1778983637.spans.jsonl`: 18 loops
- `auto_LATTICE_MEET_STABLE_CASE1_zai_1778959134.spans.jsonl`: 15 loops

### 3.2 Semantic Loops (long runs of same tool, different args)

**20 runs of 8+ consecutive same-tool calls** detected.

| Target | Tool | Count | File |
|--------|------|------:|------|
| WOMEN_UNPROPOSED | file_read_lines | **24** | multi_WOMEN_UNPROPOSED |
| custom_Basic_L237 | search_mathlib_lemmas | **24** | multi_custom_Basic_L237 |
| custom_Basic_L237 | search_mathlib_lemmas | 17 | multi_custom_Basic_L237 |
| custom_Basic_L242 | file_replace_sorry | 17 | multi_custom_Basic_L242 |
| GALESHAPLEY_MAN_OPTIMAL | file_read_lines | 16 | multi_GALESHAPLEY_MAN_OPTIMAL |

**Finding**: The `file_read_lines` loop of 24 means the agent re-reads the same file context 24 times without making progress. The `search_mathlib_lemmas` run of 24 means repeated lemma searches without acting on results. These are the F11 loop-detection patterns.

---

## 4. Model Performance Comparison

| Model | Calls | Errors | Error% | Med(s) | P95(s) | Max(s) | TokIn | TokOut |
|-------|------:|-------:|-------:|-------:|-------:|------:|------:|------:|
| glm-5.1 | 7,199 | 1,026 | **14.3%** | 8.0 | 376 | 4,815 | 136M | 5.6M |
| gpt-5.5 | 581 | 12 | 2.1% | 5.3 | 47 | 541 | 16M | 227K |
| qwen3.6-35b-a3b | 409 | 16 | 3.9% | 4.7 | 234 | 1,307 | 3.6M | 578K |
| claude-sonnet-4-6 | 104 | 0 | 0.0% | 5.2 | 75 | 803 | 6.3M | 169K |
| claude-haiku-4.5 | 5 | 0 | 0.0% | 5.3 | 18 | 18 | 54K | 3K |

**Finding**: glm-5.1 is the only model with significant errors, and **91.6% of its errors (940/1,026) are rate limits (429)**. The remaining 86 errors are timeouts and other transient issues. gpt-5.5 has 12x fewer errors and 8x lower P95 latency.

**glm-5.1 by role**:
- Coordinator (n=566): med=7.0s, p95=243s
- Search (n=1,453): med=6.9s, p95=87s
- Tactic (n=95): med=9.5s, p95=42s
- Other/AutonomousProver (n=4,431): med=7.2s, p95=248s

**Time wasted in 429 retries**: **43.0 hours** of wall-clock time spent on failed rate-limited requests.

---

## 5. AutonomousProver Error Cascade

The AutonomousProver (auto mode) has a **90.5% error rate** (495/547 invocations). This is NOT a prover logic bug -- it is a cascade:

- 467 errors are directly from glm-5.1 rate limits
- 28 errors are timeouts
- 495 total (some 429s trigger multiple sub-agent errors)

Every auto-mode session with LATTICE targets hits this wall. The prover keeps retrying and timing out on 429s, inflating session durations to 2.7-5.9 hours.

---

## 6. Session Outcomes

| Target | IterCap | SorryGuard | Intractable | F1Esc | Solved |
|--------|--------:|-----------:|------------:|------:|-------:|
| LATTICE_JOIN_BIJECTIVE | 5 | 3 | 6 | 0 | 0 |
| LATTICE_MEET_ANTI_COMPL | 1 | 3 | 0 | 0 | 0 |
| LATTICE_MEET_ANTI_COMPL_PRIME | 0 | 5 | 0 | 0 | 0 |
| VOTING_MEDIAN_COUNTING_LT | 0 | 2 | 0 | 0 | 2 |
| custom_Basic_L237 | 0 | 1 | 3 | 0 | 0 |
| custom_Lattice_L324 | 0 | 1 | 15 | 0 | 0 |
| GALESHAPLEY_MAN_OPTIMAL | 2 | 0 | 3 | 0 | 0 |
| GALESHAPLEY_STABLE | 0 | 0 | 9 | 0 | 0 |

**Finding**: Targets with high intractable counts (GaleShapley_stable L76: 9, custom_Lattice_L324: 15) correctly terminate via `mark_sorry_intractable`. The LATTICE targets with `SorryGuard` terminations hit a state where the prover replaced sorry but verification detected new sorrys or regressions. Only VOTING_MEDIAN_COUNTING_LT has actual solves (2).

---

## 7. Mode Comparison: Auto vs Multi

| Mode | Files | Spans | Errors | Error% | Total Duration | Avg Duration |
|------|------:|------:|-------:|-------:|---------------:|-------------:|
| auto | 25 | 14,325 | 992 | **6.9%** | 216,544s (60h) | **8,662s (2.4h)** |
| multi | 65 | 9,050 | 79 | **0.9%** | 84,403s (23h) | **1,299s (22min)** |

**Finding**: Auto mode has **7.7x higher error rate** and **6.7x longer average session duration** than multi mode. The root cause is the glm-5.1 rate limit cascade in auto mode.

---

## 8. Write-Compile Cycle Analysis

| Target | Writes | Compiles | Reads | Searches | C/W Ratio |
|--------|-------:|---------:|------:|---------:|----------:|
| LATTICE_MEET_STABLE_CASE2 | 2 | 17 | 76 | 0 | **8.5** |
| LATTICE_MEET_STABLE_CASE1 | 72 | 122 | 335 | 0 | 1.7 |
| custom_Lattice_L324 | 19 | 18 | 150 | 12 | 0.9 |
| LATTICE_DOCTOR_OPTIMAL_TOP | 155 | 172 | 446 | 0 | 1.1 |
| VOTING_MEDIAN_COUNTING_LT | 36 | 21 | 100 | 67 | 0.6 |

**Finding**: LATTICE_MEET_STABLE_CASE2 has a C/W ratio of 8.5 (17 compiles for only 2 writes), meaning the prover is probing the goal state repeatedly without making edits. LATTICE_DOCTOR_OPTIMAL_TOP is the most expensive target overall (155 writes, 172 compiles, 446 reads).

---

## 9. Top 5 Friction Points and Fix Proposals

### Friction 1: glm-5.1 Rate Limit Cascade (43 hours wasted)

**Evidence**: 940 HTTP 429 errors, all from glm-5.1. 90.5% AutonomousProver invocation failure rate. 43.0 hours of wall-clock time in failed retries. Auto-mode P95 latency 248s (vs gpt-5.5 at 47s).

**Impact**: HIGH -- this is the single largest source of wasted compute and time. It makes auto-mode sessions effectively useless for long runs.

**Fix proposal**:
1. Add exponential backoff with jitter to the z.ai API client (current behavior appears to be immediate retry).
2. Cap auto-mode session duration at 2h with graceful degradation (save state, resume).
3. **Already partially fixed**: PR #1398 replaced TacticAgent glm-5.1 with GPT-5.5 via OpenRouter. The remaining glm-5.1 usage is in the AutonomousProver auto-mode agent, which should also be migrated.
4. Add a per-minute request budget (e.g., max 15 requests/min to z.ai) with backpressure.

### Friction 2: Read-Compile-Write Loop Without Progress Detection

**Evidence**: 170 exact loops (identical tool_name + tool_args repeated 3+). 20 semantic loops (8+ consecutive same-tool calls). Worst case: 24 consecutive `file_read_lines` without action, 24 consecutive `search_mathlib_lemmas` without applying results.

**Impact**: HIGH -- the prover burns iterations reading the same context or searching lemmas without making edits. This is the F11 loop-detection issue.

**Fix proposal**:
1. Add a "stale context" detector: if `file_read_lines` is called with the same range 3+ times without an intervening `file_replace_*`, inject a warning or force a different action.
2. Cap consecutive `search_mathlib_lemmas` calls at 5; after that, require at least one `compile_probe_goal` or `file_replace_*`.
3. Add a "progress hash": hash the current file content + goal state after each write-compile cycle. If the hash is unchanged after 3 cycles, trigger a strategy change (escalate to coordinator, switch tactic approach, or mark intractable).
4. The `compile_probe_goal` exact-repeats (54 instances) suggest the prover is probing the same unchanged goal -- these should be cached with a short TTL.

### Friction 3: AutonomousProver Auto-Mode Architecture Fragility

**Evidence**: Auto mode has 6.7x longer sessions and 7.7x higher error rate than multi mode. Auto mode's AutonomousProver invokes are 90.5% errors. Auto-mode sessions routinely exceed 3-5 hours (max: 5.9h) vs multi mode's 22-minute average.

**Impact**: HIGH -- auto mode is the default for background iterations, but it is dramatically less reliable than multi mode.

**Fix proposal**:
1. Consider making multi-mode the default for all new sessions (already done for recent PRs, but config still defaults to auto).
2. If auto mode is kept, add a "heartbeat" check: if no `file_replace_*` occurs within 30 minutes, force-terminate the session as stalled.
3. The AutonomousProver's single-agent architecture means any LLM failure kills the entire iteration. Multi-mode's coordinator/tactic/critic separation provides resilience -- one agent failure doesn't cascade.

### Friction 4: compile_probe_goal Cost (2.2 hours total)

**Evidence**: 626 invocations at 12.7s median. Total wall-clock time ~2.2 hours. Many probes are redundant (54 exact-repeats detected).

**Impact**: MEDIUM -- significant but not the top issue. Each probe is a full `lake env print` invocation.

**Fix proposal**:
1. Cache compile_probe results keyed by file content hash + goal line. If the file hasn't changed since the last probe, reuse the result.
2. Reduce probe frequency: after a failed edit, batch 2-3 tactic attempts before re-probing.
3. Consider a lighter-weight goal checker that doesn't require a full `lake env print` (e.g., lean --run on just the sorry line with a mock context).

### Friction 5: No Early Termination on Known-Intractable Targets

**Evidence**: custom_Lattice_L324 triggered `intractable` 15 times across sessions. LATTICE_DOCTOR_OPTIMAL_TOP ran 3 sessions of 2.7-5.9 hours each without solving. The prover re-attempts known failures from scratch.

**Impact**: MEDIUM -- wastes compute on targets already diagnosed as intractable. 3 sessions on DOCTOR_OPTIMAL_TOP = ~30 hours of compute with no progress.

**Fix proposal**:
1. Maintain a persistent `intractable_registry` (file or DB) keyed by target + file hash. Before launching a session, check if the target was marked intractable within the last 48h. If yes, skip unless the file content has changed.
2. The `HONEST_SORRIES` registry in `proof_knowledge.json` already partially serves this purpose. Extend it with timestamp + reason + attempt count.
3. For the coordinator (multi mode): if a target was marked intractable by a previous session, require human acknowledgment before re-attempting.

---

## 10. Data Summary

| Metric | Value |
|--------|------:|
| Total trace files | 90 |
| Total spans | 23,375 |
| Total ERROR spans | 1,071 (4.6%) |
| Rate limit (429) errors | 940 (87.8% of errors) |
| Time wasted in 429s | 43.0 hours |
| Exact loop patterns (3+) | 170 |
| Semantic loops (8+) | 20 |
| Auto mode avg duration | 2.4 hours |
| Multi mode avg duration | 22 minutes |
| AutonomousProver error rate | 90.5% |
| glm-5.1 error rate | 14.3% |
| gpt-5.5 error rate | 2.1% |
| glm-5.1 P95 latency | 376s |
| gpt-5.5 P95 latency | 47s |
| Longest session | 5.9 hours (auto custom_Basic_L308) |

---

## Appendix: Methodology

- **Parsing**: All 90 `.spans.jsonl` files parsed, each line is a JSON span object.
- **Target extraction**: Filename pattern `{mode}_{TARGET}_{provider}_{timestamp}.spans.jsonl` parsed with regex.
- **Error classification**: `status == "ERROR"` spans, then event `exception` checked for "429" / "Rate limit" substrings.
- **Loop detection**: Two levels -- (a) exact hash match of tool_name + tool_args on consecutive spans, (b) same tool_name run length regardless of args.
- **Duration**: `duration_ms` field (end_time_ns - start_time_ns), converted to seconds for readability.
- **Analysis script**: `analyze_traces.py` in this directory.
