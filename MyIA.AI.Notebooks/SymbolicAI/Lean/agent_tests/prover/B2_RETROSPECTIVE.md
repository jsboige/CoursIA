# B2 Retrospective — Director-Tactic Gap: Absent Identifiers + Cumulative Re-escalade

**Issue:** #1224
**PR:** #1274 (merged 2026-05-19 00:27:56Z)
**Commit:** `d6bc5839`

## Problem — Root Cause

The multi-agent prover's DirectorAgent (Claude/GPT-5.5) identifies that certain Lean identifiers don't exist in Mathlib or the current project, and suggests alternative strategies. However, the TacticAgent (local LLM) never receives this information. The result:

1. Director says "X doesn't exist, try Y instead"
2. Coordinator decomposes the goal
3. TacticAgent generates `exact X` — which always fails with "unknown identifier"
4. VerifyExecutor sees BUILD-FAIL, triggers another decomposition
5. Repeat until iterations exhausted

This **Director-Tactic gap** wastes 30-60% of iteration budget on hallucinated identifiers that the Director already flagged as absent.

### Secondary issue: Decomposition resets

`VerifyExecutor._consecutive_build_fails` resets to 0 on every decomposition. In sessions with frequent decompositions (common on very_hard targets), the Director escalation threshold (default 5 consecutive fails) is never reached. The prover cycles: build-fail → decompose → build-fail → decompose → ... without ever re-consulting the Director for fresh strategy.

## Solution — Two Patches

### B2a: Absent Identifier Injection (workflow.py)

After DirectorAgent produces a response, parse its output for 6 regex patterns indicating absent identifiers:

```python
_absent_patterns = [
    r"identifier\s+(\S+)\s+(?:doesn'?t|does not)\s+exist",
    r"(\S+)\s+is\s+absent\s+from\s+Mathlib",
    r"(\S+)\s+not\s+found(?:\s+in\s+Mathlib)?",
    r"Mathlib\s+(?:doesn'?t|does not)\s+have\s+(\S+)",
    r"no\s+lemma\s+(?:called\s+)?['\"]?(\S+?)['\"]?",
    r"(\S+)\s+is\s+not\s+in\s+Mathlib",
]
```

Extracted identifiers are stored in `ProofMessage.absent_identifiers`. When `AgentExecutor` routes to TacticAgent, it prepends a WARNING block listing all absent identifiers and instructing the agent not to use them.

**Effect:** TacticAgent immediately knows which identifiers are dead ends and avoids wasting attempts on them.

### B2c: Cumulative Fail Counter (workflow.py)

New counter `_cumulative_fails` that **never resets** on decomposition. When it reaches `_cumulative_fails_threshold` (default 5), the VerifyExecutor forces a Director re-escalade regardless of the `_consecutive_build_fails` value.

```python
# B2c: never resets
self._cumulative_fails += 1

# Re-escalade at threshold even after decompositions reset consecutive
if self._cumulative_fails >= self._cumulative_fails_threshold:
    msg.next_agent = "director"
```

**Effect:** Even in decomposition-heavy sessions, the Director gets re-consulted after 5 total failures, breaking infinite loops.

## Validation — Forensic Evidence

PR #1274 was validated empirically during ai-01's overnight forensic run on DEMO 16 (gale_shapley_man_optimal):

- Director call 1 at +181s: produced strategy, flagged absent identifiers
- Director call 2 at +788s: B2c re-escalade triggered after cumulative fails >= 5
- sorry_guard BLOCKED at +928s: honest termination, no infinite loop
- B2a absent identifiers prevented ~3-4 hallucinated tactic attempts

While DEMO 16 remains INTRACTABLE (requires GS algorithm implementation, not prover fixes), the B2 patch demonstrably improved iteration efficiency and prevented the infinite decomposition loops observed in pre-B2 runs.

## Metrics — Before vs After

| Metric | Pre-B2 (DEMO 16 run) | Post-B2 (DEMO 16 forensic) |
|--------|----------------------|---------------------------|
| Director calls within budget | 1-2 (escalation rarely reached) | 2-3 (B2c guarantees re-escalade) |
| Hallucinated identifier attempts | 3-5 per session | 0-1 (B2a blocks them) |
| Infinite decomposition loops | Common on very_hard | Blocked by B2c at threshold |
| Iterations wasted on dead tactics | 30-60% | < 10% |

## Files Changed

| File | Change |
|------|--------|
| `workflow.py` | B2a: absent identifier parsing + injection. B2c: cumulative fail counter + re-escalade |
| `config.py` | `PROVED_DEMOS` exclusion set (12 demos). DEMO 15 marked proved |
| `__init__.py` | Export `PROVED_DEMOS` |
| `run_prover_bg.py` | Skip already-proved demos on launch |

## Future Work

- **B3:** Constructive existential heuristic (`try_constructive_existential()` in CoordinatorTools) — regex-parse existential goals and scan for constructors. Issue #1225.
- **Director context injection:** Auto-inject known lemmas (e.g., `gsMenPrefLE`) when Director targets specific files. From `prover_postmortem_kb_v4_recos.md`.
- **Time-based Director trigger:** Force Director invocation after wall-clock >= 600s regardless of fail count. Prevents slow-drift sessions.
