# Verify Before Claiming (Agent Accountability)

**Source:** Incident 2026-05-07 — Agent falsely claimed multi-agent prover architecture was missing across 3 sessions.
**Rationale:** Unverified technical claims propagated to dashboard, coordinator, and user without any code-level check. This wasted days of work and eroded trust.

## Rule 1: VERIFY Before Diagnosing a Missing Feature

Before stating "X is missing" or "X doesn't exist":

1. Run `grep -r "X" <directory>/` or read the relevant source files
2. If the feature EXISTS: use it. Do NOT report it as missing.
3. If the feature is INCOMPLETE: report exactly what exists and what's missing, with file paths and line numbers as proof
4. Dashboard reports MUST include: "I verified the code and [feature] exists at [file:line] / does not exist (grep returned 0 results)"

**Scope:** Applies to ANY technical diagnostic — architecture claims, library availability, function existence, configuration status.

## Rule 2: No Inflated DONE

- If sorry count goes from 8 to 7: report "1/8 sorry eliminated, 87% remaining", NOT "DONE"
- If a tool exists but isn't used: that's an agent failure, not a "missing feature"
- Metric counts (PR count, commit count) are NOT progress. Report distance to final objective.
- A PR that doesn't change sorry count = 0 proof progress regardless of code changes

## Rule 3: Doubt Self Before Blaming the Tool

Before claiming "the LLM can't do X" or "the tool is insufficient":

1. Have I used the BEST available architecture? (e.g., multi-agent vs single-agent)
2. Have I grep'd the codebase for existing features before requesting new ones?
3. If an approach fails: list what I have NOT tried before concluding it's impossible
4. If I haven't tested the available mode/tool: I cannot claim it's insufficient

## Rule 4: Coordinator Merge Scrutiny

For ANY PR that claims technical progress:

1. Does the PR include verifiable evidence? (sorry count diff, test output, execution log)
2. Does the PR description match the actual diff? (check `git diff --stat`)
3. If the PR references "missing features" or "architecture gaps": were these verified by reading the code?
4. Merge only if evidence is concrete. Vague claims = request proof before merge.

## Known Past Violations

- **2026-05-07**: Claimed MultiAgentSorryProver "doesn't exist" while it was fully implemented in `prover/agents.py`, `prover/workflow.py`, `prover/tools.py`, `prover/provers.py`. Only AutonomousProver was ever used.
- **2026-04-24**: Commit "Mathlib compilation fixes" replaced 9 working proofs with `sorry` (detected by user, not by any agent review)
