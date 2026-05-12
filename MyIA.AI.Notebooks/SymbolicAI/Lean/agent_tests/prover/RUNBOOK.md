# Multi-agent Lean prover — BG track runbook

Tool to attack a single `sorry` in a Lean file via 4 specialized LLM agents
(Coordinator/Search/Tactic/Critic) plus a deterministic Lean compile loop.
Designed to be launched as a background track while the agent does
foreground work (notebooks, READMEs, reviews).

## Quick start

```bash
cd d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests

# Trivial smoke test (zero_add_smoke, 1 sorry, completes <60s on local LLM)
python -u run_prover_bg.py 0 --provider local --max-iter 3 --workflow-timeout 120

# Real target: Voting.lean L355 (median voter counting LT, very_hard)
python -u run_prover_bg.py 9 --provider zai --max-iter 15 --workflow-timeout 1800

# With external Director (GPT-5.5 via OpenRouter for strategic guidance)
python -u run_prover_bg.py 13 --provider zai --director-provider openrouter \
    --max-iter 20 --workflow-timeout 2400
```

Available DEMO ids — see `prover/config.py` `DEMOS` dict. Common entries:

| ID | File | Line | Difficulty | Notes |
|----|------|------|------------|-------|
| 0 | _SmokeTest.lean | 6 | trivial | use this to smoke-test infra |
| 6 / 8 | Shapley.lean | 566 | hard / very_hard | shapley_uniqueness |
| 9 | Voting.lean | 355 | very_hard | median_voter_theorem_strict LT case |
| 13 | Voting.lean | 446 | hard | banks_set_condorcet — has scaffolding |
| 14 | Voting.lean | 385 | very_hard | median_voter_theorem_strict GT case |
| 15 | GaleShapley.lean | 73 | very_hard | existential stable matching (HONEST) |

## Launching as BG track from Claude Code

Use `Bash` with `run_in_background: true`. Capture the bash_id, do FG work
(promote ALPHA notebook, review PRs, etc.), then check the BG output via
`BashOutput` at intervals. The script writes one `[BG] ...` line per major
event so a `grep "^\[BG\]"` extracts the run summary.

```python
# Pseudo-code for a Claude Code session
bg_id = Bash(
    "cd d:/CoursIA/MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests && "
    "python -u run_prover_bg.py 9 --provider zai --max-iter 15 "
    "--workflow-timeout 1800",
    run_in_background=True,
)
# ... do FG work (notebook enrichment, README, etc.) ...
# Check BG every 10 min via BashOutput
```

## Output to watch

```
[BG] START demo_id=9 name=VOTING_MEDIAN_COUNTING_LT
[BG] FILE  d:/.../SocialChoice/Voting.lean
[BG] PRE_FILE_SORRY_COUNT 5
[BG] PROVIDER reasoning=zai fast=local director=none max_iter=15
...
[BG] POST_FILE_SORRY_COUNT 5  (or 4 if eliminated)
[BG] DELTA 0
[BG] RESULT_SUCCESS False
[BG] FINAL ok=False sorry_after=5 elapsed=873.2
```

| Line | Meaning |
|------|---------|
| `START` / `FILE` / `LINE` | Target identification |
| `PRE_FILE_SORRY_COUNT N` | sorry count before run |
| `PROVIDER` | Active LLM providers |
| `POST_FILE_SORRY_COUNT M` | sorry count after run |
| `DELTA P` | `pre - post` (positive = progress, 0 = no change) |
| `RESULT_SUCCESS True/False` | Workflow's final verdict (build_ok + sorry_decreased) |
| `FINAL ok=...` | One-line summary; grep for this when batching |

## Honest reporting

- `DELTA > 0 AND ok=True` → real progress. Open PR with `lake build` log.
- `DELTA == 0 AND ok=False` → no progress (typical for very_hard targets).
  This is **expected**, not a failure of the infrastructure. Report as
  `iter N: 0/M sorrys eliminated` in dashboard, do not claim "DONE".
- `DELTA > 0 AND ok=False` → infrastructure caught a false positive (sorry
  removed but build broken). Original file is automatically restored.
- `EXCEPTION ...` → infrastructure crash. Capture trace, file issue.

## HONEST_SORRIES (do NOT dispatch)

`config.py` `HONEST_SORRIES` registers sorrys that are theoretically
unprovable in the current Mathlib version (Bondareva LP duality, GS
existential). The prover will refuse them with `intractable=True`.
Trying to dispatch them wastes budget — pick a different target.

As of 2026-05-12 the registered HONEST sorrys are:
- `Voting.lean:262` (median_voter weak version)
- `Basic.lean:234` (bondareva_shapley_backward — **may become provable**
  after Lean v4.30 bump since `ProperCone.hyperplane_separation` (Farkas)
  landed in Mathlib master)
- `GaleShapley.lean:73,87,114` (existential stable matching — needs GS
  algorithm port, see `mmaaz-git/stable-marriage-lean`)

## Where to find traces

- `prover/.prover_history/<File>_<hash>_L<line>.json` — cross-session
  attempt log per target (recent tactics + outcomes)
- `prover/baselines/traces/multi_<NAME>_<provider>.json` — per-run
  workflow trace (agent transitions, tool calls)
- `prover/baselines/traces/multi_<NAME>_<provider>_<id>.spans.jsonl` —
  OTel spans (timing, LLM call durations)

## Common failure modes (and the right reaction)

| Symptom | Cause | Fix |
|---------|-------|-----|
| `tactic_contains_sorry` in trace | LLM gave up, emitted bare `sorry` | Expected on very_hard. Re-run with `--director-provider openrouter` |
| `RESULT_SUCCESS False, DELTA 0` for 3+ runs | Target genuinely intractable for current LLMs | Mark as HONEST in `config.py` with explanation, move on |
| `EXCEPTION OpenAI...` mid-run | z.ai 5xx | Already mitigated by `max_retries=4`. If persistent, switch to `--provider local` |
| `iteration cap hit` | Workflow looping on Critic↔Tactic | F1 escalation should kick in at 3 fails. Increase `--max-iter` or check Coordinator plan |
| Build broken after run | Should be impossible — final-verify reverts | File issue, attach trace, do NOT commit the broken file |

## Dispatch pattern (cluster agents)

When dispatched a Lean prover BG track:

1. Pick a target from the DEMOS table that is NOT in HONEST_SORRIES.
2. Launch via `run_prover_bg.py <id>` with `run_in_background=true`.
3. Continue with FG work (notebook ALPHA promotion, README enrichment,
   audit). Do NOT sit and watch the BG output.
4. Every ~10 min, BashOutput on the BG to check `[BG]` summary lines.
5. When `FINAL ok=...` appears, parse the verdict, log to dashboard.
6. If `DELTA > 0`: open PR with body containing `grep -c sorry` before/after,
   `lake build SUCCESS` confirmation, and the trace file path.
7. If `DELTA == 0`: report honestly on dashboard, pick next target.
