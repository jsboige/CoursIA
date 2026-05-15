# Prover session summary

## 2026-05-15 — forensic run C34-01

**Target:** `stable_marriage_lean/StableMarriage/GaleShapley.lean:76` —
`gale_shapley_stable`, goal `∃ μ, IsStable prof μ` (GS stable matching existence).
Mode: multi-agent, provider zai (GLM-5.1), Director on OpenRouter Opus 4.7,
reference docs injection ACTIVE (first run after #1129).

**Outcome:** marked intractable (CORRECT). sorry 3 -> 3, FAILED, 138s,
0 tactic attempts, 0 wasted iterations.

**Trace:** `traces/multi_custom_GaleShapley_L76_zai.json` (4 entries).

### What worked
- **Reference-docs grounding confirmed working.** Coordinator cited the
  mmaaz-git reference (~1000 LOC of supporting lemmas), the GS
  deferred-acceptance algorithm requirement, and registered
  `INTRACTABLE_UNTIL_GS_IMPL` / HONEST_SORRIES. Context comes from the
  session_state reference docs merged in #1129 — the injection reaches
  the Coordinator and improves its reasoning.
- **F5 intractable fast-path solid.** Coordinator reached the verdict in a
  single pass (~124s), `mark_sorry_intractable` -> clean yield. No tactic
  attempts burned, no spurious compiles.

## 2026-05-15 — forensic run C34-02 (consistency check)

**Target:** GaleShapley.lean:91 `gale_shapley_man_optimal`, goal
`∃ μ, IsManOptimal prof μ`. Same configuration.

**Outcome:** marked intractable (CORRECT) in **66.5s** — faster than L76,
with even better-grounded reasoning. Coordinator cited the dependency chain
explicitly: L76 itself a sorry, GSState/gsStep/gsRunSteps absent from the
file, ~1000 LOC invariants, `IsManOptimal` universal quantification over all
stable matchings. sorry 3 -> 3, FAILED, 83.3s wall, 0 tactic attempts.

Confirms the reference-docs grounding (#1129) is reproducibly active. L119
`gale_shapley_woman_pessimal` would give the same verdict — marginal value,
skipped.

## 2026-05-15 — forensic run C34-03 (revert-a-proven-sorry benchmark)

**Setup:** the recommendation from C34-01/02 was a tractable benchmark to
exercise the Tactic/Critic/Coordinator/Director loop end-to-end. Procedure:
take a recently-proven hard target (`gsChooseMax_maximal` in GSState.lean:140,
proven in #1120, commit `10ddc8ef`), revert the proof body (lines 144-166)
to `sorry`, run the prover, restore the file unconditionally afterwards.

**Target:** GSState.lean:144 `gsChooseMax_maximal`, goal
`gsMenPrefLE prof m w (gsChooseMax prof σ m h)`. Multi-agent, provider zai,
**Director Opus 4.7 wired via OpenRouter for the first time** (new
`--director-provider` flag added to `run_prover_bg.py` — the flag was missing
from the CLI even though `MultiAgentSorryProver(__init__)` already accepted
the parameter).

**Outcome:** **partial progress** — first run ever to get past the
intractable fast-path. sorry 1 -> 1 net (no closure), but the file evolved
from `:= by sorry` to a real proof skeleton:
- `unfold gsChooseMax` + instance setup (letI/haveI for IsTrans on
  `gsMenPrefLE`)
- `Classical.choose_spec (Finset.exists_maximal h)` destructured as
  `⟨hmem, hmax⟩`
- `change` rewrites the goal to the disjunction form
- `by_cases heq : w = gsChooseMax prof σ m h`
- Equality case closed with `left; exact heq`
- Inequality case: derived `hne : ... ≠ ...` via `prof.menPref_bijective m`
  injectivity, then **`sorry`** on the final strict-inequality step (the
  maximality contradiction that uses `hmax`).

Stopped at +2517s (~42min) — the agent loop was caught in a recovery cycle
after a z.ai chat-client API error around +2453s and was not closing the
residual sorry. The agent had attempted 10+ `file_replace_sorry` calls all
ending in BUILD-FAIL, one decomposition attempt grew the sorries 1→2
("within budget 5") but still BUILD-FAILed and reverted.

Partial proof preserved as a forensic artifact in
`session_state/reference_docs/stable_marriage/c34-03-gsChooseMax_maximal-partial.lean`
for the next prover iteration to learn from. GSState.lean restored to the
#1120-merged proof (`git checkout`) — anti-regression respected.

**Trace:** `traces/multi_custom_GSState_L144_zai.json` (run cut short, partial
trace).

### What worked — C34-03
- **F6 already-solved fast-path** (this PR) prevents the DEMO 9 bug
  (file with 0 real sorry → loop agents + 300s compile). Mirrors F5 in
  shape: detected before agent spin-up, clean yield.
- **`--director-provider` flag** (this PR) lets the BG launcher wire the
  Director — without it the Director Python class was instantiated but
  the CLI couldn't enable it.
- **Real strategic insight from Coordinator.** At +93.7s: "the proof
  mirrors `gsChooseMax_mem` exactly, but uses the second component" —
  correctly identifying the sister lemma at GSState.lean:118 as the
  template. That insight came AFTER reference-docs grounding (#1129),
  consistent with C34-01/02 behaviour.
- **Coordinator set an attack_plan** (3 steps) rather than escalating
  intractable. First time the algo got past F5.

### Open weaknesses — C34-03 (forensic findings → next iterations)

1. **DirectorAgent has 0 invocations in the trace despite being wired.**
   The Coordinator never escalated `next_agent="director"`. The F1
   escalation chain (deterministic Critic→Coordinator after N build-fails)
   apparently does not include the Director leg, or its threshold was not
   met. **The "Director Opus 4.7 ACTIVE" claim earlier in this tour was
   wired but never executed — honest correction.** Next iteration must
   wire the F1 chain to escalate to Director after K build-fails (or
   reduce K) so the frontier model actually gets to weigh in on stuck
   targets.

2. **SearchAgent (local Qwen3.6 fast) burned ~217s emitting no final
   text — only tool calls.** The trace shows the [harness summary]
   reasoning-content burn previously documented in `agents.py:26-30`.
   The 16384 max_tokens budget bump helped but not enough. Consider:
   (a) downgrade Search to a non-reasoning model for tool-call work, or
   (b) hard-cap reasoning budget on Search and forward the partial
   tool-call output regardless.

3. **z.ai chat-client API error mid-run** (`OpenAIChatCompletionClient
   service failed to complete the prompt`) at +2453s. The agent loop
   recovered (CriticAgent caught it and routed to Search) but the loop
   then stalled — no further closure attempts succeeded. Need a budget
   cap on the recovery loop so a flaky upstream doesn't burn 30+ min.

4. **No iteration counter or wall-clock budget in workflow.py.** The
   max_iterations=10 setting did not stop the run at +2517s. Need an
   explicit per-run wall-clock budget (e.g. 600s default, override via
   CLI) so forensic runs are time-bounded.

5. **Cosmetic:** `traces/multi_custom_GSState_L144_zai*.json` were never
   written because the run was killed before the result block. Need a
   `try/finally` write so partial trace is always persisted.

### Recommendation for next session
- Wire the Director into the F1 escalation chain (it's the whole point
  of the frontier lane — exercise it on the stuck recovery state above).
- Add a `--wall-clock-budget` flag to `run_prover_bg.py` (default 600s).
- Re-run the gsChooseMax_maximal benchmark with the Director escalation
  fixed — this is the alternation slot for po-2026 once it finishes the
  bondareva skeleton.
- Track: the residual goal at GSState.lean:176 (after this PR's
  intermediate-state cookbook entry) is
  `prof.menPref m (gsChooseMax prof σ m h) < prof.menPref m w` under
  `hmax : ∀ x ∈ ..., Classical.choose ... ≤ x → Classical.choose ... = x`,
  `heq : w ≠ gsChooseMax ...`, `hne : prof.menPref m (...) ≠ prof.menPref m w`.
  The original proof closes it via `Nat.lt_trichotomy` + `rcases`. Provide
  this hint to the Director's reference docs.

## 2026-05-15 — forensic run C34-04 (F7 verification, FAILED)

**Setup:** PR #1135 F7 fix wires F1 escalation directly to Director when
the lane is wired and budget remains. Same revert-a-proven-sorry benchmark
as C34-03 (`gsChooseMax_maximal` at GSState.lean:144), same configuration
(zai GLM-5.1 local agents + OpenRouter Opus 4.7 Director).

**Outcome:** sorry 1 -> 1, FAILED at the 6000s wall-clock cap (the cap
itself addresses C34-03 open weakness #4 — already-present in this PR's
workflow). 68 trace entries: 30 build_check, 6 decomposition_progress,
13 TacticAgent, 10 SearchAgent, 4 CriticAgent, 3 CoordinatorAgent, **0
DirectorAgent**.

### Why F7 didn't fire — root cause

The F1 escalation in `VerifyExecutor` resets `_consecutive_build_fails`
to 0 whenever a decomposition succeeds (workflow.py:397, branch
`if msg.is_decomposition and new_sorry_count > msg.sorry_count`). The
6 decomposition_progress events in this run all triggered that reset.
Net effect: even with 30 BUILD-FAILs over 6000s, the consecutive counter
never reached the escalation threshold (5). F7 routes via the same
threshold, so it inherits the same blind spot.

The forensic ALSO showed real strategic progress that NEVER got promoted
to Director consultation:
- +1963s: TacticAgent attempted dual unfold (gsChooseMax + gsMenPrefLE)
- +2818s: SearchAgent queried mathlib for `gsMenPrefLE prof m w (gsChooseMax ...)`
- +5045s: TacticAgent attempted **`rcases Nat.lt_trichotomy (prof.menPref m w) (prof.menPref m (Classical.choose ...))`** — THE EXACT correct closure from the lessons_learned.json cookbook, but failed to integrate (`dsimp` artifact left lines 155-156 residual)
- +5988s: SearchAgent correctly identified meta-recursion (`gsChooseMax_maximal` lemma is itself the current goal — the agent recognized that the goal already exists as a named lemma in scope)
- +5156s: CriticAgent routed to CoordinatorAgent after 4 attempts following the same failed pattern — but CoordinatorAgent (3 total invocations) never escalated to Director

### F8 — next fix iteration

F7 hard-coded the right intent (skip Coordinator re-invocation) but used
the wrong trigger. **F8 should escalate to Director on `total_fails >= K`
in addition to (or instead of) consecutive_fails.** `_total_fails` is
already tracked on the executor (workflow.py:296) and is NOT reset by
decomposition. K=10 would have fired at ~+3500s in this run, giving the
Director a chance with the proof skeleton + the residual `Nat.lt_trichotomy`
attempt visible in the message history.

Alternative complementary fix: when decomposition introduces a new sorry
that ALSO fails on subsequent build, count THAT as a fail toward the F7
escalation. Currently decomposition is treated as "progress" even when
the sub-goals immediately fail.

### Honest verdict for PR #1135

- F7 wiring is correct (ast.parse OK, grep confirms 4 hook points).
- F7 did NOT trigger Director invocation on this benchmark.
- PR #1135 should NOT be merged as a "fix" without the F8 follow-up.
  Recommendation: keep #1135 open as wiring scaffold, ship F8 as the
  actual behavioral fix that exercises the Director on stuck targets.
