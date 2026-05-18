# Lean Prover Iteration History — Stable Marriage Project

**Period:** 2026-05-07 to 2026-05-18
**Machine:** myia-po-2026
**Status:** 6 sorrys remaining (all INTRACTABLE until new formalization)

---

## Summary

47 prover-related commits over 12 days. The multi-agent Lean 4 prover successfully proved 4 sorrys (hP_conv, hP_closed, hP_nonempty, hK_empty) while agent-guided manual proofs closed 10+ targets. The prover architecture went through 7 iterations (F6–F11, B3). All remaining sorrys require new mathematical formalization (rural hospitals theorem, Bondareva-Shapley core) that the prover cannot invent.

---

## 1. Prover Session Timeline

### Phase 1: Manual Foundations (May 7–14)

| Date | Target | Result | Key Insight |
|------|--------|--------|-------------|
| 2026-05-07 | Bondareva-Shapley forward | PROVED | Manual, committed `5ef28a8b` |
| 2026-05-12 | Voting L385 (minor) | PROVED | Multi-agent, committed `09adc8d2` |
| 2026-05-12 | CooperativeGames convex_core | PROVED sorry 3→2 | Manual, committed `8c00058f` |
| 2026-05-13 | Bondareva-Shapley backward | PROVED | Manual, committed `76284d33` |
| 2026-05-14 | Lemmas menProposedDownward.step | PROVED sorry 3→1 | Manual, committed `44fc4081` |
| 2026-05-14 | Lemmas womenBestState.step | PROVED | Manual, committed `0665cdea` |
| 2026-05-14 | KB seed + proof_knowledge.json | CREATED | Infrastructure `8902fa6d` |
| 2026-05-14 | Lemmas womenUnproposed | FAILED (69min BG) | Prover used wrong API |
| 2026-05-14 | Lemmas womenUnproposed | PROVED | Manual contrapositive `7ace74fb` |
| 2026-05-14 | 9 GS invariants | PROVED sorry 16→4 | Manual, committed `70664fae` |

### Phase 2: Prover Architecture Build-up (May 14–15)

| Date | Change | Commit |
|------|--------|--------|
| 2026-05-14 19:56 | mine_lean_sessions + run_prover_bg | `f93228dd` |
| 2026-05-14 20:27 | KB v3 upgrade + loop detection | `c1ba5862` |
| 2026-05-14 20:41 | Cookbook Bijective.injectivity | `ccd7273c` |
| 2026-05-14 22:03 | Cookbook maximal_trichotomy | `c9e3dd77` |
| 2026-05-14 22:22 | JSONL session mining | `87c2bd22` |
| 2026-05-15 03:42 | KB v3 refactor merged | `6feebd5d` |
| 2026-05-15 04:16 | DirectorAgent finalized (Opus 4.7) | `1a0348f6` |

### Phase 3: Prover Successes — Bondareva (May 15)

| Date | Target | Mode | Iters | Result |
|------|--------|------|-------|--------|
| 2026-05-15 15:25 | hP_conv (Basic L227) | multi (silent) | ~10 | PROVED sorry 5→3 |
| 2026-05-15 16:06 | hP_nonempty (Basic L237) | multi (silent) | ~8 | PROVED sorry 3→2 |
| 2026-05-15 16:47 | hK_empty (Basic L280) | autonomous | ~3 | PROVED sorry 2→1 |
| 2026-05-15 | hCore (Basic L308) | autonomous | 10 | INTRACTABLE (5.9h) |

**Key finding:** Multi-agent prover silently succeeds (writes proofs to disk but hangs on output). Always check `grep -c sorry` after "stuck" runs.

### Phase 4: GS Lemmas Manual Breakthrough (May 16)

| Date | Target | Result |
|------|--------|--------|
| 2026-05-16 13:52 | gsTerminated_allMenMatched | PROVED Lemmas 0 sorry |
| 2026-05-16 14:42 | gale_shapley_stable (6-step contradiction) | PROVED sorry 3→2 |
| 2026-05-16 18:16 | Migration stable_marriage_lean → GameTheory/ | MERGED #1201 |

### Phase 5: Knuth Lattice (May 16–17)

| Date | Target | Result |
|------|--------|--------|
| 2026-05-16 20:22 | join_isStable (Wu-Roth Lemma 3.2) | PROVED |
| 2026-05-17 15:57 | meet_inverse_anti_pref' (full proof) | PROVED sorry 6→5 |
| 2026-05-17 19:57 | meetSpouse_injective same-woman sub-cases | PROVED (2 sorrys) |

### Phase 6: Final Prover Runs (May 17–18)

| Date | Target | Mode | Iters | Result |
|------|--------|------|-------|--------|
| 2026-05-15 | GaleShapley L97 man_optimal | multi | 8 | INTRACTABLE |
| 2026-05-17 | GaleShapley L97 (F8+Director) | multi | 15 | INTRACTABLE (Director 2×) |
| 2026-05-18 | GaleShapley L97 (F8+Director) | multi | 15 | INTRACTABLE (9080s timeout) |

---

## 2. BUILD-FAIL Pattern Categories

From 20 prover history files containing 89 tactic attempts:

| Category | % of Fails | Description |
|----------|-----------|-------------|
| **Missing math infrastructure** | 37% | Rural hospitals, separating hyperplane, lattice duality — theorems not in codebase or Mathlib |
| **Incorrect API usage** | 25% | Wrong arg order, missing `@` implicit args, nonexistent lemma names |
| **Structural/unfold failures** | 20% | `dite`/`match` expressions resist `simp`, custom LE instances |
| **Type coercion issues** | 12% | `Fin n` `<=`/`<` require `mod_cast` before `omega` |
| **Prover infrastructure bugs** | 6% | Verifier treated lake config errors as build failure (fixed `7985e547`) |

### Top BUILD-FAIL Patterns

1. **dite artifacts**: After `simp only [gsStepWith]`, `match` expressions remain. Fix: `split at hmatch` or `rw [dif_pos hT]` before `simp`.

2. **Fin n comparisons**: `omega` fails on `Fin n` directly (nested coercions). Fix: `have : (a : Nat) ≤ (b : Nat) := mod_cast ha; omega`.

3. **Implicit-heavy API**: `proposedSet.mem_iff (m', w)` fails without `@`. Fix: `@proposedSet.mem_iff n _ prof σ (m', w)`.

4. **Classical.choose vs Option.get**: `Option.get` needs `isSome = true` but invariants give `≠ none`. Fix: `Classical.choose` + `Classical.choose_spec`.

5. **rcases before subst**: `subst` on reflexive equality (after prior unification) fails. Fix: `rcases` first, then `subst`.

---

## 3. Successful Proof Techniques

### Manual Proofs (Agent-Guided)

| Proof | Technique |
|-------|-----------|
| gale_shapley_stable | 6-step contradiction: assume blocking pair → derive each invariant violation |
| gsTerminated_allMenMatched | Pigeonhole: n proposed = n total → all matched |
| join_isStable | Wu-Roth Lemma 3.2: split into sub-goals by preference ordering |
| meet_inverse_anti_pref' | `¬hνpref` + meet condition → `Nat.le` both directions → injectivity → trivial `le_refl` |
| meetSpouse_injective | Stability sub-proofs + `le_refl` for same-woman cases |

### Prover Proofs

| Proof | Mode | Pattern |
|-------|------|---------|
| hP_conv | multi (silent) | convex_iInter — standard convexity tactics |
| hP_closed | multi (silent) | isClosed_iInter — standard topology tactics |
| hP_nonempty | multi (silent) | Constructive `|M|` cardinality witness |
| hK_empty | autonomous | linarith — simple arithmetic contradiction |

### Key Success Factors

1. Incremental 1–2 line changes → build → read error → adapt (most reliable)
2. Manual decomposition into sub-lemmas before attempting main proof
3. `change` to normalize expressions before `split`
4. `mod_cast` for Fin/Nat coercion before `omega`
5. Explicit `@` for implicit-heavy API calls

---

## 4. Failed Targets

| Target | Time Invested | Root Cause | Effort to Fix |
|--------|--------------|------------|---------------|
| hCore (Basic L308) | 5.9h (10 iters) | Missing hyperplane separation / Farkas' lemma | 100–150 lines |
| man_optimal (GaleShapley L116/L117) | ~24h across 3 sessions | Missing rural hospitals theorem | 80–120 lines |
| woman_pessimal (GaleShapley L146) | — | Depends on man_optimal + lattice duality | 40–60 lines (after man_optimal) |
| meetSpouse "different women" (Lattice L324/L387) | ~3h | Needs rural hospitals or lattice argument | 60–80 lines per case |
| doctor_optimal (Lattice L727) | — | Man-optimality rephrased as ManLE | 20–30 lines (after man_optimal) |

**Director (GPT-5.5) confirmation:** The missing piece is mathematical formalization, not search depth. The prover architecture functions correctly but cannot invent new theorems.

---

## 5. Prover Architecture Evolution

| Fix | Date | PR | Description |
|-----|------|-----|-------------|
| **DirectorAgent** | 2026-05-09 | — | Opus 4.7 escalation agent for hard targets |
| **Director finalize** | 2026-05-15 | #1129 | Reference docs injection, wall-clock trigger |
| **KB v3→v4** | 2026-05-15 | — | 13 new entries from postmortem, JSONL mining |
| **F6** | 2026-05-15 | #1134 | Already-solved fast-path, `--director-provider` CLI |
| **F7** | 2026-05-15 | #1135 | Wire F1 escalation directly to Director |
| **F8** | 2026-05-15 | — | `total_fails` trigger — stop after N consecutive build failures |
| **F9** | 2026-05-17 | #1227 | Gate `mark_sorry_intractable` behind Director consultation |
| **F10** | 2026-05-17 | — | Critical verifier bug fix (lake config error ≠ build failure) |
| **F11** | 2026-05-17 | #1231 | SearchAgent loop detection for sterile queries |
| **B3** | 2026-05-18 | #1225 | Constructive existential heuristic (regex parse ∃ goals → scan constructors) |

### Dual-Track Workflow (established May 11)

1. **ORIENT** — Identify target, check HONEST_SORRIES registry
2. **LAUNCH BG** — Run prover in background
3. **WORK OTHER** — Immediately continue with dispatched tasks (2 tracks minimum, rule G.5)
4. **REVIEW** — Check traces at intervals (not event-by-event)
5. **ITERATE** — Improve based on postmortem

---

## 6. Statistics

- **Prover-related commits:** 47
- **Proofs proved by prover:** 4 (hP_conv, hP_closed, hP_nonempty, hK_empty)
- **Proofs proved manually (agent-guided):** 15+ (including all GS invariants, lattice, Bondareva forward/backward)
- **Prover infrastructure iterations:** 7 (F6–F11, B3)
- **Remaining sorrys:** 6 (5 rural hospitals cluster + 1 Bondareva hCore)
- **Prover history files:** 20 JSON files in `agent_tests/prover/`

---

## 7. Files

- **Prover source:** `MyIA.AI.Notebooks/GameTheory/stable_marriage_lean/prover/` (agents.py, workflow.py, tools.py, provers.py, config.py)
- **Knowledge base:** `prover/proof_knowledge.json`
- **History files:** `agent_tests/prover/*.json`
- **Intractable diagnosis:** `docs/lean/stable_marriage_intractable_diagnosis.md`
- **CI workflow:** `.github/workflows/lean-game-theory.yml`
