# KS Pilier 1 — Candidate Proofs for L159 + L176 (UNVERIFIED)

**Date:** 2026-05-28
**Branch:** `feature/conway-ks-prover-1651`
**File targeted:** `MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/KochenSpecker.lean`
**Status:** **UNVERIFIED** — `lake build` blocked by olean header corruption (cache get rev mismatch). KochenSpecker.lean is **NOT** modified by this branch (`grep -c sorry` = 2 preserved per anti-regression.md).

## Pre-flight baseline

```bash
$ grep -n "sorry" MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/Conway/KochenSpecker.lean
159:  sorry  -- TODO Pilier 1: verify by `decide` / explicit case-split on v
176:  sorry  -- TODO Pilier 1: parity argument via Finset double-sum reorder
```

## Blockers encountered

1. **Olean header corruption** — `failed to read file '.../Mathlib/Data/Real/Basic.olean', incompatible header`.
   - Root cause: partial `lake exe cache get` overlays on top of a manifest-mismatched build dir.
   - Symptom: `Mathlib.Tactic.olean` timestamp 21:37, `Real.Basic` 21:38, `Fin.Basic` 22:41 (inconsistent).
   - Fix candidate (not attempted — would race with sibling BG agents on same dir):
     ```bash
     rm -rf MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/.lake/packages/mathlib/.lake/build/
     cd MyIA.AI.Notebooks/SymbolicAI/Lean/conway_lean/ && lake exe cache get && lake build Conway.KochenSpecker
     ```

2. **Workspace contention** — parallel Lean-13 Grothendieck + Lean-14 Conway GoL BG agents racing for the same `.lake/packages/mathlib/.lake/build/` directory. My `lake build Conway.KochenSpecker` timed out at 388/3316 modules after 600s (cold rebuild while sibling holds files).

3. **Prover script (DEMO 53/54) could not run** — `LeanVerifier` would block on the same broken `lake build`. Per `feedback-lean-no-manual-proofs.md` the prover is the primary tool, but env precludes invocation.

## Candidate proof — L159 `each_vector_in_two_contexts`

Cabello overlap is fully concrete (9 contexts × 4 = 36 case-rows in `contextMembers`). `fin_cases v <;> decide` should resolve all 18 vectors mechanically — each unfolds the 36-case `contextMembers` and counts the `if .. = v` hits (always 2 by the Cabello construction).

```lean
lemma each_vector_in_two_contexts (v : VecIdx) :
    (∑ k : ContextIdx, ∑ i : Fin 4,
      if contextMembers k i = v then (1 : ℕ) else 0) = 2 := by
  fin_cases v <;> decide
```

Alternative if `decide` times out: explicit `<;> rfl` after a more aggressive `simp [contextMembers, Finset.sum_fin_eq_sum_range]` unfolding.

## Candidate proof — L176 `kochen_specker`

Parity argument: total sum = 9 (odd, from `IsValidColoring`) vs total sum = 2 × #colored (even, from the lemma). Sketch verified pen-and-paper against the textbook proof.

```lean
theorem kochen_specker : ¬ ∃ c : Coloring, IsValidColoring c := by
  rintro ⟨c, hc⟩
  -- Total count = 9 via hc (1 per context, 9 contexts)
  have htotal : (∑ k : ContextIdx, ∑ i : Fin 4,
      if c (contextMembers k i) then (1 : ℕ) else 0) = 9 := by
    have : ∀ k : ContextIdx,
        (∑ i : Fin 4, if c (contextMembers k i) then (1 : ℕ) else 0) = 1 := hc
    simp [this]
  -- Reorder: same total = ∑ v 2 * [c v]
  have hreord : (∑ k : ContextIdx, ∑ i : Fin 4,
      if c (contextMembers k i) then (1 : ℕ) else 0) =
      ∑ v : VecIdx, 2 * (if c v then (1 : ℕ) else 0) := by
    rw [show (∑ k : ContextIdx, ∑ i : Fin 4,
        if c (contextMembers k i) then (1 : ℕ) else 0) =
        ∑ v : VecIdx, (∑ k : ContextIdx, ∑ i : Fin 4,
          if contextMembers k i = v then (if c v then (1 : ℕ) else 0) else 0) from ?_]
    · apply Finset.sum_congr rfl; intro v _
      have hv := each_vector_in_two_contexts v
      have : (∑ k : ContextIdx, ∑ i : Fin 4,
            if contextMembers k i = v then (if c v then (1 : ℕ) else 0) else 0) =
          (if c v then (1 : ℕ) else 0) *
            (∑ k : ContextIdx, ∑ i : Fin 4,
              if contextMembers k i = v then (1 : ℕ) else 0) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
        split_ifs <;> simp
      rw [this, hv]; ring
    · apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_ite_eq' Finset.univ (contextMembers k i)
        (fun v => if c v then (1 : ℕ) else 0)]
      simp
  -- 9 = 2 * sum_v [c v] is impossible (9 odd)
  have : (9 : ℕ) = 2 * ∑ v : VecIdx, (if c v then (1 : ℕ) else 0) := by
    have := htotal.symm.trans hreord
    simpa [Finset.mul_sum] using this
  omega
```

Risk points (if a future iteration tries these):
- The `rw [show ... from ?_]` deferred-goal trick may need `refine` instead.
- `Finset.sum_ite_eq'` requires `DecidableEq` on `VecIdx` — `Fin 18` has it.
- `Finset.mul_sum` inside `simpa [Finset.mul_sum]` could loop — try `linear_combination` or `Finset.sum_const` + manual algebra if it does.
- `ring` over `ℕ` works only because all terms are `≥ 0`; `omega` finishes the parity contradiction.

## Recommendation to next iteration

1. **Nuke + clean rebuild** the conway_lean Mathlib build dir BEFORE any prover invocation.
2. Verify L159 with `fin_cases v <;> decide` first (cheapest, isolated). If it works, drop the explicit branch enumeration.
3. Then try L176 with the candidate above. If the `rw [show .. from ?_]` fails, the inner `Finset.sum_ite_eq'` step likely needs `Finset.sum_eq_single` instead.
4. Fallback: if the inner reorder is too brittle, prove L176 by `decide` directly over `(c : Fin 18 → Bool)` enumeration (2^18 = 262144 cases) — slow but mechanical.

## What was actually committed this cycle

Only `lean_server.py` (+22/-12) — WSL backend preference toggle for `_resolve_lake_command` so `LEAN_USE_WSL=1` takes precedence over Windows `lake.exe` (the Windows lake.exe was triggering 1-2h Mathlib rebuilds because OS-specific `.c` IR files differ). `KochenSpecker.lean` left untouched (sorry=2 preserved). Test proofs file (`KS_test_proofs.lean`) kept untracked — explicitly tagged "DO NOT COMMIT" until verified.
