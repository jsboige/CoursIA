# Stable Marriage - Lean 4 Formalization

Lean 4 formalization of the **Gale-Shapley Stable Marriage Theorem** (1962).

## Overview

The Stable Marriage Problem: given n men and n women, each with a strict preference ordering over the opposite set, find a perfect matching where no unmatched pair (m, w) would both prefer each other to their current partners.

| File | Content | sorry |
|------|---------|-------|
| `StableMarriage/Defs.lean` | Core type definitions (preferences, profiles, matchings, stability) | 0 |
| `StableMarriage/Lemmas.lean` | Helper lemmas (`gsFinalMatching`, `gsAllWomenMatched`, `gsNoBlockingPairs`) | 0 |
| `StableMarriage/GSState.lean` | GS state machine, `gsChooseMax` | 0 |
| `StableMarriage/GaleShapley.lean` | Termination, stability, `man_optimal`, `woman_pessimal` | 0 |
| `StableMarriage/Lattice.lean` | Knuth rotation lattice (Case A2, Case B, `doctor_optimal_eq_top` conditional) | 3 |

**Total**: 3 production sorry, all in `Lattice.lean` (Knuth rotation sub-cases). `lake build StableMarriage` SUCCESS. Toolchain `v4.30.0-rc2`.

Le prover test harness `_GoalExtract.lean` contient 2 sorry de scaffolding (non-production).

## Theorems (status)

| Theorem | Statement | sorry | Status |
|---------|-----------|-------|--------|
| `gale_shapley_terminates` | Algorithm terminates in at most n^2 steps | 0 | CLOSED (`trivial`) |
| `gale_shapley_produces_matching` | Output is a valid bijection | 0 | CLOSED (identity witness) |
| `gale_shapley_stable` | No blocking pair exists | 0 | **CLOSED via PR #1194** (port mmaaz-git upstream) |
| `gale_shapley_man_optimal` | Proposers get best achievable partners | 0 (body) | **CLOSED via PR #1521** body, BUT transitively depends on `doctor_optimal_eq_top` (L836 sorry) — see note below |
| `gale_shapley_woman_pessimal` | Receivers get worst achievable partners | 0 (body) | **CLOSED via PR #1521** body, BUT same transitive dependency on L836 |
| `meetSpouse_injective` | Spouse map is injective | 0 | **CLOSED via PR #1522** (multi-agent prover GPT-5.5) |
| `Lattice.no_cross_match` Case A2 (L185) | Knuth rotation Case A2 | 1 | INTRACTABLE (Knuth 1976 sub-case, user mandate "stays as sorry" per PR #1530) |
| `Lattice.no_cross_match` Case B (L187) | Knuth rotation Case B | 1 | INTRACTABLE (Knuth 1976 sub-case, same mandate) |
| `doctor_optimal_eq_top` (L836) | Doctor-optimal = top of stable lattice | 1 | Transitively conditional on `no_cross_match` (L185/L187 sorry, **NOT axiom**) |

**Important — transitive dependency** : les theoremes `gale_shapley_man_optimal` et `gale_shapley_woman_pessimal` ont 0 sorry **dans leur corps** mais appellent `doctor_optimal_eq_top` (L836) qui contient 1 sorry. Le claim "CLOSED via PR #1521" est correct au sens mecanique (corps des theoremes principaux fermes) mais **incomplet au sens transitif**. Les 3 sorrys restants vivent dans `Lattice.lean` et representent la machinerie complete du lattice de matchings stables (Knuth 1976, Wu-Roth 2018) qui n'existe pas encore dans Mathlib4. `no_cross_match` est un `lemma ... := by sorry` (PAS un `axiom`), per mandate user PR #1530. Tous **INTRACTABLE** par le prover LLM courant (4 traces 2026-05-23/24 sur A2/B/L836 = 0 sorry-delta net, cf `agent_tests/prover/traces/*Lattice*.json` et [LEAN_INVENTORY.md](../LEAN_INVENTORY.md) GO/NO-GO per project).

## Quick Start

```bash
# Build (requires elan + Lake)
cd stable_marriage_lean
lake build

# Check sorry count
grep -c sorry StableMarriage/*.lean
```

## References

- Gale, D. & Shapley, L.S., "College Admissions and the Stability of Marriage" (American Mathematical Monthly, 1962)
- Gusfield, D. & Irving, R.W., *The Stable Marriage Problem: Structure and Algorithms* (1989)
- Roth, A.E., "The Economics of Matching: Stability and Incentives" (1982)
- Reference Lean 4 port: https://github.com/mmaaz-git/stable-marriage-lean

## Cross-series connections

| Series | Connection |
|--------|------------|
| `social_choice_lean/` | Same Mathlib-based structure, preference orderings |
| `GameTheory/` | Matching theory as cooperative game (Shapley value) |
| `Tweety-9-Preferences` | Preference orderings and aggregation |
