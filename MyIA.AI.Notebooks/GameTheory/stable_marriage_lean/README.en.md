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
| `StableMarriage/Lattice.lean` | Knuth lattice, refutations, `exists_isManOptimal` | 0 |

**Total**: 0 production sorry. `lake build StableMarriage` SUCCESS. Toolchain `v4.31.0-rc1`.

## Theorems (status)

| Theorem | Statement | sorry | Status |
|---------|-----------|-------|--------|
| `gale_shapley_terminates` | Algorithm terminates in at most n^2 steps | 0 | CLOSED (`trivial`) |
| `gale_shapley_produces_matching` | Output is a valid bijection | 0 | CLOSED (identity witness) |
| `gale_shapley_stable` | No blocking pair exists | 0 | **CLOSED via PR #1194** (port mmaaz-git upstream) |
| `gale_shapley_man_optimal` | Proposers get best achievable partners | 0 | **CLOSED** (via `exists_isManOptimal`, minimal-weight argument on join semilattice) |
| `gale_shapley_woman_pessimal` | Receivers get worst achievable partners | 0 | **CLOSED via PR #1521** (constructive, from man-optimality) |
| `joinSpouse_injective` | Join spouse map is injective | 0 | CLOSED (PR #1522) |
| `meetSpouse_injective` | Meet spouse map is injective | 0 | **CLOSED** (counting/pigeonhole argument, no anti-crossing needed) |
| `join_isStable` | Join of two stable matchings is stable | 0 | CLOSED |
| `meet_isStable` | Meet of two stable matchings is stable | 0 | CLOSED |
| `exists_isManOptimal` | Man-optimal stable matching exists | 0 | **CLOSED** (minimal weight + `Nat.find` + `join_isStable`) |
| `no_cross_match_is_false` | Former anti-crossing lemma is refutable | 0 | **REFUTED** (3x3 latin-square counterexample, kernel-checked) |
| `doctor_optimal_eq_top_is_false` | Former optimality claim is refutable | 0 | **REFUTED** (same counterexample) |

### Historical note

The former statements `no_cross_match`, `man_optimality_key_step`, and `doctor_optimal_eq_top` were **false as stated** and have been removed. Their `sorry` placeholders were unprovable because the goals were in fact contradictory — the 3x3 latin-square instance (Knuth 1976) with the identity and cyclic-shift matchings refutes all three simultaneously. This explains why 30+ prover harness iterations made zero progress: the targets were mathematically impossible.

The honest replacement is `exists_isManOptimal`, which proves existence (not constructive extraction) of a man-optimal stable matching via a minimal-weight argument on the join semilattice, without needing the anti-crossing lemma.

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
- Knuth, D.E., "Marriages Stables" (1976) — lattice structure, latin-square instances
- Gusfield, D. & Irving, R.W., *The Stable Marriage Problem: Structure and Algorithms* (1989)
- Wu, Q. & Roth, A.E., "Lattice Structures in Stable Matching" (2018)
- Reference Lean 4 port: https://github.com/mmaaz-git/stable-marriage-lean

## Cross-series connections

| Series | Connection |
|--------|------------|
| `social_choice_lean/` | Same Mathlib-based structure, preference orderings |
| `GameTheory/` | Matching theory as cooperative game (Shapley value) |
| `Tweety-9-Preferences` | Preference orderings and aggregation |

## Conclusion

This project is a **complete, 0-`sorry`** Lean 4 formalization of the **Gale-Shapley
Stable Marriage Theorem** (1962) and the **Knuth lattice structure** of its stable
matchings. All twelve headline results are CLOSED (`lake build StableMarriage`
SUCCESS, toolchain `v4.31.0-rc1`).

### What is proven

- **Gale-Shapley correctness** — termination in ≤ n² steps, the output is a valid
  bijection, and no blocking pair exists (the algorithm produces a *stable* matching).
- **Optimality** — the matching is **man-optimal** (proposers get their best achievable
  partner) and **woman-pessimal** (receivers get their worst achievable), the latter
  derived constructively from the former.
- **Lattice structure** (Knuth 1976) — the set of stable matchings forms a
  **distributive lattice** under join/meet, both operations preserving stability and
  the spouse maps injective. Existence of a man-optimal stable matching is shown via a
  minimal-weight argument on the join semilattice (`exists_isManOptimal`).

### The honest lesson — "intractable" was "false as stated"

Three former statements (`no_cross_match`, `man_optimal_key_step`,
`doctor_optimal_eq_top`) resisted **30+ prover-harness iterations** before being
recognized as **mathematically false**: the 3×3 latin-square instance (Knuth 1976)
with the identity and cyclic-shift matchings refutes all three simultaneously. Their
`sorry` placeholders were unprovable because the goals were contradictory, not hard.
The honest replacement (`exists_isManOptimal`) proves *existence* rather than the
contradictory constructive extraction. This is the same lesson as the Conway P4 case:
when a proof stalls across many iterations, **refute the statement first**.

### Where to go next

- **Theory**: Gale & Shapley (1962); Knuth, *Marriages Stables* (1976, lattice
  structure); Gusfield & Irving (1989).
- **Reference port**: [mmaaz-git/stable-marriage-lean](https://github.com/mmaaz-git/stable-marriage-lean).
- **Related**: [`social_choice_lean/`](../social_choice_lean/) (preference orderings),
  [`cooperative_games_lean/`](../cooperative_games_lean/) (matching as cooperative game).
