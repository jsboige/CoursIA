# Stable Marriage - Lean 4 Formalization

Lean 4 formalization of the **Gale-Shapley Stable Marriage Theorem** (1962).

## Overview

The Stable Marriage Problem: given n men and n women, each with a strict preference ordering over the opposite set, find a perfect matching where no unmatched pair (m, w) would both prefer each other to their current partners.

| File | Content | Status |
|------|---------|--------|
| `StableMarriage/Definitions.lean` | Types, preference profiles, matchings, stability | Scaffold (compiles) |
| `StableMarriage/GaleShapley.lean` | Algorithm, stability/optimality theorems | 4 sorry |

## Theorems (planned)

| Theorem | Statement | sorry |
|---------|-----------|-------|
| `gale_shapley_terminates` | Algorithm terminates in at most n^2 steps | 1 |
| `gale_shapley_produces_matching` | Output is a valid bijection | 1 |
| `gale_shapley_stable` | No blocking pair exists | 1 |
| `gale_shapley_man_optimal` | Proposers get best achievable partners | 1 |
| `gale_shapley_woman_pessimal` | Receivers get worst achievable partners | 1 |

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
