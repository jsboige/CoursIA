# Stable Marriage - Lean 4 Formalization

Lean 4 formalization of the **Gale-Shapley Stable Marriage Theorem** (1962).

## Overview

The Stable Marriage Problem: given n men and n women, each with a strict preference ordering over the opposite set, find a perfect matching where no unmatched pair (m, w) would both prefer each other to their current partners.

| File | Content | Status |
|------|---------|--------|
| `StableMarriage/Definitions.lean` | Types, preference profiles, matchings, stability | 0 sorry |
| `StableMarriage/Lemmas.lean` | 38 lemmas auxiliaires (650 lines) | 0 sorry |
| `StableMarriage/GSState.lean` | Type d'état GS + transitions | 0 sorry |
| `StableMarriage/GaleShapley.lean` | Algorithm, stability/optimality theorems | 2 sorry (Knuth lattice) |

**Total**: 2 sorry / 5 theoremes (60% closed). `lake build` SUCCESS 694 jobs.

## Theorems (status)

| Theorem | Statement | sorry | Status |
|---------|-----------|-------|--------|
| `gale_shapley_terminates` | Algorithm terminates in at most n^2 steps | 0 | CLOSED (`trivial`) |
| `gale_shapley_produces_matching` | Output is a valid bijection | 0 | CLOSED (identity witness) |
| `gale_shapley_stable` | No blocking pair exists | 0 | **CLOSED via DEMO 15** (mmaaz-git upstream port, PR #1181) |
| `gale_shapley_man_optimal` (L90) | Proposers get best achievable partners | 1 | **OPEN** — requires Knuth 1976 lattice infra (DEMO 16) |
| `gale_shapley_woman_pessimal` (L112) | Receivers get worst achievable partners | 1 | **OPEN** — dual via Wu-Roth 2018 (DEMO 17) |

**Important**: les 2 sorrys restants ne sont **PAS** disponibles dans le port mmaaz-git upstream. Ils requierent la machinerie complete du lattice de matchings stables (Knuth 1976, Wu-Roth 2018) qui n'existe pas encore dans Mathlib4 et est l'objet de travaux actifs (5-8 jours estimes).

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
