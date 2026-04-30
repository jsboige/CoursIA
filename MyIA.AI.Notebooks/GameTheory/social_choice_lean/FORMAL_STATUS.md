# Social Choice Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.29.1` |
| Mathlib | `v4.29.1` (`5e932f97dd25`) |
| Last CI verified | 2026-04-30 (CI GREEN) |
| Total sorry | **0** (all files) |
| Total lines | 1,872 |
| Total theorems | 62 |
| Total definitions | 60 |

## Per-File Status

### SocialChoice/Basic.lean — FOUNDATIONAL

| Metric | Value |
|--------|-------|
| Lines | 207 |
| Definitions | 15 |
| Theorems | 16 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Key definitions: `PrefOrder`, `P` (strict preference), `I` (indifference), `Profile`, `SWF`,
`maketop`/`makebot`/`makeabove` preference modifiers.

### SocialChoice/Framework.lean — FRAMEWORK

| Metric | Value |
|--------|-------|
| Lines | 266 |
| Definitions | 16 |
| Theorems | 8 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Helper infrastructure: `PrefOrder` constructors, relation lemmas, Finset cardinality utilities.

### SocialChoice/Arrow.lean — ARROW'S IMPOSSIBILITY THEOREM

| Metric | Value |
|--------|-------|
| Lines | 701 |
| Definitions | 7 |
| Theorems | 22 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Proof chain (Geanakoplos 2005):
1. `extremal_lemma` — if all place b at top or bottom, society does too
2. `pivot_exists` — every alternative has a pivotal individual
3. `pivot_is_dictator_except_b` — pivots are dictators on non-b pairs
4. `partial_dictator_is_full_dictator` — partial dictatorship extends to full
5. `arrow` — main theorem: Pareto + IIA = dictatorship on 3+ alternatives
6. `no_perfect_swf` — corollary: no SWF satisfies all desiderata

### SocialChoice/Sen.lean — SEN'S LIBERAL PARADOX

| Metric | Value |
|--------|-------|
| Lines | 358 |
| Definitions | 2 |
| Theorems | 2 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Theorems:
- `sen_impossibility` — minimal liberalism + weak Pareto = inconsistent on 3+ alternatives
- `book_paradox_demonstrates_sen` — concrete instance with book allocation

### SocialChoice/Voting.lean — VOTING THEORY

| Metric | Value |
|--------|-------|
| Lines | 340 |
| Definitions | 20 |
| Theorems | 14 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Key results: margin function antisymmetry, Condorcet winner uniqueness,
Condorcet loser disjointness, single-peaked preferences, Split Cycle, clone properties.

Port of chasenorman/Formalized-Voting.

## Theorem Inventory

### Certified (0 sorry)

| Theorem | File | Statement |
|---------|------|-----------|
| `arrow` | Arrow.lean | Pareto + IIA = dictatorship (3+ alts) |
| `no_perfect_swf` | Arrow.lean | No SWF satisfies all Arrow conditions |
| `sen_impossibility` | Sen.lean | Liberalism + Pareto = inconsistent |
| `book_paradox_demonstrates_sen` | Sen.lean | Concrete Sen paradox instance |
| `extremal_lemma` | Arrow.lean | Extremal placement property |
| `pivot_exists` | Arrow.lean | Pivotal individual exists |
| `pivot_is_dictator_except_b` | Arrow.lean | Pivot = dictator on non-b pairs |
| `partial_dictator_is_full_dictator` | Arrow.lean | Partial = full dictatorship |

### In Progress

None. All production theorems are sorry-free.

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | CERTIFIED (0 sorry) |
| Framework.lean | CERTIFIED (0 sorry) |
| Arrow.lean | CERTIFIED (0 sorry) |
| Sen.lean | CERTIFIED (0 sorry) |
| Voting.lean | CERTIFIED (0 sorry) |

**Project certification: FULL** — all source files compile with 0 sorry.

## References

- Original Lean 3 source: [asouther4/lean-social-choice](https://github.com/asouther4/lean-social-choice)
- Geanakoplos, J. (2005). "Three Brief Proofs of Arrow's Impossibility Theorem"
- Sen, A. (1970). "The Impossibility of a Paretian Liberal"
- Voting: [chasenorman/Formalized-Voting](https://github.com/chasenorman/Formalized-Voting)

## History

| Date | Change | Commit |
|------|--------|--------|
| 2026-01-31 | Initial port from asouther4/lean-social-choice (Lean 3) | `1ce6a047` |
| 2026-04-19 | Sen impossibility theorem completed (0 sorry) | `28d3bb5e` |
| 2026-04-24 | Anti-regression fix: restore 9 proofs from rogue commit | `47975400` revert |
| 2026-04-28 | Voting.lean — Condorcet concepts, 0 sorry | `e45e6538` |
| 2026-04-29 | Toolchain upgrade v4.28.0-rc1 -> v4.29.1 | `c1b2cde1` |
| 2026-04-30 | FORMAL_STATUS.md created, CI cache fix | PR-G |
