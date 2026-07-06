# Social Choice Lean - Formal Verification Status

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.31.0-rc1` |
| Mathlib | `v4.31.0-rc1` |
| Last CI verified | 2026-05-26 |
| Total sorry | **0** (all production files) |
| Total lines | 2,676 (7 modules) |
| Total theorems/lemmas | 76 |
| Total definitions | 53 |

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
| Lines | 875 |
| Definitions | 22 |
| Theorems/lemmas | 19 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Key results (all 0 sorry):

- **Margins**: `margin_antisymm`, `margin_self`, `margin_pos_iff_neg_rev`, `margin_pos_of_unanimous`.
- **Condorcet**: `condorcet_winner_unique`, `condorcet_winner_not_loser`.
- **Single-peaked / median voter**: `single_peaked_peak_unique`, `single_peaked_peak_best`,
  `median_voter_theorem_strict`, `median_voter_theorem`.
- **Cycles & acyclicity**: `cycle_length_pos`, `rotate_cycle`, `lt_acyclic`, `split_cycle_condorcet`.
- **Clone structure / tournaments**: `clone_set_nonempty`, `banks_set_subset`, `banks_set_condorcet`.

Port of chasenorman/Formalized-Voting. The three former sorries (Finset counting/sorting,
`IsChain` construction, rotated-list cycle contradiction) — historically gating the median
voter and single-peaked proofs — are now fully resolved (0 sorry), closed via the dedicated
`SortedListCounting.lean` combinatorial machinery (median counting lemmas).

### SocialChoice/MechanismDesign.lean — VICKREY AUCTION (MECHANISM DESIGN)

| Metric | Value |
|--------|-------|
| Lines | 76 |
| Definitions | 2 |
| Theorems | 4 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Truthfulness / incentive-compatibility of auction rules (extending the project beyond
pure social choice into mechanism design):

- `vickrey_truthful_bidder0`, `vickrey_truthful_bidder1` — the second-price (Vickrey)
  auction is truthful: bidding one's true valuation is a dominant strategy.
- `first_price_not_truthful` — the first-price auction is **not** truthful
  (counter-example to incentive compatibility).
- `vickrey3_truthful_bidder0` — truthfulness extends to the 3-bidder Vickrey auction.

### SocialChoice/SortedListCounting.lean — MEDIAN-COUNTING LEMMAS

| Metric | Value |
|--------|-------|
| Lines | 185 |
| Definitions | 0 |
| Theorems | 5 |
| sorry | **0** |
| Status | FORMAL-CERTIFIED |

Combinatorial lemmas on sorted lists and `Finset.filter` cardinality that back the
median-voter counting arguments in `Voting.lean`: `countP_lt_kth_le_half`,
`countP_ge_kth_ge_half_succ`, `countP_le_kth_ge_half_succ`,
`finset_filter_card_eq_toList_countP`, `finset_filter_lt_card_eq_toList_map_countP`.
Decoupled from the voting module so the counting kernel is reusable.

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
| `margin_antisymm` | Voting.lean | Margin function antisymmetry |
| `condorcet_winner_unique` | Voting.lean | Condorcet winner is unique |
| `single_peaked_peak_unique` | Voting.lean | Single-peaked preference has a unique peak |
| `median_voter_theorem` | Voting.lean | Majority selects the median voter's peak (single-peaked) |
| `median_voter_theorem_strict` | Voting.lean | Strict single-peaked median voter theorem |
| `split_cycle_condorcet` | Voting.lean | Split Cycle satisfies the Condorcet criterion |
| `countP_lt_kth_le_half` | SortedListCounting.lean | Median-counting kernel lemma |
| `vickrey_truthful_bidder0` | MechanismDesign.lean | Vickrey (2nd-price) auction is truthful (bidder 0) |
| `vickrey_truthful_bidder1` | MechanismDesign.lean | Vickrey auction is truthful (bidder 1) |
| `first_price_not_truthful` | MechanismDesign.lean | First-price auction is not truthful |
| `vickrey3_truthful_bidder0` | MechanismDesign.lean | 3-bidder Vickrey auction is truthful |

### In Progress (contains sorry)

None — all modules are fully certified (0 sorry). The three former `Voting.lean` sorries
gating the median-voter / single-peaked proofs were resolved via the `SortedListCounting.lean`
counting kernel; Vickrey truthfulness (`MechanismDesign.lean`) is fully proved.

## Certification Level

| File | Level |
|------|-------|
| Basic.lean | CERTIFIED (0 sorry) |
| Framework.lean | CERTIFIED (0 sorry) |
| Arrow.lean | CERTIFIED (0 sorry) |
| Sen.lean | CERTIFIED (0 sorry) |
| Voting.lean | CERTIFIED (0 sorry) |
| MechanismDesign.lean | CERTIFIED (0 sorry) |
| SortedListCounting.lean | CERTIFIED (0 sorry) |

**Project certification: COMPLETE** — all seven modules fully certified (0 sorry). Arrow,
Sen and the Voting/median-voter results are all closed, and the project additionally covers
mechanism design (Vickrey truthfulness) backed by a dedicated median-counting kernel.

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
| 2026-05-26 | Toolchain upgrade v4.29.1 -> v4.30.0-rc2, 0 sorry | — |
| 2026-06-23 | **Docs anti-dérive (G.1 source-verified):** FORMAL_STATUS was stale — Voting.lean had grown 340->875 lines and its 3 historical sorries were resolved (median-counting kernel `SortedListCounting.lean`), yet the doc still said "3 sorry / FORMAL-PARTIAL". Corrected: Voting 0 sorry/CERTIFIED, project PARTIAL->COMPLETE, total lines 1,872->2,676, theorems 62->76. Added undocumented modules `MechanismDesign.lean` (Vickrey truthfulness) + `SortedListCounting.lean` to per-file status + inventory. README.md (FR) structure + counts realigned. | po-2026 |
