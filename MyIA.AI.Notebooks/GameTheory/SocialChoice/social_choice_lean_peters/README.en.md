# Social Choice Lean (Peters Reference)

Reference project importing [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) as a Lake dependency. Curated tour of Peters' formalized results.

## Status

- **Toolchain**: `leanprover/lean4:v4.32.1` (aligned with the fleet, effective `lean-toolchain` pin)
- **Sorry count**: 0 production sorry
- **Build**: `lake build` -- SUCCESS
- **Dependencies**: Mathlib4 (`520045ab`), DominikPeters/SocialChoiceLean (`94a4c650`) — effective `lake-manifest.json` revs

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `PetersTour.lean` | 0 | Curated tour of Peters' formalized results |

## Key Results

Imports and demonstrates Peters' library, including:

- **Gibbard-Satterthwaite**: Strategy-proofness implies dictatorship (>= 3 candidates)
- **Duggan-Schwartz**: Extension to multi-winner with optimist/pessimist strategy-proofness
- **4 Condorcet impossibilities**: Participation, Reinforcement, Strategy-proofness, Anon+Neutral+Resolute
- **15+ voting rules** with axiom verification: Split Cycle, Schulze, Copeland, Black, IRV, Borda, etc.

## Relationship to `social_choice_lean`

Complementary, not duplicate. `social_choice_lean` uses custom `PrefOrder` (our proofs); this project uses Peters' `LinearOrder` (external reference). Different frameworks, different proofs.

## Notes

- Backend Lake for a (planned, not yet created) tour companion notebook
- Peters' repo pinned at commit `94a4c650b6a3ef14df801a613c3b46169dbd754d` (`lake-manifest.json` rev) for reproducibility
- Peters uses `LinearOrder` (strict, Mathlib); we use `PrefOrder` (reflexive, total, transitif)

## EPIC #4365 Status (anti-proliferation GT 6→2)

This lake is **explicitly out of scope** for absorption into
[`game_theory_lean/`](../game_theory_lean/) under EPIC #4365 Phase 4 (merge
cohesive post-convergence lakes). History of the status:

1. **Upstream lock (`INTRINSIC` verdict, since lifted)**: at decision time
   (c.576, 2026-07-17), the external repo
   [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean)
   was pinned at `355075e3` on the `v4.27.0-rc1` family, and its port to the
   post-#4364 target was not under our control — `INTRINSIC` verdict per
   [`sota-not-workaround.md`](../../../.claude/rules/sota-not-workaround.md).
   **That lock was lifted by upstream itself**: since 2026-08-21 (#12134,
   commit `d8ec0b08ba`), the effective pin is Peters `94a4c650` /
   Mathlib `520045ab` on `lean-toolchain` `v4.32.1` — the family of the rest
   of the fleet. The #4364 convergence now applies here too; Peters is no
   longer a v4.27 residue.

2. **Distinct semantic framework (still active)**: this lake exposes a Mathlib
   strict `LinearOrder` which **does not** line up with the
   reflexive-total-transitive `PrefOrder` API used by
   `game_theory_lean/SocialChoice/`. A merge would force either (a) a dual
   linear/preorder port or (b) a rewrite of Peters' proofs. **This is the
   autonomy rationale that remains** after the toolchain convergence: this
   lake is an *external port* (the proofs are Peters') while
   `game_theory_lean/` carries our own proofs.

**Consequence**: `social_choice_lean_peters/` stays a **self-contained
autonomous lake** with its own `lake build`, its own `lean-toolchain`
`v4.32.1` (converged), and its own CI. Autonomy is no longer motivated by a
version lock — it is motivated by the nature of the project: a reference tour
of an external library, in its own semantic framework.

Firsthand status check (2026-08-26): `lake-manifest.json` Peters rev
`94a4c650b6a3ef14df801a613c3b46169dbd754d`, Mathlib rev
`520045ab14e26149ee970e2e617ca04b09bde5d6`, `lean-toolchain` =
`v4.32.1`, `PetersTour.lean` + `PetersTour_en.lean` (i18n #4980), 0 sorry —
**the status quo is intentional and documented**, not an oversight.

See also: [`#4365`](https://github.com/jsboige/CoursIA/issues/4365) (GT 6→2
merge target), [`#4364`](https://github.com/jsboige/CoursIA/issues/4364)
(Mathlib convergence — `COMPLETED 2026-07-03`), [`#4362`](https://github.com/jsboige/CoursIA/issues/4362)
(parent EPIC "Lean — harmonize Mathlib, regroup lakes").

## Conclusion

This project is a **reference tour** of
[DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean),
imported as a Lake dependency (pinned at commit `94a4c650b6a3ef14df801a613c3b46169dbd754d`, toolchain
`v4.32.1`) and exhibited via `#check`s in `PetersTour.lean` — **0 `sorry`**,
`lake build` SUCCESS. It is **not** original formalization: it presents Peters'
results, the current reference implementation of social-choice theory in Lean 4.

### What the tour covers

- **Gibbard-Satterthwaite** — strategy-proofness implies dictatorship (≥ 3
  candidates);
- **Duggan-Schwartz** — multi-winner extension with optimist/pessimist
  strategy-proofness;
- **4 Condorcet impossibilities** — Participation, Reinforcement,
  Strategy-proofness, Anon+Neutral+Resolute;
- **15+ voting rules** with axiom verification (Split Cycle, Schulze, Copeland,
  Black, IRV, Borda, …).

### Complementary, not duplicate

This project and [`social_choice_lean/`](../social_choice_lean/) cover the same
theory through **different frameworks**: Peters uses Mathlib's strict
`LinearOrder`, while `social_choice_lean/` uses the reflexive-total-transitive
`PrefOrder` (closer to the welfare-economics tradition). Reading both shows how
the framework choice shapes the definitions and proofs.

### Where to go next

- **Companion notebook**: planned (not yet created) — a teaching tour of Peters'
  results, which this project would back.
- **Upstream**: [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) (MIT).
- **Our proofs**: [`social_choice_lean/`](../social_choice_lean/) — Arrow / Sen /
  median voter in the `PrefOrder` framework.
