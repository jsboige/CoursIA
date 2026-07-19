# Social Choice Lean (Peters Reference)

Reference project importing [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) as a Lake dependency. Curated tour of Peters' formalized results.

## Status

- **Toolchain**: v4.27.0-rc1 (pinned to Peters' version)
- **Sorry count**: 0 production sorry
- **Build**: `lake build` -- SUCCESS
- **Dependencies**: Mathlib4, DominikPeters/SocialChoiceLean

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
- Peters' repo pinned at commit `355075e3e35f940a2ade0cbfb5be27b4a53c6776` for reproducibility
- Peters uses `LinearOrder` (strict, Mathlib); we use `PrefOrder` (reflexive, total, transitif)

## EPIC #4365 Status (anti-proliferation GT 6→2)

This lake is **explicitly out of scope** for absorption into
[`game_theory_lean/`](../game_theory_lean/) under EPIC #4365 Phase 4 (merge
cohesive post-convergence lakes), for two cumulative reasons:

1. **Upstream lock (`INTRINSIC` verdict)**: this lake **imports**
   [`DominikPeters/SocialChoiceLean`](https://github.com/DominikPeters/SocialChoiceLean),
   pinned at commit `d679d950`, which itself depends on a Mathlib in the
   `v4.27.0-rc1` family. The port of that upstream to `v4.31.0-rc1`
   (post-#4364 target) is **not** under our control — it is an external project
   (MIT, Dominik Peters) and the port is potentially heavy (4-version gap, multiple
   API breakages). **`INTRINSIC` verdict** per
   [`sota-not-workaround.md`](../../../.claude/rules/sota-not-workaround.md):
   no real SOTA path to absorb without breaking the dependency.

2. **Distinct semantic framework**: this lake exposes a Mathlib strict
   `LinearOrder` which **does not** line up with the reflexive-total-transitive
   `PrefOrder` API used by `game_theory_lean/SocialChoice/`. A merge would
   force either (a) a dual linear/preorder port or (b) a rewrite of Peters'
   proofs — beyond the "atomic R3 PR" budget.

**Consequence**: `social_choice_lean_peters/` stays a **self-contained
autonomous lake** with its own `lake build`, its own `lean-toolchain`
`v4.27.0-rc1`, and its own CI. The #4364 Phase 3 convergence (10 lakes rc2
bumps to `d568c8c0` / `v4.31.0-rc1`, completed 2026-07-03 by another worker)
**does not apply** here — Peters is the sole v4.27 residue in the fleet.

Firsthand status check (c.576, 2026-07-17): `lake-manifest.json` pinned at
Peters commit `355075e3e35f940a2ade0cbfb5be27b4a53c6776` (`rev`), Mathlib
rev `8cb9319191fd34b6f23d7ffea58a4f8fb674cefd`, `lean-toolchain` =
`v4.27.0-rc1`, `PetersTour.lean` 234 lines, 0 sorry (grep verified),
build SUCCESS — **the status quo is intentional and documented**, not an
oversight.

See also: [`#4365`](https://github.com/jsboige/CoursIA/issues/4365) (GT 6→2
merge target), [`#4364`](https://github.com/jsboige/CoursIA/issues/4364)
(Mathlib convergence — `COMPLETED 2026-07-03`), [`#4362`](https://github.com/jsboige/CoursIA/issues/4362)
(parent EPIC "Lean — harmonize Mathlib, regroup lakes").

## Conclusion

This project is a **reference tour** of
[DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean),
imported as a Lake dependency (pinned at commit `355075e3e35f940a2ade0cbfb5be27b4a53c6776`, toolchain
`v4.27.0-rc1`) and exhibited via `#check`s in `PetersTour.lean` — **0 `sorry`**,
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
