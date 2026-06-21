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

- Backend for notebook `GameTheory-16e-SocialChoiceLean-Tour.ipynb`
- Peters' repo pinned at commit `d679d950` for reproducibility
- Peters uses `LinearOrder` (strict, Mathlib); we use `PrefOrder` (reflexive, total, transitif)

## Conclusion

This project is a **reference tour** of
[DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean),
imported as a Lake dependency (pinned at commit `d679d950`, toolchain
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

- **Notebook**: `GameTheory-16e-SocialChoiceLean-Tour.ipynb` — the teaching
  companion this project backs.
- **Upstream**: [DominikPeters/SocialChoiceLean](https://github.com/DominikPeters/SocialChoiceLean) (MIT).
- **Our proofs**: [`social_choice_lean/`](../social_choice_lean/) — Arrow / Sen /
  median voter in the `PrefOrder` framework.
