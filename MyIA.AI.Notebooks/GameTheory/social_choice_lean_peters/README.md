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
