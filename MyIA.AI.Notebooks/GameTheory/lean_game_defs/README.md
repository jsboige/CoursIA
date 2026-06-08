# Lean Game Definitions

Shared Lean 4 type definitions used by multiple GameTheory Lean projects. **NOT** a standalone Lake project — provides reference definitions imported or copied into adjacent Lake projects.

## Status

- **Type:** Code snippets (no `lakefile.lean`, no toolchain pin)
- **Files:** 6 `.lean`
- **`sorry` count:** 0 (definitions only, no proofs)
- **Buildable in isolation:** No — meant to be imported by Lake projects
- **Last sorry audit:** 2026-05-29

## Files

- [Basic.lean](Basic.lean) — 107 lines. `NormalFormGame`, `FiniteGame`, `Game2x2` structures + expected payoffs. Source: `GameTheory-16-Lean-Definitions.ipynb`.
- [Nash.lean](Nash.lean) — 139 lines. Best response, pure/mixed Nash equilibrium, strict dominance. Source: `GameTheory-16-Lean-Definitions.ipynb`.
- [Combinatorial.lean](Combinatorial.lean) — 113 lines. `GameTree`, minimax evaluation, win/loss determination. Source: `GameTheory-18-Lean-CombinatorialGames.ipynb`.
- [SocialChoice.lean](SocialChoice.lean) — 126 lines. `Preference`, `StrictPref`, Arrow's axioms (statements). Source: `GameTheory-19-Lean-SocialChoice.ipynb`.
- [Bayesian.lean](Bayesian.lean) — Bayesian games with incomplete information: `BayesianGame`, `TypeStrategy`, `BayesianNashEquilibrium`, `InformationSet`, `SignalingGame`, `FirstPriceAuction`, Kuhn poker definitions. Source: `GameTheory-11-BayesianGames.ipynb`, `GameTheory-13-ImperfectInfo-CFR.ipynb`.
- [Regret.lean](Regret.lean) — Regret minimization and CFR: `CumulativeRegret`, `regretMatchingStrategy`, `CounterfactualRegret`, `CFRState`, `FictitiousPlayState`. Source: `GameTheory-13-ImperfectInfo-CFR.ipynb`, `GameTheory-17-MultiAgent-RL.ipynb`.

## Usage

These files are reference definitions, not a buildable library. Use them by:

1. **Copy-paste into a notebook cell** (typical pedagogical workflow in `GameTheory-2b`, `GameTheory-8b`, etc.).
2. **Import from an adjacent Lake project** by adding the file path to the project's `lakefile.lean`. Example from `social_choice_lean/`:

   ```lean
   import GameTheory.lean_game_defs.Basic
   import GameTheory.lean_game_defs.SocialChoice
   ```

3. **Standalone exploration** via the Lean 4 WSL kernel (see [scripts/README.md](../scripts/README.md) for kernel setup).

For full `PGame` support (combinatorial game theory in its mathematical generality), use Mathlib directly:

```lean
import Mathlib.SetTheory.PGame.Basic
import Mathlib.SetTheory.Game.Nim
```

## Relation to other GameTheory Lean projects

- [stable_marriage_lean/](../stable_marriage_lean/) — Independent Lake project (Gale-Shapley formalization).
- [social_choice_lean/](../social_choice_lean/) — Independent Lake project (Arrow / Sen / median voter, port of asouther4/lean-social-choice).
- [social_choice_lean_peters/](../social_choice_lean_peters/) — Independent Lake project pinned on Peters' commit `d679d950` (Gibbard-Satterthwaite, Duggan-Schwartz).
- [cooperative_games_lean/](../cooperative_games_lean/) — Independent Lake project (Shapley value, core, nucleolus).

These projects do **not** depend on `lean_game_defs/` at build time — they vendor their own definitions tailored to their proof obligations. `lean_game_defs/` is the **introductory** layer used by the teaching notebooks.

## See also

- [GameTheory/README.md](../README.md) — Series overview (OpenSpiel + Lean tracks)
- [scripts/README.md](../scripts/README.md) — Lean 4 WSL kernel setup
- [.claude/rules/wsl-kernels.md](../../../.claude/rules/wsl-kernels.md) — Kernel rules
