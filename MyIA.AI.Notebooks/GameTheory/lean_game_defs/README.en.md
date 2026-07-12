# Lean Game Definitions

Shared Lean 4 type definitions used by multiple GameTheory Lean projects. **NOT** a standalone Lake project — provides reference definitions imported or copied into adjacent Lake projects.

## Status

- **Type:** Code snippets (no `lakefile.lean`, no toolchain pin)
- **Files:** 6 `.lean`
- **`sorry` count:** 0 (definitions only, no proofs)
- **Mathlib dependency:** None — all files use core Lean 4 only
- **Buildable in isolation:** No — meant to be imported by Lake projects
- **Last sorry audit:** 2026-05-29
- **Last compilation fix:** 2026-06-10 (See #2748)

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

- [game_theory_lean/](../game_theory_lean/) — Multi-module Lake project (StableMarriage = Gale-Shapley formalization, EPIC #4365).
- [social_choice_lean/](../social_choice_lean/) — Independent Lake project (Arrow / Sen / median voter, port of asouther4/lean-social-choice).
- [social_choice_lean_peters/](../social_choice_lean_peters/) — Independent Lake project pinned on Peters' commit `d679d950` (Gibbard-Satterthwaite, Duggan-Schwartz).
- [cooperative_games_lean/](../cooperative_games_lean/) — Independent Lake project (Shapley value, core, nucleolus).

These projects do **not** depend on `lean_game_defs/` at build time — they vendor their own definitions tailored to their proof obligations. `lean_game_defs/` is the **introductory** layer used by the teaching notebooks.

## See also

- [GameTheory/README.md](../README.md) — Series overview (OpenSpiel + Lean tracks)
- [scripts/README.md](../scripts/README.md) — Lean 4 WSL kernel setup
- [.claude/rules/wsl-kernels.md](../../../.claude/rules/wsl-kernels.md) — Kernel rules

## Conclusion

`lean_game_defs/` is the **introductory definition layer** of the GameTheory Lean
track: shared Lean 4 type definitions (no proofs, 0 `sorry`) used by the teaching
notebooks and importable by adjacent Lake projects. It is **not** a standalone Lake
project — there is no `lakefile.lean`, no toolchain pin, and no Mathlib dependency;
every file is core Lean 4 only.

### What it provides

Six reference files covering the game-theory curriculum: normal-form / finite games
([Basic.lean](Basic.lean)), Nash equilibrium and dominance ([Nash.lean](Nash.lean)),
combinatorial game trees with minimax ([Combinatorial.lean](Combinatorial.lean)),
social-choice primitives and Arrow's axioms ([SocialChoice.lean](SocialChoice.lean)),
Bayesian games and signaling ([Bayesian.lean](Bayesian.lean)), and regret
minimization / CFR ([Regret.lean](Regret.lean)). Each maps to a specific teaching
notebook and is self-contained.

### How it is used

- **Copy-paste** into a notebook cell (the typical pedagogical workflow);
- **Import** from an adjacent Lake project via `import GameTheory.lean_game_defs.*`; or
- **Standalone exploration** via the Lean 4 WSL kernel.

For full combinatorial-game theory (`PGame`, surreals, nimbers), the track points to
Mathlib's `SetTheory.PGame` / the [`conway_cgt_lean/`](../conway_cgt_lean/) tour
rather than redefining it here.

### Where to go next

- **Buildable projects** (each vendors its own proof-tailored definitions):
  [`social_choice_lean/`](../social_choice_lean/) (Arrow / Sen / median voter),
  [`cooperative_games_lean/`](../cooperative_games_lean/) (Shapley value, Core),
  [`game_theory_lean/`](../game_theory_lean/) (StableMarriage module, Gale-Shapley, EPIC #4365).
- **CGT tour**: [`conway_cgt_lean/`](../conway_cgt_lean/) — surreals, nimbers via
  `vihdzp/combinatorial-games`.
- **Kernel setup**: [scripts/README.md](../scripts/README.md) and
  [.claude/rules/wsl-kernels.md](../../../.claude/rules/wsl-kernels.md).
