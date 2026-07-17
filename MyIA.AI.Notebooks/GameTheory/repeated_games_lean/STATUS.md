# Repeated Games Lean - Build Status

> **⚑ Archive — le build Lake actif a déménagé.** Depuis la PR [#6146](https://github.com/jsboige/CoursIA/pull/6146)
> (EPIC [#4365](https://github.com/jsboige/CoursIA/issues/4365) Phase-4), la lib `RepeatedGames` est
> buildée depuis le home canonique [`game_theory_lean/RepeatedGames/`](../game_theory_lean/RepeatedGames/)
> (le `lean_lib` de cette coquille archive est neutralisé dans `lakefile.lean` — ses `globs` pointaient
> vers des sources déplacées). Les commandes de build ci-dessous sont conservées pour référence
> historique. Voir [README.md](README.md) (bannière archive).

## CI

| Workflow | Status |
|----------|--------|
| Lake build | Pending (J2 — après `lake update` junction cache) |
| Proof integrity | Pending (J3 — après premiers sorries éliminés par prover BG) |

## Build commands

```bash
# Junction cache (J1 — assuming ai-01 has -Mode Scan available)
cd MyIA.AI.Notebooks/GameTheory/repeated_games_lean
pwsh scripts/lean/setup_shared_mathlib.ps1 -Mode Scan

# First-time build (J1, ~5-10 min via junction cache restoration)
lake build

# Iterative build (J3+, <60s after first oleans)
lake build RepeatedGames.Stage RepeatedGames.Discounting
```
