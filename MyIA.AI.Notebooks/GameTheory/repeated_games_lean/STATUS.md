# Repeated Games Lean - Build Status

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
