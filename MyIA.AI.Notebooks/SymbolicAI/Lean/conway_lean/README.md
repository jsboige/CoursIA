# Conway Lean

Lean 4 formalization of Conway's mathematical games and algorithms.

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 0 production sorry (grep hits in comments only)
- **Build**: `lake build Conway` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

| File | sorry | Description |
|------|-------|-------------|
| `Conway/Doomsday.lean` | 0 | Doomsday algorithm (day-of-week calculation) |
| `Conway/DoomsdayLemmas.lean` | 0 | Lemmas for the Doomsday algorithm |
| `Conway/Fractran.lean` | 0 | FRACTRAN programming language |
| `Conway/LookAndSay.lean` | 0 | Look-and-Say sequence |
| `Conway/LookAndSayLemmas.lean` | 0 | Lemmas for the Look-and-Say sequence |
| `Conway/Nim.lean` | 0 | Nim game theory |
| `Conway/Angel.lean` | 0 | Angel problem |
| `Conway/KochenSpecker.lean` | 0 | Kochen-Specker theorem (18-vec Cabello, Pilier 1 FWT) |
| `Conway/Life.lean` | 0 | Game of Life (B3/S23, still lifes/oscillators/spaceships, `native_decide` proofs, Phase 2 Epic #1647) |

## Key Results

- **COMPLETE**: All proofs done, 0 sorry in production code
- Doomsday algorithm correctness
- FRACTRAN computation formalization
- Look-and-Say sequence properties
- Nim game strategy
- Angel problem formalization
- Conway's Game of Life cellular automaton — `B3/S23` rules, still lifes (block, beehive), oscillators (blinker, toad, beacon period 2), spaceship (glider). All theorems via `native_decide`.
- Kochen-Specker theorem (Pilier 1 of Epic #1651 Conway FWT) — full proof via parity argument (sum = 9 odd vs 2k even, contradiction)

## Kochen-Specker (Pilier 1 of Free Will Theorem)

The `KochenSpecker.lean` module formalizes the 18-vector proof by Cabello,
Estebaranz and Garcia-Alcaine (1996). It is the combinatorial kernel of the
Conway-Kochen Free Will Theorem (2006/2009, Epic #1651).

**Hall of Fame**:
- Kochen & Specker (1967) — original 117-vector proof
- Cabello, Estebaranz, Garcia-Alcaine (1996) — 18-vector tight proof
- Conway & Kochen (2006) — 33-vector proof + Free Will Theorem
- Peres (1991), Mermin (1993) — simplifications and pedagogy

## Notes

- Part of the GameTheory Lean series
- Companion notebooks in the GameTheory series
- Cross-link: Epic #1647 Conway Phase 2 (Life-as-Computation)
- Cross-link: Epic #1651 Conway Phase 3 (Free Will Theorem)
