# Conway Lean

Lean 4 formalization of Conway's mathematical games and algorithms.

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 0 production sorry (grep hits in comments only)
- **Build**: `lake build Conway` -- SUCCESS
- **Dependencies**: Mathlib4

## Modules

### Phase 1 — Classic algorithms (Epic #1151, COMPLETE)

| File | sorry | Description |
|------|-------|-------------|
| `Conway/Doomsday.lean` | 0 | Doomsday algorithm (day-of-week calculation) |
| `Conway/DoomsdayLemmas.lean` | 0 | Lemmas for the Doomsday algorithm |
| `Conway/Fractran.lean` | 0 | FRACTRAN programming language |
| `Conway/LookAndSay.lean` | 0 | Look-and-Say sequence |
| `Conway/LookAndSayLemmas.lean` | 0 | Lemmas for the Look-and-Say sequence |
| `Conway/Nim.lean` | 0 | Nim game theory |
| `Conway/Angel.lean` | 0 | Angel problem |

### Phase 2 — Game of Life (Epic #1647, IN PROGRESS)

| File | sorry | Description |
|------|-------|-------------|
| `Conway/Life.lean` | 0 | B3/S23 rules, grid operations, step/evolve, `native_decide` proofs |
| `Conway/Life.Spaceships` | 0 | LWSS/MWSS/HWSS (period 4, displacement (0,2)), 3 `native_decide` proofs |
| `Conway/Life.Oscillators` | 0 | 5 still-lifes + pulsar (p3) + pentadecathlon (p15), 7 `native_decide` |
| `Conway/Life.RLE` | 0 | RLE pattern parser + glider/LWSS/pulsar/Gosper gun, 8 `native_decide` proofs |
| `Conway/Life.MacroCell` | 0 | Quadtree datatype + `toGrid`/`buildFromGrid` round-trip |
| `Conway/Life.Hashlife` | 0 | `step4x4` + `hashlifeResult` recursive + `padCenter2` + `hashlifeJump` + `evolveHashlifeFast` |
| `Conway/Life.Computation` | 0 | Hashlife cross-validation (6 + 6 fast), eater1 still-life (1), glider composition (5) |

### Phase 3 — Free Will Theorem (Epic #1651, IN PROGRESS)

| File                          | sorry | Description                                              |
|-------------------------------|-------|----------------------------------------------------------|
| `Conway/KochenSpecker.lean`   | 0     | KS 18-vec Cabello proof (parity argument, Pilier 1)      |
| `Conway/FreeWillTheorem.lean` | 0     | Conway-Kochen FWT (SPIN + TWIN + MIN, Pilier 2)          |

## Key Results

### Classic algorithms (Phase 1)

- Doomsday algorithm correctness
- FRACTRAN computation formalization
- Look-and-Say sequence properties
- Nim game strategy
- Angel problem formalization

### Game of Life (Phase 2)

- **Grid/List encoding**: `Grid = List (Int x Int)` with Bool predicates, `native_decide` proofs
- **RLE parser**: Complete Run Length Encoded format parser with proven correctness
  - 4 parse-success theorems, 2 round-trip equalities, 2 cell-count theorems
  - Gosper Glider Gun (36 live cells, period 30) parsed and verified
- **Spaceships**: LWSS, MWSS, HWSS with period-4 displacement proofs
- **Oscillators**: Blinker (p2), toad (p2), beacon (p2), pulsar (p3), pentadecathlon (p15)
- **Hashlife**: Quadtree MacroCell + recursive hashlife algorithm with exponential speedup
  - `step4x4`: level-2 base case (B3/S23 direct)
  - `hashlifeResult`: recursive level-k → level-(k-1), `2^(k-2)` generations
  - `padCenter2`: proper centered padding (+2 levels, single copy)
  - `hashlifeJump` + `evolveHashlifeFast`: exponential-speedup API
  - Cross-validated against list-based reference on 12 patterns (6 + 6 fast path)
  - Eater 1 (fishhook) still-life proved by `native_decide`
  - Multi-period glider composition theorems

### Kochen-Specker + Free Will Theorem (Phase 3, PROVED)

The `KochenSpecker.lean` module formalizes the 18-vector proof by Cabello,
Estebaranz and Garcia-Alcaine (1996). It is the combinatorial kernel of the
Conway-Kochen Free Will Theorem (2006/2009, Epic #1651).

The `FreeWillTheorem.lean` module proves the full Free Will Theorem from
three physically motivated axioms (SPIN, TWIN, MIN), reducing to the
Kochen-Specker contradiction.

**Hall of Fame**:
- Kochen & Specker (1967) — original 117-vector proof
- Cabello, Estebaranz, Garcia-Alcaine (1996) — 18-vector tight proof
- Conway & Kochen (2006) — 33-vector proof + Free Will Theorem
- Peres (1991), Mermin (1993) — simplifications and pedagogy

## Notes

- Part of the GameTheory Lean series
- Companion notebook: `Lean-14b-Conway-Game-of-Life-Lean.ipynb`
- Cross-link: Epic #1647 Conway Phase 2 (Life-as-Computation)
- Cross-link: Epic #1651 Conway Phase 3 (Free Will Theorem)

## Conway.Life Design

- **List(Int x Int) + Bool predicates + `native_decide`** = works reliably
- **Finset(Int x Int) + decide/native_decide** = BLOCKED (Quot.lift, Eq.rec)
- Pulsar (48 cells) and pentadecathlon (p15) are borderline but pass `native_decide`
- Hashlife: partial def (no termination proof) with recursive MacroCell decomposition
- `evolveHashlifeFast`: exponential speedup via `padCenter2` + `hashlifeResult`, validated by `native_decide`
- MacroCell round-trip verified by `#eval` and `native_decide` theorem
