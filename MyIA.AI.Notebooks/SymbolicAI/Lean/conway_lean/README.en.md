# Conway Lean

Lean 4 formalization of Conway's mathematical games and algorithms.

## Status

- **Toolchain**: v4.30.0-rc2
- **Sorry count**: 7 (all in `HashlifeCorrectness.lean` — P4 double-nine inductive step [5] + P5 large-n jump [2], Epic #2162)
- **Build**: `lake build Conway` -- SUCCESS (3352 jobs)
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
| `Conway/CollatzLike.lean` | 0 | Collatz-like functions and undecidability (`native_decide`) |

### Phase 2 — Game of Life (Epic #1647, IN PROGRESS)

| File | sorry | Description |
|------|-------|-------------|
| `Conway/Life.lean` | 0 | B3/S23 rules, grid operations, step/evolve, `native_decide` proofs |
| `Conway/Life/Spaceships.lean` | 0 | LWSS/MWSS/HWSS (period 4, displacement (0,2)), 3 `native_decide` proofs |
| `Conway/Life/Oscillators.lean` | 0 | 5 still-lifes + pulsar (p3) + pentadecathlon (p15), 7 `native_decide` |
| `Conway/Life/RLE.lean` | 0 | RLE pattern parser + glider/LWSS/pulsar/Gosper gun, 8 `native_decide` proofs |
| `Conway/Life/MacroCell.lean` | 0 | Quadtree datatype + `toGrid`/`buildFromGrid` round-trip + `wf` predicate |
| `Conway/Life/Hashlife.lean` | 0 | `step4x4` + `hashlifeResult` recursive + `padCenter2` + `hashlifeJump` + `evolveHashlifeFast` |
| `Conway/Life/GridCanonical.lean` | 0 | `sortDedup` canonical forms, lex-sorted uniqueness, grid equality via canonical form |
| `Conway/Life/Computation.lean` | 0 | Hashlife cross-validation (6 + 6 fast), eater1 still-life (1), glider composition (5) |
| `Conway/Life/HashlifeMemo.lean` | 0 | Memoized Hashlife for community pillar witnesses (OTCA 35K, UnitCell 4096, Gemini 33M) |
| `Conway/Life/Pillars.lean` | 0 | Community-witness theorem scaffolding (4 pillars) |
| `Conway/Life/HashlifeCorrectness.lean` | 7 | Bounded correctness `hashlife_correct`; P4/P5 prover targets (Epic #1453, #2162) |

### Phase 3 — Free Will Theorem (Epic #1651, COMPLETE)

| File | sorry | Description |
|------|-------|-------------|
| `Conway/KochenSpecker.lean` | 0 | KS 18-vec Cabello proof (parity argument) |
| `Conway/FreeWillTheorem.lean` | 0 | Conway-Kochen FWT (SPIN + TWIN + MIN) |

## Key Results

### Classic algorithms (Phase 1)

- Doomsday algorithm correctness
- FRACTRAN computation formalization
- Look-and-Say sequence properties
- Nim game strategy
- Angel problem formalization
- Collatz-like undecidability (`native_decide` on finite instances)

### Game of Life (Phase 2)

- **Grid/List encoding**: `Grid = List (Int x Int)` with Bool predicates, `native_decide` proofs
- **RLE parser**: Complete Run Length Encoded format parser with proven correctness
  - 4 parse-success theorems, 2 round-trip equalities, 2 cell-count theorems
  - Gosper Glider Gun (36 live cells, period 30) parsed and verified
- **Spaceships**: LWSS, MWSS, HWSS with period-4 displacement proofs
- **Oscillators**: Blinker (p2), toad (p2), beacon (p2), pulsar (p3), pentadecathlon (p15)
- **MacroCell well-formedness**: `MacroCell.wf` predicate (PR #2795), grid-side constructors produce wf cells
- **Grid canonical forms**: `sortDedup` outputs are lex-sorted and unique (PR #2797)
- **Hashlife**: Quadtree MacroCell + recursive hashlife algorithm with exponential speedup
  - `step4x4`: level-2 base case (B3/S23 direct)
  - `hashlifeResult`: recursive level-k to level-(k-1), `2^(k-2)` generations
  - `padCenter2`: proper centered padding (+2 levels, single copy)
  - `hashlifeJump` + `evolveHashlifeFast`: exponential-speedup API
  - Cross-validated against list-based reference on 12 patterns (6 + 6 fast path)
  - Eater 1 (fishhook) still-life proved by `native_decide`
  - Multi-period glider composition theorems
- **Memoized Hashlife**: Community pillar witnesses (OTCA 35K gen, UnitCell 4096 gen, Gemini 33M gen)
- **HashlifeCorrectness**: bounded correctness `hashlife_correct`, decomposed P1-P5
  - **P1-P3 proven** (base case `k=0` via `2^16 native_decide`, PR #2810)
  - **P4 inductive step** (5 sorry): decomposed by #2975 scaffolding into four `: True`
    sub-lemmas (`p4_double_nine_shape`, `p4_wave1_ih`, `p4_wave2_ih`,
    `p4_half_steps_compose`) + glue `p4_succ_membership` (the real pointwise
    biconditional). Research-level double-nine light-cone composition. The scaffolds'
    real statements live in their docstrings — restate + prove, do not eliminate as `True`.
  - **P5 large-n** (2 sorry): `p5_small_n_fallback` **PROVEN** (PR #2984); `p5_large_n_jump`
    (P5.2, blocked on P4) + `p5_inductive_step` large-n branch (P5.3 glue) remain. Base
    `n=0` proven (`hashlife_correct_base_zero` #2898, `evolveHashlifeFastAux_zero_n` #2901).

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

## Conclusion

Ce workspace formalise en Lean 4 trois facettes de l'oeuvre de John Conway, des algorithmes classiques (Phase 1) au calcul universel du Jeu de la Vie (Phase 2) jusqu'au fondement quantique (Phase 3, Free Will Theorem). Le fil conducteur est la **certification formelle** : chaque résultat est un théorème prouvé, pas une simulation.

### Ce que ce formalisme démontre

- **Les algorithmes classiques** (Doomsday, FRACTRAN, Look-and-Say, Nim, Angel, Collatz) sont prouvés sur leurs instances finies via `native_decide` ou par arguments combinatoires directs (`decide`, `omega`, parité pour Kochen-Specker). Aucun `sorry`.
- **Le Jeu de la Vie comme moteur de calcul** : règles B3/S23, vaisseaux (LWSS/MWSS/HWSS), oscillateurs (blinker, pulsar p3, pentadecathlon p15), et la méthode Hashlife à accélération exponentielle. La cross-validation sur 12 patterns + eater1 + compositions de planeurs confirme que l'implémentation rapide `evolveHashlifeFast` agree avec la référence `evolve` sur tous les cas testés.
- **Le Free Will Theorem** (Conway-Kochen 2006/2009) est prouvé depuis les trois axiomes physiques SPIN + TWIN + MIN, en se réduisant à la contradiction 18-vecteurs de Kochen-Specker (Cabello et al. 1996). Phase 3 COMPLETE, sorry-free.

### État honnête du verrou HashlifeCorrectness

Le théorème central `hashlife_correct` (borné par l'hypothèse de padding `BoxAssezGrand`) n'est **pas encore prouvé en pleine généralité** : il reste **7 `sorry`** dans `HashlifeCorrectness.lean`. Le socle est solide — cas de base `k=0` prouvé (`2^16 native_decide`), cas de base `n=0` prouvé, P1/P2/P3 (padding, light-cone, locality) prouvés, `p5_small_n_fallback` prouvé — mais le pas inductif P4 (double-nine decomposition, 5 sorry) et le grand-n P5 (2 sorry, bloqué sur P4) sont **research-level**. Ce sont les cibles du BG-prover (`agent_tests/prover/`), pas des grains bornés : la composition light-cone multi-vagues résiste à l'automatisation tactique courante. Les scaffolds P4 (`p4_double_nine_shape`, `p4_wave1_ih`, `p4_wave2_ih`, `p4_half_steps_compose`, `p4_succ_membership`) énoncent précisément chaque sous-but dans leurs docstrings.

### Leçons méthodologiques

- **`List (Int × Int)` + prédicats `Bool` + `native_decide`** est l'encodage qui passe pour les grilles ; l'encodage `Finset` est bloqué par `Quot.lift`/`Eq.rec`.
- **Le concept "intractable" cache souvent un énoncé faux** : la même intuition que pour la percée Lattice (7→0) s'applique — le contre-exemple certifié `p4_unrestricted_counterexample` montre qu'une forme d'énoncé non restreinte est fausse, orientant vers la bonne hypothèse `MacroCell.wf`.
- **Les ingrédients additifs sorry-free** (level/wf preservation, `box_assez_grand` arithmetic) s'accumulent derrière le verrou et seront mobilisables quand P4 cédera.

### Prochaines étapes

1. **BG-prover sur P4** : attaquer le pas inductif double-nine via le harness multi-agent (`agent_tests/prover/`), en s'appuyant sur les scaffolds docstring-restated.
2. **Sub-claim géométrique sorry-free** : le bound `gridBoundingBox (g').2 ≤ gridBoundingBox g .2 + 2 * jumpSize` (light-cone growth) est un grain additif sur la frame P5.2, dischargeable par arithmétique `Nat` une fois le cas light-cone borué — queueable derrière le verrou P4.
3. **Extension des témoins** : ajouter des motifs HashlifeMemo supplémentaires (community pillars) pour renforcer le socle `native_decide`.

## Notes

- Part of the GameTheory Lean series
- Companion notebook: `Lean-16b-Conway-Game-of-Life-Lean.ipynb`
- Cross-link: Epic #1647 Conway Phase 2 (Life-as-Computation)
- Cross-link: Epic #1651 Conway Phase 3 (Free Will Theorem)
- Cross-link: Epic #2162 Conway depth (HashlifeCorrectness P4/P5)

## Conway.Life Design

- **List(Int x Int) + Bool predicates + `native_decide`** = works reliably
- **Finset(Int x Int) + decide/native_decide** = BLOCKED (Quot.lift, Eq.rec)
- Pulsar (48 cells) and pentadecathlon (p15) are borderline but pass `native_decide`
- Hashlife: partial def (no termination proof) with recursive MacroCell decomposition
- `evolveHashlifeFast`: exponential speedup via `padCenter2` + `hashlifeResult`, validated by `native_decide`
- MacroCell round-trip verified by `#eval` and `native_decide` theorem
- HashlifeMemo: memoization layer for pillar witnesses, `9^k` worst case reduced to tractable

## References

Foundational sources for the results formalized across the three phases. Each entry maps to a module of this workspace.

- **Conway, J. H.** *On Numbers and Games* (ONAG). Academic Press, 1976; 2nd ed., A K Peters, 2001. — Conway's broader framework for combinatorial games (context for the games below).
- **Bouton, C. L.** "Nim, A Game with a Complete Mathematical Theory." *Annals of Mathematics*, 2nd ser., 3(1-4) (1901-1902): 35-39. — Foundational analysis of Nim (`Nim.lean`).
- **Conway, J. H.** "The Weird and Wonderful Chemistry of Audioactive Decay." *Eureka* 46 (1986): 5-16. — The Look-and-Say sequence (`LookAndSay.lean`).
- **Conway, J. H.** "FRACTRAN: A Simple Universal Programming Language for Arithmetic." In *Open Problems in Communication and Computation* (Cover & Gopinath, eds.), Springer, 1987. — FRACTRAN (`Fractran.lean`).
- **Conway, J. H.** "The Angel Problem." In *Games of No Chance*, MSRI Publications 29, Cambridge University Press, 1996. — The Angel vs Devil problem (`Angel.lean`).
- Conway's **Doomsday** algorithm for day-of-week computation — the calendar anchor method formalized in `Doomsday.lean`.
- The **Collatz** (3n+1) conjecture, Lothar Collatz (1937) — bounded instances handled via `native_decide` (`CollatzLike.lean`).
- **Gardner, M.** "The Fantastic Combinations of John Conway's New Solitaire Game 'Life'." *Scientific American* 223(4) (October 1970): 120-123. — First public presentation of the Game of Life (`Life.lean`).
- **Rokicki, T.** "An Algorithm for Compressing Space and Time." *Dr. Dobb's Journal* (2006). — The Hashlife algorithm (`Life/Hashlife.lean`).
- **Rendell, P.** "A Universal Turing Machine in Conway's Game of Life." In *Collision-Based Computing* (Adamatzky, ed.), Springer, 2002. — Life as universal computation (`Life/Computation.lean`).
- **Kochen, S.; Specker, E. P.** "The Problem of Hidden Variables in Quantum Mechanics." *Journal of Mathematics and Mechanics* 17(1) (1967): 59-81. — The original 117-vector theorem (`KochenSpecker.lean`).
- **Cabello, A.; Estebaranz, J. M.; Garcia-Alcaine, G.** "Bell-Kochen-Specker Theorem: A Proof with 18 Vectors." *Physics Letters A* 212 (1996). — The 18-vector tight proof formalized in `KochenSpecker.lean`.
- **Conway, J. H.; Kochen, S.** "The Free Will Theorem." *Foundations of Physics* 36(10) (2006): 1443-1473. — FWT from the SPIN, TWIN, and MIN axioms (`FreeWillTheorem.lean`).
- **Conway, J. H.; Kochen, S.** "The Strong Free Will Theorem." *Notices of the American Mathematical Society* 56(2) (2009): 226-232.
- **Peres, A.** "Two Simple Proofs of the Kochen-Specker Theorem." *Journal of Physics A* 24(4) (1991): L175-L178.
- **Mermin, N. D.** "Hidden Variables and the Two Theorems of John Bell." *Reviews of Modern Physics* 65(3) (1993): 803-815.
