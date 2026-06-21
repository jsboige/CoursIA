# conway_cgt_lean — Tour of vihdzp/combinatorial-games

A **curated tour** (`#check`-based) of the combinatorial game theory formalized in
[`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games),
imported as a Lake dependency — surreal numbers, nimbers, and general
combinatorial games. This is **not** an original formalization: it presents and
exhibits the upstream results, which are the current home of CGT in the Lean
ecosystem after Mathlib's CGT modules were removed.

Reference: Conway, J.H. — *On Numbers and Games* (2001).

## Status

- **Toolchain**: `leanprover/lean4:v4.31.0-rc1` (tracks the upstream repo — newer than the other Lean series on v4.30.0-rc2)
- **Sorry**: **0** — the file is a tour of `#check`s and docstrings, no proofs
- **Build**: `lake build CGTTour` (depends on Mathlib4 + CombinatorialGames)
- **Dependencies**:
  - **Mathlib4** (latest)
  - **[CombinatorialGames](https://github.com/vihdzp/combinatorial-games)** (Apache-2.0) — Violeta Hernandez Palacios

## Why this exists — Mathlib CGT removal

The upstream repository **superseded Mathlib's CGT modules**
(`SetTheory.Surreal`, `SetTheory.PGame`, `SetTheory.Game`, `SetTheory.Nimber`),
which were deprecated in Mathlib PR [#28063](https://github.com/leanprover-community/mathlib4/pull/28063)
(Aug 2025) and **removed in PR [#35550](https://github.com/leanprover-community/mathlib4/pull/35550)**
(Feb 2026). The upstream author (vihdzp) is the same person who maintained the
Mathlib CGT code. This tour points learners to where CGT now lives.

## What the tour covers

The file imports the upstream modules and exhibits their key results:

### 1. Combinatorial games
- **`IGame`** (pre-games): concrete representation by left/right option sets
  (`left`/`right : Set IGame`) — you can inspect individual moves.
- **`Game`** (games up to equivalence `≈`): the quotient
  `Antisymmetrization IGame (· ≤ ·)`, an `OrderedAddCommGroup`.
- Birthday, canonical form, player.

### 2. Surreal numbers
- **`Surreal`**: numeric games quotiented by equivalence — a **`LinearOrder`**,
  a complete ordered field containing every ordered field as a subfield.
- **Simplicity theorem** (`IGame.Fits.equiv_of_forall_not_fits`): the key tool
  for computing surreal values.
- Full field arithmetic: addition (from `Game`), multiplication, division.
- **Dyadic** embedding (`Dyadic.toIGame`) — dyadic surreals = finite birthday.
- **Ordinal** embedding (`NatOrdinal.toSurreal`).

### 3. Nimbers
- **`Nimber`**: ordinals with nim arithmetic; arise from impartial games via the
  **Sprague-Grundy theorem** (every impartial game ≈ a game of nim).
- **Nim addition** via minimum-excluded (`Nimber.add_def`).
- **Field of characteristic 2** (`Field Nimber`) — every element is its own
  additive inverse. Long-term project goal: prove nimbers algebraically closed.

### Mathlib vs upstream (comparison table in the file)

| Aspect | Mathlib (removed) | combinatorial-games (current) |
|--------|-------------------|-------------------------------|
| Games | `PGame` (basic) | `IGame` (concrete) + `Game` (quotient) |
| Surreals | Basic/Dyadic/Mul | + Division, Hahn series, Birthday, Pow |
| Nimbers | Basic/Field | + Nat, SimplestExtension |
| Games lib | 8 modules | 15+ modules (Impartial, Loopy, Specific…) |

## Modules

| File | Lines | Content |
|------|-------|---------|
| `CGTTour.lean` | 169 | Imports the upstream `CombinatorialGames.*` modules and tours their key types/instances/theorems via `#check` + docstrings (`IGame`/`Game`, `Surreal` + simplicity theorem, `Nimber` + Sprague-Grundy), with a Mathlib-vs-upstream comparison table. |

## Build

```bash
# From this directory (WSL required)
lake build CGTTour
# Depends on Mathlib4 + CombinatorialGames (two git deps) — first build is heavy
```

## Cite, not vendor

The upstream repo is a **Lake dependency** (`require CombinatorialGames from git`),
not vendored. License: **Apache-2.0**. The tour file is original exposition built
on top of the imported results.

## See also

- **Upstream**: [`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games) (Apache-2.0, Violeta Hernandez Palacios)
- **`knot_lean/`** — references this tour in its dependencies table (Conway game-theory foundation)
- **`conway_lean/`** — Conway's Game of Life / Free Will Theorem (the *other* Conway series)
- **Epic #2651** — README/structure audit (Lean-series)

## Conclusion

This project is a **curated tour** (`#check`-based, 0 `sorry`) of the
combinatorial game theory now living in
[`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games),
imported as a Lake dependency. It exists because Mathlib's CGT modules were
**removed in Feb 2026** (PR [#35550](https://github.com/leanprover-community/mathlib4/pull/35550)),
and this tour points learners to where that theory now lives.

### What it covers

- **Combinatorial games** — `IGame` (concrete pre-games by left/right option
  sets) and `Game` (the quotient up to equivalence `≈`), with birthday and
  canonical form.
- **Surreal numbers** — `Surreal` as a complete ordered field containing every
  ordered field; the **simplicity theorem** as the key computation tool; full
  field arithmetic; dyadic and ordinal embeddings.
- **Nimbers** — ordinals with nim arithmetic, arising from impartial games via
  the **Sprague-Grundy theorem**; a field of characteristic 2 (long-term goal:
  prove the nimbers algebraically closed).

### Why this exists

Mathlib deprecated its CGT code (`SetTheory.Surreal/PGame/Game/Nimber`) in favor
of the upstream repository, whose author (vihdzp) is the same maintainer. Rather
than vendor or re-derive, the tour **cites** the upstream as a dependency and
exhibits its results via `#check` + docstrings — original exposition on top of
imported theorems. A Mathlib-vs-upstream comparison table documents the richer
upstream coverage (15+ modules vs Mathlib's former 8).

### Where to go next

- **Upstream**: [`vihdzp/combinatorial-games`](https://github.com/vihdzp/combinatorial-games)
  (Apache-2.0, Violeta Hernandez Palacios) — the current home of CGT in Lean.
- **Source**: Conway, J.H. — *On Numbers and Games* (2001).
- **Related**: `conway_lean/` (Conway's Game of Life / Free Will — the *other*
  Conway series) and `knot_lean/` (references this tour in its deps table).
