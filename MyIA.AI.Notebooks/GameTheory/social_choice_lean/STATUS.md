# Social Choice Lean - Status

> **⚑ Archive (PR [#6058](https://github.com/jsboige/CoursIA/pull/6058)).** Sources déplacées
> byte-identique vers [`game_theory_lean/SocialChoice/`](../game_theory_lean/SocialChoice/)
> (home canonique). Statut figé à la date d'absorption ; voir `game_theory_lean/` pour le statut
> actif. La CI qui le porte est `.github/workflows/lean-ci-matrix.yml` : le wrapper
> `lean-social-choice.yml` a été absorbé dans la matrice par #17374, et le pin Lean a avancé
> depuis (voir [`game_theory_lean/lean-toolchain`](../game_theory_lean/lean-toolchain)). Les
> valeurs du tableau ci-dessous sont donc un **instantané historique**, pas l'état courant.

## Build Info

| Item | Value |
|------|-------|
| Lean toolchain | `leanprover/lean4:v4.31.0-rc1` |
| Mathlib | `v4.30.0-rc2` |
| Sorry count | **0** (all production files) |
| Last verified | 2026-05-26 |

## Source Files

| File | Lines | Definitions | Theorems | Status |
|------|-------|-------------|----------|--------|
| `Basic.lean` | ~300 | PrefOrder helpers, P/I relations, Finset lemmas | 15+ | Compiles, 0 sorry |
| `Arrow.lean` | ~500 | SWF, Arrow conditions, Geanakoplos 2005 proof | 20+ | Compiles, 0 sorry |
| `Sen.lean` | ~200 | Liberal paradox, Sen impossibility theorem | 2 theorems | Compiles, 0 sorry |
| `Voting.lean` | ~200 | Condorcet concepts, margin function, SCC criteria | 6 theorems | Compiles, 0 sorry |

## Key Theorems

- **Arrow's Impossibility** (`Arrow.lean`): Geanakoplos 2005 proof chain — any SWF satisfying weak Pareto and IIA on 3+ alternatives is a dictatorship.
- **Sen's Impossibility** (`Sen.lean`): Minimal liberalism + weak Pareto = inconsistent on 3+ alternatives.
- **Condorcet Properties** (`Voting.lean`): Margin function antisymmetry, Condorcet winner uniqueness, Condorcet loser disjointness.

## CI

GitHub Actions workflow: `.github/workflows/lean-ci-matrix.yml` — le wrapper
`lean-social-choice.yml` a été absorbé dans la matrice (#17374) ; le fichier n'existe plus.
Trigger: push/PR touching `game_theory_lean/**` ou
`game_theory_lean/SocialChoice/CERTIFIED.txt`. **Plus** `social_choice_lean/**` : ce répertoire
ne porte plus aucune source Lean, donc il ne déclenche plus rien.
Steps: elan install, Mathlib cache, `lake build`, sorry detection.

## History

| Date | Change | Commit |
|------|--------|--------|
| 2026-01-31 | Initial port from asouther4/lean-social-choice | `1ce6a047` |
| 2026-04-19 | Sen impossibility theorem (0 sorry) | `28d3bb5e` |
| 2026-04-28 | Voting.lean - Condorcet concepts | `e45e6538` |
| 2026-04-29 | Toolchain upgrade v4.28.0-rc1 -> v4.29.1 | `c1b2cde1` |
| 2026-05-26 | Toolchain upgrade v4.29.1 -> v4.30.0-rc2 | — |
