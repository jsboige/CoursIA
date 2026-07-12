# Repeated Games — Lean (formal companion of GT-6c)

> **Formal companion** of the pedagogical notebook [GameTheory-6c](../GameTheory-6c-RepeatedGames-FolkTheorem.ipynb) (`Repeated Games` — Iterated prisoner's dilemma).
> This companion fills the gap in the GameTheory series (which has 7 Lean lakes: `conway_cgt`, `cooperative_games`, `minimax`, `repeated_games`, `social_choice`, `social_choice_lean_peters`, `stable_marriage`).

## Headline theorem

**Grim trigger sustains cooperation iff δ ≥ (T − R) / (T − P)** (one-shot deviation principle).

For an infinitely repeated game, discount factor δ ∈ [0,1), real parameters `T > R > P > S` with `2R > T + S`:

- **Perpetual cooperation** yields `R / (1 − δ)` (geometric series).
- **One-shot deviation followed by eternal punishment** yields `T + δ · P / (1 − δ)`.
- Indifference threshold: `δ · (T − R) ≥ (T − R)` ⇔ `δ ≥ (T − R) / (T − P)`.

> Above the threshold, **no unilateral deviation is profitable**. Grim is a subgame-perfect Nash equilibrium strategy.

## Toolchain cohort (Issue #4880)

| Parameter | Value | Reference |
|-----------|-------|-----------|
| Toolchain | `leanprover/lean4:v4.31.0-rc1` | 18-lake mutualised cohort |
| Mathlib rev | `d568c8c0` | `#4363` junction shared cache |
| Total sorry (production) | See [FORMAL_STATUS.md](FORMAL_STATUS.md) | Headline theorem 0 sorry required |
| Total sorry (stretch) | Folk.lean — tolerated | `#4880` § "Critères de fermeture" §1 |

## Modules

| Module | Role | Theorem status |
|--------|------|----------------|
| `RepeatedGames.Stage` | Parametric PD, actions C/D, payoffs, default > cooperate in stage game | FORMAL-CERTIFIED (0 sorry) |
| `RepeatedGames.Discounting` | Discount factor, geometric sums, threshold rewrite lemma | FORMAL-CERTIFIED (0 sorry) |
| `RepeatedGames.GrimTrigger` | Grim strategy, headline theorem `grim_trigger_sustains_iff`, NE corollary | FORMAL-CERTIFIED (0 sorry — headline theorem certified) |
| `RepeatedGames.Folk` (STRETCH) | Discounted Folk theorem (Fudenberg–Maskin 1986) | Sorries tolerated (stretch) |

## ICT-13 bridge

The numeric threshold `δ ≥ (T − R) / (T − P)` is the **falsifiable gate** for [ICT-13](https://github.com/jsboige/CoursIA/issues/4879) — strategies as stable forms (Axelrod):
- ICT-13 STABLE strategies are precisely those whose grim-trigger threshold is satisfied by the empirical parameters (T-R)/(T-P) of the observed dilemma.

## See also

- [Issue #4880 (lake creation)](https://github.com/jsboige/CoursIA/issues/4880)
- [Issue #4363 (junction shared Mathlib cache)](https://github.com/jsboige/CoursIA/issues/4363)
- Notebook: [`GameTheory-6c.ipynb`](../GameTheory-6c-RepeatedGames-FolkTheorem.ipynb)
- Sibling lake `cooperative_games_lean` (sorries closed 2026-06-09, see BONDAREVA_SHAPLEY_HARDNESS.md)
