# Linearity Axiom Refactor — Spec for prover BG multi-agent

> **STATUS 2026-05-13 23:18 Paris (post PR #1024 merge `cf31ea49`)** : **OBSOLETE / SUPERSEDED**. `shapley_uniqueness` was proved on `feat/lean-mobius-shapley` (po-2026, commit `1eb5a4a0`) WITHOUT the Linearity refactor — `game_eq_mobius_sum` via `dif_pos + simp` on dependent if-then-else + `finsetSumGames` distribution proved sufficient with the existing binary `Additivity` axiom. Shapley.lean sorry count: 1 → 0. Lake build SUCCESS verified locally ai-01 (v5 full cache nuke + rebuild, 3319 jobs, EXIT=0, `Built CooperativeGames.Shapley (140s)`).
>
> The Linearity refactor remains **a valid optional cleanup** (matches Shapley 1953 / Roth 1988 axiomatic form more closely), but is no longer required for `shapley_uniqueness` provability. Keep as future-work spec if axiomatic foundations cleanup becomes a priority.

**Date** : 2026-05-13
**Author** : ai-01 (research side-track A, post user A.1 decision)
**Target** : `cooperative_games_lean/CooperativeGames/Shapley.lean`
**Goal** : strengthen `Solution.Additivity` (binary) to `Solution.Linearity` (ℝ-linear) so that `shapley_uniqueness` L780 becomes provable via the existing Möbius decomposition infrastructure on branch `feat/lean-mobius-shapley` (PR #1024).

## Why this refactor

The current `Additivity` axiom states `φ(G+H)=φG+φH` for binary sums only. To prove `shapley_uniqueness` we need additivity extended to finite ℝ-linear combinations of unanimity games (Möbius decomposition `G = Σ_T a_T · u_T`). The binary form does not give:

1. Homogeneity : `φ(c·G) = c · φG` for `c : ℝ` (needed to extract Möbius coefficients `a_T`)
2. Additivity for finite sums : `φ(G_1 + G_2 + ... + G_k) = Σ_i φ(G_i)`

Combining both = **Linearity**. This matches Shapley (1953) "A Value for n-Person Games" §3 and Roth (1988) *The Shapley Value: Essays* p.2-5 where the axiom is stated in ℝ-linear form directly.

## Existing infrastructure on `feat/lean-mobius-shapley`

The branch already has :

- `Solution.AddGames G H : TUGame N` (binary sum, L57-60)
- `Solution.SmulGame (c : ℝ) (G : TUGame N) : TUGame N` (scalar mult, L548-550)
- `Solution.sumGames : List α → (α → TUGame N) → TUGame N` (finite sum via list induction, L553-556)
- `Mobius.mobiusCoeff`, `Mobius.mobiusReconstruction`, `mobius_decomposition_axiom` PROVED (L567-...) — already gives `G = Σ_T mobiusCoeff G T · u_T`

## Proposed axiom definition

Insert after current `Additivity` at L67 (do not remove Additivity, keep as derived lemma) :

```lean
/-- Axiom 4 (strengthened): Linearity
    The solution is ℝ-linear over the vector space of TU games.
    Shapley (1953) §3, Roth (1988) p.2-5. -/
def Linearity : Prop :=
  ∀ (c d : ℝ) (G H : TUGame N) (i : N),
    φ (AddGames (SmulGame c G) (SmulGame d H)) i = c * φ G i + d * φ H i
```

## Derived lemma (trivial)

```lean
/-- Linearity implies Additivity (c = d = 1, SmulGame 1 G = G). -/
theorem linearity_implies_additivity (h_lin : φ.Linearity) : φ.Additivity := by
  intro G H i
  have h := h_lin 1 1 G H i
  simp [SmulGame, AddGames] at h  -- expand 1 * G.v S = G.v S
  exact h
```

The proof requires a `simp` lemma `SmulGame 1 G = G` or unfolding (likely 5-10 lines).

## Theorem signature change

`shapley_uniqueness` at L560 :

```lean
theorem shapley_uniqueness (φ : Solution N)
    (h_eff : φ.Efficiency)
    (h_sym : φ.Symmetry)
    (h_null : φ.NullPlayerAxiom)
    (h_lin : φ.Linearity)  -- WAS: h_add : φ.Additivity
    (G : TUGame N) (i : N) :
    φ G i = shapleyValue G i := by
  ...
```

This is strictly stronger hypothesis (Linearity implies Additivity), so the theorem still holds for the Shapley value (which is linear, see below). The existing `shapley_uniqueness` proof body (still 1 sorry at L780) becomes provable by combining :

1. `mobius_decomposition_axiom` : `G = Σ_T mobiusCoeff G T · u_T`
2. `h_lin` extended to finite sums via `Finset.induction_on` or `List.foldr`
3. `phi_unanimity` for each `u_T`
4. Symmetry of Σ over `T`

## Shapley value satisfies Linearity (new obligation)

The Shapley solution itself must satisfy the new axiom (otherwise the uniqueness theorem is vacuous). Add :

```lean
/-- The Shapley value is ℝ-linear. -/
theorem shapley_linearity : (shapleySolution : Solution N).Linearity := by
  intro c d G H i
  -- shapleyValue is a Finset.sum over orderings of c(s,n) * marginalContribution
  -- marginalContribution is linear in v (it's a difference v(S∪{i}) - v(S))
  -- SmulGame.v scales v by c, AddGames.v adds v components
  -- Thus shapleyValue (c·G + d·H) i = c · shapleyValue G i + d · shapleyValue H i
  unfold shapleySolution shapleyValue
  unfold Solution.AddGames Solution.SmulGame TUGame.marginalContribution
  simp only [...]
  ring  -- or `linarith` / explicit `Finset.sum_add_distrib` + `Finset.mul_sum`
```

Probable proof structure (3 tactics combined) :
- `unfold` definitions
- `Finset.sum_add_distrib` to split the sum
- `Finset.mul_sum` + `ring` to factor scalars

Estimated effort by prover BG : 1-2 cycles per theorem (linearity + uniqueness).

## Existing `shapley_additivity` theorem

Keep `shapley_additivity` at L530 unchanged (it's the binary form, derivable from `shapley_linearity` via c=d=1). Optionally refactor body to `exact linearity_implies_additivity shapley_linearity G H i` (1-line proof).

## Prover BG multi-agent dispatch

Recommended sequence for po-2026 multi_agent_proof.py (prover_main.py / agents.py / workflow.py / tools.py / provers.py) :

| Step | Theorem | Hypotheses | Estimated cycles |
|------|---------|------------|------------------|
| 1 | `linearity_implies_additivity` | trivial unfolding | 1 cycle |
| 2 | `shapley_linearity` | `Finset.sum_add_distrib`, `Finset.mul_sum`, `ring` | 1-2 cycles |
| 3 | `shapley_uniqueness` L780 | `mobius_decomposition_axiom`, `h_lin`, `phi_unanimity`, `Finset.induction_on` or List induction | 2-3 cycles |

**HARD discipline** (user A.1 decision) :
- Each step = prover BG dispatch, NOT manual proof by agent
- If prover BG fails 3 cycles : **fix/strengthen prover script** (do not bypass to manual)
- ai-01 may strengthen script lemma library (add `phi_sum_lemma` derivable from Linearity) if needed
- Fallback Tentative #3 (Harsanyi formula direct) requires user sign-off, ~3× longer

## Fallback if prover BG cannot close shapley_uniqueness

If 3+ cycles fail with Linearity hypothesis, the **finite sum extension lemma** may need explicit construction :

```lean
private lemma phi_sum_lemma (φ : Solution N) (h_lin : φ.Linearity)
    (l : List (Finset N × ℝ × N → Prop)) (G_l : ... → TUGame N) (i : N) :
    φ (Solution.sumGames l G_l) i = ∑_{a ∈ l}, φ (G_l a) i := by
  induction l with
  | nil => simp [Solution.sumGames]; exact phi_zero_game ...
  | cons a as ih => ...
```

This lemma + Möbius decomposition close `shapley_uniqueness`. Estimated ~15-20 lines additional. Could be added before step 3 of the prover BG dispatch.

## Acceptance criteria

PR `feat/lean-mobius-shapley` (#1024) closes when :
1. `Linearity` def + `linearity_implies_additivity` lemma compile
2. `shapley_linearity` proved (no sorry)
3. `shapley_uniqueness` proved (no sorry) — closing L780
4. Lake build SUCCESS post-modification (rule feedback_lake_build_required_before_lean_merge.md)
5. Sorry count Shapley.lean : 1 → 0
6. Total cluster sorrys : 5 → 4

## References

- Shapley L.S. (1953), "A Value for n-Person Games", §3
- Roth A.E. (1988), *The Shapley Value: Essays in Honor of L.S. Shapley*, p.2-5
- Hart S., Mas-Colell A. (1989), "Potential, Value, and Consistency" (alternative potential route, longer)
- Stanley R. (1986), *Enumerative Combinatorics* §3.7-3.8 (Möbius Boolean lattice)
- Harsanyi J. (1963), "A Simplified Bargaining Model for the n-Person Cooperative Game" (dividends, fallback Tentative #3)
