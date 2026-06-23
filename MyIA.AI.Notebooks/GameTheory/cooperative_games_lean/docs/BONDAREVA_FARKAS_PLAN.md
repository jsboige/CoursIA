# Bondareva-Shapley `hb_witness`: Farkas plan via `(Option N) → ℝ`

> **⚠ SUPERSEDED (2026-06-22).** Ce plan Farkas / séparation d'hyperplan est **historique**.
> Le noyau d'atteinte `hb_witness` a été **prouvé** par PR #3954 (`a5288f0a7`) via un
> argument de **tranche compacte + Weierstrass** (`Basic.lean:348`) — qui contourne le
> lemme `ProperCone.hyperplane_separation` manquant dans Mathlib **sans axiome ajouté**.
> Le projet `cooperative_games_lean` est désormais **0 sorry** et `bondareva_shapley`
> (`Core.Nonempty ↔ Balanced`) est entièrement certifié. Ce document est conservé pour
> la traçabilité de la stratégie ; ne pas le suivre comme un plan actif. Voir
> [`../FORMAL_STATUS.md`](../FORMAL_STATUS.md) pour l'état réel.

**Agent:** po-2026 | **Date:** 2026-06-20 | **Issue:** #2959

This plan **supersedes** the older `BONDAREVA_SHAPLEY_HARDNESS.md` strategy (which used a
product space `(N → ℝ) × ℝ` and hit an `IsOrderedAddMonoid` instance blocker). It documents
infrastructure that has been **validated to compile** against the project's Mathlib v4.30-rc2.

## The open kernel

`CooperativeGames/Basic.lean:312`:

```lean
have hb_witness : ∃ x ∈ P, ∑ i : N, x i ≤ G.v Finset.univ := by
  sorry
```

where `P = { x | ∀ S : Finset N, ∑ i ∈ S, x i ≥ G.v S }` and `hb : G.Balanced`.

## Why `(Option N) → ℝ` (not the product space)

The natural encoding of the Farkas alternative needs both the coalition-incidence vector
`w ↦ (i ↦ ∑_{S ∋ i} w_S)` **and** the value functional `w ↦ ∑_S w_S · v(S)`. The naive product
space `(N → ℝ) × ℝ` fails: `ProperCone.positive ℝ ((N → ℝ) × ℝ)` does not synthesize
(`IsOrderedAddMonoid` is not automatic on products).

**Fix:** work in `E := (Option N) → ℝ`. The `none` coordinate carries the value functional;
the `some i` coordinates carry the coalition sums. `Pi` instances over `Fintype (Option N)`
give us `LocallyConvexSpace`, `ProperCone.positive`, etc. **for free** (verified to compile).

## Validated infrastructure (compiles in scratch, ~17s incremental)

```lean
variable {N : Type*} [Fintype N] [DecidableEq N]

-- The augmented incidence map. (Value-functional branch left as 0 placeholder; plug G.v.)
noncomputable def phiAugLinear : (Finset N → ℝ) →ₗ[ℝ] ((Option N) → ℝ) where
  toFun w := fun j => match j with
    | some i => ∑ S ∈ Finset.univ.filter (fun S => i ∈ S), w S
    | none   => 0  -- replace with ∑ S, w S * G.v S once G is in scope
  map_add'   := …   -- match on `some`/`none`; simp [Pi.add_apply, Finset.sum_add_distrib]
  map_smul'  := …   -- match; simp [Finset.mul_sum, Pi.smul_apply]

noncomputable def phiAugCont : (Finset N → ℝ) →L[ℝ] ((Option N) → ℝ) :=
  LinearMap.toContinuousLinearMap phiAugLinear  -- finite-dim auto-continuity

noncomputable def augCone : ProperCone ℝ ((Option N) → ℝ) :=
  (ProperCone.positive ℝ (Finset N → ℝ)).map phiAugCont
```

Applicability of Farkas **verified**:

```lean
-- hyperplane_separation_point applies directly on augCone
example (x₀ : (Option N) → ℝ) (h : x₀ ∉ augCone) :
    ∃ f : StrongDual ℝ ((Option N) → ℝ),
      (∀ x ∈ augCone, 0 ≤ f x) ∧ f x₀ < 0 :=
  ProperCone.hyperplane_separation_point augCone h
```

## Remaining work to close `hb_witness` (the hard translation)

1. **Instantiate `phiAugLinear.none` branch** with `∑ S, w S * G.v S` (needs `G : TUGame N` in
   scope; move the construction inside the `bondareva_shapley_backward` proof body, where `G` is).
2. **Exhibit `x₀ ∉ augCone`** under `¬(∃ x ∈ P, ∑ xᵢ ≤ v(N))`. Candidate:
   `x₀(some i) = 1`, `x₀(none) = v(N) + 1`. Membership in `augCone` means `∃ w ≥ 0,`
   `∑_{S∋i} w_S = 1` (balanced) and `∑_S w_S v(S) ≤ v(N)` — the second conjunct contradicts the
   "no witness" hypothesis once normalized. The exact `x₀` and the closure/`mem_map` reasoning
   are the crux (~40-60 lines).
3. **Translate `f : StrongDual ℝ ((Option N) → ℝ)` into concrete balanced weights.** Since
   `(Option N) → ℝ` is finite-dimensional with the dot-product pairing, `f` is represented by a
   vector `q : (Option N) → ℝ`: `f y = ∑ⱼ qⱼ yⱼ`. The condition `∀ x ∈ augCone, 0 ≤ f x`
   forces `q ≥ 0` (i.e. `q` is a non-negative weight system); `f x₀ < 0` gives the strict
   inequality that, combined with `x₀`'s shape, yields a balanced-weight violation of `hb`.
   This representation lemma (~60-80 lines) is the hardest piece.
4. **Conclude**: the balanced-weight violation contradicts `hb : G.Balanced`, so `x₀ ∈ augCone`,
   so the witness `x` exists.

## Estimates

| Piece | Lines | Difficulty | Status |
|-------|-------|------------|--------|
| `(Option N) → ℝ` infrastructure | ~25 | EASY | **COMPILES** (scratch) |
| `hyperplane_separation_point` application | ~5 | EASY | **COMPILES** (scratch) |
| `x₀ ∉ augCone` under ¬witness | ~40-60 | MEDIUM-HARD | TODO |
| `StrongDual → balanced weights` translation | ~60-80 | HARD | TODO |
| Conclusion (contradict `hb`) | ~15 | EASY | TODO |
| **Total to close** | **~150-180** | **MEDIUM-HARD** | WIP |

## Why not commit the scratch helpers into Basic.lean yet

The validated pieces (`phiAugLinear`, `augCone`, the applicability example) do not by themselves
reduce the sorry count — they are scaffolding. Committing them as named lemmas in `Basic.lean`
before the translation (3) is wired would be churn that does not advance `hb_witness` (anti-G.3).
The plan is to land them as a single PR together with the proof, once the translation is done.

## See also

- `BONDAREVA_SHAPLEY_HARDNESS.md` — older strategy (product space, instance blocker). Kept for
  historical context; the `(Option N) → ℝ` approach here is the active path.
- `FORMAL_STATUS.md` — corrected to 1 sorry (`hb_witness`), WIP_HARD.
