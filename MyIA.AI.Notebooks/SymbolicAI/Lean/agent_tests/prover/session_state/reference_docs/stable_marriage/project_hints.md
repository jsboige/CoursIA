# Domain tactic patterns — Stable Marriage / Gale-Shapley Lean proofs

Consolidated from issue #1081 Part 1 (5 manually-discovered patterns) and the
`tactic_cookbook` section of `agent_tests/prover/proof_knowledge.json` (150 patterns,
seeded from the ~4 manual sessions that proved `womenBestState.step`).

These hints are project-specific. They apply to proofs over `GSState` / `GSMatching` /
`gsStep` / `gsStepWith` / `gsChooseMax` and the invariant lemmas in `existing_proofs.lean`.

## The 5 core patterns (issue #1081 Part 1)

### 1. `change` to normalize hypotheses
**When:** a hypothesis contains raw `Classical.choose` / `gsChooseMax` that does not
syntactically match the local definitions, so `simp` and `split` stay stuck.
**Do:** `change (normalized_expr) at h` to rewrite the hypothesis into its unfolded form.
**Example (`womenBestState.step`):**
`change (gsStepWith prof σ m₀ w₀).matching.womenMatch w = some m at hmatch`
— after `set m₀`/`set w₀`, `hmatch` still held the raw `gsStep`/`gsChooseMax`; `change`
normalizes it so the following `simp only [gsStepWith]` + `split` can fire.

### 2. `split at h` for an irreducible `match`
**When:** `simp only [Def] at h` leaves an irreducible `match` expression in the hypothesis
and `simp [discriminant_eq]` cannot reduce it.
**Do:** `split at h` — it creates the `none` / `some` branches directly.
**Example:** `simp only [gsStepWith] at hmatch; split at hmatch` — `gsStepWith` matches on
`womenMatch w`; `split` gives the `none` (matchFree) and `some mOld` (swap/reject) cases.

### 3. `rcases` before `subst` (anti-reflexivity)
**When:** you need both `rcases` and `subst` on a potentially-reflexive equality. An
`rcases ... with rfl` can unify variables, making a later equality reflexive so `subst`
fails ("motive is not type correct" / "did not find instance of the pattern").
**Do:** do the `rcases` with `rfl` patterns first, handle each branch separately.
**Example:** `rcases hsrc with (hw' | ⟨rfl, rfl⟩)` — the `⟨rfl, rfl⟩` branch unifies
`m = m₀` and `w = w₀`; the other branch keeps them distinct.

### 4. Explicit `@` for implicit-heavy lemmas
**When:** a lemma has implicit args (`{n}`, `[NeZero n]`, section variables) that Lean
cannot infer in the current context.
**Do:** apply it with `@` and pass the implicits positionally.
**Example:** `(@proposedSet.mem_iff n _ prof (gsStepWith prof σ m₀ w₀) (m', w)).mpr hprop`
— `proposedSet.mem_iff` needs `n`, the `NeZero n` instance, `prof`, `σ` before the pair.

### 5. `dsimp` before `rw` on `match` constructs
**When:** the goal/hypothesis contains a structure update (`GSMatching.matchFree` /
`swapMatch`) and you want to `rw [Function.update_apply]`, but `rw` fails because the term
is still wrapped in a `match`/projection.
**Do:** `dsimp [GSMatching.swapMatch]` (or `matchFree`) first, then `rw [Function.update_apply]`.
**Example:** `dsimp [GSMatching.swapMatch] at hmatch ⊢; rw [Function.update_apply, Function.update_apply] at hmatch`.

## Additional domain patterns (from proof_knowledge.json tactic_cookbook)

### `Function.update` + `split_ifs`
Goal/hypothesis from `matchFree`/`swapMatch` contains `Function.update`. Do
`simp only [GSMatching.matchFree, Function.update_apply]; split_ifs` — `update_apply`
turns the update into an if-then-else; `split_ifs` produces the branches (4 for a single
update, 6 for the nested double update in `swapMatch` — name them:
`split_ifs with h_mOld h_ww h_m h_nw h_nm`). Close each branch with `simp_all`, and the
default (neither) branch with `exact h m' w'`.

### Consistency chain via the `iff`
`GSConsistent μ` is `∀ m w, menMatch m = some w ↔ womenMatch w = some m`. Use
`(h m w).mp` for men→women, `(h m w).mpr` for women→men, `(h m w).symm` for the reversed
iff. To prove an inequality `womenMatch w' ≠ some m`, assume equality then derive a
contradiction through the consistency chain (`intro heq; have := (h m w').mpr heq; simp_all`).

### `runSteps` invariant induction (universal skeleton)
Every `*.runSteps` invariant lemma has the same shape:
```
induction k with
| zero => exact <initial_lemma> prof
| succ k' ih =>
  simp only [gsRunSteps]
  by_cases h : ∃ m, gsIsFree prof (gsRunSteps prof k') m
  · exact <step_lemma> prof ih h
  · have hid : gsStep prof (gsRunSteps prof k') = gsRunSteps prof k' := by
      unfold gsStep; simp [h]
    rw [hid]; exact ih
```
Either a free man exists (apply the `step` lemma) or not (`gsStep` is the identity, proved
by `unfold gsStep; simp [h]`).

### `Classical.choose` / `choose_spec` for existentials
`hfree : ∃ m, gsIsFree prof σ m` → `let m := Classical.choose hfree;
have hm : gsIsFree prof σ m := Classical.choose_spec hfree`. Always introduce the witness
and its spec together.

### `gsChooseMax` maximality — trichotomy strategy
To prove `∀ y ∈ candidates, y ≤ choose` for the custom `gsMenPrefLE` preorder:
`obtain ⟨-, hmax⟩ := Classical.choose_spec (Finset.exists_maximal h)`, then
`Nat.lt_trichotomy (prof.menPref m w) (prof.menPref m choose)` and `rcases` into 3 cases.
CRITICAL: `hmax` from `Maximal` is CONDITIONAL — `hmax hw` has type
`(choose ≤ w → w ≤ choose)`, not `w ≤ choose` directly. The equal-preference case is
closed by `(prof.menPref_bijective m).injective` turning a `menPref` equality into a
`Fin` equality.

### Custom `LE` / `IsTrans` instance for `Finset.exists_maximal`
`Finset.exists_maximal` needs `LE` + `IsTrans`. Build them locally:
`letI : LE (Fin n) := ⟨gsMenPrefLE prof m⟩` then `haveI : IsTrans (Fin n) (· ≤ ·) := ⟨...⟩`
(transitivity by `cases` on the `Or` of `gsMenPrefLE`, `lt_trans` for the `inr`/`inr` case).

### `injection` for `Option` equality
After `Function.update` reduction a hypothesis is `some x = some y` (or `none = none`):
`injection hmatch with hw; subst hw` extracts the underlying equality.

### `by_contra` / `exfalso` for blocking-pair contradictions
The GS correctness theorems are proved by contradiction: `intro h; by_contra hnot` (or
`exfalso`), `obtain` the witnesses, then derive `False` by exhibiting a blocking pair or a
violated invariant. `exfalso` is also useful when the goal is a non-`False` proposition but
the context already holds a contradiction (`exfalso; exact h hw`).

## Pitfalls to avoid (failed approaches)

- `simp` / `aesop` alone never closes a `gsStepWith` case-analysis goal — the `match` must
  be `split` first.
- `omega` only works after every quantity is a pure `Nat`/`Int`; `menPref m w` IS a `Fin n`
  — convert or use `.val` / `Fin.lt_iff_val_lt_val` before `omega`.
- Do not `rw` into a `match` construct; `dsimp` the structure update first (pattern 5).
- Do not `subst` a variable that a prior `rcases ⟨rfl, ...⟩` already unified (pattern 3).
- Modifying the target theorem or its hypotheses to make a proof go through is forbidden
  (anti-regression rule) — `mark_sorry_intractable` instead if genuinely stuck.
