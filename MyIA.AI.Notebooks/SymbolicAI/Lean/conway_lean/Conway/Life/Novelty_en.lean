/-
Copyright (c) 2026 CoursIA. All rights reserved.
Distributed under the Apache 2.0 license as described in the LICENSE file.

## Conway's Game of Life — Novelty bound for the class of oscillators

The EFFICIENCY axis of hashlife (#11162): the quantity that makes Golly
fast is not confinement (`jumpCaptured`, #11007 — the licence) but
NOVELTY, i.e. the stability of the set of states visited along the
trajectory. This module formalizes the stability invariant for the
simplest class: oscillators.

**Result.** If `evolve p g = g` with `p > 0` (g is a fixed point of the
p-th iterate — the period in the sense of `isOscillator`), then the whole
trajectory `t |-> evolve t g` only visits states already seen within the
first `p` steps (`novelty_bound_of_period`), hence there exists a `Finset`
of cardinal at most `p` containing the entire trajectory
(`trajectory_states_le_of_period`). The grid-level novelty is bounded by
`p`, independently of the horizon: this is the quantitative counterpart of
the empirical fact "Golly is fast on oscillators".

**Scope and limit, documented.** The bound is at the GRID level (distinct
states). The operational novelty of hashlife is measured at the level of
MACROCELL NODES (memoization cache hit rate, with subtree sharing): for a
bounded oscillator each periodic state grows a tree whose subtrees repeat,
but the grid -> macrocell tree passage has a size growing with the window,
and the node-level bound requires an induction over the `MacroCell`
structure which remains out of reach of this module (written diagnosis,
cf #11162 acceptance: the "derived bound or diagnosis" alternative is here
the diagnosis of the node-level bound, the grid-level bound being
delivered).

The characterization "which patterns have persistent novelty" is
undecidable in the limit (Life is Turing-complete: a programmed Turing
machine encodes the infinite production of new patterns) — pathological
patterns (TM, #6724) are the witnesses of this ceiling.

This module is fully proved (no `sorry`, no native axioms).
-/

/-
  i18n convention (EPIC #4980, user decision 2026-07-04): this file is the
  **English sibling** of the canonical French `Novelty.lean` (sibling-pair
  model ratified 2026-07-04, cf `code-style.md` §Lean i18n). Theorem
  statements, Lean tactics, lemma names and Mathlib references stay in
  English (Mathlib 4 compatibility); only theorem docstrings and this
  header block differ between the two files.
-/

import Conway.Life
import Conway.Life.HashlifeCorrectness.Foundation

namespace Conway_en
open Conway
namespace Life_en
open Life

/-! ## Multiples of the period

The iteration lemma `evolve_add` (Foundation, P4.4) says that `evolve` is a
morphism of addition: composing `q` blocks of period `p` returns to the
initial state. This is the only arithmetic the bound needs. -/

/-- The period re-applies at every point of the trajectory: if
`evolve p g = g`, then `evolve p (evolve m g) = evolve m g` for all `m`.
This is the commutativity of iterate addition at work: `p + m = m + p`,
and the `p` block on the right reduces by `hp`. -/
theorem evolve_period_shift (g : Grid) (p : Nat) (hp : evolve p g = g) (m : Nat) :
    evolve p (evolve m g) = evolve m g := by
  rw [← evolve_add, Nat.add_comm, evolve_add, hp]

/-- Every multiple of the period leaves every point of the trajectory
invariant: if `evolve p g = g`, then `evolve (p * q) (evolve m g) = evolve m g`
for all `q`, `m` — the `p * q` block decomposes into `q` blocks `p`, each
reducing by `evolve_period_shift`. -/
theorem evolve_mul_shift (g : Grid) (p : Nat) (hp : evolve p g = g) (q m : Nat) :
    evolve (p * q) (evolve m g) = evolve m g := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, evolve_add, evolve_period_shift g p hp m, ih]

/-- Every multiple of the period returns to the initial state: if
`evolve p g = g`, then `evolve (p * q) g = g` for all `q` (the `m = 0`
case of the shift). -/
theorem evolve_mul_of_period (g : Grid) (p : Nat) (hp : evolve p g = g) (q : Nat) :
    evolve (p * q) g = g := by
  simpa using evolve_mul_shift g p hp q 0

/-! ## Novelty bound (grid level)

The stability invariant: after `p` steps, the trajectory produces no new
state. Everything visited at time `t` has already been seen at some time
`r < p`. -/

/-- **Novelty bound for an oscillator**: if `evolve p g = g` with `p > 0`,
then every state visited at an arbitrary time `t` has already been seen
within the first `p` steps — the trajectory never produces a new state
after the period. The witness is the remainder `t % p`. -/
theorem novelty_bound_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) (t : Nat) :
    ∃ r, r < p ∧ evolve t g = evolve r g := by
  obtain ⟨r, hr, hdecomp⟩ : ∃ r, r < p ∧ t = p * (t / p) + r :=
    ⟨t % p, Nat.mod_lt t hp0, (Nat.div_add_mod t p).symm⟩
  refine ⟨r, hr, ?_⟩
  rw [hdecomp, evolve_add, evolve_mul_shift g p hp (t / p) r]

/-- **Trajectory cardinal**: the whole trajectory of an oscillator of
period `p` fits in a `Finset` of cardinal at most `p`. This is the
set-theoretic formulation of "at most `p` distinct states", the formal
counterpart of the empirical fact "Golly is fast on oscillators": the
memoization hit rate cannot degrade with the horizon. -/
theorem trajectory_states_le_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) :
    ∃ s : Finset Grid, s.card ≤ p ∧ ∀ t : Nat, evolve t g ∈ s := by
  refine ⟨(Finset.range p).image (fun r => evolve r g),
    Finset.card_image_le.trans_eq (Finset.card_range p), fun t => ?_⟩
  obtain ⟨r, hr, heq⟩ := novelty_bound_of_period g p hp0 hp t
  exact Finset.mem_image.2 ⟨r, Finset.mem_range.2 hr, heq.symm⟩

/-! ## Application: the blinker

The blinker (period 2, `blinker_period_two` in `Conway.Life`) visits at
most 2 states — horizontal and vertical — whatever the horizon. -/

/-- The trajectory of the horizontal blinker (period 2) fits in a `Finset`
of cardinal at most 2: two distinct states, never more, whatever the
simulation horizon. -/
theorem blinker_h_trajectory_states_le :
    ∃ s : Finset Grid, s.card ≤ 2 ∧ ∀ t : Nat, evolve t blinker_h ∈ s :=
  trajectory_states_le_of_period _ 2 (by norm_num) (by decide)

end Life_en
end Conway_en
