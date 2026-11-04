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

**Scope and limit, documented.** Two levels of bound are delivered: GRID
(`trajectory_states_le_of_period`: at most `p` distinct states) and NODES
(`nodes_novelty_bound_of_period`: at most `p * nodesBound k` distinct
subtrees of the trajectory framed at level `k`). The second is the
operational quantity of hashlife — the memoization cache hit rate, with
subtree sharing: the induction over the `MacroCell` structure that this
module declared out of reach at the initial delivery (#11162, where the
"bound or diagnosis" alternative had retained the diagnosis) is now the
content of the dedicated section below. Still open, for good: the
characterization "which patterns have persistent novelty" is undecidable in
the limit (Life is Turing-complete: a programmed Turing machine encodes
the infinite production of new patterns) — pathological patterns (TM,
#6724) are the witnesses of this ceiling.

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
import Conway.Life.MacroCell
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

open Conway.Life.MacroCell

/-! ## Novelty bound at the node level (macrocells)

The diagnosis of the preamble is lifted here: the induction over the
`MacroCell` structure declared out of reach there is the content of this
section. The operational novelty of hashlife is measured at the level of
the quadtree NODES — the memoization cache keys, with subtree sharing. The
trajectory of an oscillator, framed at level `k`, visits only a bounded
number of distinct subtrees, with upper bound `p * nodesBound k`
independent of the horizon: the quantitative counterpart, at the cache
level, of the grid bound above. -/

/-- Counts the nodes of a perfect quadtree of depth `k`: the geometric sum
`1 + 4 + 16 + ... + 4^k = (4^(k+1) - 1) / 3`, defined by its recurrence —
the proof-friendly form. -/
def nodesBound : Nat → Nat
  | 0 => 1
  | k + 1 => 1 + 4 * nodesBound k

/-- Structural depth of a macrocell: the height of the tree, measured on
the deepest of the four sub-cells. Unlike `level` (which only looks at the
north-west quadrant), it assumes no well-formedness: it is the natural
parameter of the cardinal bound below, valid for any macrocell, balanced
or not. -/
def depth : MacroCell → Nat
  | leaf _ => 0
  | node nw ne sw se =>
      1 + max (depth nw) (max (depth ne) (max (depth sw) (depth se)))

/-- All the subtrees of a macrocell, itself included. Every element is a
node of the quadtree — a potential memoization cache key of hashlife. The
node-level novelty of a state is the cardinal of this set. -/
def allSubtrees (c : MacroCell) : Finset MacroCell :=
  match c with
  | leaf _ => {c}
  | node nw ne sw se =>
      insert c (allSubtrees nw ∪ allSubtrees ne ∪ allSubtrees sw ∪ allSubtrees se)

/-- `nodesBound` grows with the depth. -/
theorem nodesBound_mono {k m : Nat} (h : k ≤ m) : nodesBound k ≤ nodesBound m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = k + n := ⟨m - k, by omega⟩
  clear h
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    calc nodesBound k ≤ nodesBound (k + n) := ih
      _ ≤ 1 + 4 * nodesBound (k + n) := by omega
      _ = nodesBound ((k + n) + 1) := rfl.symm
      _ = nodesBound (k + (n + 1)) := by rw [Nat.add_assoc]

/-- A macrocell of depth `d` carries at most `nodesBound d` distinct
subtrees: the induction over the `MacroCell` structure announced in the
preamble. The union may deduplicate (subtrees shared across quadrants),
never grow — the bound holds even for unbalanced trees. -/
theorem allSubtrees_card (c : MacroCell) : (allSubtrees c).card ≤ nodesBound (depth c) := by
  induction c with
  | leaf b =>
    simp only [allSubtrees, depth, nodesBound]
    simp
  | node nw ne sw se ihnw ihne ihsw ihse =>
    simp only [allSubtrees, depth]
    set M := max (depth nw) (max (depth ne) (max (depth sw) (depth se))) with hM
    have h1 := Finset.card_insert_le (a := node nw ne sw se)
      (s := allSubtrees nw ∪ allSubtrees ne ∪ allSubtrees sw ∪ allSubtrees se)
    have e1 := Finset.card_union_le (allSubtrees nw ∪ allSubtrees ne ∪ allSubtrees sw)
      (allSubtrees se)
    have e2 := Finset.card_union_le (allSubtrees nw ∪ allSubtrees ne) (allSubtrees sw)
    have e3 := Finset.card_union_le (allSubtrees nw) (allSubtrees ne)
    have hn : (allSubtrees nw).card ≤ nodesBound M := ihnw.trans (nodesBound_mono (by omega))
    have he : (allSubtrees ne).card ≤ nodesBound M := ihne.trans (nodesBound_mono (by omega))
    have hs : (allSubtrees sw).card ≤ nodesBound M := ihsw.trans (nodesBound_mono (by omega))
    have hd : (allSubtrees se).card ≤ nodesBound M := ihse.trans (nodesBound_mono (by omega))
    have hstep : nodesBound (1 + M) = 1 + 4 * nodesBound M := by
      rw [Nat.add_comm]; rfl
    omega

/-- The level-`k` framing of a grid is a quadtree of depth exactly `k`:
`buildFromGrid` builds the perfect tree covering the square, all quadrants
present down to the leaves. -/
theorem depth_buildFromGrid (g : Grid) (lvl : Nat) (r0 c0 : Int) :
    depth (buildFromGrid g r0 c0 lvl) = lvl := by
  induction lvl generalizing r0 c0 with
  | zero => rfl
  | succ n ih =>
    simp only [buildFromGrid, depth]
    simp only [ih]
    omega

/-- **Node-level novelty bound for an oscillator**: if `evolve p g = g` with
`p > 0`, then the whole trajectory, framed at level `k` at `(r0, c0)`,
visits only a bounded number of distinct nodes — at most `p * nodesBound k`
subtrees, an upper bound independent of the horizon. Every instant of the
trajectory reduces to one of the first `p` steps
(`novelty_bound_of_period`), and each of those steps contributes at most
`nodesBound k` nodes (`allSubtrees_card`, on a framing of depth exactly `k`
by `depth_buildFromGrid`). This is the quantitative counterpart, at the
hashlife cache level, of the grid bound: the memoization hit rate cannot
degrade with the horizon, on the class of oscillators. -/
theorem nodes_novelty_bound_of_period (g : Grid) (p : Nat) (hp0 : 0 < p)
    (hp : evolve p g = g) (k : Nat) (r0 c0 : Int) :
    ∃ s : Finset MacroCell, s.card ≤ p * nodesBound k ∧
      ∀ t : Nat, ∀ x ∈ allSubtrees (buildFromGrid (evolve t g) r0 c0 k), x ∈ s := by
  refine ⟨(Finset.range p).biUnion
    fun r => allSubtrees (buildFromGrid (evolve r g) r0 c0 k), ?_, ?_⟩
  · calc ((Finset.range p).biUnion
          fun r => allSubtrees (buildFromGrid (evolve r g) r0 c0 k)).card
        ≤ ∑ r ∈ Finset.range p,
            (allSubtrees (buildFromGrid (evolve r g) r0 c0 k)).card := Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ Finset.range p, nodesBound k := Finset.sum_le_sum fun r _ => by
          have h := allSubtrees_card (buildFromGrid (evolve r g) r0 c0 k)
          rw [depth_buildFromGrid] at h
          exact h
      _ = p * nodesBound k := by rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul]
  · intro t x hx
    obtain ⟨r, hr, heq⟩ := novelty_bound_of_period g p hp0 hp t
    rw [heq] at hx
    exact Finset.mem_biUnion.2 ⟨r, Finset.mem_range.2 hr, hx⟩

/-! ### Application: the blinker, node level -/

/-- The blinker (period 2), framed at level `k`: at most `2 * nodesBound k`
distinct nodes visited over the whole trajectory, whatever the horizon. -/
theorem blinker_h_nodes_novelty_bound (k : Nat) (r0 c0 : Int) :
    ∃ s : Finset MacroCell, s.card ≤ 2 * nodesBound k ∧
      ∀ t : Nat, ∀ x ∈ allSubtrees (buildFromGrid (evolve t blinker_h) r0 c0 k), x ∈ s :=
  nodes_novelty_bound_of_period _ 2 (by norm_num) (by decide) k r0 c0

/-- Exact numerical witness: the level-2 framing of the blinker carries
exactly 6 distinct nodes — the root, three distinct quadrants (the two
empty East quadrants are identified) and the two leaves — against a general
bound of `nodesBound 2 = 21` on a single state. -/
theorem blinker_h_level2_nodes_card :
    (allSubtrees (buildFromGrid blinker_h (-1) (-1) 2)).card = 6 := by
  decide

end Life_en
end Conway_en
