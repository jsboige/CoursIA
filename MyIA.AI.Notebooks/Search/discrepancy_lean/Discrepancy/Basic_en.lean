import Mathlib

/-!
# i18n convention: EN sibling file

i18n convention ratified for this repository (EPIC #4980): for each canonical
FR file `Foo.lean`, an EN sibling `Foo_en.lean` mirrors it with translated
docstrings and comments ONLY — signatures, definitions, proofs and tactics
are byte-identical; the namespace carries the `_en` suffix to avoid name
clashes. The FR file remains the canonical teaching source.
-/

/-!
# Combinatorial discrepancy: definitions, elementary lemmas, conjectures

Foundations of the `discrepancy_lean` lake (issue #12823). Given a finite
family `F` of subsets of a set of elements, **discrepancy** measures how well
one can color each element in `±1` so that every colored sum
`∑_{x ∈ S} c x` stays small in absolute value — for the **worst** set of the
family. This is the central object of combinatorial discrepancy theory
(Spencer, Beck–Fiala, Banaszczyk, Bansal–Jiang 2025).

## Disambiguation (one line, mandatory)

`Search-13-LimitedDiscrepancySearch` (same `Search/` series) uses
"discrepancy" in an **other sense**: Harvey & Ginsberg's Limited Discrepancy
Search, where the discrepancy of a branch = the number of choices where one
goes against the heuristic along a tree search. No mathematical relation
with the signed sums formalized here.

## The "decoupling" thread

The modern bounds (Banaszczyk 1998, Bansal–Jiang 2025, arXiv:2508.03961)
rest on a gesture this repository already teaches elsewhere: **decouple**
quantities that conspire — non-centered reparametrization unfolding the
funnel (PyMC-12), decoupling `|empError − μ| ≥ ε ⟺ (nε ≤ Z) ∨ (Z ≤ −nε)`
(Hoeffding.lean), the RL double estimator Q1/Q2. Here, the decoupling is
*spectral and affine*: constraints on an SDP make the discrepancy
evolutions of the different lines stop conspiring, making concentration
applicable.

## Conjectures = named `Prop`s

The open statements (Beck–Fiala `O(√k)` below, Komlós `O(1)` and
Bansal–Jiang forms in `Discrepancy.Komlos_en`) are `def ... : Prop`
**without proof** — never truncated theorems with `sorry`. The lake contains
no `sorry` (anti-regression convention D of the repository); the state of
the proofs lives in `FORMAL_STATUS.md`.
-/

namespace Discrepancy_en

/-- A `±1` coloring: every element receives exactly `1` or `-1`. -/
def IsColoring {α : Type*} (c : α → ℤ) : Prop :=
  ∀ x, c x = 1 ∨ c x = -1

/-- Discrepancy of a finite family of finite sets under a coloring: the
maximum of the absolute values of the colored sums, taken over all sets of
the family. -/
def discrepancy {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (c : α → ℤ) : ℕ :=
  (F.image fun S => (S.sum c).natAbs).sup id

/-- Degree of an element `x`: number of sets of the family containing `x`.
The "degree at most `k`" hypothesis is Beck–Fiala's: each element appears in
at most `k` constraints. -/
def degree {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) : ℕ :=
  (F.filter fun S => x ∈ S).card

/-- Maximal degree of a family over a finite type: the `k` of the Beck–Fiala
statements. -/
def maxDegree {α : Type*} [DecidableEq α] [Fintype α] (F : Finset (Finset α)) : ℕ :=
  Finset.univ.sup fun x => degree F x

/-! ## Elementary lemmas

Three immediate facts, proved right away: they anchor the definitions in
checkable limiting examples (and serve as smoke tests of the lake). -/

/-- The empty family has zero discrepancy, for any coloring. -/
theorem discrepancy_empty {α : Type*} [DecidableEq α] (c : α → ℤ) :
    discrepancy ∅ c = 0 := by
  simp [discrepancy]

/-- A family reduced to the empty set has zero discrepancy: summing over `∅`
never gives anything. -/
theorem discrepancy_singleton_empty {α : Type*} [DecidableEq α] (c : α → ℤ) :
    discrepancy {∅} c = 0 := by
  simp [discrepancy]

/-- The degree of an element is bounded by the number of sets of the
family. -/
theorem degree_le_card {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (x : α) :
    degree F x ≤ F.card := by
  simp only [degree]
  exact Finset.card_filter_le _ _

/-! ## Conjectures and target (statements, without proof) -/

/-- **Beck–Fiala conjecture (1981)**: there exists a universal constant `C`
such that every family of subsets of `Fin n` of degree at most `k` admits a
`±1` coloring with discrepancy at most `C * √k`.

This is the central open conjecture of the field. Bansal–Jiang (2025)
resolve it in the large-degree regime `k ≥ (log n)²` — see
`Discrepancy.BansalJiangLargeDegree`. -/
def BeckFialaConjecture : Prop :=
  ∃ C : ℕ, ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k),
    ∃ c : Fin n → ℤ, IsColoring c ∧ discrepancy F c ≤ C * Nat.sqrt k

/-- **Classical Beck–Fiala theorem**: every family of subsets of `Fin n` of
degree at most `k` (with `k ≥ 1`) admits a `±1` coloring with discrepancy
at most `2k - 1`.

This is the "nut" targeted by tier P1 of issue #12823: proof by *floating
variables* and partial coloring, split into bricks `b1`–`b4` (see
`FORMAL_STATUS.md`). Until the proof is assembled, the statement lives as a
named `Prop`; brick `b4` will convert it into a `theorem`. -/
def BeckFialaClassic : Prop :=
  ∀ (n k : ℕ) (F : Finset (Finset (Fin n))) (_hk : maxDegree F ≤ k) (_hk1 : 1 ≤ k),
    ∃ c : Fin n → ℤ, IsColoring c ∧ (discrepancy F c : ℤ) ≤ 2 * (k : ℤ) - 1

end Discrepancy_en
