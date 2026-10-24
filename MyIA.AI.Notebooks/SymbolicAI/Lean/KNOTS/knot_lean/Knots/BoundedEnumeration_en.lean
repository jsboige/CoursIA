/-
Knots.BoundedEnumeration — Bounded canonical enumeration + small verifier
================================================================================

Step 4 of issue #18611 (Epic #1453, point 3): "bounded decidable
equivalence — enumeration of diagrams with bounded crossings, and deciding
connectivity by moves — the arbitration's 'small verifier'", combinatorial
side.

This module delivers:

  1. `allDiagrams n` — the **finite canonical enumeration** of knot diagrams
     with at most `n` crossings: for each `c ≤ n`, the lists of `c`
     crossings whose labels are bounded by `labelBound c`, filtered on
     well-formedness `KnotDiagram.wf`; the `c = 0` case adds the two
     degenerate diagrams (`numEdges ∈ {0, 1}`);
  2. `allDiagrams_bounded` — every diagram in the enumeration has at most
     `n` crossings: the universe is **bounded by construction**;
  3. `allDiagrams_wf` — every diagram in the enumeration is well formed:
     the universe is **sound**, we only decide on legitimate diagrams;
  4. `boundedClassConnects_sound` — the **soundness of the small verifier
     restricted to the bounded class**: if `verifyMoves` answers `true` for
     two diagrams of the enumeration, they are `ReidemeisterEquiv`;
  5. two executable examples: `demo_unknot_mem` (the unknot belongs to the
     enumeration — decided by computation) and `demo_verifier_sound` (the
     verifier's R1 witness sealed into a genuine `ReidemeisterEquiv` proof).

Scope and residual (declared, not hidden):
- the **completeness** of the enumeration — "every well-formed diagram with
  at most `n` crossings belongs to `allDiagrams n`" — is **not** proved
  here; it is the named residual of this step, carried by the PR;
- the enumeration is **not evaluated** at large bounds: it is a finite
  `List`-typed object, and only the `c = 0` cases are computed by `decide`;
- no deep knot-theory theorem is proved (the permanent `sorry`s stay those
  of `Knots.Lidman`, `Knots.Slice`).

i18n convention (EPIC #4980, user decision 2026-07-04): this file is the
**EN mirror**, with the canonical French version in the sibling
`BoundedEnumeration.lean` (sibling-pair model). Theorem statements, Lean
tactics, lemma names and Mathlib references stay in English (Mathlib 4
compatibility); only the module docstrings and this header block differ
between the two files.
-/

import Knots.Basic
import Knots.Reidemeister
import Knots.ReidemeisterCombinatorial

namespace Knots.Bounded

open Knots.Combinatorial

/-! ## 1. Label bound

`labelBound c = 2c`: a well-formed diagram with `c` crossings has four
endpoints per crossing, i.e. `4c` edge occurrences. The bound is therefore
a construction constant, not a property proved here.
-/

/-- Label bound of the bounded enumeration. -/
def labelBound (c : Nat) : Nat := 2 * c

/-! ## 2. Finite universe and enumeration

The construction is **declarative**: first the admissible crossings, then
the lists of `c` such crossings, then the well-formedness filter.
-/

/-- All crossings whose four labels lie in `[1, alpha]`. -/
def allBoundedCrossings (alpha : Nat) : List PDCrossing :=
  (List.range alpha).flatMap fun a1 =>
    (List.range alpha).flatMap fun a2 =>
      (List.range alpha).flatMap fun a3 =>
        (List.range alpha).map fun a4 =>
          ⟨a1 + 1, a2 + 1, a3 + 1, a4 + 1⟩

/-- All lists of `c` crossings whose labels are bounded by `alpha`. -/
def allCrossingLists (c alpha : Nat) : List (List PDCrossing) :=
  match c with
  | 0 => [[]]
  | c' + 1 =>
    (allCrossingLists c' alpha).flatMap fun xs =>
      (allBoundedCrossings alpha).map (fun x => x :: xs)

/-- Canonical diagram built on `c` crossings: the given crossings, and
    `labelBound c` edges. -/
def mkDiag (c : Nat) (l : List PDCrossing) : KnotDiagram :=
  { crossings := l, numEdges := labelBound c }

/-- Finite canonical enumeration of knot diagrams with at most `n`
    crossings.

    Case `c = 0`: the two degenerate diagrams. Case `c > 0`: the lists of
    `c` crossings with bounded labels, filtered on `wf`, then turned into
    diagrams. -/
def allDiagrams (n : Nat) : List KnotDiagram :=
  (List.range (n + 1)).flatMap fun c =>
    if c = 0 then
      [ ⟨[], 0⟩, ⟨[], 1⟩ ]
    else
      ((allCrossingLists c (labelBound c)).filter
        (fun l => (mkDiag c l).wf)).map (mkDiag c)

/-! ## 3. Properties of the enumeration -/

/-- Lists produced by `allCrossingLists c alpha` have exactly `c`
    elements: the length is carried by the construction. -/
theorem allCrossingLists_length (c alpha : Nat) :
    ∀ l ∈ allCrossingLists c alpha, l.length = c := by
  induction c with
  | zero =>
    intro l hl
    simp only [allCrossingLists, List.mem_singleton] at hl
    subst hl
    rfl
  | succ k ih =>
    intro l hl
    simp only [allCrossingLists, List.mem_flatMap, List.mem_map] at hl
    obtain ⟨xs, hxs, x, _, rfl⟩ := hl
    simp only [List.length_cons, ih xs hxs]

/-- Every diagram in the enumeration has at most `n` crossings: the
    universe is bounded by construction. -/
theorem allDiagrams_bounded (n : Nat) (d : KnotDiagram)
    (h : d ∈ allDiagrams n) : d.numCrossings ≤ n := by
  simp only [allDiagrams, List.mem_flatMap] at h
  obtain ⟨c, hc, hd⟩ := h
  rw [List.mem_range] at hc
  by_cases hc0 : c = 0
  · subst hc0
    have hd' : d = ⟨[], 0⟩ ∨ d = ⟨[], 1⟩ := by simpa using hd
    rcases hd' with rfl | rfl <;>
      simp only [KnotDiagram.numCrossings, List.length_nil] <;> omega
  · simp only [if_neg hc0, List.mem_map] at hd
    obtain ⟨l, hl, rfl⟩ := hd
    simp only [List.mem_filter] at hl
    obtain ⟨hl', _⟩ := hl
    simp only [mkDiag, KnotDiagram.numCrossings]
    rw [allCrossingLists_length c (labelBound c) l hl']
    omega

/-- Every diagram in the enumeration is well formed: we only decide on
    legitimate diagrams. -/
theorem allDiagrams_wf (n : Nat) (d : KnotDiagram)
    (h : d ∈ allDiagrams n) : d.wf = true := by
  simp only [allDiagrams, List.mem_flatMap] at h
  obtain ⟨c, _, hd⟩ := h
  by_cases hc0 : c = 0
  · subst hc0
    have hd' : d = ⟨[], 0⟩ ∨ d = ⟨[], 1⟩ := by simpa using hd
    rcases hd' with rfl | rfl
    · decide
    · decide
  · simp only [if_neg hc0, List.mem_map, List.mem_filter] at hd
    obtain ⟨l, ⟨_, hwf⟩, rfl⟩ := hd
    exact hwf

/-! ## 4. The small verifier on the bounded class

`verifyMoves` (bounded in move budget) and its soundness towards
`ReidemeisterEquiv` live in `Knots.ReidemeisterCombinatorial`. This module
gives their statement **restricted to the enumerated universe**: the form
used by the arbitration's "small verifier".
-/

/-- Soundness of the small verifier on the bounded class: if
    `verifyMoves budget d₁ d₂ = true` for two diagrams of the enumeration
    `allDiagrams n`, then they are `ReidemeisterEquiv`. -/
theorem boundedClassConnects_sound (n budget : Nat)
    (d₁ d₂ : KnotDiagram)
    (_h₁ : d₁ ∈ allDiagrams n) (_h₂ : d₂ ∈ allDiagrams n)
    (hv : verifyMoves budget d₁ d₂ = true) :
    ReidemeisterEquiv d₁ d₂ :=
  verifyMoves_sound budget d₁ d₂ hv

/-! ## 5. Executable examples -/

/-- The unknot belongs to the enumeration: decided by computation. -/
theorem demo_unknot_mem :
    ({ crossings := [], numEdges := 1 } : KnotDiagram) ∈ allDiagrams 0 := by
  simp [allDiagrams]

/-- The verifier's verdict is sealed into a genuine proof: the R1 witness
    pair of `Knots.ReidemeisterCombinatorial` is `ReidemeisterEquiv`. -/
theorem demo_verifier_sound :
    ReidemeisterEquiv
      { crossings := [⟨1, 2, 3, 4⟩, ⟨1, 2, 3, 4⟩], numEdges := 4 }
      { crossings := [⟨1, 2, 3, 4⟩, ⟨5, 2, 3, 4⟩, ⟨1, 5, 6, 6⟩],
        numEdges := 6 } :=
  verifyMoves_sound 1 _ _ verifyMoves_one_r1_witness

end Knots.Bounded
