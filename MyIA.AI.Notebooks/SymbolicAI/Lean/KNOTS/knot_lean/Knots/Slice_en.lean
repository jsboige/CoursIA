/-
  Knots.Slice — Slice knots, Piccirillo, and the smooth/topological dichotomy
  ==========================================================================

  Extracted from the `Knots/Conway.lean` monolith into a dedicated module
  (issue #18397, tranche 1 / option B). This module is the didactic
  culmination of the lake: it consumes `conwayKnot` and the trivial
  Alexander polynomial established in `Knots.Conway`, and states the
  smooth/topological slice dichotomy.

  Course reading order (cf `Knots.lean`): Basic → Reidemeister →
  Invariant → Conway → **Slice** (this file).

  The 4 `sorry`s in this file are known limits, not debts: 4-manifold
  theory (Kirby calculus, Khovanov homology, the Rasmussen s-invariant,
  Freedman surgery) is entirely outside Mathlib. Each statement carries
  the detail of its missing prerequisites.

  Epic #2874, Phase 1 (skeleton only).
  i18n convention #4980: FR canonical twin = `Knots/Slice.lean`.
-/

/-
  English mirror of `Slice.lean` (FR canonical).
  Convention EPIC #4980 (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n) :
  distinct FR + EN sibling files — no inline bilingual block in a single file
  (Option B rejected). The body signatures, proofs, sorry markers, and tactics
  remain byte-identical between the two files (anti-§D byte-identity invariant).
-/

import Knots.Conway_en

open Knots_en

namespace Knots_en

/-! ## 1. Slice knots

Why this section: slice-ness is the 4-dimensional question of knot theory —
it can no longer be read off the diagram (unlike tricolourability or the
Alexander polynomial), but asks for the existence of a disk in B⁴. This is
the notion needed to state the final dichotomy.

A knot K is (smoothly) slice if it bounds a smooth properly embedded
disk D² in the 4-ball B⁴.

A knot is topologically slice if it bounds a locally flat topologically
embedded disk in B⁴.
-/

/-- Being smoothly slice: bounding a smooth properly embedded disk in B⁴. -/
def IsSmoothlySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ smooth), ∂D = K
  -- Reference: Fox & Milnor (1966), Singularities of 2-spheres in 4-space
  -- Mathlib prerequisites:
  --   1. Smooth manifolds (partial: Mathlib has manifolds, not smooth embeddings D²→B⁴)
  --   2. 4-ball (not in Mathlib)
  --   3. Properly embedded surfaces (not in Mathlib)
  --
  -- Digestion (#18397): the definition itself is a `sorry` because the
  -- statement quantifies over objects (smooth embeddings D² → B⁴) that
  -- Mathlib cannot yet name.

/-- Being topologically slice: bounding a locally flat disk in B⁴. -/
def IsTopologicallySlice (k : Knot) : Prop := sorry
  -- Definition: ∃ (D : D² ↪ B⁴ locally flat), ∂D = K
  -- Mathlib prerequisites: same as smoothly slice + topological manifold theory
  --
  -- Digestion (#18397): same reason — the notion "locally flat" and the
  -- TOP category of 4-manifolds do not exist in Mathlib.

/-! ## 2. Piccirillo's theorem (statement only)

The Conway knot is NOT smoothly slice. This was proved by Lisa Piccirillo
in 2018 (published Annals of Mathematics 2020). She was a graduate student
at the time and solved it in under a week.

Strategy (cf. "Getting a handle on the Conway knot", AMS Bulletin 2022):
1. Construct a knot K* that has the same trace as the Conway knot
   (the trace X_K is the 4-manifold obtained by attaching a 2-handle
   to B⁴ along K with 0-framing)
2. Show K* is NOT smoothly slice (via Rasmussen's s-invariant,
   computed from Khovanov homology)
3. By the trace embedding lemma: if Conway is smoothly slice,
   then K* is smoothly slice → contradiction

This is a **magnificent** proof strategy — attacking the problem indirectly
by finding a "companion" knot that shares the same trace.
-/

/-- Piccirillo's theorem: the Conway knot is not smoothly slice. -/
theorem conway_not_smoothly_slice : ¬ IsSmoothlySlice conwayKnot := by
  -- What the proof establishes (#18397): the obstruction to the smooth
  -- disk does not come from Conway's diagram but from its trace companion K*.
  exact sorry
  -- Reference: Piccirillo (2018), arXiv:1808.02923
  -- Published: Annals of Mathematics 191(2), 2020
  -- Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_not_smoothly_slice/
  --
  -- Proof infrastructure needed:
  --   1. Trace X_K of a knot (4-manifold from 0-framed 2-handle)
  --   2. Trace embedding lemma (if K slice ↔ ∂D = K → X_K embeds in B⁴)
  --   3. Piccirillo's companion knot K* with same trace as Conway
  --   4. Rasmussen s-invariant of K* ≠ 0 → K* not slice
  --   5. Khovanov homology (computes s-invariant)
  --
  -- Mathlib prerequisites (ALL missing):
  --   - 4-manifolds, handle decompositions, Kirby calculus
  --   - Khovanov homology
  --   - Rasmussen s-invariant
  --   - Smooth vs topological embeddings
  --   - Freedman's surgery theorem (for topological slice)
  --
  -- Estimated difficulty: **decades** away from formalization in Lean.
  -- This sorry is effectively permanent.

/-! ## 3. Freedman's theorem (statement only)

The Conway knot IS topologically slice, because it has trivial
Alexander polynomial. This is a consequence of Freedman's 1982 theorem:
every knot with trivial Alexander polynomial is topologically slice.

Digestion (#18397): this is where the work of the previous sections pays
off — Conway's trivial Alexander polynomial (established in
`Knots.Conway`) is exactly the hypothesis of Freedman's theorem.
-/

theorem conway_topologically_slice : IsTopologicallySlice conwayKnot := by
  -- What the proof establishes (#18397): Conway satisfies Freedman's
  -- "trivial Alexander" hypothesis, hence is topologically slice.
  exact sorry
  -- Reference: Freedman (1982), The topology of four-dimensional manifolds
  -- Published: Journal of Differential Geometry 17(3)
  -- Lean AI Leaderboard: https://lean-lang.org/eval/problems/conway_knot_topologically_slice/
  --
  -- Proof infrastructure needed:
  --   1. Freedman's full topological surgery machinery in dimension 4
  --   2. Disk embedding theorem
  --   3. Topological h-cobordism theorem
  --
  -- Mathlib prerequisites: essentially ALL of topological 4-manifold theory
  -- This sorry is effectively permanent.

/-! ## 4. The dichotomy

Together, Piccirillo + Freedman give:
  Conway knot: topologically slice BUT NOT smoothly slice.

This is the first explicit example of the smooth/topological dichotomy
for a named knot. It illustrates that smooth structures in dimension 4
are genuinely more restrictive than topological ones.
-/

/-- The Conway knot exhibits the smooth/topological dichotomy:
it is topologically slice but not smoothly slice. -/
theorem conway_dichotomy :
    IsTopologicallySlice conwayKnot ∧ ¬ IsSmoothlySlice conwayKnot := by
  -- Only complete proof in the file (#18397): a gluing of the two bounds —
  -- Freedman provides the left conjunct, Piccirillo the right negation.
  -- No new mathematical ingredient.
  exact ⟨conway_topologically_slice, conway_not_smoothly_slice⟩

end Knots_en
