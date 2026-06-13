/-
  Knots.Reidemeister — Reidemeister moves and knot equivalence
  ============================================================

  The three Reidemeister moves (1927) generate all equivalences between
  knot diagrams. Two diagrams represent the same knot iff one can be
  transformed into the other by a finite sequence of R1, R2, R3 moves
  and planar isotopies.

  Epic #2874, Phase 1.

  Mathlib prerequisites needed:
  - Planar graph theory (for planar isotopy)
  - Finite sequences of moves (combinatorial rewrite systems)
  - The Reidemeister theorem itself is a deep topological result
-/

import Knots.Basic

namespace Knots

/-! ## 1. The three Reidemeister moves

Each move is a local transformation on a knot diagram that preserves
the knot type. They are applied in a small disk, leaving the rest unchanged.
-/

/-- R1 (Twist/Untwist): add or remove a curl in a strand.

A positive curl creates one extra crossing of the same sign.
Diagrammatically:
  |         /\_    |
  |    ↔   /   \   |
  |        \___/   |

**Phase 3 model (symmetric existential).** The full topological R1 move
acts on a small disk of the diagram and is its own inverse (a twist followed
by its untwist is the identity). Rather than model the (delicate) PD-code
surgery (edge relabelling, well-formedness), we define R1 as a *symmetric*
existential: there exists a crossing `c` such that one diagram is obtained
from the other by appending `c` (a combinatorial stand-in for the local
twist/untwist). Symmetry is then immediate by swapping the two diagrams.

This is enough to prove `reidemeister_equiv_symm`. It does NOT yet let us
prove `tricolorable_invariant`, which needs the *semantic* effect of a twist
on edge colorings — that remains Phase 4+.
-/
def Reidemeister1 (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ c : PDCrossing,
    d₂ = { d₁ with crossings := d₁.crossings ++ [c], numEdges := d₁.numEdges + 2 } ∨
    d₁ = { d₂ with crossings := d₂.crossings ++ [c], numEdges := d₂.numEdges + 2 }

/-- R1 is symmetric by construction. -/
theorem Reidemeister1.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister1 d₁ d₂) :
    Reidemeister1 d₂ d₁ := by
  obtain ⟨c, h | h⟩ := h
  · exact ⟨c, Or.inr h⟩
  · exact ⟨c, Or.inl h⟩

/-- R2 (Poke/Unpoke): add or remove two consecutive crossings of opposite sign.

Two parallel strands can pass through each other:
  |   |        /\    |   |
  |   |   ↔   /  \   |   |
  |   |      /    \  |   |
  |   |      \    /  |   |
  |   |       \  /   |   |
  |   |        \/    |   |

**Phase 3 model (symmetric existential).** Analogous to R1: there exist two
crossings `c₁ c₂` such that one diagram is obtained from the other by
appending them.
-/
def Reidemeister2 (d₁ d₂ : KnotDiagram) : Prop :=
  ∃ c₁ c₂ : PDCrossing,
    d₂ = { d₁ with crossings := d₁.crossings ++ [c₁, c₂], numEdges := d₁.numEdges + 4 } ∨
    d₁ = { d₂ with crossings := d₂.crossings ++ [c₁, c₂], numEdges := d₂.numEdges + 4 }

theorem Reidemeister2.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister2 d₁ d₂) :
    Reidemeister2 d₂ d₁ := by
  obtain ⟨c₁, c₂, h | h⟩ := h
  · exact ⟨c₁, c₂, Or.inr h⟩
  · exact ⟨c₁, c₂, Or.inl h⟩

/-- R3 (Slide): move a strand over a crossing.

A strand can slide past a crossing without changing the knot:
  \  |  /      \  |  /
   \ | /        \ | /
    \|/    ↔    / | \
     |          /  |  \
     |         /   |   \

**Phase 3 model (symmetric existential).** R3 preserves the number of
crossings and edges; it only permutes the edge labels at a crossing. Modelled
symmetrically: there exists a witness that either diagram is obtained from the
other by a local relabelling of a single crossing's PD-code, with the same
crossing/edge count.
-/
def Reidemeister3 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.crossings.length = d₂.crossings.length ∧ d₁.numEdges = d₂.numEdges ∧
  (∃ i c, d₂ = { d₁ with crossings := d₁.crossings.set i c } ∨
               d₁ = { d₂ with crossings := d₂.crossings.set i c })

theorem Reidemeister3.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister3 d₁ d₂) :
    Reidemeister3 d₂ d₁ := by
  obtain ⟨hl, he, i, c, h | h⟩ := h
  · exact ⟨hl.symm, he.symm, i, c, Or.inr h⟩
  · exact ⟨hl.symm, he.symm, i, c, Or.inl h⟩

/-! ## 2. Single Reidemeister step

A single step is any of R1, R2, or R3.
-/

inductive ReidemeisterStep (d : KnotDiagram) : KnotDiagram → Prop where
  | r1 {d'} : Reidemeister1 d d' → ReidemeisterStep d d'
  | r2 {d'} : Reidemeister2 d d' → ReidemeisterStep d d'
  | r3 {d'} : Reidemeister3 d d' → ReidemeisterStep d d'

/-! ## 3. Reidemeister equivalence (reflexive transitive closure)

Two diagrams are Reidemeister-equivalent if connected by a finite
sequence of moves (in either direction).
-/

/-- Reflexive transitive closure of Reidemeister steps. -/
inductive ReidemeisterEquiv : KnotDiagram → KnotDiagram → Prop where
  | refl (d : KnotDiagram) : ReidemeisterEquiv d d
  | step {d₁ d₂ : KnotDiagram} :
      ReidemeisterStep d₁ d₂ → ReidemeisterEquiv d₁ d₂
  | trans {d₁ d₂ d₃ : KnotDiagram} :
      ReidemeisterEquiv d₁ d₂ → ReidemeisterEquiv d₂ d₃ → ReidemeisterEquiv d₁ d₃

/-- Symmetry: if d₁ →* d₂ then d₂ →* d₁ (each move has an inverse).

Proof: induction on the RTC. Each base move (R1/R2/R3) is symmetric by the
explicit `*.symm` lemmas above; reflexivity is trivial; transitivity inverts
the two halves and composes.
-/
theorem reidemeister_equiv_symm {d₁ d₂ : KnotDiagram}
    (h : ReidemeisterEquiv d₁ d₂) : ReidemeisterEquiv d₂ d₁ := by
  induction h with
  | refl d => exact ReidemeisterEquiv.refl d
  | step hstep => exact ReidemeisterEquiv.step (by
      cases hstep with
      | r1 h => exact ReidemeisterStep.r1 h.symm
      | r2 h => exact ReidemeisterStep.r2 h.symm
      | r3 h => exact ReidemeisterStep.r3 h.symm)
  | trans _ _ ih₁ ih₂ => exact ReidemeisterEquiv.trans ih₂ ih₁

/-- Equivalence relation. -/
theorem reidemeister_equiv_equivalence : Equivalence (@ReidemeisterEquiv) where
  refl := ReidemeisterEquiv.refl
  symm := reidemeister_equiv_symm
  trans := ReidemeisterEquiv.trans

/-! ## 4. Knot equivalence

Two knots are equivalent if their diagrams are Reidemeister-equivalent.
-/

def KnotEquiv (k₁ k₂ : Knot) : Prop :=
  ReidemeisterEquiv k₁.diagram k₂.diagram

/-! ## 5. Reidemeister's theorem (statement only)

This is the fundamental theorem of knot theory: ambient isotopy of knots
corresponds exactly to Reidemeister moves on diagrams.

**This is a very deep theorem** whose proof requires:
- Piecewise-linear (PL) topology of 3-manifolds
- General position arguments for curves in 3-space
- Alexander's theorem (every knot has a diagram)
- Reference: Reidemeister (1927), Alexander (1928)
- Modern proof: Kauffman (cf. "Knots and Physics")
-/
theorem reidemeister_theorem :
    ∀ (k₁ k₂ : Knot),
      -- Ambient isotopy of the embeddings S¹ → S³
      sorry -- ambient_isotopic k₁ k₂
      ↔
      -- Reidemeister equivalence of diagrams
      KnotEquiv k₁ k₂ := by
  exact sorry
  -- Reference: Reidemeister (1927)
  -- Mathlib prerequisites:
  --   1. PL manifolds (not in Mathlib)
  --   2. Embeddings S¹ → S³ (not in Mathlib)
  --   3. Ambient isotopy (not in Mathlib)
  --   4. General position / transversality (not in Mathlib)
  -- See Kyle Miller's talk (UCSC 2024): long-term project to build these

end Knots
