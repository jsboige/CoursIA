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
-/
inductive Reidemeister1 (d : KnotDiagram) : KnotDiagram → Prop where
  | twist (i : Nat) (sign : CrossingType) :
      -- Add a curl at edge i
      -- Result diagram has one more crossing
      sorry → Reidemeister1 d (sorry : KnotDiagram)
  | untwist (c : PDCrossing) :
      -- Remove a curl crossing c
      -- Precondition: c is a crossing where the same strand crosses itself
      sorry → Reidemeister1 d (sorry : KnotDiagram)
      -- Reference: Reidemeister (1927), Elementare Begründung der Knotentheorie

/-- R2 (Poke/Unpoke): add or remove two consecutive crossings of opposite sign.

Two parallel strands can pass through each other:
  |   |        /\    |   |
  |   |   ↔   /  \   |   |
  |   |      /    \  |   |
  |   |      \    /  |   |
  |   |       \  /   |   |
  |   |        \/    |   |
-/
inductive Reidemeister2 (d : KnotDiagram) : KnotDiagram → Prop where
  | poke (i j : Nat) :
      -- Add two crossings of opposite sign at edges i, j
      sorry → Reidemeister2 d (sorry : KnotDiagram)
  | unpoke (c₁ c₂ : PDCrossing) :
      -- Remove two consecutive opposite-sign crossings
      sorry → Reidemeister2 d (sorry : KnotDiagram)
      -- Reference: Reidemeister (1927)

/-- R3 (Slide): move a strand over a crossing.

A strand can slide past a crossing without changing the knot:
  \  |  /      \  |  /
   \ | /        \ | /
    \|/    ↔    / | \
     |          /  |  \
     |         /   |   \
-/
inductive Reidemeister3 (d : KnotDiagram) : KnotDiagram → Prop where
  | slide (c : PDCrossing) :
      -- Slide a strand over crossing c
      sorry → Reidemeister3 d (sorry : KnotDiagram)
      -- Reference: Reidemeister (1927)
      -- The slide move has exactly one non-trivial configuration

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

/-- Symmetry: if d₁ →* d₂ then d₂ →* d₁ (each move has an inverse). -/
theorem reidemeister_equiv_symm {d₁ d₂ : KnotDiagram}
    (h : ReidemeisterEquiv d₁ d₂) : ReidemeisterEquiv d₂ d₁ := by
  exact sorry
  -- TODO: each Reidemeister move is invertible by construction
  -- (twist↔untwist, poke↔unpoke, slide is self-inverse up to R3)
  -- Proof: induction on h, each constructor has an obvious inverse
  -- Mathlib prerequisite: Relation.ReflTransGen.symm (if symmetric base)

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
