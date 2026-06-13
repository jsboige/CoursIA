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
import Mathlib.Logic.Embedding.Basic

namespace Knots

/-! ## 1. The three Reidemeister moves

Each move is a local transformation on a knot diagram that preserves
the knot type. They are applied in a small disk, leaving the rest unchanged.

**Phase 5 model (concrete constructors with edge-renaming).** Each move is
stated as a `Prop`-valued existential conjunction carrying:
  (1) the surgery equation relating `d₁` and `d₂`,
  (2) well-formedness `wf` on *both* diagrams (`KnotDiagram.wf`), and
  (3) an explicit edge-renaming `ρ : Fin d₁.numEdges ↪ Fin d₂.numEdges`
      identifying how the edges of `d₁` map to edges of `d₂`.

The `wf` hypothesis on both sides is the key strengthening over the Phase 3
symmetric-existential model: it excludes the malformed witnesses (a crossing
whose PD labels fall outside `[1, numEdges]`) that refuted
`tricolorable_invariant` — see the certified counter-example diagnosis on
`tricolorable_invariant` in `Invariant.lean`. The edge-renaming `ρ` is what
the transfer lemma (PR2) will use to push a coloring across a move.

The moves are stated with `∃` (not as `structure : Prop`) because a
`Prop`-valued structure cannot project on data fields such as `ρ : Fin _ ↪ Fin _`
or `c : PDCrossing`. Symmetry (`*.symm`) holds for each move: R3 has a purely
structural proof (the surgery disjunction is symmetric); R1/R2 symmetry is
asserted here and discharged by the transfer-lemma machinery in PR2 (the
inverse move exists because a twist/poke followed by its inverse is the
identity).
-/

/-- R1 (Twist/Untwist): add or remove a curl in a strand.

Diagrammatically:
  |         /\_    |
  |    ↔   /   \   |
  |        \___/   |

A curl creates one extra crossing and two extra edges. The move is **bipolar**:
the surgery is stated as a disjunction — either `d₂` is `d₁` with `c` appended
(a twist, `d₂.numEdges = d₁.numEdges + 2`) or `d₁` is `d₂` with `c` appended
(an untwist). The edge-renaming `ρ` points from the smaller diagram's edges to
the larger diagram's edges, identifying the preserved arcs; under a swap of
`d₁`/`d₂` this direction is preserved (the smaller diagram is still the
smaller), which is what makes R1 symmetric by construction.

Well-formedness `wf` on both diagrams forces `c`'s four PD labels to lie in
`[1, (larger).numEdges]` — excluding the malformed witnesses of the Phase 3
model that refuted `tricolorable_invariant`. The renaming `ρ` is the data the
transfer lemma (PR2) pushes a coloring along.
-/
def Reidemeister1 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ c : PDCrossing,
     ∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       d₂ = { d₁ with crossings := d₁.crossings ++ [c], numEdges := d₁.numEdges + 2 } ∨
       d₁ = { d₂ with crossings := d₂.crossings ++ [c], numEdges := d₂.numEdges + 2 })

/-- R1 is symmetric: swapping `d₁`/`d₂` exchanges the two arms of the surgery
disjunction; the `min`/`max`-directed renaming is invariant under the swap
(transported along `Nat.min_comm`/`Nat.max_comm`). -/
theorem Reidemeister1.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister1 d₁ d₂) :
    Reidemeister1 d₂ d₁ := by
  obtain ⟨hwf₁, hwf₂, c, ρ, hsurg | hsurg⟩ := h
  · refine ⟨hwf₂, hwf₁, c, ?_, Or.inr hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)
  · refine ⟨hwf₂, hwf₁, c, ?_, Or.inl hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)

/-- R2 (Poke/Unpoke): add or remove two consecutive crossings of opposite sign.

Two parallel strands can pass through each other:
  |   |        /\    |   |
  |   |   ↔   /  \   |   |
  |   |      /    \  |   |
  |   |      \    /  |   |
  |   |       \  /   |   |
  |   |        \/    |   |

Bipolar like R1: one diagram has four more edges than the other. The renaming
`ρ : Fin (min) ↪ Fin (max)` points from the smaller diagram to the larger.
-/
def Reidemeister2 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.wf = true ∧ d₂.wf = true ∧
  (∃ c₁ c₂ : PDCrossing,
     ∃ ρ : Fin (min d₁.numEdges d₂.numEdges) ↪ Fin (max d₁.numEdges d₂.numEdges),
       d₂ = { d₁ with crossings := d₁.crossings ++ [c₁, c₂], numEdges := d₁.numEdges + 4 } ∨
       d₁ = { d₂ with crossings := d₂.crossings ++ [c₁, c₂], numEdges := d₂.numEdges + 4 })

/-- R2 is symmetric: same construction as R1 (transport along `Nat.min_comm`/
`Nat.max_comm`). -/
theorem Reidemeister2.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister2 d₁ d₂) :
    Reidemeister2 d₂ d₁ := by
  obtain ⟨hwf₁, hwf₂, c₁, c₂, ρ, hsurg | hsurg⟩ := h
  · refine ⟨hwf₂, hwf₁, c₁, c₂, ?_, Or.inr hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)
  · refine ⟨hwf₂, hwf₁, c₁, c₂, ?_, Or.inl hsurg⟩
    exact (Nat.min_comm d₂.numEdges d₁.numEdges ▸
           Nat.max_comm d₂.numEdges d₁.numEdges ▸ ρ)

/-- R3 (Slide): move a strand over a crossing.

A strand can slide past a crossing without changing the knot:
  \  |  /      \  |  /
   \ | /        \ | /
    \|/    ↔    / | \
     |          /  |  \
     |         /   |   \

R3 preserves the number of crossings and edges; it only relabels the edges at
one crossing. The renaming `ρ` is therefore a bijection, expressed here as an
injection `Fin d₁.numEdges ↪ Fin d₂.numEdges` (with equal dimensions).
-/
def Reidemeister3 (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.crossings.length = d₂.crossings.length ∧ d₁.numEdges = d₂.numEdges ∧
  ∃ i c, ∃ ρ : Fin d₁.numEdges ↪ Fin d₂.numEdges,
    (d₂ = { d₁ with crossings := d₁.crossings.set i c } ∨
     d₁ = { d₂ with crossings := d₂.crossings.set i c }) ∧
    d₁.wf = true ∧ d₂.wf = true

/-- R3 is symmetric by construction: the surgery disjunction is symmetric, the
well-formedness hypotheses swap, and since R3 preserves the edge count
(`d₁.numEdges = d₂.numEdges`) the edge-renaming is transportable across. -/
theorem Reidemeister3.symm {d₁ d₂ : KnotDiagram} (h : Reidemeister3 d₁ d₂) :
    Reidemeister3 d₂ d₁ := by
  obtain ⟨hl, he, i, c, ρ, h | h, hwf₁, hwf₂⟩ := h
  · refine ⟨hl.symm, he.symm, i, c, ?_, ?_, hwf₂, hwf₁⟩
    · -- Inverse renaming: transport ρ across the equal edge counts.
      exact he ▸ ρ
    · exact Or.inr h
  · refine ⟨hl.symm, he.symm, i, c, ?_, ?_, hwf₂, hwf₁⟩
    · exact he ▸ ρ
    · exact Or.inl h

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
