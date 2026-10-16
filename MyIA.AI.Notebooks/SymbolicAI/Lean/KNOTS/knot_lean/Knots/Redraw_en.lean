/-
  English mirror of `Redraw.lean` (FR canonical, header mono-lingual EN).
  Convention EPIC #4980 (decision ratified 2026-07-04, cf `code-style.md` §Lean i18n) :
  statements are byte-identical to the FR file, only docstrings and comments
  are translated; the `_en` namespace suffix prevents name collisions.
-/
import Knots.Basic_en
import Knots.Reidemeister_en

/-!
# PD code redraw (link 6, EPIC #2874)

A PD code is a presentation: the ORDER of the crossing list and the NAMES of
the edge labels carry no drawing information. Two diagrams differing only by
these two choices depict the same planar drawing. This module formalizes
that relation (`Redraws`) as the building block of link 6: connecting the
redraw certificate of link 5 (`conway_sphereMutate_redraws_kinoshitaTerasaka`,
Conway.lean) to the equivalence required by `AreMutants` (Mutation.lean).

The `Knot` docstring (Basic.lean) names the target equivalence — "modulo
Reidemeister moves AND planar isotopy" — and notes the latter is not yet
connected. `Redraws` is its combinatorial building block. See the FR
canonical file for the full design note (three closing routes).
-/

open Knots_en

namespace Knots_en

/-- Relabel a crossing by a function on edge labels.
Per-crossing version of `relabelCrossings` (Conway.lean, link 5). -/
def PDCrossing.relabel (f : Nat → Nat) (c : PDCrossing) : PDCrossing where
  e1 := f c.e1
  e2 := f c.e2
  e3 := f c.e3
  e4 := f c.e4

/-- Redraw: `d₂` is obtained from `d₁` by a permutation of the crossing list
and an injective relabeling of the edge labels preserving the `edges` window
(hence `numEdges`). Injectivity guarantees that two distinct labels of `d₁`
stay distinct in `d₂` — the minimal condition for the relabeling not to
merge two edges of the drawing. -/
def Redraws (d₁ d₂ : KnotDiagram) : Prop :=
  d₁.numEdges = d₂.numEdges ∧
  ∃ f : Nat → Nat,
    Function.Injective f ∧
    (∀ k ∈ d₁.edges, f k ∈ d₂.edges) ∧
    d₁.crossings.Perm (d₂.crossings.map (PDCrossing.relabel f))

/-- Reflexivity of redraw: identity on labels, identity permutation on the
list. -/
theorem Redraws.refl (d : KnotDiagram) : Redraws d d := by
  refine ⟨rfl, id, Function.injective_id, fun k hk => hk, ?_⟩
  have hmap : d.crossings.map (PDCrossing.relabel id) = d.crossings := by
    induction d.crossings with
    | nil => rfl
    | cons c cs ih =>
      rw [List.map_cons, ih]
      rfl
  rw [hmap]

end Knots_en
